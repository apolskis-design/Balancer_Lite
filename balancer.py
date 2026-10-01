import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import os
import sys
import subprocess
import json
import shutil
import copy
import threading
import queue
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from PIL import Image, ImageTk

IMAGE_EXTS = ('.png', '.jpg', '.jpeg', '.gif', '.bmp', '.webp', '.tif', '.tiff', '.avif', '.jfif')
DATA_FILE = 'balancer_data.json'
RESOLUTION_CACHE_FILE = 'resolution_cache.json'
DEFAULT_PROFILE_NAME = 'Default'

# Coarse-grained elimination
MIN_TOTAL_PIXELS = 720 * 1280
SCAN_WORKERS = 8

# Direct tab
DIRECT_BATCH_SIZE = 100
DIRECT_THUMB = 165
DIRECT_COLS = 4
MOVER_PANEL_WIDTH = 380

# ----------------------------------------------------------------------
# Dark theme palette
# ----------------------------------------------------------------------
DARK_BG = '#1e1e1e'
DARK_BG_ALT = '#252526'
DARK_BG_LIGHT = '#3c3c3c'
DARK_FG = '#e6e6e6'
DARK_SELECT = '#0a5a9c'
DARK_ENTRY_BG = '#2d2d2d'
DARK_TREE_BG = '#252526'

PBAR_BG = '#123a5c'
PBAR_BTN_BG = '#0a5a9c'
PBAR_BTN_ACTIVE = '#0d6fc4'
PBAR_NEW_BG = '#2fb344'
PBAR_NEW_ACTIVE = '#249236'
PBAR_DEL_BG = '#b3402f'
PBAR_DEL_ACTIVE = '#8c3125'

ACCEPT_COLOR = '#2fb344'
REJECT_COLOR = '#b3402f'
MOVE_COLOR = '#e8a317'
NEUTRAL_COLOR = '#3c3c3c'
QUEUE_COLOR = '#ff9f43'
REPLACER_COLOR = '#9b59b6'


class BalancerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Dataset Balancer")
        self.root.geometry("1500x980")

        # --- GLOBAL / SHARED data -------------------------------------
        self.categories = {}
        self.image_tags = {}        # kept only so existing caption data is preserved
        self.known_tags = []
        self.tag_categories = {}

        # --- PROFILE-SCOPED data --------------------------------------
        self.dataset = {}
        self.blacklist = {}
        self.forced_blacklist = {}
        self.auto_forced_added = {}
        self.auto_resolve_added = {}

        self.manual_target = None
        self.auto_include = True
        self.coarse_elimination = False

        self.selected_category = None

        # Direct tab state
        self.direct_current_category = None
        self.direct_batch = []
        self.direct_status = {}
        self.direct_cells = {}
        self.direct_mode = 'select'
        self.direct_page = 0
        self.direct_pool = []
        self.direct_state = {}  # Session-only {category: {path: status}} (NOT persisted)
        self.direct_search_var = tk.StringVar()
        self.direct_order_var = tk.StringVar(value='Interleaved')

        # File mover state
        self.mover_target_folder = None
        self.mover_tree_nodes = {}
        self.replacer_mode = False
        self.scripts_dir = os.path.dirname(os.path.abspath(__file__))
        self.excluded_subfolders = set()

        # Queued moves: {old_path: {'dest': folder, 'category': cat, 'replacer': bool}}
        # Nothing touches the disk until "Process All Selections" runs.
        self.pending_moves = {}

        # Profiles
        self.profiles = {}
        self.current_profile_name = DEFAULT_PROFILE_NAME

        self._image_cache = {}
        self._thumb_cache = {}

        # Coarse elimination internals
        self._coarse_cache = {}
        self._raw_counts_cache = None
        self._resolution_cache = {}
        self._resolution_scan_in_progress = False
        self._scan_cancelled = False
        self._scan_dialog = None
        self._scan_queue = None
        self._scan_processed = 0
        self._scan_total = 0
        self._scan_start_time = 0

        # Detached viewer
        self.aspect_window = None

        self.load_resolution_cache()
        self.load_data()

        self.setup_dark_theme()

        self.root.grid_rowconfigure(0, weight=0)
        self.root.grid_rowconfigure(1, weight=1)
        self.root.grid_columnconfigure(0, weight=1)

        self.build_profile_bar()

        self.notebook = ttk.Notebook(root)
        self.notebook.grid(row=1, column=0, sticky='nsew')

        self.directory_frame = ttk.Frame(self.notebook)
        self.direct_frame = ttk.Frame(self.notebook)
        self.stats_frame = ttk.Frame(self.notebook)

        self.notebook.add(self.directory_frame, text='Directory Builder')
        self.notebook.add(self.direct_frame, text='Direct')
        self.notebook.add(self.stats_frame, text='File Stats')

        self.build_directory_tab()
        self.build_direct_tab()
        self.build_stats_tab()

        self.notebook.bind('<<NotebookTabChanged>>', self.on_tab_changed)
        self.root.protocol('WM_DELETE_WINDOW', self.on_close)

        if self.coarse_elimination:
            self.root.after(400, lambda: self.start_coarse_resolution_scan(manual=False))

    # ==================================================================
    # Theme
    # ==================================================================
    def setup_dark_theme(self):
        self.root.configure(bg=DARK_BG)
        style = ttk.Style(self.root)
        try:
            style.theme_use('clam')
        except Exception:
            pass

        style.configure('.', background=DARK_BG, foreground=DARK_FG,
                        fieldbackground=DARK_ENTRY_BG, bordercolor=DARK_BG_LIGHT,
                        lightcolor=DARK_BG_LIGHT, darkcolor=DARK_BG_LIGHT,
                        troughcolor=DARK_BG_LIGHT, selectbackground=DARK_SELECT,
                        selectforeground='white')

        style.configure('TFrame', background=DARK_BG)
        style.configure('TLabel', background=DARK_BG, foreground=DARK_FG)
        style.configure('TLabelframe', background=DARK_BG, foreground=DARK_FG)
        style.configure('TLabelframe.Label', background=DARK_BG, foreground=DARK_FG)

        style.configure('TButton', background=DARK_BG_LIGHT, foreground=DARK_FG,
                        bordercolor=DARK_BG_LIGHT, focuscolor=DARK_BG_LIGHT)
        style.map('TButton',
                  background=[('active', DARK_SELECT), ('pressed', DARK_SELECT)],
                  foreground=[('active', 'white')])

        style.configure('TCheckbutton', background=DARK_BG, foreground=DARK_FG)
        style.map('TCheckbutton', background=[('active', DARK_BG)],
                  foreground=[('active', DARK_FG)])
        style.configure('TRadiobutton', background=DARK_BG, foreground=DARK_FG)
        style.map('TRadiobutton', background=[('active', DARK_BG)],
                  foreground=[('active', DARK_FG)])

        style.configure('TEntry', fieldbackground=DARK_ENTRY_BG, foreground=DARK_FG,
                        insertcolor=DARK_FG)
        style.configure('TCombobox', fieldbackground=DARK_ENTRY_BG, foreground=DARK_FG,
                        background=DARK_BG_LIGHT, arrowcolor=DARK_FG)
        style.map('TCombobox', fieldbackground=[('readonly', DARK_ENTRY_BG)])

        style.configure('TNotebook', background=DARK_BG, borderwidth=0)
        style.configure('TNotebook.Tab', background=DARK_BG_LIGHT, foreground=DARK_FG,
                        padding=(12, 6))
        style.map('TNotebook.Tab',
                  background=[('selected', DARK_SELECT)],
                  foreground=[('selected', 'white')])

        style.configure('Treeview', background=DARK_TREE_BG, foreground=DARK_FG,
                        fieldbackground=DARK_TREE_BG, bordercolor=DARK_BG_LIGHT)
        style.map('Treeview', background=[('selected', DARK_SELECT)],
                  foreground=[('selected', 'white')])
        style.configure('Treeview.Heading', background=DARK_BG_LIGHT, foreground=DARK_FG)
        style.map('Treeview.Heading', background=[('active', DARK_SELECT)])

        style.configure('TProgressbar', background='#4da6ff', troughcolor=DARK_BG_LIGHT)
        style.configure('TScrollbar', background=DARK_BG_LIGHT, troughcolor=DARK_BG,
                        arrowcolor=DARK_FG)
        style.configure('TPanedwindow', background=DARK_BG)

        style.configure("Accent.TButton", background='#2fb344', foreground='white')
        style.map("Accent.TButton", background=[('active', '#249236')])
        style.configure("Success.TButton", background='#1f8f55', foreground='white')
        style.map("Success.TButton", background=[('active', '#17703f')])
        style.configure("Warning.TButton", background='#e8a317', foreground='white')
        style.map("Warning.TButton", background=[('active', '#c48812')])
        style.configure("Danger.TButton", background='#b3402f', foreground='white')
        style.map("Danger.TButton", background=[('active', '#8c3125')])

    def style_tk_listbox(self, lb):
        lb.configure(bg=DARK_ENTRY_BG, fg=DARK_FG, selectbackground=DARK_SELECT,
                     selectforeground='white', highlightthickness=1,
                     highlightbackground=DARK_BG_LIGHT, highlightcolor=DARK_SELECT,
                     borderwidth=0)

    def _bind_mousewheel(self, canvas):
        def on_enter(_e):
            canvas.bind_all('<MouseWheel>',
                            lambda ev: canvas.yview_scroll(int(-ev.delta / 120), 'units'))

        def on_leave(_e):
            canvas.unbind_all('<MouseWheel>')

        canvas.bind('<Enter>', on_enter)
        canvas.bind('<Leave>', on_leave)

    # ==================================================================
    # Profile bar
    # ==================================================================
    def build_profile_bar(self):
        bar = tk.Frame(self.root, bg=PBAR_BG, bd=0, highlightthickness=0)
        bar.grid(row=0, column=0, sticky='ew')

        tk.Label(bar, text="PROFILE:", bg=PBAR_BG, fg='white',
                 font=('Arial', 11, 'bold')).pack(side='left', padx=(12, 8), pady=10)

        self.profile_var = tk.StringVar(value=self.current_profile_name)
        self.profile_menu = tk.OptionMenu(bar, self.profile_var, self.current_profile_name)
        self.profile_menu.config(bg=PBAR_BTN_BG, fg='white', activebackground=PBAR_BTN_ACTIVE,
                                 activeforeground='white', highlightthickness=0,
                                 font=('Arial', 10), width=22, relief='flat', bd=0)
        self.profile_menu['menu'].config(bg=DARK_ENTRY_BG, fg='white',
                                         activebackground=PBAR_BTN_ACTIVE,
                                         activeforeground='white')
        self.profile_menu.pack(side='left', padx=(0, 10), pady=8)

        def mkbtn(text, cmd, bg, active_bg):
            b = tk.Button(bar, text=text, command=cmd, bg=bg, fg='white',
                          activebackground=active_bg, activeforeground='white',
                          relief='flat', bd=0, padx=10, pady=4, font=('Arial', 9, 'bold'))
            b.pack(side='left', padx=4, pady=8)
            return b

        mkbtn("+ New Profile", self.prompt_new_profile, PBAR_NEW_BG, PBAR_NEW_ACTIVE)
        mkbtn("Duplicate", self.prompt_duplicate_profile, PBAR_BTN_BG, PBAR_BTN_ACTIVE)
        mkbtn("Rename", self.prompt_rename_profile, PBAR_BTN_BG, PBAR_BTN_ACTIVE)
        mkbtn("Delete", self.prompt_delete_profile, PBAR_DEL_BG, PBAR_DEL_ACTIVE)

        self.profile_info_label = tk.Label(bar, text="", bg=PBAR_BG, fg='#9fd3ff',
                                           font=('Arial', 9))
        self.profile_info_label.pack(side='left', padx=(14, 0))

        self.refresh_profile_selector()

    def refresh_profile_selector(self):
        names = sorted(self.profiles.keys(), key=str.lower)
        menu = self.profile_menu['menu']
        menu.delete(0, 'end')
        for name in names:
            menu.add_command(label=name, command=lambda n=name: self._on_profile_menu_selected(n))
        self.profile_var.set(self.current_profile_name)
        self.profile_info_label.config(
            text=f"(folders & captions are shared across all {len(names)} profile(s))")

    def _on_profile_menu_selected(self, name):
        if name and name != self.current_profile_name:
            self.switch_profile(name)
        else:
            self.profile_var.set(self.current_profile_name)

    def _blank_profile(self):
        return {
            'dataset': {},
            'blacklist': {},
            'forced_blacklist': {},
            'auto_forced_added': {},
            'auto_resolve_added': {},
            'manual_target': None,
            'auto_include': True,
            'coarse_elimination': False,
            'direct_state': {'direct_category': None},
        }

    def _capture_active_profile_dict(self):
        # Merge into the existing dict so legacy keys (image_tiers, sort_state, ...)
        # already stored in the data file are preserved rather than silently dropped.
        prof = self.profiles.get(self.current_profile_name)
        if not isinstance(prof, dict):
            prof = {}
        prof.update({
            'dataset': self.dataset,
            'blacklist': self.blacklist,
            'forced_blacklist': self.forced_blacklist,
            'auto_forced_added': self.auto_forced_added,
            'auto_resolve_added': self.auto_resolve_added,
            'manual_target': self.manual_target,
            'auto_include': self.auto_include,
            'coarse_elimination': self.coarse_elimination,
            'direct_state': {'direct_category': self.direct_current_category},
        })
        return prof

    def _activate_profile(self, name):
        profile = self.profiles.get(name)
        if profile is None:
            profile = self._blank_profile()
            self.profiles[name] = profile

        self.dataset = profile.get('dataset', {})
        self.blacklist = profile.get('blacklist', {})
        self.forced_blacklist = profile.get('forced_blacklist', {})
        self.auto_forced_added = profile.get('auto_forced_added', {})
        self.auto_resolve_added = profile.get('auto_resolve_added', {})
        self.manual_target = profile.get('manual_target', None)
        self.auto_include = profile.get('auto_include', True)
        self.coarse_elimination = profile.get('coarse_elimination', False)

        self._coarse_cache = {}
        self._raw_counts_cache = None

        direct_state = profile.get('direct_state', {}) or {}
        self.direct_current_category = direct_state.get('direct_category')
        self.direct_batch = []
        self.direct_status = {}
        self.direct_cells = {}
        self.direct_page = 0

        for cat in self.categories:
            self.dataset.setdefault(cat, [])
            self.blacklist.setdefault(cat, [])
            self.forced_blacklist.setdefault(cat, [])
            self.auto_forced_added.setdefault(cat, [])
            self.auto_resolve_added.setdefault(cat, [])

        self.current_profile_name = name

    def switch_profile(self, name):
        if name not in self.profiles or name == self.current_profile_name:
            return
        self.profiles[self.current_profile_name] = self._capture_active_profile_dict()
        self._activate_profile(name)
        self.save_data(silent=True)
        self.refresh_all_views()
        self.refresh_profile_selector()
        if self.coarse_elimination:
            self.start_coarse_resolution_scan(manual=False)

    def prompt_new_profile(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("New Profile")
        dialog.geometry("380x190")
        dialog.configure(bg=DARK_BG)
        dialog.transient(self.root)
        dialog.grab_set()

        ttk.Label(dialog, text="New profile name:").pack(pady=(14, 4))
        entry = ttk.Entry(dialog, width=34)
        entry.pack(pady=4)
        entry.focus_set()

        ttk.Label(dialog, text="Reuses your existing folders/categories.\n"
                               "Captions/tags are kept. Selections start empty.",
                  font=('Arial', 8), foreground='#999999', justify='center').pack(pady=(8, 4))

        def create():
            name = entry.get().strip()
            if not name:
                messagebox.showwarning("Warning", "Please enter a profile name!", parent=dialog)
                return
            if name in self.profiles:
                messagebox.showwarning("Warning", "That profile already exists!", parent=dialog)
                return
            self.profiles[self.current_profile_name] = self._capture_active_profile_dict()
            self.profiles[name] = self._blank_profile()
            self._activate_profile(name)
            self.save_data(silent=True)
            self.refresh_all_views()
            self.refresh_profile_selector()
            dialog.destroy()

        ttk.Button(dialog, text="Create & Switch To It", command=create).pack(pady=12)
        entry.bind('<Return>', lambda e: create())

    def prompt_duplicate_profile(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Duplicate Profile")
        dialog.geometry("360x150")
        dialog.configure(bg=DARK_BG)
        dialog.transient(self.root)
        dialog.grab_set()

        ttk.Label(dialog, text=f"Duplicate '{self.current_profile_name}' as:").pack(pady=(14, 4))
        entry = ttk.Entry(dialog, width=34)
        entry.pack(pady=4)
        entry.focus_set()

        def create():
            name = entry.get().strip()
            if not name:
                messagebox.showwarning("Warning", "Please enter a profile name!", parent=dialog)
                return
            if name in self.profiles:
                messagebox.showwarning("Warning", "That profile already exists!", parent=dialog)
                return
            self.profiles[self.current_profile_name] = self._capture_active_profile_dict()
            self.profiles[name] = copy.deepcopy(self.profiles[self.current_profile_name])
            self._activate_profile(name)
            self.save_data(silent=True)
            self.refresh_all_views()
            self.refresh_profile_selector()
            dialog.destroy()

        ttk.Button(dialog, text="Duplicate & Switch To It", command=create).pack(pady=12)
        entry.bind('<Return>', lambda e: create())

    def prompt_rename_profile(self):
        old_name = self.current_profile_name
        new_name = simpledialog.askstring("Rename Profile", "New name:",
                                          initialvalue=old_name, parent=self.root)
        if not new_name:
            return
        new_name = new_name.strip()
        if not new_name or new_name == old_name:
            return
        if new_name in self.profiles:
            messagebox.showwarning("Warning", "That profile already exists!")
            return
        self.profiles[old_name] = self._capture_active_profile_dict()
        self.profiles[new_name] = self.profiles.pop(old_name)
        self.current_profile_name = new_name
        self.save_data(silent=True)
        self.refresh_profile_selector()

    def prompt_delete_profile(self):
        if len(self.profiles) <= 1:
            messagebox.showwarning("Warning", "Can't delete the only remaining profile.")
            return
        name = self.current_profile_name
        if not messagebox.askyesno("Delete Profile",
                                   f"Delete profile '{name}'?\n\n"
                                   f"Only its selections/rejections are removed. "
                                   f"Folders and captions are untouched."):
            return
        del self.profiles[name]
        fallback = sorted(self.profiles.keys(), key=str.lower)[0]
        self._activate_profile(fallback)
        self.save_data(silent=True)
        self.refresh_all_views()
        self.refresh_profile_selector()

    def refresh_all_views(self):
        self.update_category_listbox()
        if hasattr(self, 'coarse_var'):
            self.coarse_var.set(self.coarse_elimination)
        if hasattr(self, 'stats_display_frame'):
            self.update_stats_view()
        if hasattr(self, 'mover_tree'):
            self.refresh_mover_tree()
        if self._active_tab() == 'Direct':
            self.refresh_direct_category_list()
            self.direct_load_batch()

    def _active_tab(self):
        try:
            return self.notebook.tab(self.notebook.select(), 'text')
        except Exception:
            return ''

    # ==================================================================
    # Scanning / counting
    # ==================================================================
    def get_raw_images_from_category(self, category, force_rescan=False):
        if not force_rescan and category in self._image_cache:
            return self._image_cache[category]
        images = []
        seen = set()
        for folder in self.categories.get(category, []):
            if os.path.isdir(folder):
                try:
                    for file in sorted(os.listdir(folder)):
                        if file.lower().endswith(IMAGE_EXTS):
                            path = os.path.join(folder, file)
                            if path not in seen:
                                seen.add(path)
                                images.append(path)
                except Exception as e:
                    print(f"Error scanning {folder}: {e}")
        self._image_cache[category] = images
        return images

    def _stat_sig(self, path):
        try:
            st = os.stat(path)
            return [st.st_mtime, st.st_size]
        except Exception:
            return None

    def _get_cached_resolution(self, path):
        entry = self._resolution_cache.get(path)
        if not entry:
            return None
        sig = self._stat_sig(path)
        if sig is None or entry.get('sig') != sig:
            return None
        return (entry.get('w', 0), entry.get('h', 0))

    def _read_resolution_uncached(self, path):
        try:
            with Image.open(path) as img:
                return img.size
        except Exception:
            return (0, 0)

    def is_low_resolution(self, path):
        cached = self._get_cached_resolution(path)
        if cached is None:
            w, h = self._read_resolution_uncached(path)
            if w == 0 or h == 0:
                return False
            return (w * h) < MIN_TOTAL_PIXELS
        w, h = cached
        return (w * h) < MIN_TOTAL_PIXELS

    def _get_raw_counts_all(self):
        if self._raw_counts_cache is None:
            self._raw_counts_cache = {c: len(self.get_raw_images_from_category(c))
                                      for c in self.categories}
        return self._raw_counts_cache

    def _category_qualifies_for_elimination(self, category):
        counts = self._get_raw_counts_all()
        nonzero = [v for v in counts.values() if v > 0]
        if not nonzero:
            return False
        raw_min = min(nonzero)
        this_count = counts.get(category, 0)
        return raw_min > 0 and this_count > raw_min * 2

    def _compute_coarse_filtered(self, category, raw_list):
        if not self._category_qualifies_for_elimination(category):
            return raw_list
        return [p for p in raw_list if not self.is_low_resolution(p)]

    def get_all_images_from_category(self, category, force_rescan=False):
        raw = self.get_raw_images_from_category(category, force_rescan=force_rescan)
        if force_rescan:
            self._coarse_cache = {}
            self._raw_counts_cache = None
        if not self.coarse_elimination:
            return raw
        if category in self._coarse_cache:
            return self._coarse_cache[category]
        filtered = self._compute_coarse_filtered(category, raw)
        self._coarse_cache[category] = filtered
        return filtered

    def _collect_pending_resolution_targets(self):
        pending = []
        for cat in self.categories:
            if not self._category_qualifies_for_elimination(cat):
                continue
            for p in self.get_raw_images_from_category(cat):
                if self._get_cached_resolution(p) is None:
                    pending.append(p)
        return pending

    def toggle_coarse_elimination(self):
        self.coarse_elimination = bool(self.coarse_var.get())
        self._coarse_cache = {}
        self._raw_counts_cache = None
        self.save_data(silent=True)
        self.update_stats_view()
        self.update_category_listbox()
        if self.coarse_elimination:
            self.start_coarse_resolution_scan(manual=False)

    def start_coarse_resolution_scan(self, manual=False):
        if self._resolution_scan_in_progress:
            if manual:
                messagebox.showinfo("Scan Running", "A resolution scan is already in progress.")
            return
        if not self.coarse_elimination:
            if manual:
                messagebox.showinfo("Coarse Elimination", "Enable coarse-grained elimination first.")
            return

        pending = self._collect_pending_resolution_targets()
        if not pending:
            self._coarse_cache = {}
            self.update_stats_view()
            self.update_category_listbox()
            if manual:
                messagebox.showinfo("Scan", "Nothing to scan — all relevant resolutions are cached.")
            return

        total = len(pending)
        self._resolution_scan_in_progress = True
        self._scan_cancelled = False
        self._scan_processed = 0
        self._scan_total = total
        self._scan_start_time = time.time()
        self._scan_queue = queue.Queue()

        self._scan_dialog = self._build_scan_progress_dialog(total)

        def worker():
            with ThreadPoolExecutor(max_workers=SCAN_WORKERS) as executor:
                futures = {}
                for p in pending:
                    if self._scan_cancelled:
                        break
                    futures[executor.submit(self._read_resolution_uncached, p)] = p
                for fut in as_completed(futures):
                    p = futures[fut]
                    try:
                        w, h = fut.result()
                    except Exception:
                        w, h = 0, 0
                    self._scan_queue.put((p, w, h))
                    if self._scan_cancelled:
                        break
            self._scan_queue.put(None)

        threading.Thread(target=worker, daemon=True).start()
        self.root.after(80, self._poll_scan_queue)

    def _build_scan_progress_dialog(self, total):
        dlg = tk.Toplevel(self.root)
        dlg.title("Scanning Image Resolutions")
        dlg.geometry("440x175")
        dlg.configure(bg=DARK_BG)
        dlg.transient(self.root)
        dlg.protocol('WM_DELETE_WINDOW', self._cancel_scan)
        ttk.Label(dlg, text="Checking resolutions for coarse-grained elimination...",
                  font=('Arial', 10, 'bold')).pack(pady=(16, 6))
        dlg._status_label = ttk.Label(dlg, text=f"0 / {total} images")
        dlg._status_label.pack()
        dlg._bar = ttk.Progressbar(dlg, length=380, mode='determinate', maximum=total or 1)
        dlg._bar.pack(pady=10)
        dlg._eta_label = ttk.Label(dlg, text="Estimating time remaining...",
                                   font=('Arial', 9), foreground='#999999')
        dlg._eta_label.pack()
        ttk.Button(dlg, text="Cancel", command=self._cancel_scan).pack(pady=10)
        return dlg

    def _cancel_scan(self):
        self._scan_cancelled = True

    def _poll_scan_queue(self):
        finished = False
        try:
            while True:
                item = self._scan_queue.get_nowait()
                if item is None:
                    finished = True
                    break
                p, w, h = item
                self._resolution_cache[p] = {'sig': self._stat_sig(p), 'w': w, 'h': h}
                self._scan_processed += 1
        except queue.Empty:
            pass

        if self._scan_dialog is not None and self._scan_dialog.winfo_exists():
            elapsed = time.time() - self._scan_start_time
            rate = self._scan_processed / elapsed if elapsed > 0.01 else 0
            remaining = (self._scan_total - self._scan_processed) / rate if rate > 0 else None
            self._scan_dialog._bar['value'] = self._scan_processed
            self._scan_dialog._status_label.config(
                text=f"{self._scan_processed} / {self._scan_total} images")
            if remaining is not None and remaining >= 0:
                m, s = divmod(int(remaining), 60)
                self._scan_dialog._eta_label.config(text=f"Estimated time remaining: {m}m {s}s")

        if finished or self._scan_cancelled:
            self._finish_scan()
            return
        self.root.after(80, self._poll_scan_queue)

    def _finish_scan(self):
        cancelled = self._scan_cancelled
        processed = self._scan_processed
        self._resolution_scan_in_progress = False
        if self._scan_dialog is not None and self._scan_dialog.winfo_exists():
            self._scan_dialog.destroy()
        self._scan_dialog = None

        self.save_resolution_cache()
        self._coarse_cache = {}
        self.update_stats_view()
        self.update_category_listbox()

        if cancelled:
            messagebox.showwarning("Scan Cancelled",
                                   f"Stopped after {processed} image(s). Run the scan again to finish.")
        else:
            messagebox.showinfo("Scan Complete",
                                f"Scanned {processed} image(s). Coarse elimination updated.")

    def rescan_all(self):
        self._image_cache = {}
        self._coarse_cache = {}
        self._raw_counts_cache = None
        for cat in self.categories:
            self.get_all_images_from_category(cat, force_rescan=True)

    def get_target(self):
        if self.manual_target:
            return int(self.manual_target)
        counts = [len(self.get_all_images_from_category(c)) for c in self.categories]
        counts = [c for c in counts if c > 0]
        return min(counts) if counts else 0

    def is_forced_category(self, category):
        target = self.get_target()
        total = len(self.get_all_images_from_category(category))
        return target > 0 and 0 < total <= target

    # ==================================================================
    # Folder-balanced ordering
    # ==================================================================
    def _folder_of(self, path):
        return os.path.dirname(path)

    def _group_paths_by_folder(self, paths):
        groups = {}
        for p in paths:
            groups.setdefault(self._folder_of(p), []).append(p)
        return groups

    def _interleave_by_folder(self, paths):
        if not paths:
            return []
        groups = self._group_paths_by_folder(paths)
        folder_names = sorted(groups.keys())
        for f in folder_names:
            groups[f].sort(key=lambda p: os.path.basename(p))
        pointers = {f: 0 for f in folder_names}
        ordered = []
        remaining = len(paths)
        while remaining > 0:
            for f in folder_names:
                p = pointers[f]
                if p < len(groups[f]):
                    ordered.append(groups[f][p])
                    pointers[f] = p + 1
                    remaining -= 1
        return ordered

    def balanced_sample(self, paths, k):
        return self._interleave_by_folder(paths)[:max(0, k)]

    # ==================================================================
    # FILE MOVER — disk move + bookkeeping remap
    # ==================================================================
    def _norm(self, p):
        return os.path.normcase(os.path.abspath(p))

    def _categories_for_folder(self, folder):
        target = self._norm(folder)
        out = []
        for cat, folders in self.categories.items():
            for f in folders:
                if self._norm(f) == target:
                    out.append(cat)
                    break
        return out

    def _remap_paths(self, mapping):
        """Rewrite every stored reference {old_path: new_path} in one pass, across ALL
        profiles, the active profile, caption data, and the resolution/thumbnail caches."""
        if not mapping:
            return
        list_keys = ('dataset', 'blacklist', 'forced_blacklist',
                     'auto_forced_added', 'auto_resolve_added')

        def remap_lists(d):
            for key, lst in d.items():
                if any(p in mapping for p in lst):
                    d[key] = [mapping.get(p, p) for p in lst]

        for pdata in self.profiles.values():
            for key in list_keys:
                d = pdata.get(key)
                if isinstance(d, dict):
                    remap_lists(d)
        for d in (self.dataset, self.blacklist, self.forced_blacklist,
                  self.auto_forced_added, self.auto_resolve_added):
            remap_lists(d)

        for old, new in mapping.items():
            if old in self.image_tags:
                self.image_tags[new] = self.image_tags.pop(old)
            entry = self._resolution_cache.pop(old, None)
            if entry is not None:
                entry['sig'] = self._stat_sig(new)
                self._resolution_cache[new] = entry

        for k in [k for k in self._thumb_cache if k[0] in mapping]:
            self._thumb_cache[(mapping[k[0]], k[1])] = self._thumb_cache.pop(k)

        # NOTE: direct_state is intentionally NOT remapped. The old path keeps a 'moved'
        # entry so the Direct grid shows a placeholder and pagination doesn't shift.

    def _move_file_on_disk(self, old_path, dest_folder, create_dest=False):
        """Physically move one file. Returns (new_path, error, retryable)."""
        if not old_path or not os.path.isfile(old_path):
            return None, "Source file no longer exists on disk.", False
        if not dest_folder:
            return None, "No destination folder.", False
        if not os.path.isdir(dest_folder):
            if create_dest:
                try:
                    os.makedirs(dest_folder, exist_ok=True)
                except Exception as e:
                    return None, f"Could not create folder: {e}", True
            else:
                return None, "Target folder does not exist.", True
        if self._norm(os.path.dirname(old_path)) == self._norm(dest_folder):
            return None, "Already in the target folder.", False

        base = os.path.basename(old_path)
        stem, ext = os.path.splitext(base)
        candidate = os.path.join(dest_folder, base)
        i = 1
        while os.path.exists(candidate):
            candidate = os.path.join(dest_folder, f"{stem}_{i}{ext}")
            i += 1
        try:
            shutil.move(old_path, candidate)
        except Exception as e:
            return None, f"Move failed: {e}", True
        return candidate, None, False

    def _build_move_progress_dialog(self, total):
        dlg = tk.Toplevel(self.root)
        dlg.title("Moving files")
        dlg.geometry("440x120")
        dlg.configure(bg=DARK_BG)
        dlg.transient(self.root)
        dlg.protocol('WM_DELETE_WINDOW', lambda: None)
        dlg._label = ttk.Label(dlg, text=f"0 / {total}")
        dlg._label.pack(pady=(18, 6))
        dlg._bar = ttk.Progressbar(dlg, length=380, mode='determinate', maximum=max(1, total))
        dlg._bar.pack(pady=6)
        dlg.update()
        try:
            dlg.grab_set()
        except tk.TclError:
            pass
        return dlg

    def _execute_pending_moves(self):
        """Physically perform EVERY queued move (all categories, replacer + armed-folder).
        Runs on the main thread. Returns a summary dict."""
        summary = {'moved': 0, 'replacer': 0, 'mover': 0, 'failed': []}
        moves = dict(self.pending_moves)
        if not moves:
            return summary

        total = len(moves)
        dlg = self._build_move_progress_dialog(total)
        mapping = {}
        affected = set()
        try:
            for i, (old, info) in enumerate(moves.items(), 1):
                dest = info.get('dest')
                is_replacer = bool(info.get('replacer'))
                try:
                    new, err, retry = self._move_file_on_disk(old, dest, create_dest=is_replacer)
                except Exception as e:
                    new, err, retry = None, f"Move failed: {e}", True

                if err is None:
                    mapping[old] = new
                    self.pending_moves.pop(old, None)
                    cat = info.get('category')
                    if cat:
                        self.direct_state.setdefault(cat, {})[old] = 'moved'
                    affected.update(self._categories_for_folder(os.path.dirname(old)))
                    affected.update(self._categories_for_folder(dest))
                    summary['moved'] += 1
                    summary['replacer' if is_replacer else 'mover'] += 1
                else:
                    summary['failed'].append((old, err))
                    if not retry:
                        self.pending_moves.pop(old, None)

                dlg._bar['value'] = i
                dlg._label.config(text=f"{i} / {total}   {os.path.basename(old)}")
                dlg.update()
        finally:
            try:
                dlg.grab_release()
            except tk.TclError:
                pass
            dlg.destroy()

        if mapping:
            self._remap_paths(mapping)
            for cat in affected:
                self._image_cache.pop(cat, None)
            self._coarse_cache = {}
            self._raw_counts_cache = None
            self.save_data(silent=True)
            self.save_resolution_cache()

        self._update_queue_label()
        return summary

    # ==================================================================
    # Provenance / auto pipeline
    # ==================================================================
    def _untrack_auto(self, category, path):
        for d in (self.auto_forced_added, self.auto_resolve_added):
            lst = d.get(category)
            if lst and path in lst:
                lst.remove(path)

    def reconcile_forced_demotions(self):
        changed = False
        for cat in list(self.categories.keys()):
            auto_list = self.auto_forced_added.get(cat)
            if not auto_list:
                continue
            if self.is_forced_category(cat):
                continue
            auto_set = set(auto_list)
            bucket = self.dataset.get(cat, [])
            remaining = [p for p in bucket if p in auto_set]
            if remaining:
                self.dataset[cat] = [p for p in bucket if p not in auto_set]
                changed = True
            self.auto_forced_added[cat] = []
        if changed:
            self.save_data(silent=True)
        return changed

    def reconcile_resolve_overflow(self):
        target = self.get_target()
        if target <= 0:
            return False
        changed = False
        for cat in list(self.categories.keys()):
            auto_list = self.auto_resolve_added.get(cat)
            if not auto_list:
                continue
            images = self.get_all_images_from_category(cat)
            img_set = set(images)
            auto_set = set(p for p in auto_list if p in img_set)
            bucket = self.dataset.get(cat, [])
            selected = [p for p in bucket if p in img_set]
            over = len(selected) - target
            if over <= 0:
                self.auto_resolve_added[cat] = list(auto_set)
                continue
            removable = [p for p in selected if p in auto_set]
            to_remove = removable[:over]
            if to_remove:
                remove_set = set(to_remove)
                self.dataset[cat] = [p for p in bucket if p not in remove_set]
                for p in to_remove:
                    auto_set.discard(p)
                changed = True
            self.auto_resolve_added[cat] = list(auto_set)
        if changed:
            self.save_data(silent=True)
        return changed

    def run_auto_pipeline(self):
        demoted = self.reconcile_forced_demotions()
        overflowed = self.reconcile_resolve_overflow()
        added, touched = self.auto_include_forced_categories()
        resolved_added, resolved = self.auto_resolve_ready_categories()
        return {'demoted': demoted, 'overflowed': overflowed, 'added': added,
                'touched': touched, 'resolved_added': resolved_added, 'resolved': resolved}

    def auto_include_forced_categories(self):
        if not self.auto_include:
            return 0, []
        target = self.get_target()
        if target <= 0:
            return 0, []
        added_total = 0
        touched = []
        changed = False
        for cat in self.categories:
            images = self.get_all_images_from_category(cat)
            if not images or len(images) > target:
                continue
            bucket = self.dataset.setdefault(cat, [])
            existing = set(bucket)
            new = [p for p in images if p not in existing]
            if new:
                bucket.extend(new)
                self.auto_forced_added.setdefault(cat, [])
                self.auto_forced_added[cat].extend(new)
                added_total += len(new)
                touched.append((cat, len(new)))
                changed = True
            img_set = set(images)
            if self.blacklist.get(cat):
                pruned = [p for p in self.blacklist[cat] if p in img_set]
                if len(pruned) != len(self.blacklist[cat]):
                    self.blacklist[cat] = pruned
                    changed = True
            if self.forced_blacklist.get(cat):
                pruned = [p for p in self.forced_blacklist[cat] if p in img_set]
                if len(pruned) != len(self.forced_blacklist[cat]):
                    self.forced_blacklist[cat] = pruned
                    changed = True
        if changed:
            self.save_data(silent=True)
        return added_total, touched

    def get_stats(self, category):
        images = self.get_all_images_from_category(category)
        img_set = set(images)
        selected = [p for p in self.dataset.get(category, []) if p in img_set]
        selected_set = set(selected)
        forced_bl = [p for p in self.forced_blacklist.get(category, [])
                     if p in img_set and p not in selected_set]
        forced_set = set(forced_bl)
        regular_bl = [p for p in self.blacklist.get(category, [])
                      if p in img_set and p not in selected_set and p not in forced_set]
        regular_set = set(regular_bl)
        candidate_after_forced = [p for p in images if p not in selected_set and p not in forced_set]
        available = [p for p in candidate_after_forced if p not in regular_set]
        target = self.get_target()
        total = len(images)
        eff_target = min(target, total) if target > 0 else 0
        needed = max(0, eff_target - len(selected))
        forced_category = target > 0 and 0 < total <= target
        surplus = max(0, total - target) if target > 0 else 0
        force_resolve_left = max(0, surplus - len(forced_bl))

        can_force_resolve = (target > 0 and total > target and len(forced_bl) > 0 and needed > 0
                             and force_resolve_left == 0 and len(candidate_after_forced) >= needed)
        over_forced = (target > 0 and total > target and len(candidate_after_forced) < needed)

        if target == 0:
            status = "no target"
        elif forced_category and len(selected) >= total:
            status = f"AUTO ✔ all {total} included"
        elif forced_category:
            status = f"AUTO pending ({total - len(selected)} to add)"
        elif len(selected) > target:
            status = f"OVER by {len(selected) - target}"
        elif needed == 0:
            status = "COMPLETE"
        elif over_forced:
            status = (f"OVER-FORCED / BLOCKED (need {needed}, only "
                      f"{len(candidate_after_forced)} non-forced left)")
        elif can_force_resolve:
            status = f"FORCE-READY (auto-fill {needed})"
        elif len(forced_bl) > 0:
            status = f"needs {needed}; force-resolve in {force_resolve_left} more"
        elif len(available) == 0 and len(regular_bl) > 0:
            status = f"RECYCLE regular rejects ({len(regular_bl)} available again)"
        else:
            status = f"needs {needed}"

        return {
            'total': total, 'selected': len(selected), 'selected_list': selected,
            'blacklisted': len(regular_bl), 'regular_blacklist_list': regular_bl,
            'forced_blacklisted': len(forced_bl), 'forced_blacklist_list': forced_bl,
            'available': len(available), 'available_list': available,
            'candidate_after_forced': len(candidate_after_forced),
            'candidate_after_forced_list': candidate_after_forced,
            'needed': needed, 'target': target, 'eff_target': eff_target,
            'forced': forced_category, 'surplus': surplus,
            'force_resolve_left': force_resolve_left,
            'can_force_resolve': can_force_resolve, 'over_forced': over_forced,
            'status': status,
        }

    def auto_resolve_category_if_ready(self, category):
        s = self.get_stats(category)
        if not s['can_force_resolve']:
            return 0
        needed = s['needed']
        if needed <= 0:
            return 0
        fresh = list(s['available_list'])
        fresh_set = set(fresh)
        recycled = [p for p in s['candidate_after_forced_list'] if p not in fresh_set]
        pool = fresh + recycled
        if len(pool) < needed:
            return 0
        chosen = pool if len(pool) == needed else self.balanced_sample(pool, needed)
        bucket = self.dataset.setdefault(category, [])
        newly_added = []
        for p in chosen:
            if p not in bucket:
                bucket.append(p)
                newly_added.append(p)
        added = len(newly_added)
        if added:
            chosen_set = set(chosen)
            self.blacklist[category] = [p for p in self.blacklist.get(category, [])
                                        if p not in chosen_set]
            self.auto_resolve_added.setdefault(category, [])
            self.auto_resolve_added[category].extend(newly_added)
            self.save_data(silent=True)
        return added

    def auto_resolve_ready_categories(self):
        resolved = []
        total_added = 0
        for cat in self.categories:
            added = self.auto_resolve_category_if_ready(cat)
            if added:
                resolved.append((cat, added))
                total_added += added
        return total_added, resolved

    def recycle_regular_blacklist(self, category):
        count = len(self.blacklist.get(category, []))
        self.blacklist[category] = []
        self.save_data(silent=True)
        return count

    # ==================================================================
    # Thumbnails / image info
    # ==================================================================
    def get_thumbnail(self, path, size):
        key = (path, size)
        photo = self._thumb_cache.get(key)
        if photo is not None:
            return photo
        try:
            with Image.open(path) as img:
                try:
                    img.draft('RGB', (size * 2, size * 2))
                except Exception:
                    pass
                img.thumbnail((size, size), Image.Resampling.LANCZOS)
                photo = ImageTk.PhotoImage(img)
        except Exception:
            return None
        if len(self._thumb_cache) > 1500:
            self._thumb_cache.clear()
        self._thumb_cache[key] = photo
        return photo

    def get_image_info_text(self, image_path):
        try:
            cached = self._get_cached_resolution(image_path)
            if cached:
                w, h = cached
            else:
                with Image.open(image_path) as img:
                    w, h = img.size
            fsize = os.path.getsize(image_path)
            if fsize >= 1_048_576:
                size_str = f"{fsize / 1_048_576:.2f} MB"
            elif fsize >= 1024:
                size_str = f"{fsize / 1024:.1f} KB"
            else:
                size_str = f"{fsize} B"
            return f"{w}×{h} px  |  {size_str}"
        except Exception:
            return "size unknown"

    # ==================================================================
    # ASPECT-RATIO VIEWER (shift+right-click / double-click)
    # ==================================================================
    def open_file_location(self, path):
        """Open the directory containing the file with the file highlighted/selected."""
        if not path or not os.path.isfile(path):
            return
        abs_path = os.path.abspath(path)
        folder = os.path.dirname(abs_path)

        try:
            if sys.platform == 'win32':
                subprocess.run(['explorer', f'/select,{abs_path}'])
            elif sys.platform == 'darwin':
                subprocess.run(['open', '-R', abs_path], check=True)
            else:
                linux_cmds = [
                    ['nautilus', '--select', abs_path],
                    ['dolphin', '--select', abs_path],
                    ['thunar', '--select', abs_path],
                    ['pcmanfm', '--select', abs_path],
                    ['nemo', '--select', abs_path],
                ]
                for cmd in linux_cmds:
                    try:
                        subprocess.run(cmd, check=True, timeout=3, capture_output=True)
                        return
                    except (subprocess.SubprocessError, FileNotFoundError, subprocess.TimeoutExpired):
                        continue
                subprocess.run(['xdg-open', folder], check=True, capture_output=True)
        except Exception as e:
            messagebox.showerror("Error", f"Could not open file location:\n{e}")

    def open_aspect_window(self, path):
        if not path or not os.path.isfile(path):
            return
        if self.aspect_window is None or not self.aspect_window.winfo_exists():
            self.aspect_window = self._make_aspect_window()
        win = self.aspect_window
        win._current_path = path
        win.title(os.path.basename(path))

        try:
            with Image.open(path) as img:
                iw, ih = img.size
        except Exception:
            iw, ih = 800, 600
        if iw <= 0 or ih <= 0:
            iw, ih = 800, 600

        chrome_h = 46
        max_w = int(win.winfo_screenwidth() * 0.88)
        max_h = int(win.winfo_screenheight() * 0.88) - chrome_h
        min_w = 380

        ratio = min(max_w / iw, max_h / ih)
        if iw < min_w and ih < max_h:
            ratio = max(ratio, min(min_w / iw, max_h / ih))
        disp_w = max(min_w, int(iw * ratio))
        disp_h = max(200, int(ih * ratio))

        if not win._fullscreen:
            win.geometry(f"{disp_w}x{disp_h + chrome_h}")
        win._info_label.config(
            text=f"{os.path.basename(path)}    |    {iw}×{ih} px    |    "
                 f"{self.get_image_info_text(path)}    |    "
                 f"{'landscape' if iw >= ih else 'portrait'}  ({iw / ih:.3f}:1)")
        win.deiconify()
        win.lift()
        win.after(30, lambda: self._render_aspect_image(win, force=True))

    def _make_aspect_window(self):
        win = tk.Toplevel(self.root)
        win.title("Full Image")
        win.configure(bg='black')
        win._current_path = None
        win._fullscreen = False
        win._saved_geom = None
        win._last_size = (0, 0)

        info = tk.Label(win, text="", bg=DARK_BG, fg='#9fd3ff', font=('Consolas', 9),
                        anchor='w', padx=8, pady=4)
        info.pack(side='bottom', fill='x')
        win._info_label = info

        label = tk.Label(win, bg='black')
        label.pack(fill='both', expand=True)
        win._img_label = label

        def toggle_fullscreen(event=None):
            if not win._fullscreen:
                win._saved_geom = win.geometry()
                win.attributes('-fullscreen', True)
                win._fullscreen = True
            else:
                win.attributes('-fullscreen', False)
                win._fullscreen = False
                if win._saved_geom:
                    win.geometry(win._saved_geom)
            win.after(60, lambda: self._render_aspect_image(win, force=True))

        def on_configure(_e):
            self._render_aspect_image(win)

        label.bind('<Double-Button-1>', toggle_fullscreen)
        win.bind('<Double-Button-1>', toggle_fullscreen)
        win.bind('<Escape>', lambda e: toggle_fullscreen() if win._fullscreen else win.withdraw())
        label.bind('<Configure>', on_configure)
        win.protocol('WM_DELETE_WINDOW', win.withdraw)
        return win

    def _render_aspect_image(self, win, force=False):
        if win is None or not win.winfo_exists():
            return
        path = getattr(win, '_current_path', None)
        if not path or not os.path.isfile(path):
            return
        label = win._img_label
        w = max(1, label.winfo_width())
        h = max(1, label.winfo_height())
        if w < 20 or h < 20:
            return
        last_rendered_path = getattr(win, '_rendered_path', None)
        if not force and win._last_size == (w, h) and last_rendered_path == path:
            return
        win._last_size = (w, h)
        win._rendered_path = path

        try:
            with Image.open(path) as src:
                ratio = min(w / src.width, h / src.height)
                ratio = ratio if ratio > 0 else 1
                ns = (max(1, int(src.width * ratio)), max(1, int(src.height * ratio)))
                resized = src.resize(ns, Image.Resampling.LANCZOS)
            photo = ImageTk.PhotoImage(resized)
            label.config(image=photo, text='')
            label.image = photo
        except Exception as e:
            label.config(image='', text=f"Error: {e}", fg='#ff6666')

    # ==================================================================
    # Directory Builder tab
    # ==================================================================
    def build_directory_tab(self):
        left_frame = ttk.Frame(self.directory_frame)
        left_frame.pack(side='left', fill='both', expand=True, padx=5, pady=5)
        ttk.Label(left_frame, text="Categories:").pack(anchor='w')
        self.category_listbox = tk.Listbox(left_frame, width=40, height=20, exportselection=False)
        self.style_tk_listbox(self.category_listbox)
        self.category_listbox.pack(fill='both', expand=True, pady=5)
        self.category_listbox.bind('<<ListboxSelect>>', self.on_category_select)
        btn_frame = ttk.Frame(left_frame)
        btn_frame.pack(fill='x', pady=5)
        ttk.Button(btn_frame, text="Add Category", command=self.add_category).pack(side='left', padx=2)
        ttk.Button(btn_frame, text="Remove Category", command=self.remove_category).pack(side='left', padx=2)

        right_frame = ttk.Frame(self.directory_frame)
        right_frame.pack(side='right', fill='both', expand=True, padx=5, pady=5)
        ttk.Label(right_frame, text="Folders for selected category:").pack(anchor='w')
        self.folder_listbox = tk.Listbox(right_frame, width=60, height=20, exportselection=False)
        self.style_tk_listbox(self.folder_listbox)
        self.folder_listbox.pack(fill='both', expand=True, pady=5)
        folder_btn_frame = ttk.Frame(right_frame)
        folder_btn_frame.pack(fill='x', pady=5)
        ttk.Button(folder_btn_frame, text="Add Folder", command=self.add_folder).pack(side='left', padx=2)
        ttk.Button(folder_btn_frame, text="Remove Folder", command=self.remove_folder).pack(side='left', padx=2)
        ttk.Button(folder_btn_frame, text="Save", command=self.save_data).pack(side='right', padx=2)
        self.update_category_listbox()

    def update_category_listbox(self):
        self.category_listbox.delete(0, tk.END)
        names = list(self.categories.keys())
        for category in names:
            s = self.get_stats(category)
            flag = "  ⚙AUTO" if s['forced'] else ""
            self.category_listbox.insert(
                tk.END, f"{category}  [{s['selected']}/{s['total']}]  "
                        f"forceBL:{s['forced_blacklisted']}{flag}")
        if self.selected_category in names:
            idx = names.index(self.selected_category)
            self.category_listbox.selection_clear(0, tk.END)
            self.category_listbox.selection_set(idx)
            self.category_listbox.activate(idx)
            self.category_listbox.see(idx)
        else:
            self.selected_category = None
            self.folder_listbox.delete(0, tk.END)

    def _selected_category_name(self):
        if self.selected_category and self.selected_category in self.categories:
            return self.selected_category
        selection = self.category_listbox.curselection()
        if not selection:
            return None
        name = list(self.categories.keys())[selection[0]]
        self.selected_category = name
        return name

    def update_folder_listbox(self, category):
        self.folder_listbox.delete(0, tk.END)
        for folder in self.categories.get(category, []):
            self.folder_listbox.insert(tk.END, folder)

    def on_category_select(self, event):
        selection = self.category_listbox.curselection()
        if not selection:
            return
        category = list(self.categories.keys())[selection[0]]
        self.selected_category = category
        self.update_folder_listbox(category)

    def add_category(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Add Category")
        dialog.geometry("300x150")
        dialog.configure(bg=DARK_BG)
        dialog.transient(self.root)
        dialog.grab_set()
        ttk.Label(dialog, text="Category Name:").pack(pady=10)
        entry = ttk.Entry(dialog)
        entry.pack(pady=5)
        entry.focus_set()

        def save_category():
            name = entry.get().strip()
            if not name:
                messagebox.showwarning("Warning", "Please enter a category name!")
                return
            if name in self.categories:
                messagebox.showwarning("Warning", "Category already exists!")
                return
            self.categories[name] = []
            for pdata in self.profiles.values():
                pdata.setdefault('dataset', {}).setdefault(name, [])
                pdata.setdefault('blacklist', {}).setdefault(name, [])
                pdata.setdefault('forced_blacklist', {}).setdefault(name, [])
                pdata.setdefault('auto_forced_added', {}).setdefault(name, [])
                pdata.setdefault('auto_resolve_added', {}).setdefault(name, [])
            self.dataset.setdefault(name, [])
            self.blacklist.setdefault(name, [])
            self.forced_blacklist.setdefault(name, [])
            self.auto_forced_added.setdefault(name, [])
            self.auto_resolve_added.setdefault(name, [])
            self._image_cache.pop(name, None)
            self._coarse_cache = {}
            self._raw_counts_cache = None
            self.selected_category = name
            self.save_data(silent=True)
            self.update_category_listbox()
            self.update_folder_listbox(name)
            self.refresh_mover_tree()
            dialog.destroy()

        ttk.Button(dialog, text="Save", command=save_category).pack(pady=10)

    def remove_category(self):
        category = self._selected_category_name()
        if not category:
            messagebox.showwarning("Warning", "Please select a category first!")
            return
        if messagebox.askyesno("Confirm", f"Remove category '{category}'? (Removes it from ALL profiles.)"):
            del self.categories[category]
            for pdata in self.profiles.values():
                pdata.get('dataset', {}).pop(category, None)
                pdata.get('blacklist', {}).pop(category, None)
                pdata.get('forced_blacklist', {}).pop(category, None)
                pdata.get('auto_forced_added', {}).pop(category, None)
                pdata.get('auto_resolve_added', {}).pop(category, None)
            self.dataset.pop(category, None)
            self.blacklist.pop(category, None)
            self.forced_blacklist.pop(category, None)
            self.auto_forced_added.pop(category, None)
            self.auto_resolve_added.pop(category, None)
            self._image_cache.pop(category, None)
            self._coarse_cache = {}
            self._raw_counts_cache = None
            if self.selected_category == category:
                self.selected_category = None
            if self.direct_current_category == category:
                self.direct_current_category = None
            self.save_data(silent=True)
            self.update_category_listbox()
            self.folder_listbox.delete(0, tk.END)
            self.refresh_mover_tree()

    def add_folder(self):
        category = self._selected_category_name()
        if not category:
            messagebox.showwarning("Warning", "Please select a category first!")
            return
        folder = filedialog.askdirectory(title=f"Select folder for {category}")
        if folder and folder not in self.categories[category]:
            self.categories[category].append(folder)
            self.get_all_images_from_category(category, force_rescan=True)
            self.run_auto_pipeline()
            self.save_data(silent=True)
            self.update_folder_listbox(category)
            self.update_category_listbox()
            self.refresh_mover_tree()
            if self.coarse_elimination:
                self.start_coarse_resolution_scan(manual=False)

    def remove_folder(self):
        category = self._selected_category_name()
        if not category:
            messagebox.showwarning("Warning", "Please select a category first!")
            return
        folder_selection = self.folder_listbox.curselection()
        if not folder_selection:
            messagebox.showwarning("Warning", "Please select a folder to remove!")
            return
        folder = self.folder_listbox.get(folder_selection[0])
        if folder in self.categories[category]:
            self.categories[category].remove(folder)
            self.get_all_images_from_category(category, force_rescan=True)
            self.run_auto_pipeline()
            self.save_data(silent=True)
            self.update_folder_listbox(category)
            self.update_category_listbox()
            self.refresh_mover_tree()

    # ==================================================================
    # DIRECT TAB (+ file mover panel)
    # ==================================================================
    def build_direct_tab(self):
        top = ttk.Frame(self.direct_frame)
        top.pack(fill='x', padx=10, pady=(8, 4))

        ttk.Label(top, text="Category:").pack(side='left')
        self.direct_category_var = tk.StringVar()
        self.direct_category_combo = ttk.Combobox(top, textvariable=self.direct_category_var,
                                                  state='readonly', width=24)
        self.direct_category_combo.pack(side='left', padx=(4, 12))
        self.direct_category_combo.bind('<<ComboboxSelected>>', self.on_direct_category_selected)

        ttk.Label(top, text="Mode:").pack(side='left')
        self.direct_mode_var = tk.StringVar(value='Auto')
        mode_combo = ttk.Combobox(top, textvariable=self.direct_mode_var, state='readonly',
                                  width=9, values=('Auto', 'Select', 'Remove'))
        mode_combo.pack(side='left', padx=(4, 12))
        mode_combo.bind('<<ComboboxSelected>>', lambda e: self.direct_load_batch())

        ttk.Button(top, text="⟲ Reload", command=self.direct_load_batch).pack(side='left', padx=(12, 3))
        ttk.Button(top, text="◀ Prev Page", command=self.direct_prev_page).pack(side='left', padx=3)
        ttk.Button(top, text="Next Page ▶", command=self.direct_next_page).pack(side='left', padx=3)

        ttk.Label(top, text="Ext:").pack(side="left", padx=(10, 4))
        self.direct_ext_filter_var = tk.StringVar(value="All")
        ext_filter_combo = ttk.Combobox(top, textvariable=self.direct_ext_filter_var,
                                        values=["All", "JFIF/AVIF Only", "Unrated Only"],
                                        state="readonly", width=14)
        ext_filter_combo.pack(side="left", padx=(4, 10))
        ext_filter_combo.bind("<<ComboboxSelected>>", lambda e: self.direct_set_ext_filter())

        ttk.Label(top, text="Page:").pack(side='left', padx=(10, 4))
        self.direct_page_entry = ttk.Entry(top, width=8)
        self.direct_page_entry.pack(side='left', padx=(4, 4))
        ttk.Button(top, text="Go", command=self.direct_go_to_page).pack(side='left', padx=(0, 10))

        ttk.Label(top, text="Search:").pack(side='left', padx=(15, 4))
        search_entry = ttk.Entry(top, textvariable=self.direct_search_var, width=20)
        search_entry.pack(side='left', padx=(4, 10))
        search_entry.bind('<KeyRelease>', lambda e: self.direct_load_batch())
        ttk.Button(top, text="✕ Clear", command=self._clear_direct_search).pack(side='left', padx=(0, 10))

        ttk.Label(top, text="Order:").pack(side='left', padx=(10, 4))
        order_combo = ttk.Combobox(top, textvariable=self.direct_order_var,
                                   values=["Interleaved", "A-Z (File Name)"],
                                   state="readonly", width=14)
        order_combo.pack(side='left', padx=(4, 10))
        order_combo.bind("<<ComboboxSelected>>", lambda e: self.direct_set_order())

        self.direct_page_count_label = ttk.Label(top, text="")
        self.direct_page_count_label.pack(side='left', padx=(5, 10))

        ttk.Button(top, text="✔ Commit Page", command=lambda: self.direct_commit_batch(partial=True),
                   style="Accent.TButton").pack(side='left', padx=3)
        ttk.Button(top, text="💾 Process All Selections", command=self.direct_process_all_selections,
                   style="Success.TButton").pack(side='left', padx=10)
        ttk.Button(top, text="Rest→Accept",
                   command=lambda: self.direct_mark_rest('accept')).pack(side='left', padx=3)
        ttk.Button(top, text="Rest→Reject", style="Danger.TButton",
                   command=lambda: self.direct_mark_rest('reject')).pack(side='left', padx=3)
        ttk.Button(top, text="✕ Clear Current Page", style="Warning.TButton",
                   command=self.direct_reset_current_batch).pack(side='left', padx=10)
        ttk.Button(top, text="↻ Reset Category", style="Danger.TButton",
                   command=self.direct_reset_category).pack(side='left', padx=3)

        self.direct_mode_banner = tk.Label(self.direct_frame, text="", bg=DARK_BG,
                                           fg='white', font=('Arial', 11, 'bold'),
                                           anchor='w', padx=10, pady=5)
        self.direct_mode_banner.pack(fill='x', padx=10, pady=(2, 2))

        self.direct_info_label = ttk.Label(self.direct_frame, text="", font=('Arial', 9))
        self.direct_info_label.pack(fill='x', padx=10, anchor='w')

        self.direct_progress_label = ttk.Label(self.direct_frame, text="", font=('Arial', 10, 'bold'))
        self.direct_progress_label.pack(fill='x', padx=10, pady=(2, 2), anchor='w')

        ttk.Label(self.direct_frame,
                  text="LEFT-CLICK accept/keep   •   RIGHT-CLICK reject/remove   •   "
                       "SHIFT+LEFT-CLICK queue a move (again = unqueue)   •   "
                       "SHIFT+RIGHT-CLICK open full image   •   "
                       "💾 Process All Selections executes everything",
                  font=('Arial', 9), foreground='#999999').pack(fill='x', padx=10, pady=(0, 4))

        split = ttk.Frame(self.direct_frame)
        split.pack(fill='both', expand=True, padx=10, pady=(0, 8))

        mover = tk.Frame(split, bg=DARK_BG_ALT, width=MOVER_PANEL_WIDTH,
                         highlightthickness=1, highlightbackground=DARK_BG_LIGHT)
        mover.pack(side='right', fill='y', padx=(10, 0))
        mover.pack_propagate(False)
        self._build_mover_panel(mover)

        grid_holder = ttk.Frame(split)
        grid_holder.pack(side='left', fill='both', expand=True)
        self.direct_canvas = tk.Canvas(grid_holder, bg=DARK_BG, highlightthickness=0)
        self.direct_canvas.pack(side='left', fill='both', expand=True)
        dsb = ttk.Scrollbar(grid_holder, orient='vertical', command=self.direct_canvas.yview)
        dsb.pack(side='right', fill='y')
        self.direct_canvas.configure(yscrollcommand=dsb.set)
        self.direct_grid_frame = ttk.Frame(self.direct_canvas)
        self.direct_canvas.create_window((0, 0), window=self.direct_grid_frame, anchor='nw')
        self.direct_grid_frame.bind(
            '<Configure>',
            lambda e: self.direct_canvas.configure(scrollregion=self.direct_canvas.bbox('all')))
        self._bind_mousewheel(self.direct_canvas)

        self.refresh_direct_category_list()

    # ---------------- file mover panel ----------------
    def _build_mover_panel(self, parent):
        tk.Label(parent, text="📂  FILE MOVER", bg='#7a3b12', fg='white',
                 font=('Arial', 11, 'bold'), anchor='w', padx=10, pady=6).pack(fill='x')

        tk.Label(parent,
                 text="Click a folder below to arm it as the move target,\n"
                      "then SHIFT+LEFT-CLICK any image to QUEUE it.\n"
                      "Nothing moves until you press 💾 Process All Selections.",
                 bg=DARK_BG_ALT, fg='#bbbbbb', font=('Arial', 8), justify='left',
                 anchor='w', padx=10, pady=4).pack(fill='x')

        target_box = tk.Frame(parent, bg=DARK_BG_ALT)
        target_box.pack(fill='x', padx=8, pady=(2, 4))
        tk.Label(target_box, text="ACTIVE TARGET", bg=DARK_BG_ALT, fg='#888888',
                 font=('Arial', 8, 'bold'), anchor='w').pack(fill='x')
        self.mover_target_label = tk.Label(target_box, text="(none — no folder armed)",
                                           bg='#2d2d2d', fg='#888888', font=('Consolas', 8),
                                           anchor='w', justify='left', wraplength=MOVER_PANEL_WIDTH - 40,
                                           padx=6, pady=6, relief='flat')
        self.mover_target_label.pack(fill='x')

        btn_row = tk.Frame(parent, bg=DARK_BG_ALT)
        btn_row.pack(fill='x', padx=8, pady=(2, 6))
        ttk.Button(btn_row, text="Clear Target", command=self.mover_clear_target).pack(side='left')
        ttk.Button(btn_row, text="Refresh List", command=self.refresh_mover_tree).pack(side='left', padx=4)

        self.replacer_btn = tk.Button(btn_row, text="Replacer Mode",
                                      font=('Arial', 8),
                                      bg='#3a3a3a', fg='#aaaaaa',
                                      activebackground='#3a3a3a', activeforeground='#aaaaaa',
                                      relief='flat', borderwidth=1,
                                      command=self.toggle_replacer_mode)
        self.replacer_btn.pack(side='right', padx=4)

        self.mover_queue_label = tk.Label(parent, text="No moves queued", bg='#2d2d2d',
                                          fg='#888888', font=('Arial', 8, 'bold'), anchor='w',
                                          justify='left', wraplength=MOVER_PANEL_WIDTH - 24,
                                          padx=8, pady=5)
        self.mover_queue_label.pack(fill='x', padx=8, pady=(0, 6))

        tree_holder = tk.Frame(parent, bg=DARK_BG_ALT)
        tree_holder.pack(fill='both', expand=True, padx=8, pady=(0, 8))
        self.mover_tree = ttk.Treeview(tree_holder, show='tree', selectmode='browse')
        msb = ttk.Scrollbar(tree_holder, orient='vertical', command=self.mover_tree.yview)
        self.mover_tree.configure(yscrollcommand=msb.set)
        self.mover_tree.pack(side='left', fill='both', expand=True)
        msb.pack(side='right', fill='y')
        self.mover_tree.tag_configure('cat', background='#123a5c', foreground='white')
        self.mover_tree.tag_configure('folder', background=DARK_TREE_BG, foreground=DARK_FG)
        self.mover_tree.tag_configure('armed', background=MOVE_COLOR, foreground='black')
        self.mover_tree.tag_configure('missing', foreground='#ff6666')
        self.mover_tree.tag_configure('excluded', foreground='#ff6b6b', font=('Arial', 9, 'italic'))
        self.mover_tree.bind('<<TreeviewSelect>>', self.on_mover_tree_select)
        self.mover_tree.bind('<Button-3>', self.on_mover_tree_right_click)

        self.mover_log = tk.Label(parent, text="", bg=DARK_BG_ALT, fg='#4ade80',
                                  font=('Arial', 8), anchor='w', justify='left',
                                  wraplength=MOVER_PANEL_WIDTH - 24, padx=10, pady=6)
        self.mover_log.pack(fill='x')

        self.refresh_mover_tree()

    def refresh_mover_tree(self):
        if not hasattr(self, 'mover_tree'):
            return
        tree = self.mover_tree
        for item in tree.get_children():
            tree.delete(item)
        self.mover_tree_nodes = {}
        for cat in self.categories:
            folders = self.categories.get(cat, [])
            cat_id = tree.insert('', 'end', text=f"  {cat}   ({len(folders)} folder(s))",
                                 open=True, tags=('cat',))
            for folder in folders:
                exists = os.path.isdir(folder)
                base = os.path.basename(folder.rstrip('/\\')) or folder
                parent_dir = os.path.basename(os.path.dirname(folder.rstrip('/\\')))
                label = f"    {base}" + (f"   ⟨{parent_dir}⟩" if parent_dir else "")
                if not exists:
                    label += "   [MISSING]"
                is_excluded = base in self.excluded_subfolders
                if is_excluded:
                    label += "   [EXCLUDED]"
                armed = (self.mover_target_folder is not None
                         and self._norm(self.mover_target_folder) == self._norm(folder))
                if is_excluded:
                    tags = ('excluded',)
                elif armed:
                    tags = ('armed',)
                else:
                    tags = ('folder',) if exists else ('missing',)
                node = tree.insert(cat_id, 'end', text=label, tags=tags)
                self.mover_tree_nodes[node] = folder
        self._update_mover_target_label()

    def on_mover_tree_select(self, _event=None):
        sel = self.mover_tree.selection()
        if not sel:
            return
        node = sel[0]
        folder = self.mover_tree_nodes.get(node)
        if folder is None:
            self.mover_tree.selection_remove(node)
            return
        base = os.path.basename(folder.rstrip('/\\')) or folder
        if base in self.excluded_subfolders:
            self.mover_tree.selection_remove(node)
            return
        if self.mover_target_folder and self._norm(self.mover_target_folder) == self._norm(folder):
            self.mover_target_folder = None
        else:
            self.mover_target_folder = folder
        for n in self.mover_tree_nodes:
            f = self.mover_tree_nodes[n]
            b = os.path.basename(f.rstrip('/\\')) or f
            if b in self.excluded_subfolders:
                self.mover_tree.item(n, tags=('excluded',))
            elif self.mover_target_folder and self._norm(f) == self._norm(self.mover_target_folder):
                self.mover_tree.item(n, tags=('armed',))
            else:
                self.mover_tree.item(n, tags=('folder',) if os.path.isdir(f) else ('missing',))
        self._update_mover_target_label()

    def on_mover_tree_right_click(self, event):
        item = self.mover_tree.identify_row(event.y)
        if not item:
            return
        folder = self.mover_tree_nodes.get(item)
        if not folder:
            return

        base = os.path.basename(folder.rstrip('/\\')) or folder
        menu = tk.Menu(self.root, tearoff=0)

        if base in self.excluded_subfolders:
            menu.add_command(label="Include Subdirectory",
                             command=lambda: self.toggle_subfolder_exclusion(base, False))
        else:
            menu.add_command(label="Exclude Subdirectory",
                             command=lambda: self.toggle_subfolder_exclusion(base, True))
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def toggle_subfolder_exclusion(self, subfolder_name, exclude):
        if exclude:
            self.excluded_subfolders.add(subfolder_name)
            self.mover_log_msg(f"Excluded subdirectory: {subfolder_name}", '#ff6b6b')
        else:
            self.excluded_subfolders.discard(subfolder_name)
            self.mover_log_msg(f"Included subdirectory: {subfolder_name}", '#4ade80')
        self.refresh_mover_tree()
        if self.direct_current_category:
            self.direct_load_batch()

    def mover_clear_target(self):
        self.mover_target_folder = None
        self.mover_tree.selection_remove(*self.mover_tree.selection())
        for n, f in self.mover_tree_nodes.items():
            self.mover_tree.item(n, tags=('folder',) if os.path.isdir(f) else ('missing',))
        self._update_mover_target_label()

    def _update_mover_target_label(self):
        if not hasattr(self, 'mover_target_label'):
            return
        if self.mover_target_folder:
            self.mover_target_label.config(text=self.mover_target_folder,
                                           bg=MOVE_COLOR, fg='black')
        else:
            self.mover_target_label.config(text="(none — no folder armed)",
                                           bg='#2d2d2d', fg='#888888')

    def _update_queue_label(self):
        if not hasattr(self, 'mover_queue_label'):
            return
        n = len(self.pending_moves)
        if n:
            r = sum(1 for m in self.pending_moves.values() if m.get('replacer'))
            self.mover_queue_label.config(
                text=f"⏳ {n} move(s) queued ({r} replacer, {n - r} armed-folder)\n"
                     f"Run 💾 Process All Selections to execute.",
                fg=QUEUE_COLOR)
        else:
            self.mover_queue_label.config(text="No moves queued", fg='#888888')

    def toggle_replacer_mode(self):
        """Toggle replacer mode. Toggling never moves files; Process All Selections does."""
        self.replacer_mode = not self.replacer_mode
        if self.replacer_mode:
            self.replacer_btn.config(bg='#2ecc71', fg='black', relief='raised')
            self.mover_log_msg("Replacer mode ON — shift-click queues into <Category>_Replacers.",
                               '#2ecc71')
        else:
            self.replacer_btn.config(bg='#3a3a3a', fg='#aaaaaa', relief='flat')
            self.mover_log_msg("Replacer mode OFF — shift-click queues into the armed folder.",
                               '#bbbbbb')

    def get_replacer_folder(self, category_name, subfolder_name=None):
        if not self.scripts_dir:
            return None
        base_path = os.path.join(self.scripts_dir, f"{category_name}_Replacers")
        if subfolder_name:
            return os.path.join(base_path, subfolder_name)
        return base_path

    def mover_log_msg(self, text, color='#4ade80'):
        if hasattr(self, 'mover_log'):
            self.mover_log.config(text=text, fg=color)

    # ---------------- direct batch ----------------
    def refresh_direct_category_list(self):
        names = [c for c in self.categories if len(self.get_all_images_from_category(c)) > 0]
        self.direct_category_combo['values'] = names
        if self.direct_current_category not in names:
            self.direct_current_category = names[0] if names else None
        self.direct_category_var.set(self.direct_current_category or '')
        self.refresh_mover_tree()

    def on_direct_category_selected(self, event=None):
        cat = self.direct_category_var.get()
        if not cat:
            return
        self.direct_search_var.set('')
        self.direct_current_category = cat
        self.direct_page = 0
        self.direct_load_batch()

    def _clear_direct_search(self):
        self.direct_search_var.set('')
        self.direct_page = 0
        self.direct_load_batch()

    def direct_set_order(self):
        self.direct_page = 0
        self.direct_load_batch()

    def _direct_order_pool(self, pool):
        seen = set()
        unique_pool = []
        for p in pool:
            if p not in seen:
                seen.add(p)
                unique_pool.append(p)
        if self.direct_order_var.get() == "A-Z (File Name)":
            return sorted(unique_pool, key=lambda p: os.path.basename(p).lower())
        return self._interleave_by_folder(unique_pool)

    def direct_effective_mode(self, cat):
        """'remove' when it's less work to reject the surplus than to
        hand-pick the target (e.g. 510 files, target 500 -> reject 10)."""
        choice = self.direct_mode_var.get()
        if choice == 'Select':
            return 'select'
        if choice == 'Remove':
            return 'remove'
        s = self.get_stats(cat)
        if s['target'] <= 0 or s['total'] <= s['target']:
            return 'select'
        if s['force_resolve_left'] <= 0:
            return 'select'
        return 'remove' if s['force_resolve_left'] < s['needed'] else 'select'

    def _paint_direct_cell(self, path):
        """Colour a grid cell from self.direct_status[path]."""
        cell = self.direct_cells.get(path)
        if not cell:
            return
        status = self.direct_status.get(path)
        if status == 'accept':
            color = ACCEPT_COLOR
            text = "ACCEPT" if self.direct_mode == 'select' else "KEEP"
            fg = '#7ef29a'
        elif status == 'reject':
            color = REJECT_COLOR
            text = "REJECT" if self.direct_mode == 'select' else "REMOVE"
            fg = '#ff8a7a'
        elif status == 'moved':
            color, text, fg = MOVE_COLOR, "MOVED", MOVE_COLOR
        elif status == 'queued':
            if self.pending_moves.get(path, {}).get('replacer'):
                color, text, fg = REPLACER_COLOR, "QUEUED (REPLACER)", REPLACER_COLOR
            else:
                color, text, fg = QUEUE_COLOR, "QUEUED", QUEUE_COLOR
        else:
            color, text, fg = NEUTRAL_COLOR, "PENDING", '#888888'
        cell['frame'].configure(highlightbackground=color, highlightcolor=color)
        cell['status'].configure(text=text, fg=fg)

    def direct_load_batch(self, page=None):
        cat = self.direct_current_category
        for w in self.direct_grid_frame.winfo_children():
            w.destroy()
        self.direct_batch = []
        self.direct_status = {}
        self.direct_cells = {}

        if not cat:
            self.direct_mode_banner.config(text="No category selected.", bg=DARK_BG_LIGHT)
            self.direct_info_label.config(text="")
            self.direct_progress_label.config(text="")
            return

        self.run_auto_pipeline()
        s = self.get_stats(cat)
        mode = self.direct_effective_mode(cat)
        self.direct_mode = mode

        if mode == 'remove':
            self.direct_mode_banner.config(
                bg='#7a3b12',
                text=f"REMOVAL MODE — {s['total']} files for a target of {s['target']} "
                     f"(surplus {s['surplus']}). Right-click {s['force_resolve_left']} more "
                     f"image(s) to remove; everything else is auto-kept.")
        else:
            self.direct_mode_banner.config(
                bg='#1f4a6b',
                text=f"SELECTION MODE — pick {s['needed']} more image(s) for '{cat}' "
                     f"(target {s['target']}, surplus {s['surplus']}).")

        self.direct_info_label.config(
            text=f"selected {s['selected']}/{s['target']}  |  on disk {s['total']}  |  "
                 f"forced rejects {s['forced_blacklisted']}/{s['surplus']}  |  "
                 f"regular rejects {s['blacklisted']}  |  available {s['available']}  |  {s['status']}")

        def build_pool(stats):
            pool = list(stats['available_list'])
            pool_set = set(pool)
            state = self.direct_state.get(cat, {})
            # Keep accepted / moved / rejected images visible so pagination stays stable.
            for p, status in state.items():
                if status in ('accept', 'moved', 'reject') and p not in pool_set:
                    pool_set.add(p)
                    pool.append(p)
            for p in stats['selected_list']:
                if p not in pool_set:
                    pool_set.add(p)
                    pool.append(p)
            return pool

        pool = build_pool(s)
        if not pool and s['blacklisted'] > 0 and s['candidate_after_forced'] > 0:
            self.recycle_regular_blacklist(cat)
            s = self.get_stats(cat)
            pool = build_pool(s)

        pool = self._direct_order_pool(pool)

        if self.excluded_subfolders:
            pool = [p for p in pool
                    if os.path.basename(os.path.dirname(p)) not in self.excluded_subfolders]

        selected_set = set(s['selected_list'])

        filter_val = self.direct_ext_filter_var.get()
        if filter_val == "JFIF/AVIF Only":
            pool = [p for p in pool if p.lower().endswith(('.jfif', '.avif'))]
        elif filter_val == "Unrated Only":
            blacklisted_set = set(s.get('blacklisted_list', []))
            forced_blacklisted_set = set(s.get('forced_blacklisted_list', []))
            rated_set = selected_set | blacklisted_set | forced_blacklisted_set
            pool = [p for p in pool if p not in rated_set]

        search_term = self.direct_search_var.get().strip().lower()
        if search_term:
            pool = [p for p in pool if search_term in os.path.basename(p).lower()]

        self.direct_pool = list(pool)

        if page is not None:
            self.direct_page = page
        max_page = max(0, (len(pool) - 1) // DIRECT_BATCH_SIZE)
        self.direct_page = min(max(0, self.direct_page), max_page)

        self.direct_page_entry.delete(0, tk.END)
        self.direct_page_entry.insert(0, str(self.direct_page + 1))
        self.direct_page_count_label.config(text=f"of {max_page + 1}")

        start_idx = self.direct_page * DIRECT_BATCH_SIZE
        batch = pool[start_idx:start_idx + DIRECT_BATCH_SIZE]
        self.direct_batch = batch

        if not batch:
            self.direct_progress_label.config(text="Nothing left to review in this category.")
            ttk.Label(self.direct_grid_frame,
                      text="✔ No remaining candidates in this category.",
                      font=('Arial', 13, 'bold')).grid(row=0, column=0, padx=20, pady=40)
            self._update_queue_label()
            return

        cat_state = self.direct_state.get(cat, {})
        for idx, path in enumerate(batch):
            if cat_state.get(path) == 'moved':
                self.direct_status[path] = 'moved'
            elif path in self.pending_moves:
                self.direct_status[path] = 'queued'
            elif path in cat_state:
                self.direct_status[path] = cat_state[path]
            elif path in selected_set:
                self.direct_status[path] = 'accept'
            else:
                self.direct_status[path] = None
            r, c = (idx // DIRECT_COLS) * 2, idx % DIRECT_COLS
            self._build_direct_cell(path, r, c)

        for path, status in self.direct_status.items():
            if status is not None:
                self._paint_direct_cell(path)

        self.direct_grid_frame.update_idletasks()
        self.direct_canvas.configure(scrollregion=self.direct_canvas.bbox('all'))
        self.direct_canvas.yview_moveto(0)
        self._update_direct_progress_label()

    def _build_direct_cell(self, path, row, col):
        cat = self.direct_current_category
        cat_state = self.direct_state.get(cat, {})

        # Compact placeholder only for files that were physically moved and are gone.
        should_show_placeholder = cat_state.get(path) == 'moved' and not os.path.exists(path)

        if should_show_placeholder:
            frame = tk.Frame(self.direct_grid_frame, bg=DARK_BG_ALT, highlightthickness=2,
                             highlightbackground=MOVE_COLOR, highlightcolor=MOVE_COLOR,
                             width=60, height=80)
            frame.grid(row=row, column=col, padx=6, pady=6, sticky='n')
            frame.grid_propagate(False)

            icon_lbl = tk.Label(frame, text="✓", font=('Arial', 24, 'bold'),
                                bg=MOVE_COLOR, fg='#1e1e1e', width=3, height=1)
            icon_lbl.pack(pady=(10, 5))

            status_lbl = tk.Label(frame, text="MOVED", bg=DARK_BG_ALT, fg=MOVE_COLOR,
                                  font=('Arial', 7, 'bold'))
            status_lbl.pack()

            fn = os.path.basename(path)
            name_lbl = tk.Label(frame, text=fn[:20] + ('...' if len(fn) > 20 else ''),
                                bg=DARK_BG_ALT, fg='#888888', font=('Arial', 6))
            name_lbl.pack(fill='x', pady=(2, 0))

            self.direct_cells[path] = {'frame': frame, 'status': status_lbl,
                                       'folder': None, 'name': name_lbl}

            def show_info_handler(e, p=path):
                self._show_moved_file_info(p)

            for w in (icon_lbl, status_lbl, name_lbl, frame):
                w.bind('<Button-1>', show_info_handler)
                w.config(cursor='hand2')
            return

        frame = tk.Frame(self.direct_grid_frame, bg=DARK_BG_ALT, highlightthickness=4,
                         highlightbackground=NEUTRAL_COLOR, highlightcolor=NEUTRAL_COLOR)
        frame.grid(row=row, column=col, padx=6, pady=6, sticky='n')

        photo = self.get_thumbnail(path, DIRECT_THUMB)
        if photo is not None:
            img_lbl = tk.Label(frame, image=photo, bg='black',
                               width=DIRECT_THUMB, height=DIRECT_THUMB, cursor='hand2')
            img_lbl.image = photo
        else:
            img_lbl = tk.Label(frame, text="⚠ unreadable", bg=DARK_BG_ALT, fg='#ff6666',
                               font=('Arial', 8, 'bold'), cursor='hand2')
        img_lbl.pack()

        fn = os.path.basename(path)
        name_lbl = tk.Label(frame, text=fn[:26] + ('...' if len(fn) > 26 else ''),
                            bg=DARK_BG_ALT, fg=DARK_FG, font=('Arial', 8))
        name_lbl.pack(fill='x')

        folder_lbl = tk.Label(frame,
                              text="⤷ " + (os.path.basename(os.path.dirname(path)) or '?'),
                              bg=DARK_BG_ALT, fg='#7fa8cc', font=('Arial', 7))
        folder_lbl.pack(fill='x')

        status_lbl = tk.Label(frame, text="PENDING", bg=DARK_BG_ALT, fg='#888888',
                              font=('Arial', 8, 'bold'))
        status_lbl.pack(fill='x')

        for w in (img_lbl, name_lbl, folder_lbl, status_lbl):
            w.bind('<Button-1>', lambda e, p=path: self.direct_mark(p, 'accept'))
            w.bind('<Button-3>', lambda e, p=path: self.direct_mark(p, 'reject'))
            w.bind('<Shift-Button-1>', lambda e, p=path: self.direct_move_image(p))
            w.bind('<Shift-Button-3>', lambda e, p=path: self.open_aspect_window(p))
            w.bind('<Double-Button-1>', lambda e, p=path: self.open_aspect_window(p))
            w.bind('<Control-Button-3>', lambda e, p=path: self.open_file_location(p))

        self.direct_cells[path] = {'frame': frame, 'status': status_lbl,
                                   'folder': folder_lbl, 'name': name_lbl}

    def _show_moved_file_info(self, path):
        """Show a tooltip-style dialog with full file name and path, copying path to clipboard"""
        tooltip = tk.Toplevel(self.root)
        tooltip.title("Moved File Info")
        tooltip.attributes('-topmost', True)

        x = tooltip.winfo_pointerx() + 10
        y = tooltip.winfo_pointery() + 10
        tooltip.geometry(f"+{x}+{y}")
        tooltip.overrideredirect(True)
        tooltip.configure(bg=DARK_BG_ALT, highlightthickness=2, highlightbackground=MOVE_COLOR)

        full_name = os.path.basename(path)
        name_label = tk.Label(tooltip, text=f"File: {full_name}",
                              bg=DARK_BG_ALT, fg=DARK_FG, font=('Consolas', 10, 'bold'),
                              anchor='w', padx=10, pady=5)
        name_label.pack(fill='x')

        full_path = os.path.abspath(path)
        path_label = tk.Label(tooltip, text=f"Original path: {full_path}",
                              bg=DARK_BG_ALT, fg='#AAAAAA', font=('Consolas', 9),
                              anchor='w', padx=10, pady=3, wraplength=500, justify='left')
        path_label.pack(fill='x')

        self.root.clipboard_clear()
        self.root.clipboard_append(full_path)
        self.root.update()

        info_label = tk.Label(tooltip, text="(Path copied to clipboard - click anywhere to close)",
                              bg=DARK_BG_ALT, fg='#666666', font=('Arial', 7, 'italic'),
                              anchor='center', padx=10, pady=5)
        info_label.pack(fill='x')

        def close_tooltip(event=None):
            try:
                tooltip.destroy()
            except Exception:
                pass

        tooltip.bind("<Button-1>", close_tooltip)
        tooltip.bind("<Button-3>", close_tooltip)
        for lbl in (name_label, path_label, info_label):
            lbl.bind("<Button-1>", close_tooltip)
            lbl.bind("<Button-3>", close_tooltip)

    # ---------------- queueing moves ----------------
    def direct_move_image(self, path):
        """SHIFT+LEFT-CLICK — queue a move (armed folder, or <Category>_Replacers/<subfolder>
        in replacer mode). Shift-click again to unqueue. Nothing touches the disk until
        'Process All Selections'."""
        if path in self.pending_moves:
            self._direct_unqueue(path)
            return 'break'

        if self.replacer_mode:
            cat = self.direct_current_category
            if not cat:
                self.mover_log_msg("⚠ No category selected. Select a category first.", QUEUE_COLOR)
                return 'break'
            source_dir = os.path.dirname(path)
            subfolder_name = os.path.basename(os.path.dirname(source_dir))
            target_folder = self.get_replacer_folder(cat, subfolder_name)
            if not target_folder:
                self.mover_log_msg("⚠ Scripts directory not set.", QUEUE_COLOR)
                return 'break'
            target_label = f"{cat}_Replacers" + (f"/{subfolder_name}" if subfolder_name else "")
            replacer = True
        else:
            if not self.mover_target_folder:
                self.mover_log_msg("⚠ No target folder armed. Click a folder in the list first.",
                                   QUEUE_COLOR)
                return 'break'
            target_folder = self.mover_target_folder
            target_label = os.path.basename(target_folder.rstrip("/\\")) or target_folder
            replacer = False

        if self.queue_file_move(path, target_folder, replacer=replacer):
            self.direct_status[path] = 'queued'
            self._paint_direct_cell(path)
            self.mover_log_msg(
                f"✔ Queued{' (REPLACER)' if replacer else ''}: "
                f"{os.path.basename(path)} → {target_label}")
            self._update_direct_progress_label()
        return 'break'

    def queue_file_move(self, old_path, dest_folder, replacer=False):
        """Record a move. The disk is NOT touched here."""
        if not old_path or not os.path.isfile(old_path):
            self.mover_log_msg("✖ Source file no longer exists on disk.", '#ff6666')
            return False
        if not dest_folder:
            self.mover_log_msg("✖ No destination folder.", '#ff6666')
            return False
        if not replacer and not os.path.isdir(dest_folder):
            self.mover_log_msg("✖ Target folder does not exist.", '#ff6666')
            return False
        if self._norm(os.path.dirname(old_path)) == self._norm(dest_folder):
            self.mover_log_msg("✖ Image is already in that folder.", '#ff6666')
            return False
        self.pending_moves[old_path] = {
            'dest': dest_folder,
            'category': self.direct_current_category,
            'replacer': replacer,
        }
        self._update_queue_label()
        return True

    def _direct_unqueue(self, path):
        self.pending_moves.pop(path, None)
        cat = self.direct_current_category
        prev = self.direct_state.get(cat, {}).get(path) if cat else None
        self.direct_status[path] = prev if prev in ('accept', 'reject') else None
        self._paint_direct_cell(path)
        self.mover_log_msg(f"Unqueued: {os.path.basename(path)}", '#bbbbbb')
        self._update_queue_label()
        self._update_direct_progress_label()

    # ---------------- marking ----------------
    def direct_mark(self, path, status):
        if path not in self.direct_status:
            return
        if self.direct_status[path] == 'moved':
            return
        if path in self.pending_moves:
            self.mover_log_msg("Queued for a move — SHIFT+LEFT-CLICK it again to unqueue first.",
                               QUEUE_COLOR)
            return
        if self.direct_status[path] == status:
            status = None  # clicking the same choice again un-marks it
        self.direct_status[path] = status

        cat = self.direct_current_category
        if cat:
            state = self.direct_state.setdefault(cat, {})
            if status is None:
                state.pop(path, None)
            else:
                state[path] = status

        self._paint_direct_cell(path)
        self._update_direct_progress_label()

        if self.direct_status and all(v is not None for v in self.direct_status.values()):
            self.direct_commit_batch(partial=False)

    def direct_mark_rest(self, status):
        self.root.after(10, lambda: self._direct_mark_rest_impl(status))

    def _direct_mark_rest_impl(self, status):
        if not self.direct_status:
            return
        cat = self.direct_current_category
        for p in list(self.direct_status.keys()):
            if self.direct_status.get(p) is None:
                self.direct_status[p] = status
                if cat:
                    self.direct_state.setdefault(cat, {})[p] = status
                self._paint_direct_cell(p)

        self._update_direct_progress_label()
        if all(v is not None for v in self.direct_status.values()):
            self.direct_commit_batch(partial=False)

    def _update_direct_progress_label(self):
        cat = self.direct_current_category
        if not cat:
            self.direct_progress_label.config(text="")
            return
        total = len(self.direct_status)
        done = sum(1 for v in self.direct_status.values() if v is not None)
        rejects = sum(1 for v in self.direct_status.values() if v == 'reject')
        accepts = sum(1 for v in self.direct_status.values() if v == 'accept')
        moved = sum(1 for v in self.direct_status.values() if v == 'moved')
        queued = len(self.pending_moves)

        s = self.get_stats(cat)
        extras = ""
        if moved:
            extras += f"   moved: {moved}"
        if queued:
            extras += f"   queued moves: {queued}"

        if self.direct_mode == 'remove':
            left = max(0, s['force_resolve_left'] - rejects)
            extra = "  ← surplus covered, rest auto-fills on commit!" if left == 0 else ""
            self.direct_progress_label.config(
                text=f"page {done}/{total}   |   marked REMOVE: {rejects}{extras}   |   "
                     f"removals still required: {left}{extra}")
        else:
            self.direct_progress_label.config(
                text=f"page {done}/{total}   |   accept: {accepts}   reject: {rejects}{extras}   |   "
                     f"still needed: {max(0, s['needed'] - accepts)}")
        self._update_queue_label()

    # ---------------- commit / process ----------------
    def direct_commit_batch(self, partial=False):
        """Commit accept/reject marks on the current page (bookkeeping only; never moves files)."""
        cat = self.direct_current_category
        if not cat or not self.direct_status:
            return

        mode = self.direct_mode
        accepted = [p for p, v in self.direct_status.items() if v == 'accept']
        rejected = [p for p, v in self.direct_status.items() if v == 'reject']

        if partial and not accepted and not rejected:
            q = len(self.pending_moves)
            extra = (f"\n\n{q} file move(s) are queued — use 'Process All Selections' "
                     f"to execute them.") if q else ""
            messagebox.showinfo("Commit Page", "Nothing marked on this page yet." + extra)
            return

        valid = set(self.get_all_images_from_category(cat))
        bucket = self.dataset.setdefault(cat, [])
        for p in accepted:
            if p not in valid:
                continue
            if p not in bucket:
                bucket.append(p)
            self._untrack_auto(cat, p)

        if mode == 'remove':
            fbl = self.forced_blacklist.setdefault(cat, [])
            for p in rejected:
                if p not in valid:
                    continue
                if p not in fbl:
                    fbl.append(p)
                if p in self.blacklist.get(cat, []):
                    self.blacklist[cat].remove(p)
        else:
            bl = self.blacklist.setdefault(cat, [])
            for p in rejected:
                if p not in valid:
                    continue
                if p not in bl:
                    bl.append(p)

        self.save_data(silent=True)

        if cat in self.direct_state:
            for p in accepted + rejected:
                self.direct_state[cat].pop(p, None)
            if not self.direct_state[cat]:
                del self.direct_state[cat]

        auto_added = self.auto_resolve_category_if_ready(cat)
        self.run_auto_pipeline()
        self.update_category_listbox()
        self.direct_load_batch()

        if auto_added:
            messagebox.showinfo(
                "Category Complete",
                f"'{cat}' hit its removal quota.\n\n"
                f"{auto_added} remaining image(s) were auto-accepted to fill the target of "
                f"{self.get_target()}.")

    def direct_process_all_selections(self):
        """THE trigger for everything:
          * accept / reject marks of the current category (bookkeeping)
          * EVERY queued move, in every category (replacer + armed-folder), physically on disk
        """
        cat = self.direct_current_category
        state = self.direct_state.get(cat, {}) if cat else {}
        accepted = [p for p, v in state.items() if v == 'accept']
        rejected = [p for p, v in state.items() if v == 'reject']
        moves = dict(self.pending_moves)

        if not accepted and not rejected and not moves:
            messagebox.showinfo("Nothing to Process",
                                "No accept/reject marks and no queued moves.")
            return

        n_repl = sum(1 for m in moves.values() if m.get('replacer'))
        n_mov = len(moves) - n_repl

        parts = []
        if accepted or rejected:
            parts.append(f"Marks in '{cat}':\n"
                         f"  • {len(accepted)} accept\n"
                         f"  • {len(rejected)} reject")
        if moves:
            dest_counts = {}
            for m in moves.values():
                dest_counts[m['dest']] = dest_counts.get(m['dest'], 0) + 1
            lines = [f"Queued file moves (all categories): {len(moves)}",
                     f"  • {n_repl} → replacer folders",
                     f"  • {n_mov} → armed folders"]
            for dest, n in sorted(dest_counts.items(), key=lambda kv: -kv[1])[:8]:
                lines.append(f"      {n} → {dest}")
            if len(dest_counts) > 8:
                lines.append(f"      … and {len(dest_counts) - 8} more destination(s)")
            parts.append("\n".join(lines))
        parts.append("Queued files will be PHYSICALLY moved. Continue?")

        if not messagebox.askyesno("Process All Selections", "\n\n".join(parts)):
            return

        # 1) accept / reject bookkeeping (current category) — done BEFORE the moves so the
        #    path remap afterwards also repoints these entries.
        processed_accepts = processed_rejects = 0
        if cat and (accepted or rejected):
            valid = set(self.get_all_images_from_category(cat))
            bucket = self.dataset.setdefault(cat, [])
            for p in accepted:
                if p not in valid:
                    continue
                if p not in bucket:
                    bucket.append(p)
                self._untrack_auto(cat, p)
                processed_accepts += 1

            mode = self.direct_mode
            for p in rejected:
                if p not in valid:
                    continue
                if mode == 'remove':
                    fbl = self.forced_blacklist.setdefault(cat, [])
                    if p not in fbl:
                        fbl.append(p)
                    if p in self.blacklist.get(cat, []):
                        self.blacklist[cat].remove(p)
                else:
                    bl = self.blacklist.setdefault(cat, [])
                    if p not in bl:
                        bl.append(p)
                processed_rejects += 1
            self.save_data(silent=True)

        # 2) physical moves (everything queued, saved once at the end)
        summary = self._execute_pending_moves()

        # 3) refresh
        auto_added = self.auto_resolve_category_if_ready(cat) if cat else 0
        self.run_auto_pipeline()
        self.update_stats_view()
        self.update_category_listbox()
        if cat:
            self.direct_load_batch()
        else:
            self._update_queue_label()

        lines = [f"  • {processed_accepts} accepted",
                 f"  • {processed_rejects} rejected",
                 f"  • {summary['moved']} file(s) moved "
                 f"({summary['replacer']} replacer, {summary['mover']} armed-folder)"]
        failed = summary['failed']
        if failed:
            lines.append(f"\n{len(failed)} move(s) FAILED:")
            for p, err in failed[:12]:
                lines.append(f"  - {os.path.basename(p)}: {err}")
            if len(failed) > 12:
                lines.append(f"  … and {len(failed) - 12} more")
            still = sum(1 for p, _ in failed if p in self.pending_moves)
            if still:
                lines.append(f"\n{still} of them are still queued — fix the cause and run "
                             f"Process All Selections again.")
            messagebox.showwarning("Process Complete (with errors)", "\n".join(lines))
        else:
            messagebox.showinfo("Process Complete", "\n".join(lines))

        if auto_added:
            messagebox.showinfo(
                "Category Complete",
                f"'{cat}' hit its removal quota.\n\n"
                f"{auto_added} remaining image(s) were auto-accepted to fill the target of "
                f"{self.get_target()}.")

    def direct_reset_current_batch(self):
        """Reset accept/reject marks on the current page to Pending."""
        if not self.direct_status:
            return
        if not messagebox.askyesno(
                "Reset Current Batch",
                "Clear all pending Accept/Reject marks on this page?\n\n"
                "This does NOT undo anything already saved by 'Commit Page' or "
                "'Process All Selections', and it leaves queued/moved files alone."):
            return

        cat = self.direct_current_category
        for p in list(self.direct_status.keys()):
            if self.direct_status[p] == 'moved' or p in self.pending_moves:
                continue
            self.direct_status[p] = None
            if cat:
                self.direct_state.get(cat, {}).pop(p, None)
            self._paint_direct_cell(p)
        self._update_direct_progress_label()

    # ---------------- paging ----------------
    def _direct_total_pages(self):
        total = len(self.direct_pool or [])
        if total == 0:
            return 1
        return (total + DIRECT_BATCH_SIZE - 1) // DIRECT_BATCH_SIZE

    def direct_prev_page(self):
        if self.direct_page > 0:
            self.direct_page -= 1
            self.direct_load_batch()

    def direct_next_page(self):
        if not self.direct_current_category:
            return
        max_page = self._direct_total_pages() - 1
        if self.direct_page < max_page:
            self.direct_page += 1
            self.direct_load_batch()

    def direct_go_to_page(self):
        try:
            page_str = self.direct_page_entry.get().strip()
            if not page_str:
                return
            page = int(page_str) - 1
            if not self.direct_current_category:
                return
            max_page = self._direct_total_pages() - 1
            if 0 <= page <= max_page:
                self.direct_page = page
                self.direct_load_batch()
        except ValueError:
            pass

    def direct_set_ext_filter(self):
        self.direct_page = 0
        self.direct_load_batch()

    def direct_reset_category(self):
        """Reset all ratings for a category so it can be rebuilt from scratch."""
        cat = self.direct_current_category
        if not cat:
            messagebox.showwarning("No Category", "Please select a category first.")
            return

        selected = set(self.dataset.get(cat, []))
        blacklisted = set(self.blacklist.get(cat, []))
        forced_blacklisted = set(self.forced_blacklist.get(cat, []))
        total_ratings = len(selected) + len(blacklisted) + len(forced_blacklisted)

        if total_ratings == 0:
            messagebox.showinfo("Reset Category",
                                f"No ratings to clear for '{cat}'.\n\n"
                                f"The category is already in its initial state.")
            return

        if not messagebox.askyesno(
                "Reset Category Ratings",
                f"Are you sure you want to reset ALL ratings for category '{cat}'?\n\n"
                f"This will:\n"
                f"• Clear {len(selected)} selected/accepted image(s)\n"
                f"• Clear {len(blacklisted)} rejected image(s)\n"
                f"• Clear {len(forced_blacklisted)} force-rejected image(s)\n\n"
                f"Total: {total_ratings} rating(s) will be cleared.\n\n"
                f"The category will be rebuilt from scratch with no prior decisions."):
            return

        self.dataset.pop(cat, None)
        self.blacklist.pop(cat, None)
        self.forced_blacklist.pop(cat, None)
        self.direct_state.pop(cat, None)

        self.direct_page = 0
        self.direct_search_var.set('')
        self.save_data(silent=True)

        self.run_auto_pipeline()
        self.update_category_listbox()
        self.refresh_direct_category_list()
        self.direct_load_batch()

        messagebox.showinfo("Category Reset Complete",
                            f"All ratings for '{cat}' have been cleared.\n\n"
                            f"The category is now ready to be rebuilt from scratch.")

    # ==================================================================
    # FILE STATS tab
    # ==================================================================
    def build_stats_tab(self):
        container = ttk.Frame(self.stats_frame)
        container.pack(fill='both', expand=True, padx=20, pady=20)

        ttk.Label(container, text="File Visibility Statistics",
                  font=('Arial', 16, 'bold')).pack(pady=(0, 15))

        info_text = ("This tab shows why some files on disk don't appear in the UI.\n"
                     "Files can be hidden due to coarse-grained elimination (low resolution),\n"
                     "or simply be already selected/rejected.")
        ttk.Label(container, text=info_text, justify='center',
                  font=('Arial', 10)).pack(pady=(0, 15))

        cat_frame = ttk.Frame(container)
        cat_frame.pack(fill='x', pady=10)
        ttk.Label(cat_frame, text="Select Category:", font=('Arial', 11)).pack(side='left', padx=(0, 10))
        self.stats_category_var = tk.StringVar()
        self.stats_category_combo = ttk.Combobox(cat_frame, textvariable=self.stats_category_var,
                                                 state='readonly', width=30)
        self.stats_category_combo.pack(side='left')
        self.stats_category_combo.bind('<<ComboboxSelected>>', lambda e: self.update_stats_view())
        ttk.Button(cat_frame, text="⟲ Refresh", command=self.update_stats_view).pack(side='left', padx=(10, 0))

        opt = ttk.Frame(container)
        opt.pack(fill='x', pady=(4, 0))
        self.coarse_var = tk.BooleanVar(value=self.coarse_elimination)
        ttk.Checkbutton(opt,
                        text="Coarse-grained elimination: in categories with >100% more images than "
                             "the smallest, discount low-res images (< 720×1280 px total)",
                        variable=self.coarse_var,
                        command=self.toggle_coarse_elimination).pack(side='left')
        ttk.Button(opt, text="Scan Resolutions Now",
                   command=lambda: self.start_coarse_resolution_scan(manual=True)
                   ).pack(side='left', padx=(10, 0))

        self.stats_display_frame = ttk.Frame(container)
        self.stats_display_frame.pack(fill='both', expand=True, pady=20)

        self.update_stats_view()

    def update_stats_view(self):
        if not hasattr(self, 'stats_display_frame'):
            return

        names = [c for c in self.categories if len(self.get_all_images_from_category(c)) > 0]
        self.stats_category_combo['values'] = names
        category = self.stats_category_var.get()
        if category not in names:
            category = names[0] if names else ''
            self.stats_category_var.set(category)

        for w in self.stats_display_frame.winfo_children():
            w.destroy()

        if not category:
            ttk.Label(self.stats_display_frame, text="No category with images to show.",
                      font=('Arial', 12)).pack(pady=50)
            return

        raw = self.get_raw_images_from_category(category)
        s = self.get_stats(category)
        visible_set = (set(s['selected_list']) | set(s['regular_blacklist_list'])
                       | set(s['forced_blacklist_list']) | set(s['available_list']))

        ext_counts, visible_ext, hidden_ext, hidden_folders = {}, {}, {}, {}
        for img in raw:
            ext = os.path.splitext(img)[1].lower()
            ext_counts[ext] = ext_counts.get(ext, 0) + 1
            if img in visible_set:
                visible_ext[ext] = visible_ext.get(ext, 0) + 1
            else:
                hidden_ext[ext] = hidden_ext.get(ext, 0) + 1
                fname = os.path.basename(os.path.dirname(img)) or os.path.dirname(img)
                hidden_folders[fname] = hidden_folders.get(fname, 0) + 1

        total_on_disk = len(raw)
        hidden_total = sum(hidden_ext.values())
        visible_total = total_on_disk - hidden_total
        sorted_folders = sorted(hidden_folders.items(), key=lambda x: x[1], reverse=True)[:10]

        bar = "━" * 54
        lines = [
            f"Category: {category}",
            f"Coarse elimination: {'ON' if self.coarse_elimination else 'OFF'}",
            f"Queued moves (all categories): {len(self.pending_moves)}",
            "",
            "📊 OVERVIEW",
            bar,
            f"Total files on disk:        {total_on_disk}",
            f"Visible in UI:              {visible_total}",
            f"  • Selected:               {s['selected']}",
            f"  • Regular rejected:       {s['blacklisted']}",
            f"  • Force rejected:         {s['forced_blacklisted']}",
            f"  • Available (unrated):    {s['available']}",
            f"Hidden (coarse eliminated): {hidden_total}",
            "",
            "📁 FILE EXTENSION BREAKDOWN (All files on disk)",
            bar,
        ]
        for ext in sorted(ext_counts):
            lines.append(f"{ext.upper():8}: {ext_counts[ext]:5} total  |  "
                         f"{visible_ext.get(ext, 0):5} visible  |  {hidden_ext.get(ext, 0):5} hidden")
        if sorted_folders:
            lines += ["", "📂 TOP FOLDERS WITH HIDDEN FILES", bar]
            for folder, count in sorted_folders:
                lines.append(f"  {folder}: {count} hidden files")

        text = tk.Text(self.stats_display_frame, wrap='word', height=30,
                       bg=DARK_BG_ALT, fg=DARK_FG, font=('Consolas', 11))
        text.pack(fill='both', expand=True, padx=10, pady=10)
        text.insert('1.0', "\n".join(lines))
        text.config(state='disabled')

    # ==================================================================
    # Tab switching / persistence
    # ==================================================================
    def on_tab_changed(self, event):
        t = self._active_tab()
        if t == 'Direct':
            self.refresh_direct_category_list()
            self.direct_load_batch()
        elif t == 'File Stats':
            self.update_stats_view()
        elif t == 'Directory Builder':
            self.update_category_listbox()

    def save_data(self, silent=False):
        self.profiles[self.current_profile_name] = self._capture_active_profile_dict()
        data = {
            'categories': self.categories,
            'image_tags': self.image_tags,
            'known_tags': self.known_tags,
            'tag_categories': self.tag_categories,
            'current_profile': self.current_profile_name,
            'profiles': self.profiles,
        }

        try:
            if os.path.exists(DATA_FILE):
                shutil.copyfile(DATA_FILE, DATA_FILE + '.bak')
            tmp = DATA_FILE + '.tmp'
            with open(tmp, 'w') as f:
                json.dump(data, f, indent=4)
            os.replace(tmp, DATA_FILE)
            if not silent:
                messagebox.showinfo("Success", "Data saved!")
        except PermissionError:
            if not silent:
                messagebox.showerror("Error", "Save failed: File is locked by another process")
            else:
                print("Autosave failed: File is locked by another process")
        except Exception as e:
            if not silent:
                messagebox.showerror("Error", f"Save failed: {e}")
            else:
                print(f"Autosave failed: {e}")

    def load_resolution_cache(self):
        self._resolution_cache = {}
        try:
            if os.path.exists(RESOLUTION_CACHE_FILE):
                with open(RESOLUTION_CACHE_FILE, 'r') as f:
                    self._resolution_cache = json.load(f) or {}
        except Exception as e:
            print(f"Resolution cache load error: {e}")
            self._resolution_cache = {}

    def save_resolution_cache(self):
        try:
            tmp = RESOLUTION_CACHE_FILE + '.tmp'
            with open(tmp, 'w') as f:
                json.dump(self._resolution_cache, f)
            os.replace(tmp, RESOLUTION_CACHE_FILE)
        except Exception as e:
            print(f"Resolution cache save error: {e}")

    def load_data(self):
        try:
            if os.path.exists(DATA_FILE):
                with open(DATA_FILE, 'r') as f:
                    data = json.load(f)

                self.categories = data.get('categories', {})
                self.image_tags = data.get('image_tags', {})
                self.known_tags = data.get('known_tags', [])
                self.tag_categories = data.get('tag_categories', {}) or {}
                if not self.tag_categories:
                    self.tag_categories = {'General': list(self.known_tags)}
                else:
                    categorized = {tag for tags in self.tag_categories.values() for tag in tags}
                    uncategorized = [t for t in self.known_tags if t not in categorized]
                    if uncategorized:
                        self.tag_categories.setdefault('General', []).extend(uncategorized)

                if 'profiles' in data:
                    self.profiles = data.get('profiles', {}) or {}
                    self.current_profile_name = data.get('current_profile', DEFAULT_PROFILE_NAME)
                    if not self.profiles:
                        self.profiles = {DEFAULT_PROFILE_NAME: self._blank_profile()}
                        self.current_profile_name = DEFAULT_PROFILE_NAME
                    if self.current_profile_name not in self.profiles:
                        self.current_profile_name = sorted(self.profiles.keys(), key=str.lower)[0]
                else:
                    legacy = {
                        'dataset': data.get('dataset', {}),
                        'blacklist': data.get('blacklist', {}),
                        'forced_blacklist': data.get('forced_blacklist', {}),
                        'image_tiers': data.get('image_tiers', {}),
                        'auto_forced_added': data.get('auto_forced_added', {}),
                        'auto_resolve_added': data.get('auto_resolve_added', {}),
                        'manual_target': data.get('manual_target', None),
                        'auto_include': data.get('auto_include', True),
                        'coarse_elimination': data.get('coarse_elimination', False),
                        'direct_state': {'direct_category': None},
                    }
                    self.profiles = {DEFAULT_PROFILE_NAME: legacy}
                    self.current_profile_name = DEFAULT_PROFILE_NAME

                self._activate_profile(self.current_profile_name)
                return
        except Exception as e:
            print(f"Load error: {e}")

        self.categories, self.image_tags, self.known_tags = {}, {}, []
        self.tag_categories = {}
        self.profiles = {DEFAULT_PROFILE_NAME: self._blank_profile()}
        self.current_profile_name = DEFAULT_PROFILE_NAME
        self._activate_profile(self.current_profile_name)

    def on_close(self):
        self._scan_cancelled = True

        if self.pending_moves:
            n = len(self.pending_moves)
            ans = messagebox.askyesnocancel(
                "Unprocessed queued moves",
                f"{n} queued file move(s) have not been processed yet.\n\n"
                f"Yes  = move them now, then quit\n"
                f"No   = discard them and quit\n"
                f"Cancel = go back")
            if ans is None:
                self._scan_cancelled = False
                return
            if ans:
                summary = self._execute_pending_moves()
                if summary['failed']:
                    detail = "\n".join(f"  - {os.path.basename(p)}: {e}"
                                       for p, e in summary['failed'][:12])
                    if not messagebox.askyesno(
                            "Some moves failed",
                            f"{len(summary['failed'])} move(s) failed:\n{detail}\n\n"
                            f"Quit anyway?"):
                        self._scan_cancelled = False
                        return

        if self.aspect_window is not None and self.aspect_window.winfo_exists():
            self.aspect_window.destroy()
        self.save_resolution_cache()
        self.save_data(silent=True)
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    app = BalancerApp(root)
    root.mainloop()