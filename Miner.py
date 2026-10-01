
import sys
import os
import json
import shutil
import tempfile
import uuid
import re
import bisect
import difflib
from datetime import datetime

from PyQt5.QtCore import (
    Qt, QSize, QPoint, QPointF, QRect, pyqtSignal, QObject, QRunnable,
    QThreadPool, QThread, QTimer, QEvent, QMimeData, QUrl, QDate
)
from PyQt5.QtGui import (QPixmap, QColor, QPalette, QImageReader, QCursor,
                         QDrag, QPainter, QPen)
# NOTE: qRegisterDraggedWidget is not part of PyQt5 — the old "drag proxy"
# registration that referenced it has been removed; drag events are now
# forwarded manually by DraggableCell itself.
from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QLabel, QVBoxLayout, QHBoxLayout,
    QPushButton, QComboBox, QMessageBox, QSplitter, QAbstractItemView,
    QListWidget, QListWidgetItem, QLineEdit, QTabWidget, QFileDialog,
    QGroupBox, QFormLayout, QCheckBox, QInputDialog, QMenu, QDateEdit, QSpinBox
)

# =============================================================================
# Configuration
# =============================================================================
BALANCER_DATA_FILE = "balancer_data.json"
RATER_DATA_FILE = "image_ratings.json"
SWAP_LOG_FILENAME = "swap_log.json"
DIRECTORY_HISTORY_FILENAME = "rated_directory_history.json"
CLUSTER_DATA_FILENAME = "cluster_groups.json"

THUMB_SIZE = 120
DEFAULT_PROFILE_NAME = "Default"

PAGE_SIZE_OPTIONS = [24, 48, 96, 144]
DEFAULT_PAGE_SIZE = 48


MAX_DIRECTORY_HISTORY = 25
ALL_DIRECTORIES_LABEL = "— All Directories (unfiltered) —"

MAX_THUMBNAIL_THREADS = min(8, (os.cpu_count() or 4) * 2)

# Container styles
STYLE_PENDING = "background-color:#3a3d90; border:2px solid #f5c518; border-radius:8px;"
STYLE_GROUP_MEMBER = "background-color:#1f3a1a; border:2px solid #4caf50; border-radius:8px;"
STYLE_GROUP_PRIME = "background-color:#3d2410; border:2px solid #ff9800; border-radius:8px;"
STYLE_STAGED = "background-color:#14323d; border:2px dashed #29b6f6; border-radius:8px;"
STYLE_SELECTED_FOR_GROUPING = "background-color:#3d1432; border:2px solid #e91e63; border-radius:8px;"
STYLE_VACANT = "background-color:#141420; border:2px dashed #55576a; border-radius:8px;"
STYLE_HL = "background-color:#26324a; border:2px solid #f5c518; border-radius:8px;"
STYLE_NONE = ""

ENLARGED_LOAD_SIZE = 900
ENLARGED_DISPLAY_SIZE = 700

VACANT_TOKEN = ""  # what a vacant slot holds in the dataset list


# =============================================================================
# "Date created" ordering + filter helpers (rated + selected galleries)
# =============================================================================
# Order-by combos: how the tiles are ARRANGED by creation date.  None keeps
# whatever order the data source already provides (rating order for the
# rated pool, slot order for the selected pool).
DATE_ORDER_OPTIONS = [
    ("⏳ Default order", None),
    ("⏳ Oldest first", "asc"),
    ("⏳ Newest first", "desc"),
    ("🏷️ By file name (similar together)", "name"),
]


def _name_sort_key(path):
    """Natural-sort key for a file path's BASE NAME: case-insensitive, with
    embedded digit runs compared numerically (so img2 sorts before img10).
    Files whose name can't be read sort to the very end."""
    if not path:
        return (1, "", ())
    base = os.path.basename(str(path)).lower()
    parts = []
    for chunk in re.split(r"(\d+)", base):
        if chunk.isdigit():
            parts.append((1, int(chunk), ""))
        elif chunk:
            parts.append((0, 0, chunk))
    return (0, 0, tuple(parts))


def _filename_similarity_order(items, get_path):
    """Order ``items`` by FILE NAME SIMILARITY — cheap and O(n log n).

    No pairwise comparison is performed (no greedy nearest-neighbour walk,
    no SequenceMatcher over every atom of every name pair — that was an
    O(n^2) trap that froze the UI on large galleries).  Instead, similar
    names naturally become ADJACENT once sorted, so we sort each filename
    under three complementary natural-sort keys and round-robin-merge the
    three lists:

      1. forward   – clusters by shared PREFIX   ('DSC_0012' vs 'DSC_0013')
      2. reversed  – clusters by shared SUFFIX   ('cat_day' vs 'dog_day')
      3. middle-out – clusters by shared STEM   ('IMG_a7x' vs 'IMG_b7y')

    A tiny final pass swaps neighbours when swapping strictly increases the
    sum of adjacent common-prefix lengths — at most one pass, each check
    O(name length), so it cannot stall.  The result is fully deterministic
    (identical layout on every rebuild → grouping never reshuffles the
    grid), and empty/unknown names sink to the end in stable order.
    """
    n = len(items)
    if n < 2:
        return list(items)
    keys = [_name_sort_key(get_path(it)) for it in items]
    bases = []
    for k in keys:
        toks = []
        for t in k[2]:
            if t[0] == 1:
                toks.append("%012d" % t[1])
            else:
                toks.append(t[2])
        bases.append("".join(toks))
    unknown = sorted((i for i in range(n) if not bases[i]),
                     key=lambda i: (keys[i], i))
    known = [i for i in range(n) if bases[i]]
    if not known:
        return [items[i] for i in unknown]
    if len(known) < 3:
        order = sorted(known, key=lambda i: (keys[i], i))
        order.extend(unknown)
        return [items[i] for i in order]

    # --- three single-pass sorts (O(n log n), no pairwise work) ---------
    fwd = sorted(known, key=lambda i: (keys[i], i))
    rev = sorted(known, key=lambda i: (bases[i][::-1], keys[i], i))
    mid = sorted(known, key=lambda i: (bases[i][len(bases[i]) // 2:],
                                       keys[i], i))

    # --- round-robin merge, skipping duplicates (stable, deterministic) -
    merged = []
    seen = set()
    for src in (fwd, rev, mid):
        for i in src:
            if i not in seen:
                seen.add(i)
                merged.append(i)
    order = merged

    # --- ONE bounded local-improvement pass (adjacent swaps only) -------
    def cpl(a, b):
        m = min(len(a), len(b))
        p = 0
        while p < m and a[p] == b[p]:
            p += 1
        return p

    changed = True
    while changed:
        changed = False
        for x in range(1, len(order) - 1):
            a, b, c = order[x - 1], order[x], order[x + 1]
            before = cpl(bases[a], bases[b]) + cpl(bases[b], bases[c])
            after = cpl(bases[a], bases[c]) + cpl(bases[c], bases[b])
            if after > before:
                order[x], order[x + 1] = order[x + 1], order[x]
                changed = True
    order.extend(unknown)
    return [items[i] for i in order]


DATE_FILTER_OPTIONS = [
    ("📅 Any date", None),
    ("📅 Created today", "today"),
    ("📅 Created this week", "week"),
    ("📅 Created this month", "month"),
    ("📅 Created this year", "year"),
    ("📅 On/after chosen date…", "from"),
    ("📅 Before chosen date…", "to"),
    ("📅 Between two dates…", "range"),
]


def file_created_date(path):
    """Best-effort CREATION date of an image file as a datetime.date.

    Windows exposes the real creation time via ``st_ctime``; on Unix it is
    only the metadata-change time, so we fall back to ``st_mtime`` there.
    Returns ``None`` when the file cannot be stat'ed (the caller decides how
    to treat unknown dates)."""
    try:
        st = os.stat(path)
    except OSError:
        return None
    ts = getattr(st, "st_birthtime", None)   # macOS / some BSDs
    if not ts:
        ts = st.st_ctime if os.name == "nt" else st.st_mtime
    try:
        return datetime.fromtimestamp(ts).date()
    except (OverflowError, OSError, ValueError):
        return None


def date_filter_matches(created, mode, d1, d2, today=None):
    """True when ``created`` (a datetime.date) passes the active window's
    date-created filter.  ``d1``/``d2`` are datetime.date bounds (either may
    be None); items with an UNKNOWN creation date always pass so they never
    silently vanish from a gallery."""
    if not mode or created is None:
        return True
    if today is None:
        today = datetime.now().date()
    if mode == "today":
        return created == today
    if mode == "week":
        return (today - created).days <= today.weekday() and created <= today
    if mode == "month":
        return created.year == today.year and created.month == today.month
    if mode == "year":
        return created.year == today.year
    if mode == "from":
        return d1 is None or created >= d1
    if mode == "to":
        return d2 is None or created <= d2
    if mode == "range":
        if d1 is not None and created < d1:
            return False
        if d2 is not None and created > d2:
            return False
        return True
    return True


# =============================================================================
# Dark Theme
# =============================================================================
DARK_STYLESHEET = """
QWidget { background-color:#1e1f22; color:#e6e6e6;
          font-family:"Segoe UI", Arial, sans-serif; font-size:10.5pt; }
QMainWindow { background-color:#17181a; }
QLabel { background: transparent; }
QLabel[role="heading"] { font-size:12pt; font-weight:600; color:#fff; padding:2px 0; }
QPushButton { background-color:#2b2d31; border:1px solid #3d3f44; border-radius:6px;
              padding:6px 14px; color:#e6e6e6; }
QPushButton:hover { background-color:#35373c; border-color:#5865f2; }
QPushButton:pressed { background-color:#23252a; }
QPushButton:disabled { color:#666870; border-color:#2c2d30; }
QListWidget { background-color:#1b1c1e; border:1px solid #2c2d30; border-radius:6px; outline:none; }
QListWidget::item { background-color:#232427; border-radius:8px; padding:6px; margin:4px; color:#dcdcdc; }
QListWidget::item:selected { background-color:#3a3d90; }
QComboBox { background-color:#26282c; border:1px solid #3d3f44; border-radius:5px;
            padding:5px 8px; color:#e6e6e6; }
QComboBox::drop-down { border:none; width:20px; }
QComboBox QAbstractItemView { background-color:#26282c; border:1px solid #3d3f44;
                              selection-background-color:#5865f2; }
QStatusBar { background-color:#17181a; color:#9a9da3; border-top:1px solid #2c2d30; }
QGroupBox { border:1px solid #3d3f44; border-radius:6px; margin-top:12px; font-weight:600; }
QGroupBox::title { subcontrol-origin:margin; left:10px; padding:0 5px; }
QCheckBox { spacing:6px; }
QCheckBox::indicator { width:16px; height:16px; border:1px solid #3d3f44;
                       border-radius:3px; background-color:#26282c; }
QCheckBox::indicator:checked { background-color:#5865f2; border-color:#5865f2; }
QTabWidget::pane { border:1px solid #3d3f44; border-radius:4px; }
QTabBar::tab { background-color:#26282c; border:1px solid #3d3f44; border-bottom:none;
               border-top-left-radius:6px; border-top-right-radius:6px;
               padding:6px 16px; color:#9a9da3; }
QTabBar::tab:selected { background-color:#1e1f22; color:#e6e6e6; border-bottom:2px solid #5865f2; }
QTabBar::tab:hover { background-color:#35373c; }
QMenu { background-color:#26282c; border:1px solid #3d3f44; }
QMenu::item { padding:6px 22px; color:#e6e6e6; }
QMenu::item:selected { background-color:#5865f2; }
QMenu::item:disabled { color:#7a7d83; }
"""


def apply_dark_theme(app):
    app.setStyle("Fusion")
    p = QPalette()
    p.setColor(QPalette.Window, QColor("#1e1f22"))
    p.setColor(QPalette.WindowText, QColor("#e6e6e6"))
    p.setColor(QPalette.Base, QColor("#232427"))
    p.setColor(QPalette.AlternateBase, QColor("#2b2d31"))
    p.setColor(QPalette.Text, QColor("#e6e6e6"))
    p.setColor(QPalette.Button, QColor("#2b2d31"))
    p.setColor(QPalette.ButtonText, QColor("#e6e6e6"))
    p.setColor(QPalette.Highlight, QColor("#5865f2"))
    p.setColor(QPalette.HighlightedText, QColor("#ffffff"))
    app.setPalette(p)
    app.setStyleSheet(DARK_STYLESHEET)


# =============================================================================
# GLOBAL HOTKEY TRACKER
# -----------------------------------------------------------------------------
# THE BUG LAST TIME: a widget-level keyPressEvent() never fires while a
# QListWidget has focus, so "G" was never observed and G+click did nothing.
# The only reliable way to know whether a key is *physically held* while a
# mouse click happens is an application-level event filter, which sees every
# key event delivered to every widget (including detached windows).
# =============================================================================
class HotkeyTracker(QObject):
    changed = pyqtSignal(bool)
    copy_pressed = pyqtSignal()      # Shift+C anywhere outside a text field
    rename_pressed = pyqtSignal()    # Shift+R pressed (arms rename mode)
    rename_released = pyqtSignal()   # Shift+R released (disarms rename mode)

    def __init__(self):
        super().__init__()
        self._g_held = False
        self._r_held = False

    def is_group_key_held(self):
        return self._g_held

    def is_rename_key_held(self):
        """True while Shift+R is physically held — galleries treat the next
        left-click on a GROUP tile as 'rename this group to the clipboard'."""
        return self._r_held

    def _set(self, value):
        if value != self._g_held:
            self._g_held = value
            self.changed.emit(value)

    @staticmethod
    def _is_text_sink(w):
        """Widgets that OWN Shift-based keystrokes.  Typing capital letters
        into a QLineEdit must never trigger the global Shift+C / Shift+R
        hotkeys, so those events are ignored while such a widget has focus."""
        while w is not None:
            if isinstance(w, (QLineEdit, QInputDialog)):
                return True
            p = getattr(w, "parentWidget", None)
            w = p() if callable(p) else None
        return False

    def _set_r(self, value):
        if value != self._r_held:
            self._r_held = value
            self.rename_pressed.emit() if value else self.rename_released.emit()

    def eventFilter(self, obj, event):
        t = event.type()
        if t == QEvent.KeyPress:
            if event.key() == Qt.Key_G and not event.isAutoRepeat():
                self._set(True)
            if not event.isAutoRepeat() and not self._is_text_sink(obj):
                mods = event.modifiers()
                if (event.key() == Qt.Key_C
                        and mods & Qt.ShiftModifier):
                    self.copy_pressed.emit()
                elif event.key() == Qt.Key_R and mods & Qt.ShiftModifier:
                    self._set_r(True)
        elif t == QEvent.KeyRelease:
            if event.key() == Qt.Key_G and not event.isAutoRepeat():
                self._set(False)
            if event.key() == Qt.Key_R and not event.isAutoRepeat():
                self._set_r(False)
        elif t in (QEvent.WindowDeactivate, QEvent.ApplicationDeactivate,
                   QEvent.FocusOut):
            # Never let the key get "stuck" if focus leaves mid-hold.
            self._set(False)
            self._set_r(False)
        return False


HOTKEYS = HotkeyTracker()


# =============================================================================
# Image helpers
# =============================================================================
def load_qimage(path, max_size=None):
    reader = QImageReader(path)
    reader.setAutoTransform(True)
    if max_size:
        size = reader.size()
        if size.isValid() and size.width() > 0 and size.height() > 0:
            reader.setScaledSize(size.scaled(max_size, max_size, Qt.KeepAspectRatio))
    return reader.read()


def make_pixmap(path, max_size=THUMB_SIZE):
    if not path:
        return QPixmap()
    try:
        img = load_qimage(path, max_size)
    except Exception:
        return QPixmap()
    if img.isNull():
        return QPixmap()
    return QPixmap.fromImage(img)


def path_is_under_directory(path, directory):
    if not directory:
        return True
    try:
        np_ = os.path.normcase(os.path.normpath(os.path.abspath(path)))
        nd_ = os.path.normcase(os.path.normpath(os.path.abspath(directory)))
    except Exception:
        return True
    return np_ == nd_ or np_.startswith(nd_ + os.sep)


def short_name(path, limit=20):
    name = os.path.basename(path) if path else "(empty)"
    return name if len(name) <= limit else name[: limit - 3] + "..."


# =============================================================================
# JSON helpers
# =============================================================================
def atomic_write_json(path, data):
    directory = os.path.dirname(os.path.abspath(path)) or "."
    fd, tmp = tempfile.mkstemp(dir=directory, suffix=".tmp")
    try:
        with os.fdopen(fd, "w") as f:
            json.dump(data, f, indent=2)
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            try:
                os.remove(tmp)
            except OSError:
                pass


def append_swap_log(log_path, record):
    log = []
    if os.path.exists(log_path):
        try:
            with open(log_path, "r") as f:
                log = json.load(f)
            if not isinstance(log, list):
                log = []
        except Exception:
            log = []
    log.append(record)
    atomic_write_json(log_path, log)


def load_directory_history(path):
    if path and os.path.exists(path):
        try:
            with open(path, "r") as f:
                data = json.load(f)
            if isinstance(data, dict):
                hist = data.get("history", [])
                last = data.get("last_selected")
                if isinstance(hist, list):
                    hist = [h for h in hist if isinstance(h, str)]
                    return hist, (last if isinstance(last, str) else None)
        except Exception as e:
            print(f"Error loading directory history: {e}")
    return [], None


def save_directory_history(path, history, last_selected):
    if not path:
        return
    try:
        atomic_write_json(path, {"history": history, "last_selected": last_selected})
    except Exception as e:
        print(f"Error saving directory history: {e}")


# =============================================================================
# Thumbnail thread pool
# =============================================================================
class ThumbnailSignals(QObject):
    finished = pyqtSignal(str, int, QPixmap)


class ThumbnailTask(QRunnable):
    def __init__(self, path, generation, max_size=THUMB_SIZE):
        super().__init__()
        self.setAutoDelete(True)
        self.path = path
        self.generation = generation
        self.max_size = max_size
        self.signals = ThumbnailSignals()

    def run(self):
        try:
            pm = make_pixmap(self.path, self.max_size)
        except Exception:
            pm = QPixmap()
        self.signals.finished.emit(self.path, self.generation, pm)


_THUMB_POOL = QThreadPool.globalInstance()
_THUMB_POOL.setMaxThreadCount(MAX_THUMBNAIL_THREADS)


# =============================================================================
# Cluster Manager
# =============================================================================
_CANON_CACHE = {}


def canon_path(path):
    """Canonical form of a filesystem path for identity comparisons.

    The same image can reach the app through different spellings — e.g.
    Qt's ``QUrl.toLocalFile()`` on Windows yields forward slashes
    (``C:/dir/img.jpg``) while other code paths store backslashes or
    relative forms (``.\\dir\\img.jpg``).  Exact string matching then fails
    and the SAME file looks like two distinct images: dropping an already
    grouped file into a new group "succeeds" a second time, producing a
    duplicate member entry that surfaces as a phantom unrated tile.

    This normalises separators, case (on case-insensitive OSes), relative
    segments and symlinks/junctions so identical files always compare
    equal.  It NEVER raises on missing files.

    MEMOISED: ``realpath``/``abspath`` hit the filesystem on every call,
    and galleries/badges/collapse checks ask the same handful of paths
    thousands of times per render.  Paths don't move mid-session, so one
    dict lookup replaces thousands of syscalls."""
    if not path:
        return ""
    key = str(path)
    cached = _CANON_CACHE.get(key)
    if cached is not None:
        return cached
    try:
        p = os.path.normcase(os.path.realpath(os.path.abspath(os.path.normpath(key))))
    except Exception:
        p = key
    _CANON_CACHE[key] = p
    return p


def pc_ok(a, b):
    """True when paths ``a`` and ``b`` point at the SAME file, comparing in
    canonical form.  Group members/primes are stored canonically while
    dataset slots keep whatever spelling they were placed with — raw string
    equality between the two silently fails (forward vs. backward slashes
    on Windows), which is why prime tiles used to stop highlighting."""
    if not a or not b:
        return False
    ca = a if a == canon_path(a) else canon_path(a)
    cb = b if b == canon_path(b) else canon_path(b)
    return ca == cb


class ClusterManager:
    """
    Burst-shoot groups.  Each group:
        { "id", "name", "prime": path|None, "members": [paths] }
    Persisted to cluster_groups.json next to the balancer data.

    All membership / prime comparisons go through ``canon_path`` so that
    differently-spelled paths to the same file can never create duplicate
    members or orphan a prime.

    A reverse index (``_member_to_gid``: canonical path -> [gid, ...]) is
    rebuilt once after every load/mutation so ``groups_for_path`` — used by
    every tile badge, restyle pass and hidden-path computation — is an
    O(1) dict lookup instead of a full scan of all groups × all members.
    """

    def __init__(self, filepath=None):
        self.filepath = filepath
        self.groups = {}
        self._counter = 0
        self._member_to_gid = {}   # canon_path -> [gid, ...]  (O(1) lookups)
        # Bumped on every persisted mutation so caches built on top of the
        # groups (hidden-path sets in the viewer) can invalidate cheaply.
        self.groups_version = 0
        if filepath and os.path.exists(filepath):
            self.load()
        self._rebuild_index()

    # ---- reverse index ---------------------------------------------------
    def _rebuild_index(self):
        """(Re)build canon_path -> [gids]. Call after bulk changes."""
        idx = {}
        for gid, g in self.groups.items():
            for m in g.get("members", []):
                idx.setdefault(canon_path(m), []).append(gid)
        self._member_to_gid = idx

    def _index_add(self, gid, c):
        lst = self._member_to_gid.setdefault(c, [])
        if gid not in lst:
            lst.append(gid)

    def _index_remove(self, gid, c):
        lst = self._member_to_gid.get(c)
        if not lst:
            return
        try:
            lst.remove(gid)
        except ValueError:
            pass
        if not lst:
            del self._member_to_gid[c]

    # ---- persistence -----------------------------------------------------
    def load(self, preferred_spellings=None):
        try:
            with open(self.filepath, "r") as f:
                data = json.load(f)
            groups = data.get("groups", {}) if isinstance(data, dict) else {}

            clean = {}
            dirty = False          # file contained duplicates / stale spellings
            for gid, g in groups.items():
                if not isinstance(g, dict):
                    continue
                raw_members = [m for m in g.get("members", []) if isinstance(m, str)]
                # De-duplicate members by CANONICAL path: legacy files may
                # hold the same image twice under different spellings
                # (forward vs. backward slashes, relative vs. absolute),
                # which used to surface as phantom unrated tiles.
                # When several spellings collapse into one entry, KEEP the
                # spelling that carries the rating data — never let the
                # dedupe leave us holding an unrated-looking variant.
                members = []
                seen = set()
                chosen = {}        # canon -> kept spelling
                for m in raw_members:
                    c = canon_path(m)
                    if c in seen:
                        dirty = True
                        prev = chosen.get(c)
                        if prev is not None and preferred_spellings:
                            prev_info = preferred_spellings.get(prev)
                            prev_rating = (int(prev_info.get("primary", 0))
                                           if isinstance(prev_info, dict) else 0)
                            new_info = preferred_spellings.get(m)
                            new_rating = (int(new_info.get("primary", 0))
                                          if isinstance(new_info, dict) else 0)
                            if new_rating > prev_rating:
                                chosen[c] = m
                        continue
                    seen.add(c)
                    chosen[c] = m
                    members.append(m)
                members = [chosen[canon_path(m)] for m in members]
                prime = g.get("prime")
                pc = canon_path(prime) if prime else None
                if prime != pc:
                    dirty = True
                if pc not in seen:
                    if prime is not None:
                        dirty = True
                    prime = None
                else:
                    prime = chosen.get(pc, pc)
                clean[gid] = {
                    "id": gid,
                    "name": g.get("name") or f"Group {len(clean) + 1}",
                    "prime": prime,
                    "members": members,
                    "category": g.get("category"),
                }
            self.groups = clean
            self._counter = data.get("counter", len(clean))
            self._rebuild_index()
            # One-time migration: rewrite the file in normalised form so any
            # other consumer of cluster_groups.json sees deduped members too.
            if dirty:
                self.save()
            return True
        except Exception as e:
            print(f"Error loading cluster data: {e}")
            return False

    def save(self):
        if not self.filepath:
            return False
        try:
            atomic_write_json(self.filepath,
                              {"counter": self._counter, "groups": self.groups})
            self.groups_version += 1
            return True
        except Exception as e:
            print(f"Error saving cluster data: {e}")
            return False

    # ---- CRUD ------------------------------------------------------------
    def create_group(self, name=None):
        self._counter += 1
        gid = uuid.uuid4().hex[:12]
        self.groups[gid] = {
            "id": gid,
            "name": name or f"Group {self._counter}",
            "prime": None,
            "members": [],
            "category": None,
        }
        self.save()
        return gid

    def delete_group(self, gid):
        if gid in self.groups:
            for m in self.groups[gid].get("members", []):
                self._index_remove(gid, canon_path(m))
            del self.groups[gid]
            self.save()

    def rename_group(self, gid, name):
        if gid in self.groups and name.strip():
            self.groups[gid]["name"] = name.strip()
            self.save()

    # ---- category tagging -------------------------------------------------
    def group_category(self, gid):
        g = self.groups.get(gid)
        return (g or {}).get("category")

    def set_group_category(self, gid, cat):
        g = self.groups.get(gid)
        if g is not None and g.get("category") != cat:
            g["category"] = cat
            self.save()

    def member_fits(self, gid, path, cat):
        """A group belongs to exactly ONE category (the active one when the
        first image landed in it).  Empty groups accept anything; populated
        groups only accept images from their own category."""
        g = self.groups.get(gid)
        if g is None:
            return False
        gc = g.get("category")
        return (gc is None) or (cat is None) or (gc == cat)

    def add_member(self, gid, path, category=None):
        g = self.groups.get(gid)
        if g is None or not path:
            return False
        c = canon_path(path)
        if not c or c in {canon_path(m) for m in g["members"]}:
            # already a member (possibly stored under a different spelling)
            return False
        g["members"].append(c)
        self._index_add(gid, c)
        if category and not g.get("category"):
            g["category"] = category
        self.save()
        return True

    def remove_member(self, gid, path):
        g = self.groups.get(gid)
        if not g:
            return
        c = canon_path(path)
        kept = [m for m in g["members"] if canon_path(m) != c]
        if len(kept) != len(g["members"]):
            self._index_remove(gid, c)
        g["members"] = kept
        if g["prime"] and canon_path(g["prime"]) == c:
            g["prime"] = None
        self.save()

    def set_prime(self, gid, path, balancer=None):
        """Set the prime image for a group. The PRIME is the group's
        representative: it always stays visible in the rated pool unless a
        member of the group actually sits in the Selected Images (dataset).

        If balancer is provided, only stale bookkeeping is cleaned up — the
        prime is NEVER force-injected into dataset slots and never gets
        excluded from the rated pool just because it was made prime."""
        g = self.groups.get(gid)
        if not g:
            return
        c = canon_path(path)
        members = g["members"]
        if c not in members:
            members.append(c)
            self._index_add(gid, c)
        g["prime"] = c
        self.save()

        # If balancer is provided, drop any exclusion that still points at
        # the prime but no longer corresponds to a real dataset slot or a
        # vacancy (leftovers from older versions used to hide the prime).
        if balancer is not None:
            profile = balancer.current_profile
            used = {canon_path(p) for p in balancer.get_used_paths(profile)}
            vacant_originals = set()
            vac = balancer.data.get("vacant_slots", {}).get(profile, {})
            for cats in vac.values():
                for info in cats.values():
                    op = (info or {}).get("original_path")
                    if op:
                        vacant_originals.add(canon_path(op))
            if c in used or c in vacant_originals:
                balancer.remove_excluded_path(profile, path)
                balancer.save()

    def clear_prime(self, gid):
        g = self.groups.get(gid)
        if g:
            g["prime"] = None
            self.save()

    # ---- queries ---------------------------------------------------------
    def get_group(self, gid):
        return self.groups.get(gid)

    def get_group_name(self, gid):
        g = self.groups.get(gid)
        return g["name"] if g else "?"

    def all_groups(self):
        return list(self.groups.values())

    def groups_for_path(self, path):
        """O(1) reverse-index lookup (was a full groups × members scan,
        which dominated badge/restyle time on large datasets)."""
        if not path:
            return []
        gids = self._member_to_gid.get(canon_path(path))
        return list(gids) if gids else []

    def primary_group_for_path(self, path):
        gids = self.groups_for_path(path)
        return gids[0] if gids else None

    def is_prime(self, path):
        c = canon_path(path)
        for gid in self.groups_for_path(path):
            p = self.groups[gid]["prime"]
            if p and canon_path(p) == c:
                return True
        return False

    def representative_for_group(self, g, used, used_canonical=False,
                                 slot_of=None):
        """Pick the ONE member of group ``g`` that represents it in the
        rated pool.  Preference order:
          1. the PRIME itself whenever it is a real member of the group —
             the prime IS the group's face everywhere: on the Selected
             Images page, in the ratings pool, in badges.  Only a prime
             that was removed from the group (stale pointer) loses this
             priority;
          2. otherwise the first member sitting in the Selected Images;
          3. otherwise the first member (group has no usable prime).
        The representative is NEVER hidden — a group always keeps exactly
        one visible entry in the ratings window unless it is in the
        selected window instead.

        ``used`` may be a set/list of raw paths or a pre-canonicalised set;
        pass ``used_canonical=True`` when the caller already canonicalised
        it (members are stored canonical, so then the comparison is pure
        dict/set membership with zero extra syscalls).

        ``slot_of`` (optional): mapping canon(path) -> truthy for every
        path currently occupying a dataset slot.  When given, "selected"
        is answered by a single dict lookup per member instead of
        re-canonicalising the whole used-paths set."""
        members = g["members"]
        prime = g.get("prime")
        pc = canon_path(prime) if prime else None
        if pc and any(canon_path(m) == pc for m in members):
            # THE PRIME IS THE REPRESENTATIVE — unconditionally.  Earlier
            # versions preferred "whichever member happens to sit in a
            # dataset slot", which made a transplanted CHILD win over a
            # newly-set prime: the Selected Images page kept showing the
            # stale child tile forever after the prime changed.
            return prime
        if slot_of is not None:
            for m in members:
                if slot_of.get(canon_path(m)):
                    return m
        else:
            used_set = set(used) if used_canonical else {canon_path(u) for u in used if u}
            used_members = [m for m in members if canon_path(m) in used_set]
            if used_members:
                return used_members[0]
        return members[0]

    def compute_hidden_paths(self, used_paths, used_canonical=False):
        """
        THE VISIBILITY RULE.

        Every group keeps exactly ONE representative visible in the rated
        pool — all other members are hidden:

        * group has a member sitting in the Selected Images
              -> that member IS the representative; since selected images
                 never appear in the rated pool anyway, every other member
                 is hidden.
        * group has no member in the Selected Images
              -> the PRIME is the representative and stays visible
                 (if no prime exists yet, the first member represents the
                 group).  Only the remaining children are hidden.

        A grouped image can therefore never vanish from the ratings window
        completely: there is always a surviving representative.

        Returns CANONICAL paths — callers must canonicalise their own sets
        before comparing (see ``canon_path``).

        ``used_canonical=True`` skips re-canonicalising the used-paths set
        (the viewer already keeps one cached in canonical form), turning the
        whole computation into dict/set lookups.

        NOTE: hiding is decided purely by "is this member the group's
        representative (= the prime)".  Whether a member happens to sit in
        a dataset slot is irrelevant here — slot occupancy is handled by
        collapsing/exclusions, never by this visibility rule.  Mixing the
        two made transplanted children survive as phantom tiles after the
        prime changed.
        """
        hidden = set()
        for g in self.groups.values():
            members = g["members"]
            if len(members) < 2:
                continue
            rep = canon_path(self.representative_for_group(g, (), True))
            for m in members:
                c = canon_path(m)
                if c != rep:
                    hidden.add(c)
        return hidden


# =============================================================================
# Balancer / Rater data
# =============================================================================
class BalancerData:
    def __init__(self, filepath=None):
        self.filepath = filepath
        self.data = {}
        self.profiles = {}
        self.current_profile = DEFAULT_PROFILE_NAME
        self.categories = {}
        self._backed_up = False
        if filepath and os.path.exists(filepath):
            self.load()

    def load(self):
        try:
            with open(self.filepath, "r") as f:
                self.data = json.load(f)
            self.profiles = self.data.get("profiles", {})
            self.categories = self.data.get("categories", {})

            if self.profiles:
                self.current_profile = self.data.get("current_profile", DEFAULT_PROFILE_NAME)
                if self.current_profile not in self.profiles:
                    self.current_profile = sorted(self.profiles, key=str.lower)[0]
            else:
                self.profiles = {DEFAULT_PROFILE_NAME: {
                    "dataset": self.data.get("dataset", {}),
                    "blacklist": self.data.get("blacklist", {}),
                    "image_tiers": self.data.get("image_tiers", {}),
                }}
                self.current_profile = DEFAULT_PROFILE_NAME

            self._sub("rated_pool_exclusions")
            self._sub("manually_hidden")
            self._sub("vacant_slots")
            return True
        except Exception as e:
            print(f"Error loading balancer data: {e}")
            return False

    def save(self):
        if not self.filepath:
            return False
        try:
            if not self._backed_up and os.path.exists(self.filepath):
                shutil.copy2(self.filepath, self.filepath + ".bak")
                self._backed_up = True
            if "profiles" in self.data:
                self.data["current_profile"] = self.current_profile
            atomic_write_json(self.filepath, self.data)
            return True
        except Exception as e:
            print(f"Error saving balancer data: {e}")
            return False

    def _sub(self, key):
        if not isinstance(self.data.get(key), dict):
            self.data[key] = {}
        return self.data[key]

    # ---- profile / dataset ----------------------------------------------
    def get_profile_names(self):
        return sorted(self.profiles, key=str.lower)

    def get_dataset(self, profile=None):
        profile = profile or self.current_profile
        return self.profiles.get(profile, {}).get("dataset", {})

    def get_categories_list(self):
        return list(self.categories.keys())

    def get_used_paths(self, profile=None):
        used = set()
        for paths in self.get_dataset(profile).values():
            for p in paths:
                if p:
                    used.add(p)
        return used

    # ---- exclusions ------------------------------------------------------
    def get_excluded_paths(self, profile=None):
        profile = profile or self.current_profile
        return set(self._sub("rated_pool_exclusions").get(profile, []))

    def add_excluded_path(self, profile, path):
        if not path:
            return
        lst = self._sub("rated_pool_exclusions").setdefault(profile, [])
        if path not in lst:
            lst.append(path)

    def remove_excluded_path(self, profile, path):
        lst = self._sub("rated_pool_exclusions").get(profile)
        if lst and path in lst:
            lst.remove(path)

    # ---- manual hides ----------------------------------------------------
    def get_hidden_paths(self, profile=None):
        profile = profile or self.current_profile
        return set(self._sub("manually_hidden").get(profile, []))

    def add_hidden_path(self, profile, path):
        lst = self._sub("manually_hidden").setdefault(profile, [])
        if path not in lst:
            lst.append(path)

    def remove_hidden_path(self, profile, path):
        lst = self._sub("manually_hidden").get(profile)
        if lst and path in lst:
            lst.remove(path)

    def clear_hidden_paths(self, profile=None):
        profile = profile or self.current_profile
        self._sub("manually_hidden")[profile] = []

    # ---- vacant slots ----------------------------------------------------
    # structure: vacant_slots[profile][category][str(index)] = {...}
    def _vac_cat(self, profile, category, create=False):
        vac = self._sub("vacant_slots")
        prof = vac.setdefault(profile, {}) if create else vac.get(profile, {})
        if create:
            return prof.setdefault(category, {})
        return prof.get(category, {})

    def get_vacancy(self, profile, category, index):
        return self._vac_cat(profile, category).get(str(index))

    def get_vacant_indices(self, profile, category):
        return {int(k) for k in self._vac_cat(profile, category).keys()}

    def set_vacancy(self, profile, category, index, info):
        self._vac_cat(profile, category, create=True)[str(index)] = info

    def clear_vacancy(self, profile, category, index):
        cat = self._vac_cat(profile, category)
        cat.pop(str(index), None)


class RaterData:
    def __init__(self, filepath=None):
        self.filepath = filepath
        self.data = {"categories": {}, "images": {}}
        # canonical-path -> rating info.  Group members are stored in
        # CANONICAL form (see ClusterManager.add_member), while the rater
        # file keys ratings by whatever spelling was in use when the image
        # got rated.  Without this index a lookup of a grouped/dragged path
        # misses the entry and the tile renders as UNRATED even though the
        # very same file carries stars in the galleries.
        self._canon_index = {}
        if filepath and os.path.exists(filepath):
            self.load()

    def load(self):
        try:
            with open(self.filepath, "r") as f:
                self.data = json.load(f)
            self._rebuild_canon_index()
            return True
        except Exception as e:
            print(f"Error loading rater data: {e}")
            return False

    def _rebuild_canon_index(self):
        idx = {}
        for p, info in self.data.get("images", {}).items():
            c = canon_path(p)
            if c:
                idx[c] = info
        self._canon_index = idx

    def _info(self, path):
        """Rating record for ``path``, tolerant of spelling differences.

        Exact key first (cheap), then the canonical index so that a path
        normalised by the grouping pipeline still resolves to its stars.
        """
        if not path:
            return {}
        images = self.data.get("images", {})
        info = images.get(path)
        if isinstance(info, dict) and info:
            return info
        info = self._canon_index.get(canon_path(path))
        return info if isinstance(info, dict) else {}

    def get_rating(self, path):
        return self._info(path).get("primary", 0) or 0

    def get_secondary_rating(self, path):
        return self._info(path).get("secondary", 0) or 0

    def get_all_rated_images(self, min_rating=1, directory_filter=None):
        out = []
        for path, info in self.data.get("images", {}).items():
            if info.get("primary", 0) < min_rating:
                continue
            if directory_filter and not path_is_under_directory(path, directory_filter):
                continue
            out.append((path, info["primary"], info.get("secondary", 0)))
        return sorted(out, key=lambda x: (-x[1], -x[2], x[0]))


class DataLoadWorker(QThread):
    finished = pyqtSignal(bool, str, object, object)

    def __init__(self, balancer_path, rater_path):
        super().__init__()
        self.balancer_path = balancer_path
        self.rater_path = rater_path

    def run(self):
        try:
            balancer = BalancerData(self.balancer_path)
            if not balancer.profiles:
                self.finished.emit(False, "Failed to load balancer data (no profiles).", None, None)
                return
            rater = RaterData(self.rater_path)
            if not rater.data.get("images"):
                self.finished.emit(False, "Failed to load rater data (no images).", None, None)
                return
            self.finished.emit(True, "OK", balancer, rater)
        except Exception as e:
            self.finished.emit(False, f"Error loading data: {e}", None, None)


# =============================================================================
# Small widgets
# =============================================================================
class EnlargedImageLabel(QLabel):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setStyleSheet("QLabel{background-color:rgba(0,0,0,205);border-radius:8px;padding:8px;}")
        self.setAlignment(Qt.AlignCenter)
        self._pm = None
        self.hide()

    def show_at(self, pos, pixmap, max_size=ENLARGED_DISPLAY_SIZE):
        if pixmap.isNull():
            return
        self._pm = pixmap.scaled(max_size, max_size, Qt.KeepAspectRatio, Qt.SmoothTransformation)
        self.setPixmap(self._pm)
        self.adjustSize()
        self.reposition(pos)
        self.show()

    def reposition(self, pos):
        if self._pm is None:
            return
        geo = QApplication.desktop().availableGeometry(pos)
        x, y = pos.x() + 15, pos.y() + 15
        if x + self.width() > geo.right():
            x = pos.x() - self.width() - 15
        if y + self.height() > geo.bottom():
            y = pos.y() - self.height() - 15
        self.move(x, y)

    def clear_image(self):
        self._pm = None
        self.clear()

    def contains(self, global_pos):
        """True if the global cursor position is over the visible popup."""
        return (self.isVisible()
                and self.geometry().contains(global_pos))


class RatingStarsWidget(QWidget):
    def __init__(self, primary=0, secondary=0, parent=None):
        super().__init__(parent)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(1)
        row = QHBoxLayout()
        row.setSpacing(2)
        for i in range(5):
            s = QLabel("★" if i < primary else "☆")
            s.setStyleSheet(f"color:{'#f5c518' if i < primary else '#5b5d63'};font-size:15px;")
            row.addWidget(s)
        lay.addLayout(row)
        if secondary > 0:
            sub = QLabel(f"Sub: {secondary}")
            sub.setStyleSheet("color:#9a9da3;font-size:9px;")
            sub.setAlignment(Qt.AlignCenter)
            lay.addWidget(sub)


# =============================================================================
# Paginated gallery
# =============================================================================
# =============================================================================
# Drag & drop helpers
# =============================================================================
def _drop_local_paths(event):
    """Extract existing local file paths from a drop event (Qt5-safe).

    Returns each distinct file ONCE: some drag sources put every URL in
    ``mimeData().urls()`` AND repeat it in the plain-text payload, so the
    raw list can contain the same path two or three times.  Without this
    dedupe a single drop added multiple member entries to the target
    group (phantom unrated tiles in the ratings window)."""
    md = event.mimeData()
    raw = []
    if md.hasUrls():
        raw += [u.toLocalFile() for u in md.urls()]
    if md.hasText():
        for line in md.text().splitlines():
            line = line.strip()
            if line.startswith("file:"):
                line = QUrl(line).toLocalFile()
            raw.append(line)
    out = []
    seen = set()
    for p in raw:
        if not p or not os.path.isfile(p):
            continue
        c = canon_path(p)
        if c in seen:
            continue
        seen.add(c)
        out.append(p)
    return out


class DropTargetList(QListWidget):
    """QListWidget that accepts image drops.  Emits paths_dropped with the
    list of local file paths contained in the drop, plus the viewport
    position so receivers can tell WHICH row/area was targeted."""

    paths_dropped = pyqtSignal(list, object)   # (paths, QPoint)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptDrops(True)
        self._dragging_here = False

    def dragEnterEvent(self, event):
        if _drop_local_paths(event):
            self._dragging_here = True
            event.acceptProposedAction()
        else:
            event.ignore()

    def dragMoveEvent(self, event):
        if self._dragging_here or _drop_local_paths(event):
            self._dragging_here = True
            event.acceptProposedAction()
        else:
            event.ignore()

    def dragLeaveEvent(self, event):
        self._dragging_here = False
        self.viewport().update()
        super().dragLeaveEvent(event)

    def dropEvent(self, event):
        # NOTE: must run BEFORE we clear our own highlight state — the
        # receiver may repaint this viewport itself.
        super().dropEvent(event)


class GroupDropList(DropTargetList):
    """Group rows list in the Groups tab.

    Accepts image drags coming from any gallery (including detached
    floating windows).  Dropping onto a specific group row joins THAT
    group; dropping on empty space goes to the open group (or creates
    a fresh one automatically)."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.drop_hint = "Drop images here to add them to the group under the cursor"
        self._hint_color = "#29b6f6"

    def dragEnterEvent(self, event):
        if _drop_local_paths(event):
            self._dragging_here = True
            self.viewport().update()
            event.acceptProposedAction()
        else:
            event.ignore()

    def dragLeaveEvent(self, event):
        self._dragging_here = False
        self.viewport().update()
        super(DropTargetList, self).dragLeaveEvent(event)

    def paintEvent(self, event):
        super().paintEvent(event)
        if not self._dragging_here:
            return
        p = QPainter(self.viewport())
        pen = QPen(QColor(self._hint_color))
        pen.setWidth(3)
        p.setPen(pen)
        p.setBrush(Qt.NoBrush)
        r = self.viewport().rect().adjusted(1, 1, -2, -2)
        p.drawRoundedRect(r, 6, 6)
        p.setPen(QColor("#e0e0e0"))
        p.drawText(r, Qt.AlignCenter | Qt.TextWordWrap, self.drop_hint)
        p.end()

    def dropEvent(self, event):
        paths = _drop_local_paths(event)
        hit = self.itemAt(event.pos())
        target_gid = hit.data(Qt.UserRole) if hit is not None else None
        self._dragging_here = False
        self.viewport().update()
        if paths:
            event.acceptProposedAction()
            self.paths_dropped.emit(paths, target_gid)
        else:
            event.ignore()


class GalleryDropZone(DropTargetList):
    """Icon-mode thumbnail grid used by every gallery panel, including the
    Groups tab's single-panel browser.  Accepts image drags; while one
    hovers, it paints ``drop_hint`` centred over the grid.

    ``target_hint``/``drop_hint`` let the owner change the painted text
    (e.g. name of the group the drop will land in).

    Cell widgets sit on top of the viewport and Qt routes drag events to
    them first — without help that produces the red "no-drop" cursor over
    every thumbnail.  ``canReceive`` claims those proxied events so the
    list itself handles the drag."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.drop_hint = "Drop images here"
        self._hint_color = "#4caf50"

    def canReceive(self, source, event):
        # Only claim drags this widget would actually accept; anything else
        # stays with the source widget's default handling.
        return bool(_drop_local_paths(event))

    def dropEvent(self, event):
        """Resolve the tile under the cursor in OUR OWN viewport coords and
        emit paths_dropped directly.  We must NOT delegate to
        QAbstractItemView.dropEvent (the inherited path) — its internal
        mimeData() handling for a foreign QMimeData shim either raises or
        silently no-ops, which is why drops used to fall through to the
        open group ("always group 1")."""
        paths = _drop_local_paths(event)
        self._dragging_here = False
        self.viewport().update()
        if not paths:
            event.ignore()
            return
        event.acceptProposedAction()
        hit = self.itemAt(event.pos())   # already viewport coords: forwarded
                                         # events are remapped by the cell
        pos = QPoint(event.pos())
        self.paths_dropped.emit(paths, pos)

    def dragLeaveEvent(self, event):
        # The bright per-tile drop highlight lives on cell widgets that are
        # torn down right after a successful drop — clear it here while the
        # containers still exist.
        owner = self.parent()
        clear = getattr(owner, "_clear_hot_tile", None)
        if callable(clear):
            clear()
        super().dragLeaveEvent(event)

    def paintEvent(self, event):
        super().paintEvent(event)
        if not self._dragging_here:
            return
        p = QPainter(self.viewport())
        pen = QPen(QColor(self._hint_color))
        pen.setWidth(3)
        p.setPen(pen)
        p.setBrush(Qt.NoBrush)
        r = self.viewport().rect().adjusted(1, 1, -2, -2)
        p.drawRoundedRect(r, 6, 6)
        if self.drop_hint:
            p.setPen(QColor("#e0e0e0"))
            p.drawText(r, Qt.AlignCenter | Qt.TextWordWrap, self.drop_hint)
        p.end()


class MembersDropContainer(QWidget):
    """Whole right-hand image display area of the Groups tab.

    It accepts image drags itself and forwards the events to its child
    list widget, so dropping ANYWHERE in the display area (list items,
    gaps between items, header or footer) lands in the ACTIVE group —
    not just inside the small thumbnail grid."""

    paths_dropped = pyqtSignal(list)          # local file paths

    def __init__(self, list_widget, parent=None):
        super().__init__(parent)
        self._list = list_widget
        self._dragging_here = False
        self.setAcceptDrops(True)

    def _accepts(self, event):
        return bool(_drop_local_paths(event))

    def dragEnterEvent(self, event):
        if self._accepts(event):
            self._dragging_here = True
            self.update()
            event.acceptProposedAction()
        else:
            event.ignore()

    def dragMoveEvent(self, event):
        if self._accepts(event):
            self._dragging_here = True
            event.acceptProposedAction()
        else:
            event.ignore()

    def dragLeaveEvent(self, event):
        self._dragging_here = False
        self.update()

    def dropEvent(self, event):
        paths = _drop_local_paths(event)
        self._dragging_here = False
        self.update()
        if paths:
            event.acceptProposedAction()
            self.paths_dropped.emit(paths)
        else:
            event.ignore()

    def paintEvent(self, event):
        super().paintEvent(event)
        if not self._dragging_here:
            return
        p = QPainter(self)
        pen = QPen(QColor(getattr(self._list, "_hint_color", "#4caf50")))
        pen.setWidth(3)
        p.setPen(pen)
        p.setBrush(Qt.NoBrush)
        r = self.rect().adjusted(1, 1, -2, -2)
        p.drawRoundedRect(r, 6, 6)
        hint = getattr(self._list, "drop_hint", "")
        if hint:
            p.setPen(QColor("#e0e0e0"))
            p.drawText(r, Qt.AlignCenter | Qt.TextWordWrap, hint)
        p.end()


def _tile_highlight_css(base=""):
    """Bright-green border used to mark the group tile currently under a
    live image drag — tells the user exactly where the drop will land."""
    return base + ("border:3px solid #29b6f6 !important;"
                   "border-radius:6px;background-color:rgba(41,182,246,0.10);")


class _CellDropTarget(QWidget):
    """Drop-capable container for a gallery cell.

    Cell widgets sit ON TOP of the QListWidget viewport, so while dragging,
    Qt hands the drag events to the child widget — which historically had no
    handlers and ignored them, producing the 'no-drop' (red circle) cursor
    even though the list itself would happily accept the drop.  This
    transparent container instead forwards every drag event straight to the
    owning drop list (whose handlers already map positions to items), and
    lights up the tile directly under the cursor with a bright border so it
    is obvious WHICH group will receive the images.  Mouse clicks are NOT
    touched: they keep bubbling to the list's event filter exactly as before.
    """

    def __init__(self, owner_list, parent=None):
        super().__init__(parent)
        self._owner = owner_list

    # -- plumbing ----------------------------------------------------------
    def _list(self):
        lst = self._owner
        if lst is None:
            return None
        try:
            lst.viewport()          # alive? (raises once C++ side is gone)
        except RuntimeError:
            return None
        return lst

    def _pos_in_list(self, event):
        lst = self._list()
        return lst.mapFromGlobal(event.pos()) if lst is not None else QPoint()

    def _group_tile_at(self, event):
        lst = self._list()
        if lst is None:
            return None
        item = lst.itemAt(self._pos_in_list(event))
        if item is None:
            return None
        data = item.data(Qt.UserRole)
        if isinstance(data, dict) and data.get("kind") == "group":
            return data
        return None

    def _fire_drag_threshold(self):
        """The pointer left this cell while the left button is still held —
        start the image drag just like DraggableCell.mouseMoveEvent does."""
        c = getattr(self, "_drag_src", None)
        press = getattr(c, "_press_pos", None) if c is not None else None
        if c is None or press is None:
            return
        gp = QCursor.pos()
        lp = self.mapFromGlobal(gp)
        if not self.rect().contains(lp):
            move_dist = (lp - press).manhattanLength()
        else:
            move_dist = 0
        try:
            threshold = QApplication.styleHints().dragDistance()
        except Exception:
            threshold = QApplication.startDragDistance()
        if move_dist >= threshold:
            c._press_pos = None
            path = c._path_getter()
            if path:
                c._start_drag(path)

    # -- drag forwarding -----------------------------------------------------
    def dragEnterEvent(self, event):
        lst = self._list()
        if lst is not None and hasattr(lst, "dragEnterEvent"):
            lst.dragEnterEvent(event)
        self._set_hot(True, event)

    def dragMoveEvent(self, event):
        lst = self._list()
        if lst is not None and hasattr(lst, "dragMoveEvent"):
            lst.dragMoveEvent(event)
        self._set_hot(True, event)
        self._fire_drag_threshold()

    def dragLeaveEvent(self, event):
        self._set_hot(False)
        lst = self._list()
        if lst is not None and hasattr(lst, "dragLeaveEvent"):
            lst.dragLeaveEvent(event)

    def dropEvent(self, event):
        self._set_hot(False)
        lst = self._list()
        if lst is not None and hasattr(lst, "dropEvent"):
            lst.dropEvent(event)

    # -- hover highlight -------------------------------------------------------
    def _set_hot(self, hot, event=None):
        lst = self._list()
        if lst is None:
            return
        prev = getattr(lst, "_hot_tile", None)
        if prev is not None and prev is not self:
            try:
                restyle = getattr(prev, "_restyle_fn", None)
                if restyle is not None:
                    restyle(prev)
                else:
                    prev.setStyleSheet("")
            except RuntimeError:
                pass
            lst._hot_tile = None
        if hot and event is not None:
            data = self._group_tile_at(event)
            owner = getattr(self, "_drop_owner", None)
            if data is not None and owner is not None \
                    and owner.get("gid") == data.get("gid"):
                try:
                    self.setStyleSheet(_tile_highlight_css())
                except RuntimeError:
                    return
                lst._hot_tile = self


class DraggableCell(QWidget):
    """A gallery cell that can start a drag carrying its image path.

    The item widgets sit ON TOP of the QListWidget viewport, so native list
    dragging never fires — we run the QDrag ourselves on left-button press
    + move, while plain clicks still reach the list's event filter.

    The very same cell widget is also the FIRST thing an incoming drag hits
    when it hovers a thumbnail (group tiles included).  A plain QWidget has
    no drop handlers and does not accept drops, so Qt marks the whole area
    under the cursor as an invalid target — that is the red "no-drop" circle
    users saw over every group thumbnail.  These cells therefore opt into
    drops and forward every drag event to the owning drop list, remapped
    into LIST coordinates so the list resolves the correct row/tile."""

    def __init__(self, owner_list, path_getter, data_getter=None,
                 parent=None):
        super().__init__(parent)
        self._owner = owner_list
        self._path_getter = path_getter
        # Optional callable returning the item dict stored in this cell —
        # used to tell image cells from GROUP tiles.  Group tiles are drop
        # targets only: they must never arm the drag machinery below.
        self._data_getter = data_getter
        self._press_pos = None
        # Without this Qt never even asks the cell about drops and reports
        # the region under the cursor as non-droppable (red circle).
        self.setAcceptDrops(True)

    def _is_image_cell(self):
        """True when this cell holds a real (non-vacant) IMAGE — i.e. it
        is a legitimate drag source.  Group tiles and vacant slots are
        not."""
        try:
            if self._data_getter is not None:
                d = self._data_getter()
                if not isinstance(d, dict) or d.get("kind") == "group" \
                        or d.get("vacant"):
                    return False
        except Exception:
            pass
        try:
            return bool(self._path_getter())
        except Exception:
            return False

    # -- drag forwarding ---------------------------------------------------
    # Qt delivers incoming drag events to the DEEPEST widget under the
    # cursor — these cells sit on top of the list viewport, so without
    # forwarding every thumbnail showed the red "no-drop" circle even
    # though the list itself accepts drops.  PyQt5's QDropEvent has no
    # setPos(), so instead of mutating the event we translate its
    # position into LIST coordinates and call the list's own handlers
    # directly (they resolve rows via itemAt(event.pos())).
    def _target_list(self):
        lst = self._owner
        if lst is None:
            return None
        try:
            lst.viewport()              # alive? (raises once C++ side is gone)
        except RuntimeError:
            return None
        return lst

    def _accepts_drop(self, event):
        """True when the owning list would take this drag (or we are in the
        middle of one it already claimed)."""
        lst = self._target_list()
        if lst is None:
            return False
        if getattr(lst, "_dragging_here", False):
            return True
        return bool(_drop_local_paths(event))

    def _fire_drag_threshold(self):
        """Pointer left this cell while the left button is still held —
        start the image drag just like :meth:`mouseMoveEvent` does."""
        press = self._press_pos
        if press is None or not self._is_image_cell():
            return
        lp = self.mapFromGlobal(QCursor.pos())
        move_dist = 0 if self.rect().contains(lp) else (lp - press).manhattanLength()
        try:
            threshold = QApplication.styleHints().dragDistance()
        except Exception:
            threshold = QApplication.startDragDistance()
        if move_dist >= threshold:
            self._press_pos = None
            path = self._path_getter()
            if path:
                self._start_drag(path)

    # -- forwarding helper ---------------------------------------------------
    class _FakeDrop:
        """Minimal stand-in for a QDropEvent whose pos() lives in the OWNING
        LIST's viewport coordinate system.  PyQt5 gives QDropEvent no
        setPos(), so instead of mutating the real event we hand the list's
        own handlers this lookalike (they only ever read pos()/mimeData()
        and accept/ignore).  Anything else is looked up on the wrapped
        event lazily — but only attributes that exist on BOTH sides, so
        touching e.g. globalPos() (absent from synthetic drag events) can
        never crash the app."""

        __slots__ = ("_e", "_pos")

        def __init__(self, event, pos):
            self._e = event
            self._pos = QPoint(pos)

        def pos(self):  return self._pos
        def posF(self): return QPointF(self._pos)
        def x(self):    return self._pos.x()
        def y(self):    return self._pos.y()

        def __getattr__(self, name):
            if hasattr(type(self._e), name):
                return getattr(self._e, name)
            raise AttributeError(name)

    def _list_event(self, event):
        lst = self._target_list()
        p = QPoint(event.pos())
        if lst is not None:
            # mapFrom() can segfault across item-widget boundaries in some
            # PyQt builds; route through global coords instead (verified safe).
            try:
                g = self.mapToGlobal(p)
                p = lst.viewport().mapFromGlobal(g)
            except Exception:
                pass
        return DraggableCell._FakeDrop(event, p)

    def _forward_drag(self, event, kind):
        """Forward an incoming drag event to the owning list, remapped into
        viewport coordinates.  Returns True when handled."""
        lst = self._target_list()
        if lst is None or not self._accepts_drop(event):
            return False
        handler = getattr(lst, kind, None)
        if not callable(handler):
            return False
        try:
            handler(self._list_event(event))
        except TypeError:
            # The list's C++ dropEvent demands a REAL QDropEvent — calling it
            # with our coordinate-remapped shim raises TypeError.  Fall back
            # to posting the real event to the viewport; Qt re-delivers it on
            # the next loop iteration and the list resolves the row itself.
            QApplication.postEvent(lst.viewport(), event)
        return True

    def dragEnterEvent(self, event):
        if not self._forward_drag(event, "dragEnterEvent"):
            super().dragEnterEvent(event)
            return
        # claim the drop on this cell so Qt never shows the red no-drop
        # circle while the pointer is over a thumbnail
        event.acceptProposedAction()

    def dragMoveEvent(self, event):
        if not self._forward_drag(event, "dragMoveEvent"):
            super().dragMoveEvent(event)
            return
        event.acceptProposedAction()
        # A drag is live over this cell; if the pointer meanwhile escaped
        # the cell with the button still down, honour the drag threshold
        # exactly like mouseMoveEvent does (source-side drag start).
        self._fire_drag_threshold()

    def dragLeaveEvent(self, event):
        lst = self._target_list()
        handler = getattr(lst, "dragLeaveEvent", None)
        if callable(handler):
            try:
                handler(event)
            except TypeError:
                pass   # C++ handler wants its own event instance; skip it
        super().dragLeaveEvent(event)

    def dropEvent(self, event):
        lst = self._target_list()
        paths = _drop_local_paths(event)
        if lst is None or not paths:
            super().dropEvent(event)
            return
        # the per-tile highlight lives on cells that a successful drop may
        # tear down right away — clear it while everything still exists
        gallery = self.parent()
        while gallery is not None and not hasattr(gallery, "_clear_hot_tile"):
            gallery = gallery.parent()
        clear = getattr(gallery, "_clear_hot_tile", None)
        if callable(clear):
            clear()
        # ALWAYS route the finished drop through the OWNING LIST's own
        # dropEvent with the position remapped into the list's viewport
        # coordinate space.  Every drop list here (GalleryDropZone /
        # DropTargetList / GroupDropList) resolves the target row itself
        # via ``itemAt(event.pos())`` in VIEWPORT coordinates and emits
        # paths_dropped with the correct gid.  Emitting straight from the
        # cell used to hand the handler a CELL-LOCAL point — in an icon
        # grid the cell widget is inset inside its item rect, so itemAt()
        # almost never found the tile under the cursor, gid came back None
        # and every drop fell through to the open group ("always group 1").
        event.acceptProposedAction()
        self._forward_drag(event, "dropEvent")

    def mousePressEvent(self, event):
        if (event.button() == Qt.LeftButton
                and self._is_image_cell()):
            # arm the source-side drag ONLY for real image cells — group
            # tiles are drop targets, never drag sources
            self._press_pos = event.pos()
        else:
            self._press_pos = None
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if (self._press_pos is not None
                and event.buttons() & Qt.LeftButton
                and (event.pos() - self._press_pos).manhattanLength()
                >= QApplication.startDragDistance()):
            self._press_pos = None
            path = self._path_getter()
            if path:
                self._start_drag(path)
                return
        super().mouseMoveEvent(event)

    def _start_drag(self, path):
        mime = QMimeData()
        # ALWAYS ship urls + text — an empty/null pixmap mime payload makes
        # every target reject the drag with the "no-drop" (red cross) cursor.
        mime.setUrls([QUrl.fromLocalFile(path)])
        mime.setText(path)
        # Parent the QDrag to something long-lived: a successful drop can
        # synchronously refresh the gallery and destroy this cell while
        # exec_()'s nested event loop is still unwinding on the stack —
        # deleting the drag's parent mid-flight is a classic no-traceback
        # segfault in PyQt5.
        drag = QDrag(self.window() or self)
        drag.setMimeData(mime)
        pm = make_pixmap(path, THUMB_SIZE)
        if not pm.isNull():
            drag.setPixmap(pm)
            drag.setHotSpot(QPoint(pm.width() // 2, pm.height() // 2))
        else:
            ph = QPixmap(THUMB_SIZE, THUMB_SIZE)
            ph.fill(QColor("#2b2d31"))
            drag.setPixmap(ph)
        drag.exec_(Qt.CopyAction)


class PaginatedGallery(QWidget):
    """
    Grid gallery.  Handles:
      * full left-click (press + release, no drag drift)
                        -> image_clicked  (swap workflow).  A press alone
                           never fires the swap — starting a drag-and-drop
                           on a tile must not arm/complete a swap with it.
      * double-click      -> group_prime_requested (make PRIME)
      * press-drag        -> starts a drag; drop onto the Groups tab to group
      * right-click       -> quick click: context menu (vacancy restore /
                             group info / search-by-name);
                             hold: floating enlarged preview
      * the on-panel ➕ button -> finish_group_requested
      * the on-panel ➖ button -> hide/unhide the highlighted image
                                 (rated pool only)
      * the on-panel 🔍 box    -> MANUAL name filter: type text next to
                                 the magnifying glass and every file whose
                                 name contains it is shown (case-sensitive,
                                 e.g. "S" -> all files starting with S)
      * the on-panel ← button  -> leave the search view, restore the pool

    ``item_builder`` lets a subclass render its own cell type (used by the
    Groups tab's single-panel browser, which shows GROUPS as tiles).
    """

    image_clicked = pyqtSignal(dict)
    group_add_requested = pyqtSignal(dict)
    group_prime_requested = pyqtSignal(dict)
    finish_group_requested = pyqtSignal()
    hide_requested = pyqtSignal(dict)
    unhide_requested = pyqtSignal(dict)
    restore_vacancy_requested = pyqtSignal(dict)
    back_requested = pyqtSignal()
    page_changed = pyqtSignal()
    # grouped browser (Groups tab single-panel view)
    group_expand_requested = pyqtSignal(object)          # gid
    group_menu_requested = pyqtSignal(object, object)    # (gid, viewport pos)
    member_menu_requested = pyqtSignal(object, object)   # (item dict, pos)
    images_dropped = pyqtSignal(list, object)            # (paths, target gid|None)

    def __init__(self, source_name="", title="", item_builder=None, parent=None):
        super().__init__(parent)
        self.source_name = source_name
        self._item_builder = item_builder or self._build_image_item
        self.items = []
        self.current_page = 0
        self.page_size = DEFAULT_PAGE_SIZE

        self.cluster = None
        self.rater = None               # live rating lookup (fallback for
                                        # items built without a snapshot)
        self.staged_group_id = None
        self.pinned_group_id = None
        self._pending_key = None          # (path, index) currently pending swap

        self._generation = 0
        self._labels_by_path = {}
        self._entries = []                # [(item_dict, container)]

        self._enlarged = None
        self._rc_timer = QTimer(self)
        self._rc_timer.setSingleShot(True)
        self._rc_timer.timeout.connect(self._show_enlarged)
        self._rc_data = None
        self._rc_holding = False
        # ---- click-vs-drag disambiguation --------------------------------
        # A swap "click" must be a FULL click gesture: press AND release on
        # the same cell.  Emitting image_clicked on the initial press meant
        # that merely *starting* a drag-and-drop armed (or even completed)
        # a swap with whatever tile the pointer began on — the notorious
        # "drag one image, other highlighted images get swapped" blunder.
        # The press now only *arms* this pending-click; the swap signal
        # fires on release, and only if the pointer never drifted far
        # enough to count as a drag attempt.
        self._pending_click_data = None   # item armed at press-time
        self._pending_click_pos = None    # viewport pos of the press
        # The FULL file name (basename, extension included) of the cell that
        # was last clicked/highlighted — this is what Shift+C copies to the
        # clipboard, so it can later be pasted into a group-rename or the
        # group search bar.  Kept separately from _highlighted_key because
        # the key gets invalidated on reloads while the copied name should
        # survive as long as the tile existed.
        self._last_clicked_name = ""
        # ---- rename mode ----------------------------------------------------
        # While Shift+R is physically held (or "armed" for one click right
        # after release), the next left-click on a GROUP tile renames that
        # group using the clipboard contents instead of just highlighting.
        self._rename_armed = False
        self._rename_timer = QTimer(self)
        self._rename_timer.setSingleShot(True)
        self._rename_timer.timeout.connect(self._disarm_rename)
        # True once a right-click HOLD has actually popped the enlarged
        # preview.  While set, the next context-menu request is swallowed —
        # releasing after viewing the big image must never open a menu.
        # (Hide/unhide no longer lives in the context menu at all; it is a
        # dedicated ➖ toolbar button acting on the highlighted image.)
        self._rc_preview_shown = False
        # The cell the user last clicked/highlighted (for the ➖ button).
        self._highlighted_key = None      # (path, index) or None
        # ---- name-search view -------------------------------------------
        # When a "Search file name" runs we swap the gallery contents for
        # the top matches; the previous items are stashed so the ← back
        # arrow can restore them exactly (same page, same scroll position).
        self.searching = False
        self._pre_search_items = None
        self._pre_search_page = 0
        self.search_term = ""
        # ---- "date created" ordering + filter -----------------------------
        # Independent of the name search: both always act on the FULL pool
        # (_pool_items), and a name search then narrows whatever the date
        # window currently shows.  d1/d2 are datetime.date bounds used by
        # the custom filter modes (from / to / range).  order_mode sorts
        # the view by creation date ("asc" oldest first, "desc" newest
        # first, None == keep the source's default order).
        self.order_mode = None          # None == "Default order"
        self.date_mode = None           # None == "Any date"
        self.date_d1 = None
        self.date_d2 = None
        self._created_cache = {}        # path -> creation date (or None)
        # ---- view mode ------------------------------------------------------
        # "image"   -> normal gallery (one cell per image item)
        # "grouped" -> the Groups tab's single-panel browser: tiles are
        #              GROUPS, double-click / Expand shows a group's members,
        #              ← returns to the groups grid.
        self.view_mode = "image"
        self.expanded_gid = None       # group currently expanded (grouped)
        # 📌 pin button only exists in the grouped (Groups tab) browser;
        # set this before building the toolbar so it gets one.
        self._grouped_gallery = bool(item_builder)

        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(6)

        if title:
            h = QLabel(title)
            h.setProperty("role", "heading")
            lay.addWidget(h)

        # ---- group toolbar (the ➕ lives HERE, on the panel itself) -------
        bar = QHBoxLayout()
        bar.setSpacing(6)

        # ← back button: shown whenever there is somewhere to go BACK to —
        # a name-search result view, or (in the Groups browser) an expanded
        # group's members page.  Clicking it restores the previous view.
        self.back_btn = QPushButton("←")
        self.back_btn.setFixedWidth(40)
        self.back_btn.setToolTip("Back to the previous view.")
        self.back_btn.setStyleSheet(
            "background-color:#2f3640;color:#fff;font-weight:bold;font-size:13pt;"
            "border:1px solid #5865f2;border-radius:6px;padding:2px 0px;"
        )
        self.back_btn.clicked.connect(self._back_clicked)
        self.back_btn.setVisible(False)
        bar.addWidget(self.back_btn)

        # 📌 pin button (Groups browser): pins the highlighted group so
        # G+click in the Viewer feeds THAT group.
        if self._grouped_gallery:
            self.pin_btn = QPushButton("\U0001F4CC")
            self.pin_btn.setFixedWidth(40)
            self.pin_btn.setToolTip(
                "Pin / unpin the highlighted group.\n"
                "While pinned, G+click in the Viewer adds images to THIS\n"
                "group instead of arming a brand-new one.")
            self.pin_btn.setStyleSheet(
                "background-color:#2e7d32;color:#fff;font-weight:bold;font-size:12pt;"
                "border:1px solid #4caf50;border-radius:6px;padding:2px 0px;")
            self.pin_btn.setEnabled(False)
            self.pin_btn.clicked.connect(self._pin_clicked)
            bar.addWidget(self.pin_btn)

        self.group_status = QLabel("")
        self.group_status.setStyleSheet("color:#29b6f6;font-size:9pt;")
        bar.addWidget(self.group_status, 1)

        self.finish_btn = QPushButton("➕")
        self.finish_btn.setFixedWidth(40)
        self.finish_btn.setToolTip(
            "Commit the staged group and re-arm for a brand-new group.\n"
            "(Also unpins a group pinned from the Groups tab.)"
        )
        self.finish_btn.setStyleSheet(
            "background-color:#2e7d32;color:#fff;font-weight:bold;font-size:13pt;"
            "border:1px solid #4caf50;border-radius:6px;padding:2px 0px;"
        )
        self.finish_btn.clicked.connect(self.finish_group_requested.emit)
        bar.addWidget(self.finish_btn)

        # ---- hide/unhide button (rated pool) -----------------------------
        # Replaces the old right-click "Hide from rated pool" context menu,
        # which collided with the right-click-hold enlarged preview.  Acts
        # on the currently highlighted (last clicked) image.
        if source_name == "rated":
            self.hide_btn = QPushButton("➖")
            self.hide_btn.setFixedWidth(40)
            self.hide_btn.setToolTip(
                "Hide the highlighted image from the rated pool.\n"
                "If \"Show Hidden Images\" is on and the highlighted image\n"
                "is hidden, this unhides it instead."
            )
            self.hide_btn.setStyleSheet(
                "background-color:#7a1f1f;color:#fff;font-weight:bold;font-size:13pt;"
                "border:1px solid #c0392b;border-radius:6px;padding:2px 0px;"
            )
            self.hide_btn.setEnabled(False)
            self.hide_btn.clicked.connect(self._hide_clicked)
            bar.addWidget(self.hide_btn)

        # ---- manual name-search -----------------------------------------
        # The old search tried to grab a file name on its own from the
        # highlighted cell and show only the "nearest" matches — useless.
        # Search is now fully MANUAL: type into the text box that sits
        # right next to the 🔍 button; every file whose NAME contains the
        # typed text is shown.  The match is case-sensitive exactly as
        # typed ("S" lists all files beginning with a capital S, "s"
        # would list lowercase-s files).  Press Enter or click 🔍 to run;
        # clear the box + Enter to see the whole pool again; ← backs out.
        self._pool_items = []           # full unfiltered list for this view
        self.search_edit = QLineEdit()
        self.search_edit.setPlaceholderText("Search name…")
        self.search_edit.setFixedWidth(150)
        self.search_edit.setClearButtonEnabled(True)
        self.search_edit.setToolTip(
            "Type text and press Enter (or click 🔍): shows every file\n"
            "whose name CONTAINS the text, matching the exact case you\n"
            "type — e.g. \"S\" displays all files starting with capital S.\n"
            "Empty the box and press Enter to show everything again."
        )
        self.search_edit.returnPressed.connect(self._run_search)
        bar.addWidget(self.search_edit)

        self.search_btn = QPushButton("🔍")
        self.search_btn.setFixedWidth(40)
        self.search_btn.setToolTip(
            "Run the name search typed in the box beside this button.\n"
            "← returns to the full list."
        )
        self.search_btn.setStyleSheet(
            "background-color:#1f3a5c;color:#fff;font-weight:bold;font-size:12pt;"
            "border:1px solid #29b6f6;border-radius:6px;padding:2px 0px;"
        )
        self.search_btn.clicked.connect(self._run_search)
        bar.addWidget(self.search_btn)

        # ---- "date created" ordering ---------------------------------------
        # Arranges the tiles by each file's CREATION date without removing
        # anything: oldest first / newest first, or the source's default
        # order (rating order for the rated pool, slot order for selected).
        self.order_combo = QComboBox()
        for label, mode in DATE_ORDER_OPTIONS:
            self.order_combo.addItem(label, mode)
        self.order_combo.setToolTip(
            "ORDER this window's tiles by the file's DATE CREATED.\n"
            "• default order — rating order (rated) / slot order (selected)\n"
            "• oldest first / newest first — sort by creation date\n"
            "• by file name — cluster files whose NAMES are most similar\n"
            "  (nearest-neighbour chain over base names; numeric-aware)\n"
            "Files whose creation date can't be read — and vacant slots —\n"
            "keep their original position.  Works together with the\n"
            "📅 date filter and the 🔍 name search."
        )
        self.order_combo.currentIndexChanged.connect(self._order_mode_changed)
        bar.addWidget(self.order_combo)

        # ---- "date created" filter ---------------------------------------
        # Filters the pool by each file's CREATION date (Windows creation
        # time; falls back to modified time where creation isn't recorded).
        # Vacant slots and files that can't be stat'ed always stay visible.
        self.date_combo = QComboBox()
        for label, mode in DATE_FILTER_OPTIONS:
            self.date_combo.addItem(label, mode)
        self.date_combo.setToolTip(
            "Filter this window by the file's DATE CREATED.\n"
            "• today / this week / month / year — quick ranges\n"
            "• on/after, before, between — pick exact dates with the\n"
            "  calendar boxes that appear next to this list\n"
            "Works together with the 🔍 name search (both filters apply)."
        )
        self.date_combo.currentIndexChanged.connect(self._date_mode_changed)
        bar.addWidget(self.date_combo)

        def _mk_date_edit(tip):
            de = QDateEdit()
            de.setCalendarPopup(True)
            de.setDisplayFormat("yyyy-MM-dd")
            de.setDate(QDate.currentDate())
            de.setToolTip(tip)
            de.setVisible(False)
            bar.addWidget(de)
            return de

        self.date_from_edit = _mk_date_edit("Only show files created ON or AFTER this date.")
        self.date_to_edit = _mk_date_edit("Only show files created BEFORE (up to) this date.")
        self.date_from_edit.dateChanged.connect(self._date_bounds_changed)
        self.date_to_edit.dateChanged.connect(self._date_bounds_changed)
        lay.addLayout(bar)
        # stable handle to the toolbar row — subclasses add/remove widgets
        # here without guessing layout indices (title label may or may not
        # be present, so itemAt(1) is NOT reliably the bar).
        self._bar = bar

        # ---- list --------------------------------------------------------
        self.list_widget = GalleryDropZone()   # accepts image drops anywhere
        self.list_widget.paths_dropped.connect(self._on_paths_dropped)
        self.list_widget.setViewMode(QListWidget.IconMode)
        self.list_widget.setResizeMode(QListWidget.Adjust)
        self.list_widget.setMovement(QListWidget.Static)
        self.list_widget.setUniformItemSizes(True)
        self.list_widget.setSelectionMode(QAbstractItemView.NoSelection)
        self.list_widget.setGridSize(QSize(THUMB_SIZE + 26, THUMB_SIZE + 86))
        self.list_widget.setDragEnabled(True)
        self.list_widget.setDropIndicatorShown(True)
        self.list_widget.setContextMenuPolicy(Qt.CustomContextMenu)
        self.list_widget.customContextMenuRequested.connect(self._context_menu)
        # Mouse events land on the viewport, not the list itself.
        self.list_widget.viewport().installEventFilter(self)
        self.list_widget.viewport().setMouseTracking(True)
        lay.addWidget(self.list_widget, 1)

        # ---- nav ---------------------------------------------------------
        nav = QHBoxLayout()
        self.prev_btn = QPushButton("◀ Prev")
        self.prev_btn.clicked.connect(self.prev_page)
        self.page_label = QLabel("Page 0 / 0")
        self.page_label.setAlignment(Qt.AlignCenter)
        self.next_btn = QPushButton("Next ▶")
        self.next_btn.clicked.connect(self.next_page)
        self.page_size_combo = QComboBox()
        for s in PAGE_SIZE_OPTIONS:
            self.page_size_combo.addItem(f"{s}/page", s)
        self.page_size_combo.setCurrentIndex(PAGE_SIZE_OPTIONS.index(DEFAULT_PAGE_SIZE))
        self.page_size_combo.currentIndexChanged.connect(self._page_size_changed)
        # ---- go-to-page input --------------------------------------------
        # Type a page number, hit "Go" (or Enter) and the gallery jumps
        # straight to that page.  Out-of-range numbers clamp to first/last.
        self.goto_edit = QLineEdit()
        self.goto_edit.setPlaceholderText("Page #")
        self.goto_edit.setFixedWidth(64)
        # NOTE: QIntValidator lives in Qt's QtGui module, not QtCore/QtWidgets,
        # and importing it has caused ImportError on some setups.  Instead of a
        # validator we simply strip non-digits on edit — same effect, no extra import.
        self.goto_edit.setMaxLength(6)
        self.goto_edit.textChanged.connect(self._goto_text_changed)
        self.goto_edit.setToolTip("Type a page number, then press Go (or Enter).")
        self.goto_edit.returnPressed.connect(self._goto_clicked)
        goto_btn = QPushButton("Go")
        goto_btn.setFixedWidth(40)
        goto_btn.setToolTip("Jump to the page number typed in the box.")
        goto_btn.clicked.connect(self._goto_clicked)
        nav.addWidget(self.prev_btn)
        nav.addWidget(self.page_label, 1)
        nav.addWidget(self.next_btn)
        nav.addWidget(self.goto_edit)
        nav.addWidget(goto_btn)
        nav.addWidget(self.page_size_combo)
        lay.addLayout(nav)

        self.count_label = QLabel("0 images")
        self.count_label.setStyleSheet("color:#9a9da3;font-size:9px;")
        lay.addWidget(self.count_label)

        HOTKEYS.changed.connect(self._on_hotkey_changed)
        # Shift+C copies the highlighted tile's file name; Shift+R(+click)
        # renames a group from the clipboard.  Both are routed through the
        # global tracker so they work no matter which widget has focus —
        # except inside text fields (see HotkeyTracker._is_text_sink).
        HOTKEYS.copy_pressed.connect(self._copy_highlighted_name)
        HOTKEYS.rename_pressed.connect(self._arm_rename)
        HOTKEYS.rename_released.connect(self._on_rename_released)

    # ---- Shift+C: copy the highlighted file name --------------------------
    def _current_clicked_item(self):
        """The item dict behind the last click/highlight, if still visible."""
        return self._item_by_key(self._highlighted_key)

    def _copy_highlighted_name(self):
        """Shift+C: put the FULL file name (basename with extension) of the
        highlighted thumbnail on the clipboard.  Falls back to the last name
        clicked in this gallery, then to any other gallery's selection, so
        clicking elsewhere (e.g. the Groups tab) doesn't silently lose what
        you copied from the Viewer."""
        item = self._current_clicked_item()
        if item is not None and item.get("path") and not item.get("vacant"):
            name = os.path.basename(item["path"])
            self._last_clicked_name = name
        elif self._last_clicked_name:
            name = self._last_clicked_name
        else:
            for gal in self.findChildren(PaginatedGallery):
                if gal is self:
                    continue
                it = gal._current_clicked_item()
                if it is not None and it.get("path") and not it.get("vacant"):
                    name = os.path.basename(it["path"])
                    gal._last_clicked_name = name
                    break
            else:
                QApplication.beep()
                return
        QApplication.clipboard().setText(name)
        top = self.window()
        sb = top.statusBar() if hasattr(top, "statusBar") else None
        if sb is not None:
            sb.showMessage(f"📋 Copied file name: {name}", 4000)

    # ---- Shift+R rename mode ----------------------------------------------
    def _arm_rename(self):
        """Shift+R pressed: arm rename mode while the key is held."""
        self._rename_armed = True
        self._rename_timer.stop()
        self.restyle()

    def _on_rename_released(self):
        """Shift+R released.  The physical press+hold+release gesture means
        a click almost always happens *around* the key hold, not during it.
        So instead of disarming instantly we keep mode armed for one click
        for a short grace window — enabling both true 'shift+R + left-click'
        and the natural 'press R, release R, then click' rhythm."""
        if self._rename_armed:
            self._rename_timer.start(1200)   # ms of grace after key release

    def _disarm_rename(self):
        if self._rename_armed:
            self._rename_armed = False
            self.restyle()

    def _rename_from_clipboard(self, gid):
        """Rename group ``gid`` to the clipboard text — intelligently:
        only the FIRST 10 CHARACTERS of the copied file name are used
        (extension included, since burst-shoot names share their prefix),
        and if another group already carries that name, ' (1)', ' (2)', …
        is appended until the name is unique.  Empty clipboard → beep."""
        self._disarm_rename()
        if not self.cluster or not self.cluster.get_group(gid):
            return
        clip = QApplication.clipboard().text().strip()
        if not clip:
            QApplication.beep()
            return
        # The clipboard holds a FILE NAME (Shift+C).  Groups should carry the
        # stem, not the extension — "IMG_1234.jpg" names the group "IMG_1234",
        # which is also what the file-name search bar will find later.
        base_name = os.path.splitext(clip)[0].strip() or clip
        base = base_name[:10].strip()
        if not base:
            QApplication.beep()
            return
        taken = {g["name"].lower() for g in self.cluster.all_groups()
                 if g["id"] != gid}
        new_name = base
        n = 1
        while new_name.lower() in taken:
            new_name = f"{base} ({n})"
            n += 1
        self.cluster.rename_group(gid, new_name)
        self.refresh()
        self.data_changed.emit(gid)
        top = self.window()
        sb = top.statusBar() if hasattr(top, "statusBar") else None
        if sb is not None:
            sb.showMessage(f"✏️ Group renamed to “{new_name}” "
                           f"(from “{clip}”)", 5000)

    # ---- wiring ----------------------------------------------------------
    def set_cluster(self, cluster):
        self.cluster = cluster

    def set_group_context(self, staged_id, pinned_id):
        self.staged_group_id = staged_id
        self.pinned_group_id = pinned_id
        self._update_group_status()
        self.restyle()

    def _on_hotkey_changed(self, _held):
        self._update_group_status()

    def _update_group_status(self):
        if self.cluster and self.staged_group_id:
            g = self.cluster.get_group(self.staged_group_id)
            n = len(g["members"]) if g else 0
            if g:
                txt = (f"🟦 OPEN: {g['name']} ({n}) — drop images here from the "
                       f"galleries, ➕ when done")
                color = "#29b6f6"
            else:
                txt = "Drag images onto the Groups tab to create groups"
                color = "#7f8289"
        else:
            txt = "Drag images onto the Groups tab to create groups — ＋ Empty Group starts a fresh one"
            color = "#4caf50"
        self.group_status.setText(txt)
        self.group_status.setStyleSheet(f"color:{color};font-size:9pt;font-weight:600;")

    # ---- items -----------------------------------------------------------
    def set_items(self, items, preserve_page=False):
        if self.searching:
            # A refresh while a name-search is on screen must NOT wipe the
            # search view (the ← would then have nothing to go back to).
            # Update the stashed pool instead; it reappears untouched when
            # the user leaves the search.  The visible results are re-run
            # against the fresh pool so added/removed files show up live.
            self._pre_search_items = items or []
            self._pool_items = list(self._pre_search_items)
            self.apply_search_filter()
            return
        if self.view_mode == "grouped" and self.expanded_gid is not None:
            # The Groups browser is showing one group's MEMBERS — an outside
            # refresh only changes the underlying data, never this page.
            # Rebuild the members view from the live cluster so removed /
            # renamed / re-primed members are reflected, and stash the fresh
            # groups list for when ← collapses back.
            self.items = items or []
            self.refresh_expanded()
            return
        self.items = items or []
        # remember the full unfiltered pool — the manual 🔍 search always
        # filters THIS list, never whatever subset happens to be on screen
        self._pool_items = list(self.items)
        if preserve_page:
            self.current_page = max(0, min(self.current_page, self.total_pages() - 1))
        else:
            self.current_page = 0
        # apply this window's "date created" ordering + filter (both no-ops
        # while the combos sit on their defaults)
        self._apply_date_filter()
        if preserve_page:
            self.current_page = max(0, min(self.current_page, self.total_pages() - 1))
        self._load_page()

    def clear(self):
        self.set_items([])

    def total_pages(self):
        if not self.items:
            return 1
        return (len(self.items) - 1) // self.page_size + 1

    def prev_page(self):
        if self.current_page > 0:
            self.current_page -= 1
            self._load_page()

    def next_page(self):
        if self.current_page < self.total_pages() - 1:
            self.current_page += 1
            self._load_page()

    def _page_size_changed(self, _i):
        self.page_size = self.page_size_combo.currentData()
        self.current_page = 0
        self._load_page()

    def jump_to_page(self, page_number):
        """Go directly to a 1-based page number (used by the "Go" input).

        Out-of-range values are clamped to the first/last page; returns True
        if the visible page actually changed."""
        try:
            p = int(page_number)
        except (TypeError, ValueError):
            return False
        target = max(0, min(p - 1, self.total_pages() - 1))
        if target == self.current_page:
            return False
        self.current_page = target
        self._load_page()
        return True

    def _goto_text_changed(self, text):
        """Keep the go-to box digits-only (replacement for QIntValidator)."""
        digits = ''.join(ch for ch in text if ch.isdigit())
        if digits != text:
            cursor = self.goto_edit.cursorPosition() - (len(text) - len(digits))
            self.goto_edit.setText(digits)
            self.goto_edit.setCursorPosition(max(0, cursor))

    def _goto_clicked(self):
        """"Go" button / Enter in the page-number box: jump to that page."""
        text = self.goto_edit.text().strip()
        if not text:
            return
        self.jump_to_page(text)
        self.goto_edit.selectAll()

    # ---- pending highlight ----------------------------------------------
    def set_pending(self, path, index):
        self._pending_key = (path, index)
        self.restyle()

    def clear_pending(self):
        self._pending_key = None
        self.restyle()

    # ---- ➖ hide/unhide button -------------------------------------------
    def _item_by_key(self, key):
        for item, _container in self._entries:
            if (item["path"], item.get("index")) == key:
                return item
        return None

    def set_highlighted(self, key):
        """Mark the cell the ➖ button should act on."""
        self._highlighted_key = key
        btn = getattr(self, "hide_btn", None)
        if btn is not None:
            btn.setEnabled(key is not None
                           and self._item_by_key(key) is not None)
        self.restyle()

    def clear_highlight(self):
        if self._highlighted_key is not None:
            self.set_highlighted(None)

    def _hide_clicked(self):
        key = self._highlighted_key
        item = self._item_by_key(key) if key else None
        if item is None or not item.get("path") or item.get("vacant"):
            return                      # nothing highlighted — no-op
        if item.get("is_hidden"):
            self.unhide_requested.emit(item)
        else:
            self.hide_requested.emit(item)

    # ---- "date created" ordering + filter -----------------------------------
    def _created_date(self, path):
        """Creation date of ``path`` (memoised — one stat per file)."""
        if path not in self._created_cache:
            self._created_cache[path] = file_created_date(path)
        return self._created_cache[path]

    def _item_passes_date(self, item):
        """One gallery item against the window's active date filter.
        Vacant slots and files with an unknown creation date always pass."""
        path = item.get("path") or ""
        if not path or item.get("vacant"):
            return True
        return date_filter_matches(self._created_date(path),
                                   self.date_mode, self.date_d1, self.date_d2)

    def _slot_anchor(self, it):
        """The dataset SLOT number this tile occupies (None for rated-pool
        tiles).  Read from ``index`` first — but only when the item dict is
        one we built ourselves (it carries ``slot_value``), so foreign
        ``index`` keys can never be mistaken for a slot anchor.  Falls back
        to the previous view's position of the same path."""
        if "slot_value" in it:
            idx = it.get("index")
            if isinstance(idx, int) and not isinstance(idx, bool):
                return idx
        path = it.get("path") or ""
        if path:
            prev = getattr(self, "_path_to_pos", None) or {}
            pos = prev.get(path)
            if isinstance(pos, int):
                return pos
        return None

    def _remember_positions(self, items):
        """path -> current list position, used as the fallback slot anchor
        on the next rebuild."""
        m = {}
        for pos, it in enumerate(items or []):
            path = it.get("path") or ""
            if path and path not in m:
                m[path] = pos
        self._path_to_pos = m

    def _apply_date_view(self, items):
        """Return ``items`` run through this window's date-created ORDER and
        FILTER (either is a no-op while its combo sits on the default).  The
        grouped browser never gets touched — ordering/filtering by creation
        date only makes sense for image tiles.

        VACANCY HANDLING (the bug this code fixes): a vacant slot must keep
        the position that ITS OWN SLOT has inside the sorted layout, so the
        dashed VACANT thumbnail appears exactly where the collapse happened
        and the neighbour tiles stay put — ready to be re-filled.

        * The earlier sentinel-key sort dragged vacancies around every time
          the order was reversed.
        * The follow-up attempt pinned vacancies to their raw list position
          across rebuilds.  That breaks the actual workflow: grouping two
          Selected images collapses them into ONE slot — the surviving
          tile moves to the prime's position while the collapsed slot goes
          vacant.  A position-pinned vacancy stays behind at the OLD spot,
          so after every group action the whole UI looked like it shuffled
          itself and the VACANT placeholder never showed up where the
          collapse occurred.

        Now each tile is anchored to its DATASET SLOT INDEX (carried in the
        item dict by refresh_selected_gallery, with a last-known-position
        fallback).  Real images are STABLE-sorted by creation day — a plain
        ``list.sort`` keeps the incoming relative order of equal-key tiles,
        so existing images never reshuffle between rebuilds and brand-new
        files still land at their proper date position.  Vacancies are then
        placed deterministically: the Nth vacant slot (by slot number)
        lands on the Nth free position of the rebuilt view.  Collapsing a
        slot therefore puts exactly one VACANT tile where the removed
        image used to sit, and repeated refreshes leave the layout
        untouched — the spot stays clickable for re-filling.
        """
        if self.view_mode == "grouped":
            return items
        out = list(items or [])
        if self.date_mode:
            out = [it for it in out if self._item_passes_date(it)]
        if self.order_mode == "name":
            # 🏷️ FILE-NAME SIMILARITY order.  Real images are chained by a
            # deterministic greedy nearest-neighbour walk over their base
            # names (the file most similar to the current one lands right
            # next to it).  VACANT slots never join the walk — they keep
            # their position across refreshes, and a slot that just
            # collapsed takes over the exact layout position of the image
            # that left it, so the dashed VACANT thumbnail appears where
            # the user expects and stays there ready for re-filling.
            vacant = [(self._slot_anchor(it), pos, it)
                      for pos, it in enumerate(out) if it.get("vacant")]
            # Tiles WITHOUT a slot anchor (e.g. rated-pool items) can't be
            # pinned anywhere; they join the image walk so their order is
            # still by name similarity and nothing gets dropped.
            imgs = [it for it in out
                    if not it.get("vacant") or self._slot_anchor(it) is None]
            ordered_imgs = _filename_similarity_order(
                imgs, lambda it: it.get("path") or "")
            # Remembered geometry: dataset-slot -> position in the LAST
            # rendered view (the layout the user is looking at).
            geo = dict(getattr(self, "_slot_pos_geo", None) or {})
            # Continuity fallback: where the previous occupant's PATH sits
            # now (covers first render after a collapse, before geo was
            # updated for the leaving tile).
            path_now = {}
            for k, it in enumerate(out):
                pth = it.get("path") or ""
                if pth and pth not in path_now:
                    path_now[pth] = k
            prev_by_slot = {}
            for pit in (self.items or []):
                a = self._slot_anchor(pit)
                if a is not None and a not in prev_by_slot:
                    prev_by_slot[a] = pit

            def name_target(anchor, arr):
                if anchor is None:
                    return arr                       # unseen: leave in place
                pit = prev_by_slot.get(anchor)
                if (pit is not None and not pit.get("vacant")
                        and (pit.get("path") or "") in path_now):
                    # collapse: take over the exact layout position the
                    # leaving image had in the NEW similarity order — this
                    # outranks any remembered geometry of the slot itself.
                    return path_now[pit.get("path")]
                if anchor in geo:
                    return geo[anchor]               # vacancy: keep its spot
                return arr

            targets = sorted((name_target(a, arr), i)
                             for i, (a, arr, _) in enumerate(vacant))
            result = [None] * max(len(out),
                                  len(ordered_imgs) + len(vacant))
            occupied = set()
            for want, vi in targets:
                it = vacant[vi][2]
                free = [i for i in range(len(result)) if i not in occupied]
                if not free:
                    break
                want = max(0, min(want, len(result) - 1))
                target = min(free, key=lambda i: (abs(i - want), i))
                result[target] = it
                occupied.add(target)
            free = [i for i in range(len(result)) if result[i] is None]
            for slot, it in zip(free, ordered_imgs):
                result[slot] = it
            out = [it for it in result if it is not None]
            # Persist the geometry AFTER placement so already-vacant slots
            # stay put on every later refresh.  Slots that are NOT vacant
            # right now get their geo entry dropped — otherwise a slot
            # could claim a position that a different tile occupies by the
            # time it collapses, shuffling the layout.  A collapsing slot's
            # vacancy therefore always lands exactly where its own image
            # sat, via path continuity.
            seen_anchors = set(geo) | {a for a, _, _ in vacant}
            for it in out:
                a = self._slot_anchor(it)
                if a is not None:
                    seen_anchors.add(a)
            new_geo = {a: p for a, p in geo.items() if a in seen_anchors}
            for k, it in enumerate(out):
                a = self._slot_anchor(it)
                if a is not None and a not in new_geo:
                    new_geo[a] = k
            self._slot_pos_geo = new_geo
            self._remember_positions(out)
            return out
        if self.order_mode:
            from datetime import date as _date
            # Files whose creation date cannot be read sort to the very end
            # (oldest-first) or the very start (newest-first); otherwise
            # they keep their incoming relative order.
            unknown_key = (_date.max if self.order_mode == "asc"
                           else _date.min)
            vacant = []     # [(slot_anchor_or_None, arrival_pos, item)]
            imgs = []       # [(sort_key, item)] — real image tiles
            for pos, it in enumerate(out):
                if it.get("vacant"):
                    vacant.append((self._slot_anchor(it), pos, it))
                    continue
                path = it.get("path") or ""
                d = self._created_date(path) if path else None
                imgs.append(((d or unknown_key), pos, it))
            # Stable sort by creation day.  Equal keys (same day, unknown
            # dates) keep their incoming relative order.  "desc" is the
            # REVERSED oldest-first sequence with same-day ties left in
            # slot order — using reverse() here (instead of sorting by the
            # raw date descending) keeps tiles that already sit on screen
            # from flipping positions between rebuilds: collapsing a group
            # then swaps exactly one tile out for its VACANT placeholder
            # instead of shuffling the whole grid.
            imgs.sort(key=lambda t: (t[0], t[1]))
            if self.order_mode == "desc":
                ordered_imgs = [it for _, _, it in reversed(imgs)]
            else:
                ordered_imgs = [it for _, _, it in imgs]
            # Place vacancies deterministically: sorted by their slot
            # anchor, the Nth vacancy takes the Nth free position computed
            # against the pre-collapse baseline (current view minus tiles
            # that already sit vacant).  This puts the VACANT thumbnail
            # exactly where the collapsed image was, without moving any
            # other tile.
            base_len = sum(1 for it in (self.items or [])
                           if not it.get("vacant")) or len(out)
            # Target position for every vacancy = where its SLOT lived in
            # the PREVIOUS view (the layout the user actually sees), found
            # by PATH continuity: if the tile that sat at this slot before
            # is still on screen, the vacancy takes that tile's current
            # index — collapsing a group therefore swaps exactly the
            # removed image out for its VACANT placeholder while every
            # other tile keeps its spot.  If the previous occupant itself
            # moved elsewhere (e.g. a prime transplant), the vacancy lands
            # where that occupant ended up; an already-vacant slot simply
            # stays put; slots never seen before interpolate between their
            # neighbours' targets.
            # Previous view geometry: how many tiles (images AND
            # vacancies) came BEFORE each dataset slot number, plus each
            # slot's previous occupant.
            prev = list(self.items or [])
            prev_occ = {}
            for pit in prev:
                a = self._slot_anchor(pit)
                if a is not None and a not in prev_occ:
                    prev_occ[a] = pit
            sorted_slots = sorted(prev_occ)
            prefix = {}
            run = 0
            for a in sorted_slots:
                prefix[a] = run
                run += 1

            def prev_target(anchor):
                pit = prev_occ.get(anchor)
                if pit is None:
                    return None                      # slot never seen before
                if pit.get("vacant"):
                    # already-vacant slot: land where its fresh dict sits
                    # in the pool — same slot numbers on both sides keep
                    # the vacancy exactly in place across refreshes.
                    for cit in out:
                        if (cit.get("vacant")
                                and self._slot_anchor(cit) == anchor):
                            return out.index(cit)
                    return None
                # Where this slot's IMAGE sat in the previous layout,
                # translated into the new one: every OTHER collapsed slot
                # below the boundary keeps its tile there (+1 shift),
                # while this slot's own removed tile leaves a FREE spot
                # right at the old position — which is exactly where the
                # VACANT placeholder belongs.
                b = prefix[anchor] + sum(
                    1 for a2, p2 in prev_occ.items()
                    if a2 < anchor and not p2.get("vacant")
                    and a2 not in {a0 for a0, _, _ in vacant})
                return min(b + bisect.bisect_left(sorted_slots, anchor),
                           len(ordered_imgs))

            targets = []
            for anchor, arr, it in vacant:
                t = prev_target(anchor)
                targets.append(arr if t is None else t)
            result = [None] * max(base_len,
                                  len(ordered_imgs) + len(vacant))
            occupied = set()
            # place vacancies nearest their target first; ties resolved by
            # target order so multiple vacancies keep slot order between
            # themselves.  (``targets`` is index-aligned with ``vacant``,
            # so pair them up BEFORE sorting — sorting the zipped tuples
            # directly would compare raw item dicts on target ties.)
            placement = sorted(zip(targets, range(len(vacant))),
                               key=lambda z: (z[0], z[1]))
            occupied = set()
            for want, vi in placement:
                it = vacant[vi][2]
                free = [i for i in range(len(result)) if i not in occupied]
                if not free:
                    break
                want = max(0, min(want, len(result) - 1))
                target = min(free, key=lambda i: (abs(i - want), i))
                result[target] = it
                occupied.add(target)
            free = [i for i in range(len(result)) if result[i] is None]
            for slot, it in zip(free, ordered_imgs):
                result[slot] = it
            out = [it for it in result if it is not None]
        self._remember_positions(out)
        return out

    def _apply_date_filter(self):
        """Order + filter the freshly-set pool with this window's combos.
        No-op while a name search is on screen (its stashed pool was already
        updated by set_items) or when both combos sit on their defaults."""
        if (not self.date_mode and not self.order_mode) or self.searching:
            return
        if self.view_mode == "grouped":
            return
        self.items = self._apply_date_view(self.items)

    def _update_order_chrome(self):
        """Reflect the active order in the combo label so the current
        arrangement is visible at a glance even from across the room."""
        idx = self.order_combo.currentIndex()
        base_label = self.order_combo.itemText(idx).split("  |  ")[0]
        suffix = ""
        if self.order_mode == "asc":
            suffix = "  |  oldest first"
        elif self.order_mode == "desc":
            suffix = "  |  newest first"
        elif self.order_mode == "name":
            suffix = "  |  similar names together"
        self.order_combo.setItemText(idx, base_label + suffix)

    def _order_mode_changed(self, _idx):
        """⏳ combo: re-arrange the view by creation date (nothing hidden)."""
        self.order_mode = self.order_combo.currentData()
        self._update_order_chrome()
        self._refresh_date_view()

    def _update_date_chrome(self):
        """Show/hide the calendar boxes + refresh the combo label so the
        chosen dates are visible at a glance."""
        mode = self.date_mode
        self.date_from_edit.setVisible(mode in ("from", "range"))
        self.date_to_edit.setVisible(mode in ("to", "range"))
        idx = self.date_combo.currentIndex()
        base_label = self.date_combo.itemText(idx).split("  |  ")[0]
        suffix = ""
        if mode == "from" and self.date_d1:
            suffix = f"  |  from {self.date_d1.isoformat()}"
        elif mode == "to" and self.date_d2:
            suffix = f"  |  before {self.date_d2.isoformat()}"
        elif mode == "range":
            if self.date_d1 and self.date_d2:
                suffix = f"  |  {self.date_d1.isoformat()} → {self.date_d2.isoformat()}"
            elif self.date_d1:
                suffix = f"  |  from {self.date_d1.isoformat()}"
            elif self.date_d2:
                suffix = f"  |  before {self.date_d2.isoformat()}"
        self.date_combo.setItemText(idx, base_label + suffix)

    def _refresh_date_view(self):
        """Repaint after an order/filter change: re-run the search when one
        is active (it narrows within the date window), otherwise rebuild the
        ordered/filtered view straight from the untouched full pool."""
        if self.searching:
            self.apply_search_filter()
            return
        if self.view_mode == "grouped":
            return
        self.items = self._apply_date_view(list(self._pool_items or []))
        self.current_page = max(0, min(self.current_page, self.total_pages() - 1))
        self._load_page()

    def _date_mode_changed(self, _idx):
        mode = self.date_combo.currentData()
        self.date_mode = mode
        today = datetime.now().date()
        if mode in ("from", "range") and self.date_d1 is None:
            self.date_d1 = today
            self.date_from_edit.setDate(QDate(today.year, today.month, today.day))
        if mode in ("to", "range") and self.date_d2 is None:
            self.date_d2 = today
            self.date_to_edit.setDate(QDate(today.year, today.month, today.day))
        self._update_date_chrome()
        self._refresh_date_view()

    def _date_bounds_changed(self, _qdate):
        d1 = self.date_from_edit.date()
        d2 = self.date_to_edit.date()
        self.date_d1 = datetime(d1.year(), d1.month(), d1.day()).date()
        self.date_d2 = datetime(d2.year(), d2.month(), d2.day()).date()
        self._update_date_chrome()
        self._refresh_date_view()

    # ---- manual name search / back ---------------------------------------
    def _run_search(self):
        """🔍 button / Enter in the search box: filter this view by file name.

        Shows EVERY file whose name contains the typed text (case-sensitive,
        exactly as typed).  An empty box restores the full pool."""
        term = self.search_edit.text()
        if not term.strip():
            self.exit_search()
            return
        base = (self._pool_items or self._pre_search_items) if self.searching \
            else (self._pool_items or self.items)
        base = base or []
        # narrow WITHIN the active date-created order + filter (they stack)
        base = self._apply_date_view(base)
        matched = [it for it in base
                   if it.get("path")
                   and term in os.path.basename(it["path"])]
        self.enter_search(matched, term)

    def apply_search_filter(self):
        """Re-apply the active search term after the underlying pool was
        refreshed — so new/removed images are reflected without kicking
        the user out of their search."""
        if self.searching and self.search_edit.text().strip():
            self._run_search()

    def _back_clicked(self):
        """← button: leave the search / expanded-group view and restore
        whatever was showing before."""
        if self.view_mode == "grouped" and self.expanded_gid is not None:
            self.collapse_group()
            return
        self.back_requested.emit()
        self.exit_search()

    # ---- grouped browser: expand / collapse ------------------------------
    def group_items_from_cluster(self):
        """Build one tile per group (prime thumbnail or VACANT placeholder).
        Subclass (GroupsTab) may override to add filtering; keep this as a
        safe fallback so the gallery always renders something sensible."""
        out = []
        if not self.cluster:
            return out
        for g in sorted(self.cluster.all_groups(), key=lambda x: x["name"].lower()):
            out.append({"kind": "group", "gid": g["id"],
                        "path": g.get("prime") or "",
                        "vacant": not g.get("members")})
        return out

    def expand_group(self, gid):
        """Show every image of ``gid`` as ordinary tiles inside THIS panel."""
        if not self.cluster:
            return
        g = self.cluster.get_group(gid)
        if not g:
            return
        if self.searching:
            self.exit_search()          # searches stash items — clear first
        if self.expanded_gid is None:
            # remember the groups grid exactly as it stands (items + page)
            self._pre_expand_items = list(self.items)
            self._pre_expand_page = self.current_page
        self.expanded_gid = gid
        members = []
        for p in g["members"]:
            members.append({"kind": "image", "path": p, "gid": gid,
                            "is_prime": pc_ok(g.get("prime"), p),
                            "vacant": False})
        self.items = members
        self.current_page = 0
        self._highlighted_key = None
        self._pending_key = None
        self._load_page()
        self.count_label.setText(
            f"{len(members)} images in “{g['name']}”   |   ← back to groups")
        self.group_status.setText(
            f"📂 Expanded “{g['name']}” — right-click a tile for prime/remove, "
            "drop images here to add them to this group.")
        self.group_status.setStyleSheet(
            "color:#29b6f6;font-size:9pt;font-weight:600;")
        self._update_search_chrome()

    def refresh_expanded(self):
        """Rebuild the expanded members page from live cluster data (used
        when the underlying group changed while it is on screen)."""
        gid = self.expanded_gid
        g = self.cluster.get_group(gid) if self.cluster else None
        if not g:
            self.collapse_group()
            return
        members = [{"kind": "image", "path": p, "gid": gid,
                    "is_prime": pc_ok(g.get("prime"), p), "vacant": False}
                   for p in g["members"]]
        self.items = members
        self.current_page = max(0, min(self.current_page, self.total_pages() - 1))
        self._load_page()
        self.count_label.setText(
            f"{len(members)} images in “{g['name']}”   |   ← back to groups")

    def collapse_group(self):
        """← from an expanded group back to the groups grid."""
        if self.expanded_gid is None:
            return
        self.expanded_gid = None
        self.items = getattr(self, "_pre_expand_items", []) or []
        self._pre_expand_items = None
        self.current_page = max(0, min(getattr(self, "_pre_expand_page", 0),
                                       self.total_pages() - 1))
        self._pre_expand_page = 0
        self._highlighted_key = None
        self._pending_key = None
        self._load_page()
        self._update_group_status()

    def reload_groups(self):
        """Regenerate the groups-grid tiles from the (possibly changed)
        cluster and repaint.  Called by GroupsTab on every refresh()."""
        if self.view_mode != "grouped":
            return
        if self.expanded_gid is not None:
            if self.cluster and self.cluster.get_group(self.expanded_gid):
                self.refresh_expanded()
            else:
                self.collapse_group()
            return
        self.items = self.group_items_from_cluster()
        self.current_page = max(0, min(self.current_page, self.total_pages() - 1))
        self._load_page()

    # ---- drag & drop into the gallery ------------------------------------
    def _on_paths_dropped(self, paths, pos=None):
        """Images dropped onto this panel.  In the grouped browser they go
        straight into the target group: the expanded one, or the group under
        the cursor on the groups grid.  Emitted onward for the owner to act.
        """
        if self.view_mode != "grouped" or not self.cluster:
            return                       # normal galleries don't accept drops
        paths = [p for p in (paths or []) if p]
        if not paths:
            return
        gid = self.expanded_gid
        if gid is None and pos is not None:
            hit = self.list_widget.itemAt(pos)
            d = hit.data(Qt.UserRole) if hit is not None else None
            if d and d.get("kind") == "group":
                gid = d["gid"]
        self.images_dropped.emit(paths, gid)

    # ---- drag hover highlight on group tiles ------------------------------
    def _restyle_tile(self, container):
        """Re-apply the normal border style of one cell container (used to
        clear the bright drop-target highlight once the drag moves away)."""
        for item, c in self._entries:
            if c is container:
                c.setStyleSheet(self._style_for(item))
                return

    def _clear_hot_tile(self):
        hot = getattr(self.list_widget, "_hot_tile", None)
        if hot is not None:
            try:
                self._restyle_tile(hot)
            except Exception:
                pass
            self.list_widget._hot_tile = None

    def enter_search(self, matched_items, term):
        """Show ``matched_items`` (top name matches) in place of the pool.

        The current items + page are stashed so :meth:`exit_search` can put
        everything back exactly as it was.
        """
        if not self.searching:
            self._pre_search_items = self.items
            self._pre_search_page = self.current_page
            self.searching = True
        self.search_term = term or ""
        self.items = matched_items or []
        self.current_page = 0
        self._highlighted_key = None
        self._pending_key = None
        self._load_page()
        self.count_label.setText(
            f"🔎 {len(self.items)} name match(es) containing “{self.search_term}”"
            "   |   ← back")
        self.group_status.setText(
            f"Search results for “{self.search_term}” — click tiles to swap "
            "as usual; ← returns to the full list.")
        self.group_status.setStyleSheet(
            "color:#f5c518;font-size:9pt;font-weight:600;")

    def exit_search(self):
        """Restore the pool that was showing before the search started."""
        if not self.searching:
            return
        self.searching = False
        self.search_term = ""
        self.items = self._pre_search_items or []
        self._pre_search_items = None
        self.current_page = max(
            0, min(self._pre_search_page, self.total_pages() - 1))
        self._highlighted_key = None
        self._pending_key = None
        self._load_page()
        self._update_group_status()

    def _update_search_chrome(self):
        """Keep the ← button honest about the current view state.  The 🔍
        search box is a plain manual filter — always available."""
        self.back_btn.setVisible(self.searching or
                                 (self.view_mode == "grouped"
                                  and self.expanded_gid is not None))

    # ---- rendering -------------------------------------------------------
    def _load_page(self):
        self._generation += 1
        gen = self._generation
        scroll_top = (self.list_widget.verticalScrollBar().value()
                      if hasattr(self, "list_widget") else 0)
        self.list_widget.clear()
        self._labels_by_path = {}
        self._entries = []

        start = self.current_page * self.page_size
        end = min(start + self.page_size, len(self.items))
        for item in self.items[start:end]:
            li, container, thumb = self._item_builder(item)
            self.list_widget.addItem(li)
            self.list_widget.setItemWidget(li, container)
            self._entries.append((item, container))
            if item.get("path") and not item.get("vacant"):
                self._labels_by_path.setdefault(item["path"], []).append(thumb)
                t = ThumbnailTask(item["path"], gen)
                t.signals.finished.connect(self._thumb_ready)
                _THUMB_POOL.start(t)

        total = self.total_pages()
        self.page_label.setText(f"Page {self.current_page + 1} / {total}")
        if not self.searching and not (self.view_mode == "grouped"
                                       and self.expanded_gid is None):
            pool_n = len(self._pool_items)
            if self.date_mode and len(self.items) != pool_n:
                self.count_label.setText(
                    f"{len(self.items)} of {pool_n} images — date filter active")
            elif self.order_mode:
                order_txt = ("oldest first" if self.order_mode == "asc"
                             else "newest first"
                             if self.order_mode == "desc"
                             else "similar names together")
                self.count_label.setText(
                    f"{len(self.items)} images total — ordered by date "
                    f"created ({order_txt})")
            else:
                self.count_label.setText(f"{len(self.items)} images total")
        self.prev_btn.setEnabled(self.current_page > 0)
        self.next_btn.setEnabled(self.current_page < total - 1)
        # The highlighted cell (➖/🔍 target) no longer exists after a reload;
        # re-validate it so the buttons can't act on a stale path.
        if self._highlighted_key is not None and \
                self._item_by_key(self._highlighted_key) is None:
            self._highlighted_key = None
        btn = getattr(self, "hide_btn", None)
        if btn is not None:
            btn.setEnabled(self._highlighted_key is not None)
        pb = getattr(self, "pin_btn", None)
        if pb is not None:
            hl_item = (self._item_by_key(self._highlighted_key)
                       if self._highlighted_key else None)
            pb.setEnabled(hl_item is not None
                          and hl_item.get("kind") == "group")
        self._update_search_chrome()
        self.restyle()
        # restore scroll position (e.g. when ← puts the old page back)
        self.list_widget.verticalScrollBar().setValue(scroll_top)
        self.page_changed.emit()

    def _build_item(self, item):
        """Back-compat alias — the image cell builder."""
        return self._build_image_item(item)

    def _build_image_item(self, item):
        path = item["path"]
        vacant = item.get("vacant", False)

        li = QListWidgetItem()
        li.setSizeHint(QSize(THUMB_SIZE + 18, THUMB_SIZE + 78))
        li.setData(Qt.UserRole, item)
        if path and not vacant:
            # make the cell itself a drag source (drop onto the Groups tab)
            li.setFlags(li.flags() | Qt.ItemIsDragEnabled)
            li.setData(Qt.UserRole + 2, path)
        else:
            li.setFlags(Qt.ItemIsEnabled)

        container = DraggableCell(self.list_widget, lambda p=path: p,
                                  data_getter=lambda d=item: d)
        if vacant:
            vname = (item.get("vacancy_name") or "").strip()
            container.setToolTip(("Vacant slot — " + vname) if vname
                                 else "Vacant slot")
        else:
            container.setToolTip(path or "Vacant slot")
        v = QVBoxLayout(container)
        v.setContentsMargins(4, 4, 4, 4)
        v.setSpacing(3)

        thumb = QLabel("VACANT" if vacant else "Loading…")
        thumb.setAlignment(Qt.AlignCenter)
        thumb.setFixedSize(THUMB_SIZE, THUMB_SIZE)
        thumb.setStyleSheet(
            "background-color:#14141f;border-radius:4px;color:#7a7d90;"
            "font-weight:bold;letter-spacing:1px;"
            if vacant else
            "background-color:#2b2d31;border-radius:4px;color:#666;"
        )
        v.addWidget(thumb, alignment=Qt.AlignCenter)

        # group badge row
        badge = QLabel(self._badge_text(item))
        badge.setAlignment(Qt.AlignCenter)
        badge.setStyleSheet("font-size:8pt;")
        badge.setFixedHeight(14)
        v.addWidget(badge)
        item["_badge"] = badge

        if vacant:
            vname = (item.get("vacancy_name") or "").strip()
            lbl = QLabel(f"slot #{item.get('index')}")
            lbl.setAlignment(Qt.AlignCenter)
            lbl.setStyleSheet("color:#7a7d90;font-size:9px;font-style:italic;")
            v.addWidget(lbl)
            sub = QLabel(vname if vname else "empty — click to fill")
            sub.setAlignment(Qt.AlignCenter)
            sub.setStyleSheet("color:#55576a;font-size:8px;")
            sub.setWordWrap(True)
            v.addWidget(sub)
        else:
            # The snapshot stored in the item can be missing (group-member
            # tiles built from paths only) or stale.  Always fall back to
            # the live rater lookup so a grouped/dragged image never shows
            # up as an unrated tile just because its stars weren't carried
            # through the grouping pipeline.
            pr = item.get("primary")
            sec = item.get("secondary")
            if pr is None or self.rater is not None:
                pr = self.rater.get_rating(path) if self.rater else (pr or 0)
            if sec is None or self.rater is not None:
                sec = (self.rater.get_secondary_rating(path)
                       if self.rater else (sec or 0))
            item["primary"] = pr
            item["secondary"] = sec
            v.addWidget(RatingStarsWidget(pr, sec),
                        alignment=Qt.AlignCenter)
            name = QLabel(short_name(path))
            name.setAlignment(Qt.AlignCenter)
            name.setStyleSheet("color:#9a9da3;font-size:9px;")
            name.setWordWrap(True)
            v.addWidget(name)

        return li, container, thumb

    def _badge_text(self, item):
        if item.get("vacant") or not self.cluster:
            return ""
        path = item["path"]
        gids = self.cluster.groups_for_path(path)
        if not gids:
            return ""
        gid = gids[0]
        g = self.cluster.get_group(gid)
        if not g:
            return ""
        nm = g["name"]
        if len(nm) > 12:
            nm = nm[:11] + "…"
        # compare in CANONICAL form — dataset slots may hold a different
        # spelling of the same file than the group's stored prime
        if pc_ok(g.get("prime"), path):
            return f"<span style='color:#ff9800;font-weight:bold;'>★ {nm}</span>"
        return f"<span style='color:#4caf50;'>● {nm}</span>"

    # ---- GROUP TILE (grouped browser: one cell == one whole group) -------
    def _build_group_item(self, item):
        """Render a GROUP as a single tile that looks exactly like an image
        cell: prime thumbnail on top, badge row, name row.  A group with no
        images yet shows a dashed VACANT placeholder instead."""
        gid = item["gid"]
        g = self.cluster.get_group(gid) if self.cluster else None
        if not g:
            g = {"name": "?", "members": [], "prime": None}
        members = g.get("members", [])
        prime = g.get("prime")
        empty = not members
        thumb_path = prime or ""

        li = QListWidgetItem()
        li.setSizeHint(QSize(THUMB_SIZE + 18, THUMB_SIZE + 78))
        li.setData(Qt.UserRole, item)
        # groups themselves aren't draggable; their prime thumbnail isn't a
        # drag source here either — dragging happens from the galleries
        li.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)

        container = DraggableCell(self.list_widget, lambda p="": p,
                                  data_getter=lambda d=item: d)
        # NOTE: no path getter payload on purpose — group tiles are pure
        # DROP targets.  As plain QWidgets they used to swallow every drag
        # event and Qt painted the red "no-drop" circle over them; being
        # DraggableCells they now forward drags to the owning list and
        # light up when a drop would land in them.
        # Remember which group this tile is: the drag proxy uses it to light
        # up exactly the tile a drop would land in.
        container._drop_owner = item
        container.setToolTip(
            f"{g['name']} — {len(members)} image(s)\n"
            f"Prime: {os.path.basename(prime) if prime else '— none —'}\n"
            "Double-click / right-click → Expand group.\n"
            "Drop images onto this tile to add them to the group.")
        v = QVBoxLayout(container)
        v.setContentsMargins(4, 4, 4, 4)
        v.setSpacing(3)

        thumb = QLabel("VACANT" if empty else "Loading…")
        thumb.setAlignment(Qt.AlignCenter)
        thumb.setFixedSize(THUMB_SIZE, THUMB_SIZE)
        thumb.setStyleSheet(
            "background-color:#14141f;border-radius:4px;color:#7a7d90;"
            "font-weight:bold;letter-spacing:1px;"
            if empty else
            "background-color:#2b2d31;border-radius:4px;color:#666;")
        v.addWidget(thumb, alignment=Qt.AlignCenter)

        badge = QLabel("")
        badge.setAlignment(Qt.AlignCenter)
        badge.setStyleSheet("font-size:8pt;")
        badge.setFixedHeight(14)
        v.addWidget(badge)
        item["_badge"] = badge

        title = QLabel(short_name(g["name"], 18))
        title.setAlignment(Qt.AlignCenter)
        title.setStyleSheet("color:#e6e6e6;font-size:9px;font-weight:bold;")
        title.setWordWrap(True)
        v.addWidget(title)

        sub = QLabel(f"{len(members)} image(s)" if not empty
                     else "empty — drop an image in")
        sub.setAlignment(Qt.AlignCenter)
        sub.setStyleSheet(("color:#9a9da3;font-size:8px;" if not empty
                           else "color:#55576a;font-size:8px;font-style:italic;"))
        v.addWidget(sub)

        return li, container, thumb

    def _group_badge_text(self, item):
        if not self.cluster:
            return ""
        g = self.cluster.get_group(item["gid"])
        if not g:
            return ""
        n = len(g["members"])
        if n == 0:
            return "<span style='color:#55576a;font-style:italic;'>vacant</span>"
        if g.get("prime"):
            return "<span style='color:#ff9800;font-weight:bold;'>★ prime</span>"
        return "<span style='color:#4caf50;'>☆ no prime</span>"

    def _group_style_for(self, item):
        gid = item["gid"]
        if gid in (self.staged_group_id, self.pinned_group_id):
            base = STYLE_STAGED
        elif gid == getattr(self, "_hl_gid", None):
            base = STYLE_HL
        else:
            g = self.cluster.get_group(gid) if self.cluster else None
            base = STYLE_VACANT if (g and not g["members"]) else STYLE_NONE
        # Rename mode (Shift+R armed): every group tile glows magenta so the
        # user can SEE that the next click renames instead of highlights.
        if self._rename_armed or HOTKEYS.is_rename_key_held():
            return ("background-color:#3d1440;border:2px solid #e91ee0;"
                    "border-radius:8px;")
        return base

    def restyle(self):
        """Repaint borders in place — no thumbnail reload, no flicker."""
        for item, container in self._entries:
            container.setStyleSheet(self._style_for(item))
            badge = item.get("_badge")
            if badge is not None:
                badge.setText(self._badge_text_for(item))

    def _style_for(self, item):
        if item.get("kind") == "group":
            return self._group_style_for(item)
        return self._image_style_for(item)

    def _badge_text_for(self, item):
        if item.get("kind") == "group":
            return self._group_badge_text(item)
        return self._badge_text(item)

    def _image_style_for(self, item):
        key = (item["path"], item.get("index"))
        if self._pending_key == key:
            return STYLE_PENDING
        if item.get("vacant"):
            return STYLE_VACANT
        if self.cluster:
            path = item["path"]
            gids = self.cluster.groups_for_path(path)
            if gids:
                gid = gids[0]
                g = self.cluster.get_group(gid)
                # canonical comparison — the slot may hold a different
                # spelling of the same file than the stored prime
                if g and pc_ok(g.get("prime"), path):
                    return STYLE_GROUP_PRIME
                if gid in (self.staged_group_id, self.pinned_group_id):
                    return STYLE_STAGED
                return STYLE_GROUP_MEMBER
        if self._highlighted_key == key:
            return STYLE_HL
        return STYLE_NONE

    def _thumb_ready(self, path, gen, pm):
        if gen != self._generation:
            return
        for lbl in self._labels_by_path.get(path, []):
            if not pm.isNull():
                lbl.setPixmap(pm.scaled(THUMB_SIZE, THUMB_SIZE,
                                        Qt.KeepAspectRatio, Qt.SmoothTransformation))
                lbl.setText("")
            else:
                lbl.setText("No Preview")

    # ---- mouse / hotkey routing -----------------------------------------
    def eventFilter(self, obj, event):
        if obj is self.list_widget.viewport():
            t = event.type()

            # G + double-click -> PRIME  (consume so nothing else reacts)
            if t == QEvent.MouseButtonDblClick and event.button() == Qt.LeftButton:
                if HOTKEYS.is_group_key_held():
                    data = self._data_at(event.pos())
                    if data and data.get("kind") != "group":
                        self.group_prime_requested.emit(data)
                    return True
                # plain double-click on a GROUP tile -> expand it
                if self.view_mode == "grouped" and self.expanded_gid is None:
                    data = self._data_at(event.pos())
                    if data and data.get("kind") == "group":
                        self.expand_group(data["gid"])
                        self.group_expand_requested.emit(data["gid"])
                        return True

            if t == QEvent.MouseButtonPress:
                if event.button() == Qt.LeftButton:
                    data = self._data_at(event.pos())
                    # Shift+R rename mode: the next left-click on a GROUP
                    # tile renames it to the (truncated, de-duplicated)
                    # clipboard file name instead of just highlighting.
                    if data and data.get("kind") == "group" \
                            and (self._rename_armed
                                 or HOTKEYS.is_rename_key_held()):
                        self._rename_from_clipboard(data["gid"])
                        return True      # consumed: no highlight/selection
                    if data and data.get("kind") == "group":
                        # single click just highlights the group tile
                        self._hl_gid = data["gid"]
                        self._update_search_chrome()
                        self.restyle()
                        return True
                    if HOTKEYS.is_group_key_held():
                        if data:
                            self.group_add_requested.emit(data)
                        return True          # consume: no swap-selection
                    if data:
                        # Left-click = highlight this cell (➖ target).
                        self.set_highlighted((data["path"],
                                              data.get("index")))
                        # Remember the FULL file name for Shift+C even if
                        # the pending swap is later cancelled by a drag —
                        # "what did I last click?" must survive that.
                        if data.get("path") and not data.get("vacant"):
                            self._last_clicked_name = \
                                os.path.basename(data["path"])
                        # Arm the swap-selection but DO NOT emit yet: a
                        # press is only half a click.  Emitting here made
                        # drag-and-drop gestures trigger swaps with the
                        # tile the drag started on.  The signal fires in
                        # the release branch below, once we know the
                        # gesture was a full click (no drag drift).
                        self._pending_click_data = data
                        self._pending_click_pos = event.pos()
                        return True
                elif event.button() == Qt.RightButton:
                    data = self._data_at(event.pos())
                    if data and data.get("path"):
                        self._rc_data = data
                        self._rc_holding = True
                        self._rc_timer.start(200)

            elif t == QEvent.MouseButtonRelease:
                if event.button() == Qt.LeftButton:
                    pc = self._pending_click_data
                    pp = self._pending_click_pos
                    self._pending_click_data = None
                    self._pending_click_pos = None
                    if pc is not None:
                        rel = self._data_at(event.pos())
                        same_cell = (rel is not None
                                     and rel.get("path") == pc.get("path")
                                     and rel.get("index") == pc.get("index"))
                        # Guard against drag gestures sneaking through as
                        # "clicks": if the pointer ever drifted past the
                        # drag threshold since the press, this was a
                        # press-drag (grouping), not a full click — even
                        # if it happened to land back on the same tile.
                        dragged = (pp is not None and
                                   (event.pos() - pp).manhattanLength()
                                   >= QApplication.startDragDistance())
                        # Note: Qt fires the press/release pair *before*
                        # the MouseButtonDblClick event, so the second
                        # half of a double-click may still arm/emit a
                        # selection here; the DblClick branch above owns
                        # the PRIME/expand gesture itself.
                        if same_cell and not dragged:
                            self.image_clicked.emit(pc)
                        return True
                if event.button() == Qt.RightButton:
                    self._rc_holding = False
                    # If the hold popped the enlarged preview, keep it up
                    # while the cursor is still over it and swallow the
                    # release-time context menu (see _context_menu).  Once
                    # the pointer leaves the popup it closes automatically.
                    gp = QCursor.pos()
                    if not (self._rc_preview_shown and self._enlarged
                            and self._enlarged.contains(gp)):
                        self.hide_enlarged()

            elif t == QEvent.MouseMove:
                # Pointer drifted past the drag threshold while a swap
                # click was armed -> this is a press-drag gesture, not a
                # full click.  Disarm so the release cannot fire
                # image_clicked and hijack the pending-swap state.
                if self._pending_click_data is not None \
                        and self._pending_click_pos is not None \
                        and (event.pos() - self._pending_click_pos)\
                        .manhattanLength() >= QApplication.startDragDistance():
                    self._pending_click_data = None
                    self._pending_click_pos = None
                if self._rc_holding and self._enlarged and self._enlarged.isVisible():
                    self._enlarged.reposition(QCursor.pos())
                elif self._rc_preview_shown and self._enlarged \
                        and not self._enlarged.contains(QCursor.pos()):
                    # pinned preview dismissed by moving away from it
                    self._rc_preview_shown = False
                    self.hide_enlarged()

        return super().eventFilter(obj, event)

    def _data_at(self, pos):
        it = self.list_widget.itemAt(pos)
        return it.data(Qt.UserRole) if it else None

    # ---- enlarged preview -------------------------------------------------
    def _show_enlarged(self):
        if not self._rc_data or not self._rc_holding:
            return
        if self._enlarged is None:
            self._enlarged = EnlargedImageLabel(self)
        pm = make_pixmap(self._rc_data["path"], ENLARGED_LOAD_SIZE)
        if not pm.isNull():
            self._enlarged.show_at(QCursor.pos(), pm, ENLARGED_DISPLAY_SIZE)
            # The hold actually produced a popup: remember it so the
            # context menu that Qt fires on right-button release gets
            # swallowed (see _context_menu).
            self._rc_preview_shown = True

    def hide_enlarged(self):
        if self._enlarged:
            self._enlarged.hide()
            self._enlarged.clear_image()
        self._rc_data = None
        self._rc_timer.stop()
        self._rc_holding = False
        self._rc_preview_shown = False

    def leaveEvent(self, e):
        self._rc_holding = False
        self.hide_enlarged()
        super().leaveEvent(e)

    # ---- context menu ----------------------------------------------------
    def _context_menu(self, pos):
        if self._rc_preview_shown:
            # This request comes from releasing a right-click HOLD that
            # already popped the enlarged preview.  Treat it as "done
            # looking at the image", not as a menu request — no menu must
            # ever appear on top of the big image.  A quick right-click
            # (press+release before the timer fires) never sets the flag,
            # so its menu still opens normally.
            self._rc_preview_shown = False
            # keep the pinned preview up while the cursor is over it;
            # moving away dismisses it (see eventFilter MouseMove branch)
            gp = QCursor.pos()
            if not (self._enlarged and self._enlarged.contains(gp)):
                self.hide_enlarged()
            return
        data = self._data_at(pos)
        if not data:
            return

        # ---- grouped browser routing -----------------------------------
        if self.view_mode == "grouped":
            if data.get("kind") == "group" and self.expanded_gid is None:
                # right-click on a GROUP tile → owner shows the group menu
                # (Expand / rename / delete …).  The hold-preview above was
                # already swallowed, so only genuine quick right-clicks get
                # here.
                self.group_menu_requested.emit(data["gid"], pos)
                return
            if self.expanded_gid is not None or data.get("gid"):
                # right-click on a MEMBER tile inside an expanded group →
                # owner shows prime/remove menu for this image
                self.member_menu_requested.emit(data, pos)
                return

        menu = QMenu(self)

        if data.get("vacant"):
            act = menu.addAction("↩ Restore previous image into this slot")
            act.setEnabled(bool(data.get("original_path")))
            act.triggered.connect(lambda: self.restore_vacancy_requested.emit(data))
        else:
            # NOTE: hide/unhide intentionally does NOT live here anymore —
            # the right-click context menu collided with the right-click
            # hold enlarged preview.  Use the ➖ button on the rated panel,
            # which acts on the highlighted image.
            if self.cluster:
                gids = self.cluster.groups_for_path(data["path"])
                if gids:
                    menu.addSeparator()
                    for gid in gids:
                        g = self.cluster.get_group(gid)
                        tag = "★ PRIME of" if g["prime"] == data["path"] else "member of"
                        a = menu.addAction(f"{tag} “{g['name']}”  ({len(g['members'])})")
                        a.setEnabled(False)
        if menu.actions():
            menu.exec_(self.list_widget.mapToGlobal(pos))


# =============================================================================
# Detachable panel
# =============================================================================
class DetachedWindow(QWidget):
    closed = pyqtSignal()

    def __init__(self, title):
        super().__init__(None, Qt.Window)
        self.setWindowTitle(title)
        self.resize(980, 780)

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_F11:
            self.showNormal() if self.isFullScreen() else self.showFullScreen()
        elif e.key() == Qt.Key_Escape and self.isFullScreen():
            self.showNormal()
        else:
            super().keyPressEvent(e)

    def closeEvent(self, e):
        self.closed.emit()
        super().closeEvent(e)


class DetachablePanel(QWidget):
    def __init__(self, title, content, parent=None):
        super().__init__(parent)
        self.title = title
        self.content = content
        self.floating = None

        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(4)

        head = QHBoxLayout()
        head.addStretch()
        self.detach_btn = QPushButton("⧉ Detach to Window")
        self.detach_btn.clicked.connect(self.toggle)
        head.addWidget(self.detach_btn)
        outer.addLayout(head)

        self.body = QVBoxLayout()
        self.body.setContentsMargins(0, 0, 0, 0)
        outer.addLayout(self.body, 1)
        self.body.addWidget(self.content)

        self.placeholder = QLabel(f"'{title}' is open in a separate window.\n(F11 to fullscreen it.)")
        self.placeholder.setAlignment(Qt.AlignCenter)
        self.placeholder.setStyleSheet("color:#9a9da3;font-style:italic;padding:40px;")
        self.placeholder.hide()
        self.body.addWidget(self.placeholder)

    def toggle(self):
        self.reattach() if self.floating else self.detach()

    def detach(self):
        self.body.removeWidget(self.content)
        self.floating = DetachedWindow(self.title)
        fl = QVBoxLayout(self.floating)
        top = QHBoxLayout()
        b1 = QPushButton("⧉ Reattach to Main Window")
        b1.clicked.connect(self.reattach)
        b2 = QPushButton("⛶ Fullscreen (F11)")
        b2.clicked.connect(self._fs)
        top.addWidget(b1)
        top.addStretch()
        top.addWidget(b2)
        fl.addLayout(top)
        fl.addWidget(self.content, 1)
        self.floating.closed.connect(self.reattach)
        self.floating.show()
        self.placeholder.show()
        self.detach_btn.setEnabled(False)

    def _fs(self):
        if self.floating:
            self.floating.showNormal() if self.floating.isFullScreen() else self.floating.showFullScreen()

    def reattach(self):
        if self.floating is None:
            return
        fw = self.floating
        self.floating = None
        try:
            fw.layout().removeWidget(self.content)
        except Exception:
            pass
        self.content.setParent(self)
        self.body.addWidget(self.content)
        self.placeholder.hide()
        self.detach_btn.setEnabled(True)
        fw.close()
        fw.deleteLater()

    def force_close_floating(self):
        if self.floating:
            self.floating.close()


# =============================================================================
# Groups tab
# =============================================================================
class GroupsTab(PaginatedGallery):
    """SINGLE-PANEL groups browser.

    There is no side list of group names anymore.  Every group is ONE TILE
    rendered exactly like an image cell — the thumbnail shown IS the group's
    PRIME image.  An empty group shows a dashed VACANT placeholder until the
    first image is dropped onto its tile.

      * right-click a group tile → Expand group / Rename / Delete / prime ...
        (double-click expands too)
      * expanded view: every member as an ordinary tile, ← returns to the
        groups grid
      * drag images from any gallery and drop them ONTO a group tile (or
        anywhere inside an expanded group) to add them to that group
    """
    pin_toggled = pyqtSignal(object)   # gid or None
    data_changed = pyqtSignal(object)  # gid or None
    close_group_requested = pyqtSignal()       # ➕ pressed on a panel
    category_filter_changed = pyqtSignal(str)  # emitted when category filter changes

    def __init__(self, parent=None):
        super().__init__(source_name="groups", title="",
                         item_builder=self._build_group_item, parent=parent)
        self.view_mode = "grouped"
        self.pinned_id = None
        self.viewed_id = None
        self.open_gid = None          # the drag-&-drop group currently OPEN
        self.category_filter = None   # groups are filtered by category
        self._hl_gid = None

        # hide the viewer-only toolbar buttons — this panel gets its own kit
        self.finish_btn.setVisible(False)
        self.search_edit.setVisible(False)
        self.search_btn.setVisible(False)

        lay = self.layout()
        bar = self._bar

        # heading + controls live in the gallery's own toolbar row
        t = QLabel("Groups")
        t.setProperty("role", "heading")
        bar.insertWidget(0, t)

        self.pin_status = QLabel("No group pinned — Viewer is armed for NEW groups")
        self.pin_status.setStyleSheet("color:#7f8289;font-style:italic;font-size:9pt;")
        self.pin_status.setWordWrap(True)
        bar.insertWidget(1, self.pin_status, 1)

        # ---- finder bar: outsource images into a group by path -------------
        self.import_edit = QLineEdit()
        self.import_edit.setPlaceholderText("Paste image path(s)…")
        self.import_edit.setToolTip(
            "Outsource images INTO this group without dragging them.\n\n"
            "Paste one or more full file paths here and click Add — they join\n"
            "the group you're currently viewing (an expanded group, the pinned\n"
            "one, or the open one). Separate several paths with ';', newlines,\n"
            "or paste them straight from Explorer/Finder. Surrounding quotes\n"
            "are stripped automatically.")
        self.import_edit.setClearButtonEnabled(True)
        self.import_edit.setMinimumWidth(190)
        self.import_edit.returnPressed.connect(self._import_from_bar)
        bar.insertWidget(bar.count(), self.import_edit)

        ib = QPushButton("⤵ Add")
        ib.setToolTip("Add the pasted path(s) to the group currently being viewed.")
        ib.clicked.connect(self._import_from_bar)
        bar.insertWidget(bar.count(), ib)

        nb = QPushButton("＋ Empty Group")
        nb.setToolTip("Create a fresh auto-named group. It shows up as a\n"
                      "VACANT tile instantly — drop images onto it.")
        nb.clicked.connect(self._new_empty_group)
        bar.insertWidget(bar.count(), nb)

        # ---- group name search -------------------------------------------
        # Quick retrieval when categories accrue too many groups to sift
        # through visually: type (or paste, e.g. a file name copied with
        # Shift+C) and the grid live-filters to groups whose NAME contains
        # the text.  Pairs with the rename workflow — copy a member's file
        # name, Shift+R+click renames the group to its first 10 chars, then
        # pasting any related file name into THIS box finds the group fast.
        self.group_search_edit = QLineEdit()
        self.group_search_edit.setPlaceholderText("🔎 Find group…")
        self.group_search_edit.setToolTip(
            "Filter the groups grid by NAME — every group whose name\n"
            "contains the typed text stays visible (case-insensitive).\n"
            "Paste a file name here (Shift+C copies one) to jump straight\n"
            "to the group named after it.  Clear the box to show all.\n"
            "Esc or ← exits the filter.")
        self.group_search_edit.setClearButtonEnabled(True)
        self.group_search_edit.setMinimumWidth(140)
        self.group_search_edit.textChanged.connect(self._group_filter_changed)
        bar.insertWidget(bar.count(), self.group_search_edit)

        self.filter_combo = QComboBox()
        self.filter_combo.setToolTip(
            "Show only groups belonging to a category.\n"
            "Defaults to the category currently active in the Viewer.")
        self.filter_combo.addItem("🎯 Active category", "__ACTIVE__")
        self.filter_combo.addItem("All categories", None)
        self.filter_combo.currentIndexChanged.connect(self._filter_changed)
        bar.insertWidget(bar.count(), self.filter_combo)

        # routing hooks owned by this tab
        self.group_menu_requested.connect(self._group_menu)
        self.member_menu_requested.connect(self._member_menu)
        self.images_dropped.connect(self._on_tile_dropped)
        self.list_widget.drop_hint = ("⬇ Drop images onto a group tile to add "
                                      "them to that group")
        self.list_widget._hint_color = "#29b6f6"

        hint = QLabel(
            "Each tile represents one GROUP — the picture you see is that "
            "group's PRIME image.  Right-click (or double-click) a tile to "
            "expand it; ← goes back.  Drop images onto a tile to add them "
            "to the group.  Click a tile then 📌 to pin it (G+click in the "
            "Viewer feeds the pinned group)."
        )
        hint.setStyleSheet("color:#6c6f76;font-size:9px;")
        hint.setWordWrap(True)
        lay.addWidget(hint)

    # ---------------------------------------------------------------------
    def set_data(self, cluster, rater, balancer=None):
        self.cluster = cluster
        self.rater = rater
        self.balancer = balancer
        self._populate_filter_categories()
        self.refresh()

    # ---- category filtering ----------------------------------------------
    def _populate_filter_categories(self):
        """(Re)fill the filter combo with every known category."""
        cats = set()
        if self.balancer:
            try:
                cats.update((self.balancer.categories or {}).keys())
                for prof in (self.balancer.profiles or {}).values():
                    cats.update((prof.get("dataset") or {}).keys())
            except Exception:
                pass
        if self.cluster:
            for g in self.cluster.all_groups():
                if g.get("category"):
                    cats.add(g["category"])
        current = self.filter_combo.currentData()
        self.filter_combo.blockSignals(True)
        while self.filter_combo.count() > 2:
            self.filter_combo.removeItem(self.filter_combo.count() - 1)
        for c in sorted(cats, key=str.lower):
            self.filter_combo.addItem(f"\U0001F4C2 {c}", c)
        idx = self.filter_combo.findData(current)
        if idx >= 0:
            self.filter_combo.setCurrentIndex(idx)
        self.filter_combo.blockSignals(False)

    def set_active_category(self, cat, refresh=True):
        """Called by the Viewer whenever its active category changes."""
        changed = (self.category_filter != cat)
        self.category_filter = cat
        if refresh and changed:
            self.refresh()

    def _filter_changed(self, _idx):
        self.refresh()

    def _current_filter(self):
        """The category the groups grid is currently restricted to (or None)."""
        data = self.filter_combo.currentData()
        if data == "__ACTIVE__":
            return self.category_filter
        return data

    def _known_categories(self):
        cats = []
        for i in range(self.filter_combo.count()):
            d = self.filter_combo.itemData(i)
            if d and d != "__ACTIVE__":
                cats.append(d)
        if not cats and self.balancer:
            cats = sorted((self.balancer.categories or {}).keys(), key=str.lower)
        return cats

    def _guess_category_for_path(self, path):
        """Which category does this image belong to?  Check the dataset(s)
        first; fall back to matching a category name inside the path."""
        if not path:
            return None
        if self.balancer:
            try:
                for prof in (self.balancer.profiles or {}).values():
                    for cat, paths in (prof.get("dataset") or {}).items():
                        if path in paths:
                            return cat
            except Exception:
                pass
        norm = os.path.normpath(path).replace("\\", "/").lower()
        for cat in sorted(self._known_categories(), key=len, reverse=True):
            if f"/{cat.lower()}/" in norm:
                return cat
        return None

    def _ensure_group_category(self, gid):
        """Backfill a category for LEGACY groups created before tagging
        existed.  A group with no recorded category is classified from the
        categories its own members actually live in (dataset lookup first,
        then path-name matching).  If nothing can be inferred we leave it
        untagged — an untagged group stays visible under every filter and
        accepts images from any category, so pre-existing groups are never
        invalidated by the category system.
        """
        if not self.cluster:
            return
        g = self.cluster.get_group(gid)
        if not g or g.get("category"):
            return
        cats = {}
        for m in g["members"]:
            c = self._guess_category_for_path(m)
            if c:
                cats[c] = cats.get(c, 0) + 1
        if cats:
            best = max(cats.items(), key=lambda kv: kv[1])[0]
            self.cluster.set_group_category(gid, best)

    # ---------------------------------------------------------------------
    # RENDERING — one tile per group (prime thumbnail / VACANT placeholder)
    # ---------------------------------------------------------------------
    def refresh(self):
        """Repaint the whole panel from the live cluster."""
        if not self.cluster:
            return
        self._populate_filter_categories()
        self.reload_groups()
        self._update_pin_status()
        self._update_drop_hint()
        self._update_group_filter_status()

    def _group_filter_changed(self, _text):
        """Live name-filter in the 'Find group' box → repaint the grid."""
        if self.view_mode == "grouped" and self.expanded_gid is None:
            self.reload_groups()
        self._update_group_filter_status()

    def _group_name_filter(self):
        term = self.group_search_edit.text().strip().lower()
        return term or None

    def _update_group_filter_status(self):
        """Report how many groups match the active name filter (if any)."""
        term = self._group_name_filter()
        if not term or not self.cluster:
            return
        total = len(self.cluster.all_groups())
        shown = len(self.items)
        self.count_label.setText(
            f"🔎 {shown} / {total} group(s) matching “"
            f"{self.group_search_edit.text().strip()}”   |   clear the box "
            "(or press ←) to show all")

    def group_items_from_cluster(self):
        """One tile dict per visible group, honouring the category filter.
        ``path`` is the group's PRIME — the tile literally shows the prime
        image as the group's picture."""
        out = []
        if not self.cluster:
            return out
        flt = self._current_filter()
        nflt = self._group_name_filter()      # live "Find group" text
        if flt:
            for g in self.cluster.all_groups():
                if not g.get("category"):
                    self._ensure_group_category(g["id"])
        for g in sorted(self.cluster.all_groups(), key=lambda x: x["name"].lower()):
            if nflt and nflt not in g["name"].lower():
                continue                      # filtered out by name search
            gcat = g.get("category")
            if flt and gcat != flt:
                # An EMPTY untagged group belongs to whatever filter was
                # active while you're working in it — adopt the filter now
                # so it doesn't vanish under your cursor mid-session.
                # A POPULATED untagged group whose provenance can't be
                # inferred stays visible under every filter.
                if gcat is None and not g["members"]:
                    self.cluster.set_group_category(g["id"], flt)
                else:
                    continue
            out.append({"kind": "group", "gid": g["id"],
                        "path": g.get("prime") or "",
                        "vacant": not g["members"]})
        return out

    def _update_pin_status(self):
        if self.pinned_id and self.cluster and self.cluster.get_group(self.pinned_id):
            self.pin_status.setText(
                f"\U0001F4CC Pinned: {self.cluster.get_group_name(self.pinned_id)} — "
                "G+click in the Viewer adds to THIS group.")
            self.pin_status.setStyleSheet(
                "color:#4caf50;font-weight:bold;font-size:9pt;")
        else:
            self.pin_status.setText("No group pinned — Viewer is armed for NEW groups")
            self.pin_status.setStyleSheet(
                "color:#7f8289;font-style:italic;font-size:9pt;")

    def _update_drop_hint(self):
        """Paint the drag overlay text with the group a drop will land in."""
        if self.expanded_gid is not None and self.cluster:
            g = self.cluster.get_group(self.expanded_gid)
            if g:
                self.list_widget.drop_hint = (
                    f"\u2b07 Drop images here — they join \u201c{g['name']}\u201d")
                self.list_widget._hint_color = "#4caf50"
                return
        self.list_widget.drop_hint = ("\u2b07 Drop images ONTO a group tile to add "
                                      "them to that group")
        self.list_widget._hint_color = "#29b6f6"

    # ---- override: ← also collapses an expanded group ---------------------
    def _back_clicked(self):
        if self.expanded_gid is not None:
            self.collapse_group()
            self._update_pin_status()
            self._update_drop_hint()
            return
        if self.group_search_edit.text():
            # ← while a name-filter is active clears it (restore full grid)
            self.group_search_edit.clear()
            return
        super()._back_clicked()

    def keyPressEvent(self, e):
        # Esc anywhere in the Groups panel drops the "Find group" filter.
        if e.key() == Qt.Key_Escape and self.group_search_edit.text():
            self.group_search_edit.clear()
            e.accept()
            return
        super().keyPressEvent(e)

    # ---- 📌 pin button ------------------------------------------------------
    def set_highlighted(self, key):
        """Track the highlighted cell; enable 📌 only when a GROUP tile is
        under the highlight (in the groups grid)."""
        super().set_highlighted(key)
        gid = None
        if key is not None:
            item = self._item_by_key(key)
            if item is not None and item.get("kind") == "group":
                gid = item.get("gid")
        self._hl_gid = gid
        pb = getattr(self, "pin_btn", None)
        if pb is not None:
            pb.setEnabled(gid is not None)
        self.restyle()

    def _pin_clicked(self):
        """📌 toolbar button: pin/unpin the currently highlighted group."""
        gid = self._hl_gid
        if gid is None or not self.cluster or not self.cluster.get_group(gid):
            return                      # nothing highlighted — no-op
        self._toggle_pin(gid)

    # ---- drag & drop onto tiles --------------------------------------------
    def _on_tile_dropped(self, paths, gid):
        """Images dropped onto a GROUP TILE → that group.  Dropped on empty
        space (no tile under the cursor) → the OPEN/viewed group, creating a
        fresh one when nothing is active.  Forwarded via images_dropped to
        the Viewer, which performs the actual membership + collapsing."""
        if not self.cluster or not paths:
            return
        target = gid
        if target is None:
            target = self.open_gid or self.viewed_id
            if target and not self.cluster.get_group(target):
                target = None
        if target is None:
            target = self.cluster.create_group()
            self.open_gid = target
            self.viewed_id = target
        g = self.cluster.get_group(target)
        if g and not g.get("category") and self.category_filter:
            self.cluster.set_group_category(target, self.category_filter)
        # Immediate feedback that the drop landed (the gallery repaints via
        # the data_changed round-trip; detached windows may not be listening).
        top = self.window()
        sb = top.statusBar() if hasattr(top, "statusBar") else None
        if sb is not None:
            names = [os.path.basename(p) for p in paths[:3]]
            suffix = "…" if len(paths) > 3 else ""
            sb.showMessage(
                f"\u2b07 Added {len(paths)} image(s) to "
                f"\u201c{g['name'] if g else '?'}\u201d: "
                f"{', '.join(names)}{suffix}", 5000)
        self.viewer_dropped.emit(paths, target)

    viewer_dropped = pyqtSignal(list, object)   # (paths, target_gid)

    # ---- finder bar: outsource images into a group by pasting paths -------
    @staticmethod
    def _parse_pasted_paths(raw):
        """Split a pasted blob into individual file paths.

        Accepts ';' / newline separated lists and strips surrounding quotes
        (Explorer's copy-as-path wraps each entry in double quotes).  A
        quoted segment may itself contain ';', so we walk the string with a
        in-quotes flag instead of doing a blind split.
        """
        if not raw:
            return []
        segments, buf, in_q = [], [], False
        for ch in raw:
            if ch == '"':
                in_q = not in_q
                continue
            if (ch in ";\n\r") and not in_q:
                segments.append("".join(buf))
                buf = []
            else:
                buf.append(ch)
        segments.append("".join(buf))
        out = []
        for s in segments:
            s = s.strip().strip('"').strip("'").strip()
            if s and s not in out:
                out.append(s)
        return out

    def _import_target_gid(self):
        """Group the pasted paths should land in — the same priority the
        drop hint advertises: expanded view > pinned > open/viewed."""
        if not self.cluster:
            return None
        for cand in (self.expanded_gid, self.pinned_id, self.open_gid,
                     self.viewed_id):
            if cand is not None and self.cluster.get_group(cand):
                return cand
        return None

    def _flash_import_status(self, text, color="#29b6f6"):
        """Show a transient message in the group-status line without
        disturbing the normal expanded/grid status text."""
        lbl = getattr(self, "group_status", None)
        if lbl is None:
            return
        base = getattr(self, "_import_status_restore", None)
        if base is None:
            base = lbl.text()
            self._import_status_restore = base
        lbl.setText(text)
        lbl.setStyleSheet(f"color:{color};font-size:9pt;font-weight:600;")
        from PyQt5.QtCore import QTimer
        QTimer.singleShot(5000, lambda: (
            lbl.setText(base),
            lbl.setStyleSheet("color:#29b6f6;font-size:9pt;font-weight:600;"
                              if self.expanded_gid is not None
                              else "color:#7f8289;font-size:9pt;")))

    def _import_from_bar(self):
        """⤵ Add / Enter in the finder bar: outsource image(s) into the
        group currently being viewed by pasting their path(s)."""
        raw = self.import_edit.text().strip()
        if not raw or not self.cluster:
            return
        gid = self._import_target_gid()
        if gid is None:
            self._flash_import_status(
                "⚠ Open or expand a group first — pasted images need a "
                "target group.", "#ff9800")
            return
        g = self.cluster.get_group(gid)
        paths = self._parse_pasted_paths(raw)
        valid, missing = [], []
        for p in paths:
            (valid if os.path.isfile(p) else missing).append(p)
        if not valid:
            self._flash_import_status(
                f"✕ No file found at '{os.path.basename(paths[0])}' — "
                "check the pasted path.", "#ef5350")
            return
        # Route through the Viewer so membership, category checks, collapse
        # reconciliation and gallery refresh all happen exactly as for a
        # drag & drop.
        self.viewer_dropped.emit(valid, gid)
        added = [p for p in valid if p in (g.get("members") or [])]
        n_new = len(added)
        msg = (f"⤵ {len(valid)} path(s) sent to “{g['name']}”."
               + (f" ✕ {len(missing)} missing." if missing else ""))
        self._flash_import_status(msg, "#4caf50" if n_new else "#29b6f6")
        self.import_edit.clear()

    def set_open_group(self, gid):
        """Called by the viewer when a staged (auto-created) group opens."""
        self.open_gid = gid
        if gid:
            self.viewed_id = gid
        self.refresh()

    def focus_group(self, gid):
        self.viewed_id = gid
        self.refresh()

    def external_unpin(self):
        if self.pinned_id is not None:
            self.pinned_id = None
            self._update_pin_status()
            self.restyle()

    # ---------------------------------------------------------------------
    def _new_empty_group(self):
        """Instant, auto-named group — no prompts. It appears as a VACANT
        tile immediately; the very next drop onto it lands inside.  Tagged
        with the currently active category; left untagged (visible under
        every filter) when no category is active."""
        if not self.cluster:
            return
        gid = self.cluster.create_group()   # auto-named "Group N"
        if self.category_filter:
            self.cluster.set_group_category(gid, self.category_filter)
        self.open_gid = gid
        self.viewed_id = gid
        self.refresh()
        self.data_changed.emit(gid)

    # ------------------------------------------------------------------
    # CONTEXT MENUS
    # ------------------------------------------------------------------
    def _group_menu(self, gid, pos):
        """Right-click on a GROUP tile."""
        if self._rc_preview_shown:
            # release of a right-click hold that popped the enlarged
            # preview — don't open a menu on top of it
            self._rc_preview_shown = False
            self.hide_enlarged()
            return
        if not self.cluster:
            return
        g = self.cluster.get_group(gid)
        if not g:
            return
        m = QMenu(self)
        m.addAction("\U0001F50D Expand group — show all members").triggered.connect(
            lambda: self.expand_group(gid))
        m.addSeparator()
        if self.pinned_id == gid:
            m.addAction("\U0001F4CC Unpin group").triggered.connect(
                lambda: self._toggle_pin(gid))
        else:
            m.addAction("\U0001F4CC Pin group (G+click feeds it)").triggered.connect(
                lambda: self._toggle_pin(gid))
        m.addAction("\u270f\ufe0f Rename group").triggered.connect(
            lambda: self._rename(gid))
        if g["prime"]:
            m.addAction("\u2606 Clear prime").triggered.connect(
                lambda: self._clear_prime(gid))
        m.addSeparator()
        m.addAction("\U0001F5D1 Delete group").triggered.connect(
            lambda: self._delete(gid))
        m.exec_(self.list_widget.mapToGlobal(pos))

    def _toggle_pin(self, gid):
        if self.pinned_id == gid:
            self.pinned_id = None
            self.set_group_context(self.staged_group_id, None)
            self.pin_toggled.emit(None)
        else:
            self.pinned_id = gid
            self.viewed_id = gid
            self.set_group_context(self.staged_group_id, gid)
            self.pin_toggled.emit(gid)
        self._update_pin_status()
        self.restyle()

    def _rename(self, gid):
        g = self.cluster.get_group(gid)
        name, ok = QInputDialog.getText(self, "Rename Group", "New name:", text=g["name"])
        if ok and name.strip():
            self._apply_unique_name(gid, name.strip())
            self.refresh()
            self.data_changed.emit(gid)

    def _apply_unique_name(self, gid, base):
        """Give group ``gid`` the name ``base``, appending ' (1)', ' (2)' …
        when another group already carries it — the same intelligent
        de-duplication the Shift+R clipboard rename uses."""
        taken = {g["name"].lower() for g in self.cluster.all_groups()
                 if g["id"] != gid}
        name = base
        n = 1
        while name.lower() in taken:
            name = f"{base} ({n})"
            n += 1
        self.cluster.rename_group(gid, name)

    def _clear_prime(self, gid):
        self.cluster.clear_prime(gid)
        self.refresh()
        self.data_changed.emit(gid)

    def _delete(self, gid):
        g = self.cluster.get_group(gid)
        if QMessageBox.question(
                self, "Delete Group",
                f"Delete \u201c{g['name']}\u201d ({len(g['members'])} members)?\n"
                f"Images themselves are untouched — only the grouping is removed.",
                QMessageBox.Yes | QMessageBox.No) != QMessageBox.Yes:
            return
        if self.pinned_id == gid:
            self.pinned_id = None
            self.pin_toggled.emit(None)
        if self.viewed_id == gid:
            self.viewed_id = None
        if self.open_gid == gid:
            self.open_gid = None
        self.cluster.delete_group(gid)
        self.refresh()
        # gid is gone — pass None so the reconcile does a global sweep of
        # any slots that referenced the deleted group.
        self.data_changed.emit(None)

    def _member_menu(self, data, pos):
        """Right-click on a MEMBER tile inside an expanded group."""
        if self._rc_preview_shown:
            # release of a right-click hold that popped the enlarged
            # preview — don't open "Make PRIME / Remove" on top of it
            self._rc_preview_shown = False
            self.hide_enlarged()
            return
        gid, path = data.get("gid"), data.get("path")
        if not gid or not path or not self.cluster:
            return
        g = self.cluster.get_group(gid)
        if not g:
            return
        m = QMenu(self)
        if not pc_ok(g.get("prime"), path):
            m.addAction("\u2605 Make this the PRIME").triggered.connect(
                lambda: self._set_prime(gid, path))
        else:
            m.addAction("\u2606 Clear prime").triggered.connect(
                lambda: self._clear_prime(gid))
        m.addAction("\u2715 Remove from group").triggered.connect(
            lambda: self._remove(gid, path))
        m.exec_(self.list_widget.mapToGlobal(pos))

    def _set_prime(self, gid, path):
        self.cluster.set_prime(gid, path, self.balancer)
        self.refresh()
        # Trigger reconciliation to swap the prime into the selected slot
        self.data_changed.emit(gid)

    def _remove(self, gid, path):
        # If this member still occupies a dataset slot whose VACANCY record
        # points back at it (it collapsed there when the group formed), ask
        # whether to restore it into that slot on the way out — otherwise
        # removing it from the group strands the image in the vacancy book-
        # keeping with no obvious way back.
        restore_target = None
        if self.balancer:
            try:
                profile = self.balancer.current_profile
                vac = (self.balancer.data.get("vacant_slots", {})
                       .get(profile, {}))
                c = canon_path(path)
                for cat, slots in vac.items():
                    for sidx, info in (slots or {}).items():
                        op = (info or {}).get("original_path")
                        if op and canon_path(op) == c:
                            restore_target = (cat, int(sidx), op)
                            break
                    if restore_target:
                        break
            except Exception:
                restore_target = None
        if restore_target is not None:
            answer = QMessageBox.question(
                self, "Remove from group",
                f"Remove '{os.path.basename(path)}' from the group and\n"
                f"restore it into its vacant slot #{restore_target[1]}?",
                QMessageBox.Yes | QMessageBox.No)
            if answer != QMessageBox.Yes:
                restore_target = None
        self.cluster.remove_member(gid, path)
        self.refresh()
        self.data_changed.emit(gid)
        if restore_target is not None:
            cat, sidx, op = restore_target
            viewer = getattr(self, "viewer_tab", None)
            if viewer is None:
                top = self.window()
                viewer = getattr(top, "viewer_tab", None)
            if viewer is not None and hasattr(viewer, "_restore_vacancy"):
                viewer._restore_vacancy({"index": sidx,
                                         "original_path": op,
                                         "category": cat})

    # ---- expand/collapse hooks (keep pin status + hint in sync) -----------
    def expand_group(self, gid):
        super().expand_group(gid)
        self.viewed_id = gid
        self._update_drop_hint()

    def collapse_group(self):
        super().collapse_group()
        self._update_drop_hint()



# =============================================================================
# Paths tab
# =============================================================================
class PathsTab(QWidget):
    paths_changed = pyqtSignal(str, str)

    def __init__(self, b="", r="", parent=None):
        super().__init__(parent)
        lay = QFormLayout(self)
        lay.setContentsMargins(20, 20, 20, 20)
        lay.setSpacing(15)

        self.balancer_edit = QLineEdit(b)
        self.balancer_edit.setPlaceholderText("Path to balancer_data.json")
        bb = QPushButton("Browse...")
        bb.clicked.connect(lambda: self._browse(self.balancer_edit))
        h1 = QHBoxLayout()
        h1.addWidget(self.balancer_edit)
        h1.addWidget(bb)
        lay.addRow("Balancer Data File:", h1)

        self.rater_edit = QLineEdit(r)
        self.rater_edit.setPlaceholderText("Path to image_ratings.json")
        rb = QPushButton("Browse...")
        rb.clicked.connect(lambda: self._browse(self.rater_edit))
        h2 = QHBoxLayout()
        h2.addWidget(self.rater_edit)
        h2.addWidget(rb)
        lay.addRow("Rater Data File:", h2)

        lay.addRow(QLabel(""))
        info = QLabel(
            "Loading runs in the background. Swaps auto-save into the balancer "
            "JSON (with a one-time .bak) and are logged to swap_log.json.\n\n"
            "Cluster groups live in cluster_groups.json in the same folder. "
            "Hidden images and vacant slots are stored inside balancer_data.json."
        )
        info.setStyleSheet("color:#9a9da3;font-style:italic;")
        info.setWordWrap(True)
        lay.addRow(info)

        self.load_btn = QPushButton("Load Data")
        self.load_btn.setStyleSheet("background-color:#5865f2;font-weight:bold;")
        self.load_btn.clicked.connect(self._load)
        lay.addRow(self.load_btn)

        self.status_label = QLabel("")
        self.status_label.setStyleSheet("color:#f5c518;")
        lay.addRow(self.status_label)

    def _browse(self, edit):
        p, _ = QFileDialog.getOpenFileName(self, "Select JSON File", "", "JSON Files (*.json)")
        if p:
            edit.setText(p)

    def _load(self):
        b = self.balancer_edit.text().strip()
        r = self.rater_edit.text().strip()
        if not b or not r:
            self.status_label.setText("Please set both paths first.")
            return
        if not os.path.exists(b):
            self.status_label.setText(f"Balancer file not found: {b}")
            return
        if not os.path.exists(r):
            self.status_label.setText(f"Rater file not found: {r}")
            return
        self.status_label.setText("Loading data in background...")
        self.paths_changed.emit(b, r)


# =============================================================================
# Main viewer tab
# =============================================================================
class MainViewerTab(QWidget):
    groups_dirty = pyqtSignal()
    request_unpin = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.balancer = None
        self.rater = None
        self.cluster = None
        self.swap_log_path = None

        self.current_category = None
        self.pending = None
        self.undo_stack = []
        self.show_hidden = False

        # ---- GROUP ARM STATE ------------------------------------------
        # staged_group_id: the auto-created group currently being built.
        #                  None == "armed for a brand-new group".
        # pinned_group_id: a group pinned from the Groups tab; overrides
        #                  staging while set.
        self.staged_group_id = None
        self.pinned_group_id = None

        self.directory_history_path = None
        self.directory_history = []
        self.current_directory_filter = None

        lay = QVBoxLayout(self)
        lay.setContentsMargins(10, 10, 10, 10)
        lay.setSpacing(8)

        # top row ---------------------------------------------------------
        top = QHBoxLayout()
        self.profile_combo = QComboBox()
        self.profile_combo.setMinimumWidth(170)
        self.profile_combo.currentTextChanged.connect(self.on_profile_changed)
        top.addWidget(QLabel("Profile:"))
        top.addWidget(self.profile_combo)

        self.category_combo = QComboBox()
        self.category_combo.setMinimumWidth(170)
        self.category_combo.currentTextChanged.connect(self.on_category_changed)
        top.addWidget(QLabel("Category:"))
        top.addWidget(self.category_combo)

        top.addStretch()

        self.show_hidden_cb = QCheckBox("Show Hidden Images")
        self.show_hidden_cb.stateChanged.connect(self._toggle_hidden)
        top.addWidget(self.show_hidden_cb)

        self.hidden_count = QLabel("(0 hidden)")
        self.hidden_count.setStyleSheet("color:#9a9da3;font-size:9px;")
        top.addWidget(self.hidden_count)

        self.unhide_all_btn = QPushButton("Unhide All")
        self.unhide_all_btn.clicked.connect(self._unhide_all)
        top.addWidget(self.unhide_all_btn)

        self.cancel_btn = QPushButton("✕ Cancel Selection")
        self.cancel_btn.clicked.connect(self.cancel_pending)
        top.addWidget(self.cancel_btn)

        self.undo_btn = QPushButton("↶ Undo Last Swap")
        self.undo_btn.setEnabled(False)
        self.undo_btn.clicked.connect(self.undo_last_swap)
        top.addWidget(self.undo_btn)

        # ---- vacant-slot injector --------------------------------------
        # Type a name (or leave it blank), pick how many, hit Inject and
        # that many VACANT slots are inserted at the very start of the
        # current category — page 1 of the Selected Images gallery.
        self.vacant_name_edit = QLineEdit()
        self.vacant_name_edit.setPlaceholderText("Vacant slot label (optional)")
        self.vacant_name_edit.setMinimumWidth(150)
        self.vacant_name_edit.returnPressed.connect(self.inject_vacant_slots)
        top.addWidget(QLabel("Inject Vacant:"))
        top.addWidget(self.vacant_name_edit)

        self.vacant_count_spin = QSpinBox()
        self.vacant_count_spin.setRange(1, 999)
        self.vacant_count_spin.setValue(1)
        self.vacant_count_spin.setToolTip("How many vacant slots to inject on page 1")
        top.addWidget(self.vacant_count_spin)

        self.inject_vacant_btn = QPushButton("⊕ Inject")
        self.inject_vacant_btn.setToolTip(
            "Insert vacant slot(s) at the front of the current category so "
            "they appear on page 1 of Selected Images.")
        self.inject_vacant_btn.clicked.connect(self.inject_vacant_slots)
        top.addWidget(self.inject_vacant_btn)

        # ---- add-all injector --------------------------------------------
        # One pass: every image currently visible in the All Rated Images
        # pool gets a brand-new VACANT slot at the front of the category —
        # but a GROUP counts as ONE image (one vacancy per group, never one
        # per member).  Ungrouped singles each get their own vacancy.
        self.add_all_btn = QPushButton("⊕⊕ Add all")
        self.add_all_btn.setToolTip(
            "Inject one vacant slot for EVERY image in the All Rated Images "
            "pool in a single pass.\n"
            "Groups collapse to a single vacancy (one slot per group, not "
            "per member); ungrouped images each get their own slot.\n"
            "The new slots appear at the front of the current category — "
            "page 1 of Selected Images.")
        self.add_all_btn.clicked.connect(self.add_all_vacant_slots)
        top.addWidget(self.add_all_btn)
        lay.addLayout(top)

        # directory filter --------------------------------------------------
        dir_box = QGroupBox("Rated Pool Source Directory (keeps different folders' ratings from mixing)")
        dl = QHBoxLayout(dir_box)
        self.directory_combo = QComboBox()
        self.directory_combo.setEditable(True)
        self.directory_combo.setInsertPolicy(QComboBox.NoInsert)
        self.directory_combo.setMinimumWidth(300)
        self.directory_combo.lineEdit().setPlaceholderText("Paste a folder path, pick from history, or Browse…")
        self.directory_combo.lineEdit().returnPressed.connect(self.on_directory_apply)
        self.directory_combo.activated[int].connect(self.on_directory_selected)
        dl.addWidget(self.directory_combo, 1)
        b1 = QPushButton("Browse…")
        b1.clicked.connect(self.on_browse_directory)
        dl.addWidget(b1)
        b2 = QPushButton("Apply Filter")
        b2.clicked.connect(self.on_directory_apply)
        dl.addWidget(b2)
        b3 = QPushButton("Show All")
        b3.clicked.connect(self.on_directory_clear)
        dl.addWidget(b3)
        lay.addWidget(dir_box)
        self._init_directory_combo()

        # prompt ------------------------------------------------------------
        self.prompt = QLabel("")
        self.prompt.setStyleSheet("color:#f5c518;font-weight:600;")
        lay.addWidget(self.prompt)

        # galleries ---------------------------------------------------------
        split = QSplitter(Qt.Horizontal)

        lbox = QGroupBox("Selected Images (profile) — click a slot, then click a rated image to replace it")
        li = QVBoxLayout(lbox)
        self.selected_gallery = PaginatedGallery(source_name="selected")
        li.addWidget(self.selected_gallery)
        self.selected_panel = DetachablePanel("Selected Images", lbox)
        split.addWidget(self.selected_panel)

        rbox = QGroupBox("All Rated Images (candidate pool)")
        ri = QVBoxLayout(rbox)
        self.rated_gallery = PaginatedGallery(source_name="rated")
        ri.addWidget(self.rated_gallery)
        self.rated_panel = DetachablePanel("All Rated Images", rbox)
        split.addWidget(self.rated_panel)

        split.setStretchFactor(0, 1)
        split.setStretchFactor(1, 1)
        lay.addWidget(split, 1)

        self.status = QLabel("Load data from the Paths tab to begin.")
        self.status.setStyleSheet("color:#9a9da3;font-style:italic;")
        lay.addWidget(self.status)

        # signals -----------------------------------------------------------
        for gal, src in ((self.selected_gallery, "selected"), (self.rated_gallery, "rated")):
            gal.image_clicked.connect(lambda it, s=src: self.on_image_clicked(s, it))
            gal.group_add_requested.connect(self.on_group_add)
            gal.group_prime_requested.connect(self.on_group_prime)
            gal.finish_group_requested.connect(self.finish_group)
            gal.page_changed.connect(lambda s=src: self._page_changed(s))
        self.rated_gallery.hide_requested.connect(self._hide_image)
        self.rated_gallery.unhide_requested.connect(self._unhide_image)
        self.selected_gallery.restore_vacancy_requested.connect(self._restore_vacancy)

        self._update_prompt()
        self._sync_group_context()

    # ---- panels ----------------------------------------------------------
    def all_detachable_panels(self):
        return [self.selected_panel, self.rated_panel]

    # ---- data ------------------------------------------------------------
    def set_data(self, balancer, rater, cluster, swap_log_path):
        self.balancer = balancer
        self.rater = rater
        self.cluster = cluster
        self.swap_log_path = swap_log_path
        self.undo_stack.clear()
        self.pending = None
        self.staged_group_id = None
        self.pinned_group_id = None
        self.undo_btn.setEnabled(False)

        self.selected_gallery.set_cluster(cluster)
        self.rated_gallery.set_cluster(cluster)

        self.profile_combo.blockSignals(True)
        self.profile_combo.clear()
        profiles = balancer.get_profile_names()
        self.profile_combo.addItems(profiles)
        if profiles:
            self.profile_combo.setCurrentIndex(
                profiles.index(balancer.current_profile)
                if balancer.current_profile in profiles else 0)
        self.profile_combo.blockSignals(False)

        self.category_combo.blockSignals(True)
        self.category_combo.clear()
        cats = balancer.get_categories_list()
        self.category_combo.addItems(cats)
        self.category_combo.blockSignals(False)

        self._sync_group_context()

        if cats:
            self.current_category = cats[0]
            self.refresh_selected_gallery()
            self.status.setText(f"Loaded {len(profiles)} profiles, {len(cats)} categories.")
        else:
            self.selected_gallery.clear()
            self.status.setText("No categories found in profile.")
        self.refresh_rated_gallery()

    def on_profile_changed(self, name):
        if not self.balancer or not name:
            return
        self.balancer.current_profile = name
        self.cancel_pending()
        cats = self.balancer.get_categories_list()
        self.category_combo.blockSignals(True)
        self.category_combo.clear()
        self.category_combo.addItems(cats)
        self.category_combo.blockSignals(False)
        self.current_category = cats[0] if cats else None
        self.refresh_selected_gallery()
        self.refresh_rated_gallery()

    def on_category_changed(self, cat):
        if not self.balancer or not cat:
            return
        self.current_category = cat
        self.cancel_pending()
        self.refresh_selected_gallery()
        n = len(self.balancer.get_dataset().get(cat, []))
        self.status.setText(f"Category '{cat}' — {n} slots.")

    # =====================================================================
    # GROUPING
    # =====================================================================
    def _sync_group_context(self):
        self.selected_gallery.set_group_context(self.staged_group_id, self.pinned_group_id)
        self.rated_gallery.set_group_context(self.staged_group_id, self.pinned_group_id)

    def set_pinned_group(self, gid):
        """Called when a group is pinned/unpinned from the Groups tab."""
        self.pinned_group_id = gid
        if gid:
            # Pinning takes over; stop staging (but keep whatever was staged).
            self.status.setText(
                f"📌 Pinned group '{self.cluster.get_group_name(gid)}'. "
                f"G+click now adds to this group.")
        else:
            self.status.setText("Unpinned. Armed for a brand-new group again.")
        self._sync_group_context()

    def _active_category(self):
        """The category currently selected in the Viewer's combo."""
        return self.current_category or self.category_combo.currentText() or None

    def _target_group(self, create_if_needed=True):
        """
        Resolve which group a G+click should feed.

        1. a group pinned in the Groups tab wins
        2. otherwise the currently staged auto-group
        3. otherwise auto-create a fresh one  <-- the default armed state
        """
        if self.pinned_group_id and self.cluster.get_group(self.pinned_group_id):
            return self.pinned_group_id
        if self.staged_group_id and self.cluster.get_group(self.staged_group_id):
            return self.staged_group_id
        if not create_if_needed:
            return None
        gid = self.cluster.create_group()
        self.staged_group_id = gid
        return gid

    def on_group_add(self, item):
        """hold G + left-click"""
        if not self.cluster:
            return
        path = item.get("path")
        if not path or item.get("vacant"):
            self.status.setText("Vacant slots can't be grouped.")
            return

        gid = self._target_group()
        g = self.cluster.get_group(gid)
        if g is None:
            return
        cat = self._active_category()
        if cat and not g["members"]:
            self.cluster.set_group_category(gid, cat)
        added = self.cluster.add_member(gid, path, category=cat)
        g = self.cluster.get_group(gid)

        if added:
            self.status.setText(
                f"➜ '{os.path.basename(path)}' added to {g['name']} "
                f"({len(g['members'])} images). ➕ when done.")
        else:
            self.status.setText(
                f"'{os.path.basename(path)}' is already in {g['name']}.")

        # instant visual feedback, no page reload / no flicker
        self._sync_group_context()
        # a newly grouped pair that are both already in the dataset must
        # collapse — only the group that just changed needs re-checking.
        self._reconcile_collapses(log=True, only_group_id=gid)
        self.refresh_selected_gallery(preserve_page=True)
        self.groups_dirty.emit()

    def on_dropped_images(self, paths, target_gid):
        """Native drag & drop from any gallery (incl. detached windows).

        ``target_gid`` is the group row the cursor was over, or None when
        the drop landed on empty space / the members area — in that case
        it goes to the open (staged/pinned) group, creating one if needed.
        """
        if not self.cluster:
            return
        paths = [p for p in paths if p]
        if not paths:
            return
        gid = target_gid or self._target_group()
        g = self.cluster.get_group(gid)
        if g is None:
            return
        cat = self._active_category()
        # A POPULATED existing group keeps its own category — dropping images
        # onto it must never re-tag it (that used to invalidate groups that
        # were filtered into view).  Only an empty / freshly created group
        # adopts the currently active category.
        if cat and not g["members"]:
            self.cluster.set_group_category(gid, cat)
        gcat = self.cluster.group_category(gid) or cat
        added_names = []
        for p in paths:
            # a group can only hold images from ONE category — the active one.
            if gcat and not self.cluster.member_fits(gid, p, gcat):
                continue
            if self.cluster.add_member(gid, p, category=gcat):
                added_names.append(os.path.basename(p))
        skipped = len(paths) - len(added_names)
        if added_names:
            msg = (f"⬇ {len(added_names)} image(s) dropped into {g['name']} "
                   f"({len(g['members'])} total). Double-click one to make it "
                   f"the PRIME.")
            if skipped:
                msg += (f"  ⚠ {skipped} skipped — '{cat}' only; switch category "
                        f"in the Viewer or start a new group.")
            self.status.setText(msg)
        elif skipped:
            self.status.setText(
                f"Nothing added: those images don't belong to category "
                f"'{cat}'. Switch the category in the Viewer first.")
        else:
            self.status.setText(f"Those images are already in {g['name']}.")
        self._sync_group_context()
        self._reconcile_collapses(log=True, only_group_id=gid)
        self.refresh_selected_gallery(preserve_page=True)
        self.groups_dirty.emit()

    def _style_for_grouping(self, item):
        """Return STYLE_SELECTED_FOR_GROUPING for items being selected via shift+G+click."""
        # This style uses pink border (#e91e63) to indicate "selected for grouping"
        return STYLE_SELECTED_FOR_GROUPING

    def on_group_prime(self, item):
        """hold G + left-double-click  ->  master image"""
        if not self.cluster:
            return
        path = item.get("path")
        if not path or item.get("vacant"):
            return

        gid = self._target_group(create_if_needed=False)
        if gid is None:
            # Not staging/pinned: if the image already belongs to a group,
            # prime it there; otherwise start a fresh group with it.
            gid = self.cluster.primary_group_for_path(path)
            if gid is None:
                gid = self._target_group(create_if_needed=True)

        self.cluster.set_prime(gid, path, self.balancer)
        g = self.cluster.get_group(gid)
        self.status.setText(
            f"★ '{os.path.basename(path)}' is now the PRIME of {g['name']}. "
            f"{max(0, len(g['members']) - 1)} child image(s) hidden.")

        self._sync_group_context()
        # only THIS group's slots can be affected by the prime change —
        # a targeted scan also picks up stale transplanted children that
        # must vacate in favour of the new prime
        self._reconcile_collapses(log=True, only_group_id=gid)
        self.refresh_selected_gallery(preserve_page=True)
        self.refresh_rated_gallery(preserve_page=True)
        self.groups_dirty.emit()

    def finish_group(self):
        """The ➕ button on either panel."""
        if not self.cluster:
            return

        if self.pinned_group_id:
            name = self.cluster.get_group_name(self.pinned_group_id)
            self.pinned_group_id = None
            self.request_unpin.emit()
            self.status.setText(f"Unpinned '{name}'. Armed for a brand-new group.")
        elif self.staged_group_id:
            g = self.cluster.get_group(self.staged_group_id)
            if g and len(g["members"]) == 0:
                self.cluster.delete_group(self.staged_group_id)
                self.status.setText("Empty group discarded. Armed for a brand-new group.")
            elif g:
                self.status.setText(
                    f"✔ '{g['name']}' committed with {len(g['members'])} image(s)"
                    f"{' — prime: ' + os.path.basename(g['prime']) if g['prime'] else ' — no prime set'}."
                    f"  Armed for a brand-new group.")
            self.staged_group_id = None
        else:
            self.status.setText("Already armed for a brand-new group — hold G and click.")

        self._sync_group_context()
        self.refresh_selected_gallery(preserve_page=True)
        self.refresh_rated_gallery(preserve_page=True)
        self.groups_dirty.emit()

    # =====================================================================
    # SLOT COLLAPSING
    # =====================================================================
    def _find_member_slot(self, path):
        """Locate the dataset slot (category, index) that currently holds
        ``path``, comparing in CANONICAL form.

        Group membership is stored canonically while dataset slots keep the
        spelling the path had when it was placed (drag & drop via Qt yields
        forward slashes, e.g.).  A raw string comparison used to miss those
        spellings, so dropping an already-selected image into a group did NOT
        collapse its slot — the tile stayed visible instead of becoming
        VACANT.
        """
        if not self.balancer or not path:
            return None
        c = canon_path(path)
        if not c:
            return None
        dataset = self.balancer.get_dataset(self.balancer.current_profile)
        for cat, paths in dataset.items():
            for i, p in enumerate(paths):
                if p and canon_path(p) == c:
                    return (cat, i)
        return None

    def _exclusion_matches(self, profile, path):
        """Return the stored exclusion entry whose canonical form equals
        ``path`` (or None).  Exclusions may hold a different spelling than
        the canonical member path."""
        c = canon_path(path)
        for x in self.balancer.data.get("rated_pool_exclusions", {}).get(profile, []):
            if canon_path(x) == c:
                return x
        return None

    def _reconcile_collapses(self, log=False, only_group_id=None):
        """
        Enforce the PRIME rule on dataset slots: for every group, ONLY the
        prime may occupy a slot.  Any other member that currently sits in
        the Selected Images gets transplanted INTO the prime's slot (the
        prime tile swaps in place — it never moves to another position),
        and the child's old slot becomes VACANT with an undo record.

        * A newly grouped pair that are both already in the dataset
          collapses immediately: the non-prime's slot goes VACANT.
        * Changing the prime re-runs this scan for that group, so the new
          prime takes over the occupied slot and the OLD prime (now a
          child) is vacated — the selected page can no longer keep showing
          a stale transplanted child after the prime changes.
        * With no prime chosen yet, the earliest slot wins so nothing is
          lost arbitrarily; choosing a prime later moves the survivor
          accordingly.

        Comparisons happen in CANONICAL form so differently-spelled dataset
        values still collapse correctly.  ``only_group_id`` restricts the
        scan to the group that actually changed (drop / G+click / prime)
        instead of re-checking every unrelated group on every action.
        """
        if not (self.balancer and self.cluster):
            return []
        profile = self.balancer.current_profile
        dataset = self.balancer.get_dataset(profile)

        # one pass over the dataset -> canon(member path) -> [(cat, idx, raw)]
        slot_of = {}
        for cat, paths in dataset.items():
            for i, p in enumerate(paths):
                if p:
                    slot_of.setdefault(canon_path(p), []).append((cat, i, p))

        groups = ([self.cluster.get_group(only_group_id)] if only_group_id
                  else self.cluster.all_groups())
        collapsed = []

        for g in groups:
            if not g or len(set(g["members"])) < 2:
                continue

            # every (category, index) currently holding a member of this group
            occupied = []
            for m in g["members"]:
                for slot in slot_of.get(canon_path(m), []):
                    occupied.append((slot[0], slot[1], m, slot[2]))
            pc = canon_path(g.get("prime")) if g.get("prime") else None
            if not occupied and pc:
                # prime set but nothing occupies any slot — nothing to do
                continue
            if len(occupied) < 2 and not (only_group_id is not None and pc
                                          and not any(canon_path(s[2]) == pc
                                                      for s in occupied)):
                # collapse needs >=2 occupants; a targeted scan additionally
                # transplants the prime into a single occupied child slot
                continue

            keeper = None
            if pc:
                for slot in occupied:
                    if canon_path(slot[2]) == pc:
                        keeper = slot
                        break
                if keeper is None and (only_group_id is not None or len(occupied) >= 2):
                    # The prime itself does not sit in any slot, but other
                    # members do: TRANSPLANT the prime into the first
                    # occupied slot (swap in place — the surviving tile
                    # keeps its position) and vacate the rest.  A lone
                    # occupant only triggers a transplant when we know
                    # exactly which group changed (a global pass could
                    # otherwise hijack slots of unrelated groups).
                    keeper_cat, keeper_idx, _, keeper_raw = occupied[0]
                    prime_disp = next((m for m in g["members"]
                                       if canon_path(m) == pc), pc)
                    dataset[keeper_cat][keeper_idx] = prime_disp
                    info = {
                        "original_path": keeper_raw,  # exact spelling that
                                                      # was in the slot —
                                                      # undo/restore put it
                                                      # back verbatim
                        "group_id": g["id"],
                        "collapsed_into": {"category": keeper_cat,
                                           "index": keeper_idx,
                                           "path": prime_disp},
                        "timestamp": datetime.now().isoformat(timespec="seconds"),
                    }
                    self.balancer.set_vacancy(profile, keeper_cat, keeper_idx, info)
                    self.balancer.remove_excluded_path(profile, keeper_raw)
                    self.balancer.add_excluded_path(profile, keeper_raw)
                    if canon_path(keeper_raw) != keeper_raw:
                        self.balancer.add_excluded_path(profile,
                                                        canon_path(keeper_raw))
                    collapsed.append({"profile": profile, "category": keeper_cat,
                                      "index": keeper_idx, **info})
                    occupied = occupied[1:]
                    keeper = (keeper_cat, keeper_idx, prime_disp, prime_disp)
            if keeper is None:
                keeper = occupied[0]

            for cat, idx, path, raw in occupied:
                if (cat, idx) == (keeper[0], keeper[1]):
                    continue
                dataset[cat][idx] = VACANT_TOKEN
                info = {
                    "original_path": raw,   # exact spelling that was in the
                                            # slot — undo/restore put it back
                                            # verbatim and clear its exclusion
                    "group_id": g["id"],
                    "collapsed_into": {"category": keeper[0], "index": keeper[1],
                                       "path": keeper[2]},
                    "timestamp": datetime.now().isoformat(timespec="seconds"),
                }
                self.balancer.set_vacancy(profile, cat, idx, info)
                # store the EXACT spelling that was in the slot so undo can
                # restore it verbatim; exclude under every spelling we know
                self.balancer.remove_excluded_path(profile, raw)
                self.balancer.add_excluded_path(profile, raw)
                if path != raw:
                    self.balancer.add_excluded_path(profile, path)
                collapsed.append({"profile": profile, "category": cat,
                                  "index": idx, **info})

        if collapsed:
            self.balancer.save()
            if log:
                for c in collapsed:
                    self._log("collapse", c)
                self.status.setText(
                    f"⧉ Collapsed {len(collapsed)} slot(s) — "
                    f"they are now VACANT but still in place.")
        return collapsed

    def _restore_vacancy(self, item):
        """Right-click a vacant slot -> put the original image back."""
        if not self.balancer:
            return
        profile = self.balancer.current_profile
        cat = self.current_category
        idx = item.get("index")
        orig = item.get("original_path")
        if not orig:
            return
        dataset = self.balancer.get_dataset(profile)
        lst = dataset.get(cat)
        if lst is None or not (0 <= idx < len(lst)):
            return
        lst[idx] = orig
        self.balancer.clear_vacancy(profile, cat, idx)
        # drop the exclusion under EVERY spelling we know for this file —
        # collapse stored both the raw slot value and the canonical member
        # path; a leftover entry would keep the restored image out of the
        # rated pool while its tile also shows in the selected gallery.
        self.balancer.remove_excluded_path(profile, orig)
        self.balancer.remove_excluded_path(profile, canon_path(orig))
        match = self._exclusion_matches(profile, orig)
        while match:
            self.balancer.remove_excluded_path(profile, match)
            match = self._exclusion_matches(profile, orig)
        self.balancer.save()
        self._log("restore_vacancy", {"profile": profile, "category": cat,
                                      "index": idx, "path": orig})
        self.refresh_selected_gallery(preserve_page=True)
        self.refresh_rated_gallery(preserve_page=True)
        self.status.setText(f"Restored '{os.path.basename(orig)}' into slot #{idx}.")

    # =====================================================================
    # INJECT VACANT SLOTS (page 1)
    # =====================================================================
    def _inject_vacancies(self, count, labels=None):
        """Shared engine for Inject / Add all.

        Creates ``count`` brand-new VACANT slots at the very front of the
        current category's dataset list (so they land on page 1) and shifts
        every existing vacancy record right by ``count`` so collapsed-slot
        anchors stay truthful.

        ``labels`` — optional list of per-slot label strings (e.g. group
        names); missing entries fall back to the toolbar text box value.
        Returns True when the data saved cleanly.
        """
        profile = self.balancer.current_profile
        cat = self.current_category
        fallback_name = self.vacant_name_edit.text().strip()

        dataset = self.balancer.get_dataset(profile)
        lst = dataset.setdefault(cat, [])

        # every existing slot index shifts right by `count` — move its
        # vacancy record along so collapsed-slot anchors stay truthful
        old_vacs = dict(self.balancer._vac_cat(profile, cat))
        for k in old_vacs:
            self.balancer.clear_vacancy(profile, cat, int(k))
        for k, info in old_vacs.items():
            new_idx = int(k) + count
            info["slot_anchor"] = new_idx
            ci = info.get("collapsed_into")
            if isinstance(ci, dict) and ci.get("category") == cat \
                    and isinstance(ci.get("index"), int):
                ci["index"] += count
            self.balancer.set_vacancy(profile, cat, new_idx, info)

        # prepend the fresh vacancies to the dataset list itself
        lst[:0] = [VACANT_TOKEN] * count
        ts = datetime.now().isoformat(timespec="seconds")
        for i in range(count):
            name = ""
            if labels is not None and i < len(labels):
                name = labels[i] or ""
            if not name:
                name = fallback_name
            self.balancer.set_vacancy(profile, cat, i, {
                "original_path": None,      # nothing to restore — pure vacancy
                "injected": True,
                "name": name,
                "group_id": None,
                "collapsed_into": None,
                "slot_anchor": i,
                "timestamp": ts,
            })

        saved = self.balancer.save()
        self._log("inject_vacant", {"profile": profile, "category": cat,
                                    "count": count})

        # page 1 must actually SHOW the new slots: rebuild without keeping
        # the current page, then force the view back to page 1
        self.cancel_pending()
        self.refresh_selected_gallery(preserve_page=False)
        self.selected_gallery.jump_to_page(1)
        self.refresh_rated_gallery(preserve_page=True)
        return saved

    def inject_vacant_slots(self):
        """Toolbar action: create N brand-new VACANT slots at the very front
        of the current category's dataset list, so they land on PAGE 1 of the
        Selected Images gallery.

        * Text box  -> optional label stored with each vacancy ("name"),
                       shown on the tile's tooltip.
        * Spin box  -> how many vacant slots to inject.
        Vacancies created this way have no original image behind them, so
        right-click "restore" is a no-op for them — fill them by clicking
        the slot and then clicking a rated image, exactly like any other
        vacant slot.
        """
        if not (self.balancer and self.rater and self.current_category):
            QMessageBox.information(self, "No data loaded",
                                    "Load balancer + rater data first.")
            return
        cat = self.current_category
        try:
            count = int(self.vacant_count_spin.value())
        except Exception:
            count = 1
        if count < 1:
            count = 1
        name = self.vacant_name_edit.text().strip()

        saved = self._inject_vacancies(count)

        label = f" '{name}'" if name else ""
        note = "saved" if saved else "SAVE FAILED — check console"
        self.status.setText(
            f"⊕ Injected {count} vacant slot(s){label} at the front of "
            f"'{cat}' — visible on page 1 ({note}).")

    def add_all_vacant_slots(self):
        """'Add all': one-pass evolution of Inject.

        Walks the CURRENT contents of the All Rated Images pool (the same
        filtered/hidden-aware list the user sees) and injects one VACANT
        slot per candidate — BUT a burst-shoot GROUP always counts as ONE
        candidate no matter how many members it has (5-6 member groups get
        a single vacancy).  Ungrouped individual images each get their own
        vacancy.  Group membership is read from the cluster manager, never
        guessed from filenames.

        Each new slot carries the group's name (or the image's filename for
        ungrouped singles) as its vacancy label so the page-1 tiles are
        identifiable at a glance.
        """
        if not (self.balancer and self.rater and self.current_category):
            QMessageBox.information(self, "No data loaded",
                                    "Load balancer + rater data first.")
            return

        # Build the candidate list exactly like refresh_rated_gallery does,
        # so hidden/excluded/used images and the directory filter are all
        # honoured — "all" means "everything currently visible in the pool".
        profile = self.balancer.current_profile
        used = self.balancer.get_used_paths(profile)
        excluded = self.balancer.get_excluded_paths(profile)
        manual = self.balancer.get_hidden_paths(profile)
        cluster_hidden = (self.cluster.compute_hidden_paths(used)
                          if self.cluster else set())
        blocked_c = ({canon_path(p) for p in used}
                     | {canon_path(p) for p in excluded}
                     | set(cluster_hidden))
        manual_c = {canon_path(p) for p in manual}
        rated = self.rater.get_all_rated_images(1, self.current_directory_filter)

        candidates = []          # ordered [(label, ...)] — one entry per vacancy
        seen_groups = set()      # gids already granted a vacancy
        for p, _pr, _sec in rated:
            c = canon_path(p)
            if c in blocked_c or c in manual_c:
                continue         # not visible in the pool → no vacancy
            gids = self.cluster.groups_for_path(p) if self.cluster else []
            if gids:
                gid = gids[0]
                if gid in seen_groups:
                    continue     # this group already got its one slot
                seen_groups.add(gid)
                label = self.cluster.get_group_name(gid)
            else:
                label = os.path.splitext(os.path.basename(p))[0]
            candidates.append(label)

        if not candidates:
            self.status.setText("Add all: the All Rated Images pool is empty "
                                "— nothing to inject.")
            return

        n_groups = len(seen_groups)
        n_singles = len(candidates) - n_groups
        saved = self._inject_vacancies(len(candidates), labels=candidates)

        note = "saved" if saved else "SAVE FAILED — check console"
        self.status.setText(
            f"⊕⊕ Added all: injected {len(candidates)} vacant slot(s) "
            f"({n_groups} group slot(s) + {n_singles} ungrouped) at the "
            f"front of '{self.current_category}' — visible on page 1 ({note}).")

    # =====================================================================
    # HIDE / UNHIDE
    # =====================================================================
    def _toggle_hidden(self, state):
        self.show_hidden = bool(state)
        self.refresh_rated_gallery(preserve_page=True)

    def _hide_image(self, item):
        if not self.balancer:
            return
        self.balancer.add_hidden_path(self.balancer.current_profile, item["path"])
        self.balancer.save()
        self.refresh_rated_gallery(preserve_page=True)
        self.status.setText(f"Hidden: {os.path.basename(item['path'])}")

    def _unhide_image(self, item):
        if not self.balancer:
            return
        self.balancer.remove_hidden_path(self.balancer.current_profile, item["path"])
        self.balancer.save()
        self.refresh_rated_gallery(preserve_page=True)
        self.status.setText(f"Unhidden: {os.path.basename(item['path'])}")

    def _unhide_all(self):
        if not self.balancer:
            return
        n = len(self.balancer.get_hidden_paths())
        if n == 0:
            self.status.setText("Nothing is manually hidden.")
            return
        self.balancer.clear_hidden_paths()
        self.balancer.save()
        self.refresh_rated_gallery(preserve_page=True)
        self.status.setText(f"Unhid {n} image(s).")

    # =====================================================================
    # DIRECTORY FILTER
    # =====================================================================
    def set_directory_history_path(self, path):
        self.directory_history_path = path
        hist, last = load_directory_history(path)
        self.directory_history = hist
        self._init_directory_combo()
        if last:
            i = self.directory_combo.findData(last)
            if i >= 0:
                self.directory_combo.setCurrentIndex(i)
            else:
                self.directory_combo.setEditText(last)
            self.current_directory_filter = last
        else:
            self.directory_combo.setCurrentIndex(0)
            self.current_directory_filter = None

    def _init_directory_combo(self):
        self.directory_combo.blockSignals(True)
        self.directory_combo.clear()
        self.directory_combo.addItem(ALL_DIRECTORIES_LABEL, "")
        for d in self.directory_history:
            self.directory_combo.addItem(d, d)
        self.directory_combo.blockSignals(False)

    def on_directory_selected(self, i):
        self._apply_dir(self.directory_combo.itemData(i) or None)

    def on_directory_apply(self):
        t = self.directory_combo.currentText().strip()
        if not t or t == ALL_DIRECTORIES_LABEL:
            self._apply_dir(None)
            return
        if not os.path.isdir(t):
            QMessageBox.warning(self, "Invalid Directory", f"'{t}' is not an existing directory.")
            return
        self._apply_dir(os.path.normpath(t))

    def on_browse_directory(self):
        p = QFileDialog.getExistingDirectory(self, "Select Rated Images Source Directory",
                                             self.current_directory_filter or "")
        if p:
            p = os.path.normpath(p)
            self.directory_combo.setEditText(p)
            self._apply_dir(p)

    def on_directory_clear(self):
        self.directory_combo.setCurrentIndex(0)
        self._apply_dir(None)

    def _apply_dir(self, directory):
        self.current_directory_filter = directory
        if directory:
            if directory not in self.directory_history:
                self.directory_history.insert(0, directory)
                self.directory_history = self.directory_history[:MAX_DIRECTORY_HISTORY]
            self._init_directory_combo()
            i = self.directory_combo.findData(directory)
            if i >= 0:
                self.directory_combo.blockSignals(True)
                self.directory_combo.setCurrentIndex(i)
                self.directory_combo.blockSignals(False)
        save_directory_history(self.directory_history_path, self.directory_history, directory)
        self.cancel_pending()
        self.refresh_rated_gallery()
        self.status.setText(f"Rated pool filtered to: {directory}" if directory
                            else "Rated pool showing all directories (unfiltered).")

    # =====================================================================
    # REFRESH
    # =====================================================================
    def refresh_selected_gallery(self, preserve_page=False):
        if not (self.balancer and self.rater and self.current_category):
            self.selected_gallery.clear()
            return
        profile = self.balancer.current_profile
        cat = self.current_category
        paths = self.balancer.get_dataset(profile).get(cat, [])
        items = []
        for i, p in enumerate(paths):
            vac = self.balancer.get_vacancy(profile, cat, i)
            is_vacant = (not p) or (vac is not None and not p)
            items.append({
                "path": p or "",
                "slot_value": p,
                "primary": self.rater.get_rating(p) if p else 0,
                "secondary": self.rater.get_secondary_rating(p) if p else 0,
                "index": i,
                "vacant": is_vacant,
                "original_path": (vac or {}).get("original_path"),
                "vacancy_name": (vac or {}).get("name"),
            })
        self.selected_gallery.set_items(items, preserve_page=preserve_page)

    def refresh_rated_gallery(self, preserve_page=False):
        if not (self.rater and self.balancer):
            return
        profile = self.balancer.current_profile
        used = self.balancer.get_used_paths(profile)
        excluded = self.balancer.get_excluded_paths(profile)
        manual = self.balancer.get_hidden_paths(profile)
        cluster_hidden = self.cluster.compute_hidden_paths(used) if self.cluster else set()

        # Compare everything in CANONICAL form: group members are stored
        # normalised, while dataset/exclusion lists may hold legacy or
        # differently-spelled paths for the very same file.
        blocked_c = ({canon_path(p) for p in used}
                     | {canon_path(p) for p in excluded}
                     | set(cluster_hidden))
        manual_c = {canon_path(p) for p in manual}
        rated = self.rater.get_all_rated_images(1, self.current_directory_filter)

        items = []
        for p, pr, sec in rated:
            c = canon_path(p)
            if c in blocked_c:
                continue
            hidden = c in manual_c
            if hidden and not self.show_hidden:
                continue
            items.append({"path": p, "primary": pr, "secondary": sec,
                          "index": None, "vacant": False, "is_hidden": hidden})
        self.rated_gallery.set_items(items, preserve_page=preserve_page)
        self.hidden_count.setText(f"({len(manual)} hidden)")

    # =====================================================================
    # SWAP
    # =====================================================================
    def _gallery_for(self, source):
        return self.selected_gallery if source == "selected" else self.rated_gallery

    def _update_prompt(self):
        if self.pending is None:
            self.prompt.setText(
                "Click an image to select it, then click one in the other panel to swap.    "
                "│    Hold G + click = group    │    Hold G + double-click = set PRIME    "
                "│    ➕ = finish group    │    ➖ = hide highlighted image from rated pool")
        else:
            src = self.pending["source"]
            other = "rated" if src == "selected" else "selected"
            it = self.pending["item"]
            name = "VACANT slot #%s" % it["index"] if it.get("vacant") else os.path.basename(it["path"])
            self.prompt.setText(f"Pending: {name} ({src}). Click an image in the {other} "
                                f"panel to swap, or click it again to cancel.")

    def cancel_pending(self):
        if self.pending:
            self._gallery_for(self.pending["source"]).clear_pending()
        self.pending = None
        self._update_prompt()

    def _page_changed(self, source):
        if self.pending and self.pending["source"] == source:
            self.pending = None
            self._update_prompt()

    def on_image_clicked(self, source, item):
        if item is None:
            return
        # A vacant slot IS selectable (that's how you re-fill it), but only
        # from the selected panel.
        if item.get("vacant") and source != "selected":
            return

        key = (item["path"], item.get("index"))

        if self.pending is None:
            self.pending = {"source": source, "item": item}
            self._gallery_for(source).set_pending(*key)
            self._update_prompt()
            return

        p_src = self.pending["source"]
        p_item = self.pending["item"]
        p_key = (p_item["path"], p_item.get("index"))

        if p_src == source and p_key == key:
            # toggle-off of the pending selection — also drop the ➖
            # highlight on that cell so the button disables again
            self.cancel_pending()
            self._gallery_for(source).clear_highlight()
            return

        if p_src == source:
            self.pending = {"source": source, "item": item}
            self._gallery_for(source).set_pending(*key)
            self._update_prompt()
            return

        if p_src == "selected":
            sel_item, rated_item = p_item, item
        else:
            sel_item, rated_item = item, p_item

        self._gallery_for("selected").clear_pending()
        self._gallery_for("rated").clear_pending()
        self.pending = None
        self.perform_swap(sel_item, rated_item)
        self._update_prompt()

    def perform_swap(self, sel_item, rated_item):
        if not (self.balancer and self.current_category):
            return
        profile = self.balancer.current_profile
        cat = self.current_category
        idx = sel_item.get("index")
        old_value = sel_item.get("slot_value")
        new_path = rated_item["path"]

        dataset = self.balancer.get_dataset(profile)
        lst = dataset.get(cat)
        if lst is None or idx is None or not (0 <= idx < len(lst)) or lst[idx] != old_value:
            QMessageBox.warning(self, "Swap Failed",
                                "This slot no longer matches what's on screen. Swap aborted.")
            self.refresh_selected_gallery(preserve_page=True)
            return

        # If the outgoing selected image belongs to a group, remember which
        # one — after the swap _reconcile_collapses re-applies the PRIME
        # rule and would otherwise silently collapse (and exclude) the
        # incoming member into the prime's slot, losing it from Selected.
        pre_group_ids = []
        old_path = canon_path(old_value) if old_value else None
        if self.cluster and old_path:
            try:
                pre_group_ids = self.cluster.groups_for_path(old_path)
            except Exception:
                pre_group_ids = []
        was_vacant = sel_item.get("vacant", False)
        # If the slot we are swapping OUT currently holds a vacancy record
        # (its original image lives on inside a group), remember it so we
        # can re-vacate in favour of an incoming member if the PRIME rule
        # demands it after the swap.
        pre_vacancy = (self.balancer.get_vacancy(profile, cat, idx)
                       if idx is not None else None)
        lst[idx] = new_path

        if was_vacant:
            self.balancer.clear_vacancy(profile, cat, idx)
        if old_value:
            self.balancer.add_excluded_path(profile, old_value)
        self.balancer.add_excluded_path(profile, new_path)

        record = {
            "profile": profile, "category": cat, "index": idx,
            "old_path": old_value, "new_path": new_path,
            "was_vacant": was_vacant,
            "vacancy_info": self.balancer.get_vacancy(profile, cat, idx) if was_vacant else None,
        }
        # placing a group member may now collapse duplicate slots
        record["collapsed"] = self._reconcile_collapses()
        # ... and it may also make this very slot redundant: if the image
        # we just swapped IN is a non-prime member of a group whose prime
        # already occupies another slot, the PRIME rule requires this slot
        # to go VACANT again.  Without this the incoming member would be
        # silently excluded by the *next* reconcile (e.g. after removing
        # it from the group) — the image vanished from Selected for good.
        record["revacated"] = None
        if self.cluster and pre_vacancy:
            try:
                gids = [g for g in self.cluster.groups_for_path(new_path)
                        if g in pre_group_ids]
                for gid in gids:
                    g = self.cluster.get_group(gid) or {}
                    members = list(g.get("members", []))
                    pc = canon_path(g.get("prime")) if g.get("prime") else None
                    if len(members) < 2 or not pc:
                        continue
                    if pc == canon_path(new_path):
                        continue          # incoming IS the prime — keep it
                    others = [m for m in members
                              if canon_path(m) != pc
                              and canon_path(m) != canon_path(new_path)]
                    occupied_elsewhere = False
                    for om in others:
                        for c2, paths2 in dataset.items():
                            for j2, p2 in enumerate(paths2):
                                if p2 and canon_path(p2) == canon_path(om) \
                                        and not (c2 == cat and j2 == idx):
                                    occupied_elsewhere = True
                                    break
                            if occupied_elsewhere:
                                break
                        if occupied_elsewhere:
                            break
                    if not occupied_elsewhere:
                        continue
                    # The prime's group must keep exactly one occupant and
                    # that must be the prime elsewhere → vacate this slot
                    # back to its previous original.
                    orig = pre_vacancy.get("original_path") or old_value
                    lst[idx] = VACANT_TOKEN
                    self.balancer.set_vacancy(profile, cat, idx, pre_vacancy)
                    if orig:
                        self.balancer.remove_excluded_path(profile, orig)
                    self.balancer.add_excluded_path(profile, new_path)
                    record["revacated"] = {"original_path": orig}
                    break
            except Exception:
                pass

        self.undo_stack.append(record)
        self.undo_btn.setEnabled(True)
        self._log("swap", record)
        saved = self.balancer.save()

        self.refresh_selected_gallery(preserve_page=True)
        self.refresh_rated_gallery(preserve_page=True)

        note = "saved" if saved else "SAVE FAILED — check console"
        extra = ""
        if self.cluster:
            sibs = [m for gid in self.cluster.groups_for_path(new_path)
                    for m in self.cluster.get_group(gid)["members"] if m != new_path]
            if sibs:
                extra = f"  ({len(set(sibs))} sibling(s) removed from the pool)"
        if record["collapsed"]:
            extra += f"  ⧉ {len(record['collapsed'])} slot(s) collapsed to VACANT"
        self.status.setText(
            f"Swapped {os.path.basename(old_value) if old_value else '[vacant]'} → "
            f"{os.path.basename(new_path)} ({note}){extra}")

    def undo_last_swap(self):
        if not self.undo_stack:
            self.status.setText("Nothing to undo.")
            return
        rec = self.undo_stack.pop()
        self.undo_btn.setEnabled(bool(self.undo_stack))

        profile = rec["profile"]
        cat = rec["category"]
        idx = rec["index"]
        old_path = rec["old_path"]
        new_path = rec["new_path"]

        dataset = self.balancer.profiles.get(profile, {}).get("dataset", {})

        # undo collapses first
        for c in rec.get("collapsed", []):
            lst = dataset.get(c["category"])
            if lst is not None and 0 <= c["index"] < len(lst) and not lst[c["index"]]:
                lst[c["index"]] = c["original_path"]
            self.balancer.clear_vacancy(profile, c["category"], c["index"])
            self.balancer.remove_excluded_path(profile, c["original_path"])

        lst = dataset.get(cat)
        rev = rec.get("revacated") or {}
        # A "revacated" swap put the incoming member into a slot that then
        # had to go VACANT again (PRIME rule) — the slot was restored to
        # its previous original immediately, so undo must detect THAT
        # spelling too instead of only looking for new_path.
        expected = rev.get("original_path") or new_path
        if lst is not None and 0 <= idx < len(lst) and lst[idx] == expected \
                and (expected == new_path or not rev.get("skipped")):
            lst[idx] = old_path if old_path else VACANT_TOKEN
            if rec.get("was_vacant") and rec.get("vacancy_info"):
                self.balancer.set_vacancy(profile, cat, idx, rec["vacancy_info"])
        else:
            QMessageBox.warning(self, "Undo Warning",
                                "The dataset changed since this swap; the slot could not be "
                                "restored, but pool visibility has been reset.")

        if old_path:
            self.balancer.remove_excluded_path(profile, old_path)
        self.balancer.remove_excluded_path(profile, new_path)

        self._log("undo", rec)
        saved = self.balancer.save()

        if self.current_category == cat and self.balancer.current_profile == profile:
            self.refresh_selected_gallery(preserve_page=True)
        self.refresh_rated_gallery(preserve_page=True)
        self.status.setText(
            f"Undid swap: restored "
            f"{os.path.basename(old_path) if old_path else '[vacant]'} "
            f"({'saved' if saved else 'SAVE FAILED'})")

    def _log(self, action, record):
        if not self.swap_log_path:
            return
        entry = dict(record)
        entry["action"] = action
        entry["timestamp"] = datetime.now().isoformat(timespec="seconds")
        try:
            append_swap_log(self.swap_log_path, entry)
        except Exception as e:
            print(f"Error writing swap log: {e}")


# =============================================================================
# Main window
# =============================================================================
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Dataset Slot Replacer — Cluster Mapping")
        self.setMinimumSize(1280, 840)

        self.balancer = None
        self.rater = None
        self.cluster = None
        self._thread = None
        self._b_path = ""

        self.tabs = QTabWidget()
        self.setCentralWidget(self.tabs)

        b = os.path.abspath(BALANCER_DATA_FILE) if os.path.exists(BALANCER_DATA_FILE) else ""
        r = os.path.abspath(RATER_DATA_FILE) if os.path.exists(RATER_DATA_FILE) else ""

        self.paths_tab = PathsTab(b, r)
        self.paths_tab.paths_changed.connect(self.on_paths_changed)
        self.tabs.addTab(self.paths_tab, "⚙️  Paths")

        self.viewer_tab = MainViewerTab()
        self.viewer_tab.setEnabled(False)
        self.tabs.addTab(self.viewer_tab, "📁  Viewer")

        self.groups_tab = GroupsTab()
        self.groups_tab.setEnabled(False)
        self.tabs.addTab(self.groups_tab, "🔗  Groups")

        # cross-tab wiring
        self.groups_tab.pin_toggled.connect(self.viewer_tab.set_pinned_group)
        self.groups_tab.data_changed.connect(self._groups_edited)
        self.groups_tab.images_dropped.connect(self.viewer_tab.on_dropped_images)
        # finder-bar imports land in the group being viewed — same handler
        # as drag & drop, plus a direct refresh so the panel repaints even
        # when the expanded view isn't part of the data_changed round-trip.
        self.groups_tab.viewer_dropped.connect(self.viewer_tab.on_dropped_images)
        self.groups_tab.viewer_dropped.connect(self.groups_tab.refresh)
        self.groups_tab.close_group_requested.connect(self.viewer_tab.finish_group)
        self.viewer_tab.groups_dirty.connect(self._viewer_changed_groups)
        self.viewer_tab.request_unpin.connect(self.groups_tab.external_unpin)
        # keep the Groups tab's ACTIVE-category filter in sync with the Viewer
        self.viewer_tab.category_combo.currentTextChanged.connect(
            self.groups_tab.set_active_category)

        self.statusBar().showMessage("Set paths in the Paths tab to begin.")

    def on_paths_changed(self, b, r):
        if self._thread and self._thread.isRunning():
            return
        self.paths_tab.load_btn.setEnabled(False)
        self.statusBar().showMessage("Loading data in background...")
        self._b_path = b
        self._thread = DataLoadWorker(b, r)
        self._thread.finished.connect(self.on_data_loaded)
        self._thread.start()

    def on_data_loaded(self, ok, msg, balancer, rater):
        self.paths_tab.load_btn.setEnabled(True)
        if not ok:
            self.paths_tab.status_label.setText(msg)
            self.statusBar().showMessage(msg)
            QMessageBox.warning(self, "Load Error", msg)
            return

        self.balancer = balancer
        self.rater = rater
        d = os.path.dirname(self._b_path) or "."
        self.cluster = ClusterManager(os.path.join(d, CLUSTER_DATA_FILENAME))
        # Re-run the load-time dedupe/migration WITH rating knowledge: when
        # several differently-spelled duplicates of one image collapse into a
        # single group entry, keep the spelling that actually carries the
        # stars — so the surviving tile is the RATED one, never the phantom
        # unrated variant.
        self.cluster.load(preferred_spellings=self.rater.data.get("images", {}))

        self.viewer_tab.set_data(balancer, rater, self.cluster,
                                 os.path.join(d, SWAP_LOG_FILENAME))
        self.viewer_tab.set_directory_history_path(
            os.path.join(d, DIRECTORY_HISTORY_FILENAME))
        self.viewer_tab.refresh_rated_gallery()
        self.viewer_tab.setEnabled(True)

        self.groups_tab.set_data(self.cluster, rater, balancer)
        self.groups_tab.setEnabled(True)
        # default the Groups filter to the Viewer's active category
        self.groups_tab.set_active_category(self.viewer_tab._active_category())

        self.tabs.setCurrentIndex(1)
        self.paths_tab.status_label.setText("Data loaded successfully!")
        self.statusBar().showMessage(
            f"Loaded. {len(self.cluster.groups)} cluster group(s) from "
            f"{CLUSTER_DATA_FILENAME}.   Hold G + click in the Viewer to group images.")

    def _groups_edited(self, gid=None):
        self.viewer_tab._sync_group_context()
        self.viewer_tab._reconcile_collapses(only_group_id=gid)
        self.viewer_tab.refresh_selected_gallery(preserve_page=True)
        self.viewer_tab.refresh_rated_gallery(preserve_page=True)

    def _viewer_changed_groups(self):
        # keep the Groups tab's OPEN group in sync with the viewer's staged one
        self.groups_tab.open_gid = self.viewer_tab.staged_group_id
        # newly created groups belong to the category that was active at birth
        if self.viewer_tab.staged_group_id:
            cat = self.viewer_tab._active_category()
            if cat:
                self.cluster.set_group_category(self.viewer_tab.staged_group_id,
                                                cat)
        # and keep the category filter locked to whatever the Viewer shows
        self.groups_tab.set_active_category(self.viewer_tab._active_category(),
                                            refresh=False)
        self.groups_tab.refresh()

    def closeEvent(self, e):
        for p in self.viewer_tab.all_detachable_panels():
            p.force_close_floating()
        super().closeEvent(e)


# =============================================================================
if __name__ == "__main__":
    app = QApplication(sys.argv)
    apply_dark_theme(app)
    # Application-level filter: the ONLY way G-held state is reliably seen
    # while a list widget has keyboard focus, and it also covers the
    # detached gallery windows.
    app.installEventFilter(HOTKEYS)
    win = MainWindow()
    win.show()
    sys.exit(app.exec_())