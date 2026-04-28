import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import os, csv, shutil, re, threading, time, json, io, bisect
from pathlib import Path
from collections import deque
from urllib.parse import urlparse, unquote

# ────────────────────── Drag-and-Drop 지원 ────────────────────── #
try:  # tkinterdnd2 우선
    from tkinterdnd2 import TkinterDnD, DND_FILES
    DND_TYPE = 'tkinterdnd2'
except ImportError:
    try:
        from tkdnd import TkDND, DND_FILES
        DND_TYPE = 'tkdnd'
    except ImportError:
        DND_TYPE = None

SESSION_FILE = Path(__file__).parent / 'word_replacer_session.json'


class WordReplacerGUI:
    DEBOUNCE_MS = 150
    HILITE_DEBOUNCE_MS = 30
    MAX_PREVIEW_FILES = 50  # 파일 수만 제한 (출력/매치 개수 제한 없음)

    MAX_PREVIEW_MATCHES = 160_000
    MAX_PREVIEW_TEXT_CHARS = 5_000_000
    CONTEXT_CHARS_MAX = 200
    CONTEXT_LINE_MODE_BOTH = "Both"
    CONTEXT_LINE_MODE_ABOVE = "Above only"
    CONTEXT_LINE_MODE_BELOW = "Below only"
    CONTEXT_LINE_MODE_OPTIONS = (
        CONTEXT_LINE_MODE_BOTH,
        CONTEXT_LINE_MODE_ABOVE,
        CONTEXT_LINE_MODE_BELOW,
    )
    MAP_MODE_PREVIEW = "preview"
    MAP_MODE_REPLACE = "replace"
    MAP_MODE_DELETE_WORD = "delete-word"
    MAP_MODE_DELETE_LINE = "delete-line"
    MAP_MODE_INVALID = "invalid"
    ENCODING_AUTO = "Auto detect"
    ENCODING_UTF8 = "UTF-8"
    ENCODING_UTF8_BOM = "UTF-8 BOM"
    ENCODING_CP949 = "CP949"
    ENCODING_EUCKR = "EUC-KR"
    ENCODING_OPTIONS = (
        ENCODING_AUTO,
        ENCODING_UTF8,
        ENCODING_UTF8_BOM,
        ENCODING_CP949,
        ENCODING_EUCKR,
    )
    ENCODING_CODECS = {
        ENCODING_UTF8: "utf-8",
        ENCODING_UTF8_BOM: "utf-8-sig",
        ENCODING_CP949: "cp949",
        ENCODING_EUCKR: "euc-kr",
    }
    UTF8_BOM = b"\xef\xbb\xbf"
    BACKUP_SIDECAR = "Sidecar .bak"
    BACKUP_TIMESTAMPED = "Timestamped .bak"
    BACKUP_FOLDER = "Backup folder"
    BACKUP_NONE = "No backup"
    BACKUP_OPTIONS = (
        BACKUP_SIDECAR,
        BACKUP_TIMESTAMPED,
        BACKUP_FOLDER,
        BACKUP_NONE,
    )
    BACKUP_DIR_NAME = "_word_replacer_backups"
    DELETE_LINE_MODE_ALIASES = {
        "delete-line",
        "line-delete",
        "delete-lines",
        "delete-row",
        "remove-line",
        "line-remove",
        "line",
    }

    COLORS = {
        "bg": "#101114",
        "panel": "#1a1d23",
        "panel_alt": "#20242c",
        "field": "#101319",
        "border": "#343a46",
        "border_focus": "#00c2a8",
        "text": "#f4f6f8",
        "muted": "#aab1bd",
        "subtle": "#7d8490",
        "accent": "#00c2a8",
        "accent_hover": "#18d8bf",
        "accent_pressed": "#00a892",
        "accent_text": "#051716",
        "button": "#2a303b",
        "button_hover": "#363f4d",
        "button_pressed": "#222833",
        "selection": "#335cce",
        "warning": "#ffcc66",
        "danger": "#ff5d73",
        "danger_hover": "#ff7890",
        "purple": "#b68cff",
        "highlight": "#ffd166",
        "disabled_bg": "#232730",
        "disabled_text": "#68707d",
        "progress_trough": "#0b0d12",
    }
    UI_FONT = ("Segoe UI", 10)
    UI_FONT_BOLD = ("Segoe UI", 10, "bold")
    HEADING_FONT = ("Segoe UI Semibold", 11)
    TITLE_FONT = ("Segoe UI Semibold", 16)
    MONO_FONT = ("Consolas", 10)

    def _configure_theme(self):
        c = self.colors
        self.master.option_add("*Font", "{Segoe UI} 10")
        self.master.option_add("*Listbox.font", "{Segoe UI} 10")
        self.master.option_add("*TCombobox*Listbox.background", c["field"])
        self.master.option_add("*TCombobox*Listbox.foreground", c["text"])
        self.master.option_add("*TCombobox*Listbox.selectBackground", c["selection"])
        self.master.option_add("*TCombobox*Listbox.selectForeground", c["text"])

        style = ttk.Style(self.master)
        style.theme_use("clam")

        style.configure(".", font=self.UI_FONT)
        style.configure("TFrame", background=c["bg"])
        style.configure("Root.TFrame", background=c["bg"])
        style.configure("Header.TFrame", background=c["panel_alt"], relief="solid", borderwidth=1, bordercolor=c["border"])
        style.configure("AccentRail.TFrame", background=c["accent"])
        style.configure("Panel.TFrame", background=c["panel"], relief="solid", borderwidth=1, bordercolor=c["border"])
        style.configure("Toolbar.TFrame", background=c["panel"], relief="flat")
        style.configure("ActionPanel.TFrame", background=c["panel_alt"], relief="solid", borderwidth=1, bordercolor=c["border"])
        style.configure("Action.TFrame", background=c["panel_alt"])
        style.configure("StatusBar.TFrame", background=c["panel_alt"], relief="solid", borderwidth=1, bordercolor=c["border"])

        style.configure("TLabel", background=c["bg"], foreground=c["text"], font=self.UI_FONT)
        style.configure("HeaderTitle.TLabel", background=c["panel_alt"], foreground=c["text"], font=self.TITLE_FONT)
        style.configure("HeaderMeta.TLabel", background=c["panel_alt"], foreground=c["muted"], font=("Segoe UI", 9))
        style.configure("Section.TLabel", background=c["panel"], foreground=c["text"], font=self.HEADING_FONT)
        style.configure("Panel.TLabel", background=c["panel"], foreground=c["text"], font=self.UI_FONT)
        style.configure("Muted.TLabel", background=c["panel"], foreground=c["muted"], font=self.UI_FONT)
        style.configure("Mini.TLabel", background=c["panel"], foreground=c["subtle"], font=("Segoe UI", 8, "bold"))
        style.configure("Hint.TLabel", background=c["panel"], foreground=c["accent"], font=("Segoe UI", 9))
        style.configure("Warning.TLabel", background=c["panel"], foreground=c["warning"], font=("Segoe UI", 9))
        style.configure("Value.TLabel", background=c["panel"], foreground=c["text"], font=self.UI_FONT_BOLD)
        style.configure("ActionMuted.TLabel", background=c["panel_alt"], foreground=c["muted"], font=("Segoe UI", 9))
        style.configure("ActionMini.TLabel", background=c["panel_alt"], foreground=c["subtle"], font=("Segoe UI", 8, "bold"))
        style.configure("ActionHeading.TLabel", background=c["panel_alt"], foreground=c["accent"], font=("Segoe UI", 9, "bold"))
        style.configure("ActionValue.TLabel", background=c["panel_alt"], foreground=c["text"], font=self.UI_FONT_BOLD)
        style.configure("Status.TLabel", background=c["panel"], foreground=c["muted"], font=("Segoe UI", 9))
        style.configure("StatusBar.TLabel", background=c["panel_alt"], foreground=c["text"], font=self.UI_FONT)

        style.configure(
            "TButton",
            background=c["button"],
            foreground=c["text"],
            borderwidth=0,
            focusthickness=0,
            padding=(11, 7),
            font=self.UI_FONT_BOLD,
        )
        style.map(
            "TButton",
            background=[
                ("disabled", c["disabled_bg"]),
                ("pressed", c["button_pressed"]),
                ("active", c["button_hover"]),
            ],
            foreground=[("disabled", c["disabled_text"])],
        )
        style.configure(
            "Accent.TButton",
            background=c["accent"],
            foreground=c["accent_text"],
            borderwidth=0,
            focusthickness=0,
            padding=(13, 8),
            font=self.UI_FONT_BOLD,
        )
        style.map(
            "Accent.TButton",
            background=[
                ("disabled", c["disabled_bg"]),
                ("pressed", c["accent_pressed"]),
                ("active", c["accent_hover"]),
            ],
            foreground=[("disabled", c["disabled_text"])],
        )
        style.configure("Danger.TButton", background=c["danger"], foreground="#ffffff")
        style.map(
            "Danger.TButton",
            background=[("disabled", c["disabled_bg"]), ("pressed", c["danger"]), ("active", c["danger_hover"])],
            foreground=[("disabled", c["disabled_text"])],
        )
        style.configure(
            "Stepper.TButton",
            background=c["button"],
            foreground=c["text"],
            borderwidth=0,
            focusthickness=0,
            padding=(8, 4),
            font=self.UI_FONT_BOLD,
        )
        style.map(
            "Stepper.TButton",
            background=[
                ("disabled", c["disabled_bg"]),
                ("pressed", c["button_pressed"]),
                ("active", c["button_hover"]),
            ],
            foreground=[("disabled", c["disabled_text"]), ("active", c["accent"])],
        )

        style.configure("TCheckbutton", background=c["panel"], foreground=c["text"], font=self.UI_FONT)
        style.map(
            "TCheckbutton",
            background=[("active", c["panel"]), ("selected", c["panel"])],
            foreground=[("disabled", c["disabled_text"]), ("active", c["accent"])],
        )
        style.configure("TRadiobutton", background=c["panel"], foreground=c["text"], font=self.UI_FONT)
        style.map(
            "TRadiobutton",
            background=[("active", c["panel"]), ("selected", c["panel"])],
            foreground=[("disabled", c["disabled_text"]), ("active", c["accent"])],
        )
        style.configure("Action.TRadiobutton", background=c["panel_alt"], foreground=c["text"], font=("Segoe UI", 9))
        style.map(
            "Action.TRadiobutton",
            background=[("active", c["panel_alt"]), ("selected", c["panel_alt"])],
            foreground=[("disabled", c["disabled_text"]), ("active", c["accent"])],
        )

        style.configure(
            "TCombobox",
            background=c["button"],
            foreground=c["text"],
            fieldbackground=c["field"],
            selectbackground=c["selection"],
            selectforeground=c["text"],
            bordercolor=c["border"],
            lightcolor=c["border"],
            darkcolor=c["border"],
            arrowcolor=c["accent"],
            padding=(7, 4),
        )
        style.map(
            "TCombobox",
            fieldbackground=[("readonly", c["field"])],
            foreground=[("disabled", c["disabled_text"])],
            bordercolor=[("focus", c["border_focus"]), ("active", c["border_focus"])],
            arrowcolor=[("disabled", c["disabled_text"]), ("active", c["accent_hover"])],
        )

        style.configure("Horizontal.TScale", background=c["panel"], troughcolor=c["field"])
        style.configure("Action.Horizontal.TScale", background=c["panel_alt"], troughcolor=c["field"])
        style.configure(
            "Vertical.TScrollbar",
            background=c["button"],
            troughcolor=c["field"],
            arrowcolor=c["muted"],
            bordercolor=c["panel"],
            lightcolor=c["button"],
            darkcolor=c["button"],
        )
        style.configure(
            "Horizontal.TScrollbar",
            background=c["button"],
            troughcolor=c["field"],
            arrowcolor=c["muted"],
            bordercolor=c["panel"],
            lightcolor=c["button"],
            darkcolor=c["button"],
        )
        style.configure("TPanedwindow", background=c["bg"])
        style.configure("TProgressbar", troughcolor=c["progress_trough"], background=c["accent"], bordercolor=c["panel_alt"])
        style.configure("Navigator.TLabelframe", background=c["panel"], bordercolor=c["border"], borderwidth=1)
        style.configure(
            "Navigator.TLabelframe.Label",
            background=c["panel"], foreground=c["accent"], font=("Segoe UI", 9, "bold")
        )
        return style

    def _style_text_widget(self, widget):
        c = self.colors
        widget.configure(
            bg=c["field"],
            fg=c["text"],
            insertbackground=c["accent"],
            selectbackground=c["selection"],
            selectforeground=c["text"],
            relief="flat",
            bd=0,
            padx=10,
            pady=8,
            highlightthickness=1,
            highlightbackground=c["border"],
            highlightcolor=c["border_focus"],
        )

    def _style_listbox(self, widget):
        c = self.colors
        widget.configure(
            bg=c["field"],
            fg=c["text"],
            selectbackground=c["selection"],
            selectforeground=c["text"],
            relief="flat",
            bd=0,
            activestyle="none",
            highlightthickness=1,
            highlightbackground=c["border"],
            highlightcolor=c["border_focus"],
        )

    def _style_spinbox(self, widget):
        c = self.colors
        widget.configure(
            bg=c["field"],
            fg=c["text"],
            insertbackground=c["accent"],
            buttonbackground=c["button"],
            relief="flat",
            bd=0,
            width=4,
            highlightthickness=1,
            highlightbackground=c["border"],
            highlightcolor=c["border_focus"],
        )

    def _style_number_entry(self, widget):
        c = self.colors
        widget.configure(
            bg=c["field"],
            fg=c["text"],
            disabledbackground=c["disabled_bg"],
            disabledforeground=c["disabled_text"],
            insertbackground=c["accent"],
            justify="center",
            relief="flat",
            bd=0,
            width=2,
            highlightthickness=1,
            highlightbackground=c["border"],
            highlightcolor=c["border_focus"],
        )

    def schedule_preview(self):
        if self.preview_after_id:
            self.master.after_cancel(self.preview_after_id)
        self.preview_after_id = self.master.after(self.DEBOUNCE_MS, self.update_result)

    def __init__(self, master):
        self.master = master
        self.colors = self.COLORS
        c = self.colors
        master.title("Batch Text Transformer")
        master.geometry("1180x820")
        master.minsize(1020, 680)
        master.configure(bg=c["bg"])
        master.protocol("WM_DELETE_WINDOW", self.on_close)

        # ── 상태 ──
        self.preview_after_id = None
        self.hilite_after_id = None
        self.preview_seq = 0
        self.preview_thread = None
        self.replace_thread = None
        self.replace_cancel_event = threading.Event()
        self.is_replacing = False
        self.mapping_pairs: list[tuple[str, str, str]] = []
        self.last_replaced: list[str] = []
        self.total_replacements = 0
        self.file_mapping_changes: dict[str, set[tuple[str, str, str]]] = {}
        self.file_cache: dict[str, str] = {}
        self.file_lower_cache: dict[str, str] = {}
        self.file_encoding_cache: dict[str, str] = {}
        self.last_backup_paths: dict[str, str] = {}
        self.last_file_encodings: dict[str, str] = {}
        self.replace_scope_var = tk.StringVar(value="all")
        self.encoding_mode = self.ENCODING_AUTO
        self.encoding_var = tk.StringVar(value=self.ENCODING_AUTO)
        self.backup_policy_var = tk.StringVar(value=self.BACKUP_SIDECAR)

        # 프리뷰 결과(텍스트/매치구간/라인시작오프셋)
        self._pv_text: str | None = None
        self._pv_src_ranges: list[tuple[int, int]] = []  # (start_off, end_off) in combined text
        self._pv_src_starts: list[int] = []              # starts for bisect
        self._pv_line_starts: list[int] = []             # 각 라인의 시작 문자 오프셋
        self._pv_jump_nav: dict[str, dict[str, int | None]] = {}
        self._pv_delete_line_line_keys: dict[int, tuple[str, str, int]] = {}
        self.delete_line_selection_overrides: dict[tuple[str, str, int], bool] = {}

        self.context_chars_var = tk.IntVar(value=self.CONTEXT_CHARS_MAX)
        self.context_lines_var = tk.IntVar(value=0)
        self.context_line_mode_var = tk.StringVar(value=self.CONTEXT_LINE_MODE_BOTH)
        self.mapping_issue_var = tk.StringVar(value="Mapping issues: none")
        self.file_jump_var = tk.StringVar(value="")
        self.mapping_jump_var = tk.StringVar(value="")

        # ── 스타일 ──
        self.style = self._configure_theme()

        # ── 레이아웃 ──
        container = ttk.Frame(master, padding=(18, 16, 18, 14), style="Root.TFrame")
        container.pack(fill=tk.BOTH, expand=True)
        container.rowconfigure(1, weight=3)
        container.rowconfigure(2, weight=1)
        container.rowconfigure(3, weight=0)
        container.columnconfigure(0, weight=1)

        header = ttk.Frame(container, padding=(16, 12), style="Header.TFrame")
        header.grid(row=0, column=0, sticky="we", pady=(0, 12))
        header.columnconfigure(1, weight=1)
        ttk.Frame(header, width=4, style="AccentRail.TFrame").grid(row=0, column=0, rowspan=2, sticky="ns", padx=(0, 12))
        ttk.Label(header, text="Batch Text Transformer", style="HeaderTitle.TLabel").grid(row=0, column=1, sticky="w")
        ttk.Label(header, text="Replace, delete, and filter text across files", style="HeaderMeta.TLabel").grid(row=1, column=1, sticky="w", pady=(2, 0))

        self.paned = ttk.Panedwindow(container, orient=tk.HORIZONTAL)
        self.paned.grid(row=1, column=0, sticky="nsew", pady=(0, 10))
        self._sashes_initialized = False
        self.paned.bind("<Configure>", self._on_paned_configure)

        # 1) 파일 리스트
        file_frame = ttk.Frame(self.paned, padding=(12, 10), style="Panel.TFrame")
        file_frame.columnconfigure(0, weight=1)
        ttk.Label(file_frame, text="Input Files", style="Section.TLabel").grid(row=0, column=0, sticky="w")

        self.file_listbox = tk.Listbox(
            file_frame, selectmode="extended")
        self._style_listbox(self.file_listbox)
        self.file_listbox.grid(row=1, column=0, sticky="nsew", pady=(8, 0))
        self.file_listbox.bind("<Delete>", self.delete_selected)
        self.file_listbox.bind("<<ListboxSelect>>", self.on_file_selection_changed)

        self.hsb_file = ttk.Scrollbar(file_frame, orient="horizontal", command=self.file_listbox.xview)
        self.hsb_file.grid(row=2, column=0, sticky="we")
        self.vsb_file = ttk.Scrollbar(file_frame, orient="vertical", command=self.file_listbox.yview)
        self.vsb_file.grid(row=1, column=1, sticky="ns", pady=(8, 0))
        self.file_listbox.config(xscrollcommand=self.hsb_file.set, yscrollcommand=self.vsb_file.set)

        if DND_TYPE == 'tkinterdnd2':
            self.file_listbox.drop_target_register(DND_FILES)
            self.file_listbox.dnd_bind('<<Drop>>', self.on_files_dropped)
        elif DND_TYPE == 'tkdnd':
            TkDND(master).bindtarget(self.file_listbox, self.on_files_dropped, 'text/uri-list')

        btn_frame = ttk.Frame(file_frame, style="Panel.TFrame")
        btn_frame.grid(row=3, column=0, sticky="w", pady=(8, 6))
        self.browse_btn = ttk.Button(btn_frame, text="Browse Files", command=self.on_browse)
        self.browse_btn.pack(side="left", padx=(0, 8))
        self.clear_btn = ttk.Button(btn_frame, text="Clear List", command=self.on_clear)
        self.clear_btn.pack(side="left")
        if DND_TYPE is None:
            dnd_text = "Drag & drop unavailable. Install tkinterdnd2/tkdnd to enable."
        else:
            dnd_text = "Drag & drop enabled."
        self.dnd_hint_label = ttk.Label(file_frame, text=dnd_text, style="Hint.TLabel")
        self.dnd_hint_label.grid(row=4, column=0, sticky="w", pady=(0, 4))

        file_frame.rowconfigure(1, weight=1)
        self.paned.add(file_frame, weight=25)

        # 2) 매핑 창
        map_frame = ttk.Frame(self.paned, padding=(12, 10), style="Panel.TFrame")
        map_frame.rowconfigure(1, weight=1)
        map_frame.columnconfigure(0, weight=1)
        map_header = ttk.Frame(map_frame, style="Panel.TFrame")
        map_header.grid(row=0, column=0, columnspan=2, sticky="we")
        ttk.Label(map_header, text="Mapping", style="Section.TLabel").pack(side="left")
        self.mapping_help_btn = ttk.Button(map_header, text="?", width=3, command=self.show_mapping_help)
        self.mapping_help_btn.pack(side="left", padx=(8, 0))

        self.map_text = tk.Text(map_frame, wrap=tk.NONE, font=self.MONO_FONT)
        self._style_text_widget(self.map_text)
        self.map_text.grid(row=1, column=0, sticky="nsew", pady=(8, 0))

        self.vsb_map = ttk.Scrollbar(map_frame, orient="vertical", command=self.map_text.yview)
        self.vsb_map.grid(row=1, column=1, sticky="ns", pady=(8, 0))
        self.hsb_map = ttk.Scrollbar(map_frame, orient="horizontal", command=self.map_text.xview)
        self.hsb_map.grid(row=2, column=0, sticky="we")
        self.map_text.config(yscrollcommand=self.vsb_map.set, xscrollcommand=self.hsb_map.set)

        self.map_text.tag_configure("dup", background=c["danger"], foreground="#ffffff")
        self.map_text.tag_configure("same", background=c["purple"], foreground="#101114")
        self.map_text.tag_configure("csv_err", underline=True, foreground=c["danger"])
        self.map_text.tag_configure("regex_err", underline=True, foreground=c["warning"])
        self.map_text.tag_configure("mode_err", underline=True, foreground=c["warning"])
        self.map_text.bind("<<Modified>>", self.on_mapping_modified)
        self.map_text.bind("<KeyRelease>", self.on_mapping_key_release)
        self.map_text.bind("<Tab>", self.accept_mapping_autocomplete)

        opts = ttk.Frame(map_frame, style="Panel.TFrame")
        opts.grid(row=3, column=0, columnspan=2, sticky="w", pady=(8, 0))
        self.regex_var = tk.BooleanVar(value=False)
        self.case_var = tk.BooleanVar(value=False)
        self.regex_check = ttk.Checkbutton(opts, text="Regex Mode", variable=self.regex_var,
                                           command=self.on_mode_option_changed)
        self.regex_check.pack(side="left", padx=5)
        self.case_check = ttk.Checkbutton(opts, text="Case Sensitive", variable=self.case_var,
                                          command=self.on_mode_option_changed)
        self.case_check.pack(side="left", padx=5)
        self.mapping_issue_label = ttk.Label(
            map_frame,
            textvariable=self.mapping_issue_var,
            style="Warning.TLabel"
        )
        self.mapping_issue_label.grid(row=4, column=0, columnspan=2, sticky="we", pady=(6, 0))

        self.paned.add(map_frame, weight=15)

        # 3) 프리뷰 & 컨트롤
        prev_frame = ttk.Frame(self.paned, padding=(12, 10), style="Panel.TFrame")
        prev_frame.rowconfigure(2, weight=1)
        prev_frame.columnconfigure(0, weight=1)
        ttk.Label(prev_frame, text="Preview Matches", style="Section.TLabel").grid(row=0, column=0, sticky="w")

        self.src_listbox = tk.Listbox(prev_frame, height=5)
        self._style_listbox(self.src_listbox)
        self.src_listbox.grid(row=1, column=0, sticky="we", pady=(8, 0))
        self.src_listbox.bind("<<ListboxSelect>>", lambda e: self.schedule_preview())
        self.vsb_src = ttk.Scrollbar(prev_frame, orient="vertical", command=self.src_listbox.yview)
        self.vsb_src.grid(row=1, column=1, sticky="ns", pady=(8, 0))
        self.src_listbox.config(yscrollcommand=self.vsb_src.set)

        self.preview_text = tk.Text(prev_frame, wrap=tk.NONE, font=self.MONO_FONT, state="disabled")
        self._style_text_widget(self.preview_text)
        self.preview_text.grid(row=2, column=0, sticky="nsew", pady=(8, 0))

        # 하이라이트 태그: src만 (속도 이유)
        self.preview_text.tag_configure("highlight_src", background=c["highlight"], foreground=c["bg"])
        self.preview_text.tag_configure("delete_line_selected", background="#263a34", foreground=c["text"])
        self.preview_text.tag_configure("delete_line_unselected", background=c["field"], foreground=c["subtle"], overstrike=1)

        # 스크롤바
        self.vsb_preview = ttk.Scrollbar(prev_frame, orient="vertical", command=self.preview_text.yview)
        self.vsb_preview.grid(row=2, column=1, sticky="ns", pady=(8, 0))
        self.hsb_preview = ttk.Scrollbar(prev_frame, orient="horizontal", command=self.preview_text.xview)
        self.hsb_preview.grid(row=3, column=0, sticky="we")

        # yview 변경을 감지해 보이는 영역만 하이라이트
        self.preview_text.config(yscrollcommand=self._on_preview_yview, xscrollcommand=self.hsb_preview.set)
        self.preview_text.bind("<Configure>", lambda e: self._schedule_visible_highlight())
        self.preview_text.bind("<Button-1>", self.on_preview_click, add="+")

        act = ttk.Frame(prev_frame, padding=(12, 10), style="ActionPanel.TFrame")
        act.grid(row=4, column=0, sticky="we", pady=(10, 6))
        act.columnconfigure(0, weight=1)
        act_top = ttk.Frame(act, style="Action.TFrame")
        act_top.grid(row=0, column=0, sticky="we")
        act_top.columnconfigure(2, weight=1)
        act_bottom = ttk.Frame(act, style="Action.TFrame")
        act_bottom.grid(row=2, column=0, sticky="we", pady=(10, 0))

        context_frame = ttk.Frame(act_top, style="Action.TFrame")
        context_frame.grid(row=0, column=0, sticky="w")
        ttk.Label(context_frame, text="Context lines", style="ActionMuted.TLabel").pack(
            side="left", padx=(0, 5))
        context_lines_stepper = ttk.Frame(context_frame, style="Action.TFrame")
        context_lines_stepper.pack(side="left", padx=(0, 10))
        self.context_lines_down_btn = ttk.Button(
            context_lines_stepper,
            text="-",
            width=2,
            style="Stepper.TButton",
            command=lambda: self._adjust_context_lines(-1)
        )
        self.context_lines_down_btn.pack(side="left")
        context_lines_vcmd = (self.master.register(self._validate_context_lines), "%P")
        self.context_lines_entry = tk.Entry(
            context_lines_stepper,
            textvariable=self.context_lines_var,
            width=2,
            validate="key",
            validatecommand=context_lines_vcmd,
            font=self.UI_FONT_BOLD,
        )
        self._style_number_entry(self.context_lines_entry)
        self.context_lines_entry.pack(side="left", padx=3, ipady=4)
        self.context_lines_entry.bind("<KeyRelease>", lambda e: self.schedule_preview())
        self.context_lines_entry.bind("<FocusOut>", lambda e: self._clamp_context_lines())
        self.context_lines_up_btn = ttk.Button(
            context_lines_stepper,
            text="+",
            width=2,
            style="Stepper.TButton",
            command=lambda: self._adjust_context_lines(1)
        )
        self.context_lines_up_btn.pack(side="left")

        ttk.Label(context_frame, text="Show", style="ActionMuted.TLabel").pack(
            side="left", padx=(0, 5))
        self.context_line_mode_combo = ttk.Combobox(
            context_frame,
            textvariable=self.context_line_mode_var,
            values=self.CONTEXT_LINE_MODE_OPTIONS,
            state="readonly",
            width=11,
        )
        self.context_line_mode_combo.pack(side="left", padx=(0, 10))
        self.context_line_mode_combo.bind("<<ComboboxSelected>>", self.on_context_line_mode_changed)

        ttk.Label(context_frame, text="Context chars", style="ActionMuted.TLabel").pack(
            side="left", padx=(0, 5))
        self.context_chars_scale = ttk.Scale(context_frame, from_=0, to=self.CONTEXT_CHARS_MAX, variable=self.context_chars_var,
                                             orient=tk.HORIZONTAL, length=120,
                                             style="Action.Horizontal.TScale",
                                             command=lambda v: self.schedule_preview())
        self.context_chars_scale.pack(side="left", padx=(0, 4))
        self.context_chars_label = ttk.Label(
            context_frame,
            text=str(self.context_chars_var.get()),
            width=3,
            anchor="e",
            style="ActionValue.TLabel"
        )
        self.context_chars_label.pack(side="left")
        self.context_chars_var.trace_add("write", self.on_context_chars_changed)

        scope_frame = ttk.Frame(act_top, style="Action.TFrame")
        scope_frame.grid(row=0, column=1, sticky="w", padx=(22, 0))
        ttk.Label(scope_frame, text="Replace scope", style="ActionMuted.TLabel").pack(side="left", padx=(0, 6))
        self.scope_selected_rb = ttk.Radiobutton(
            scope_frame, text="Selected", value="selected", variable=self.replace_scope_var,
            command=self._on_replace_scope_changed, style="Action.TRadiobutton"
        )
        self.scope_selected_rb.pack(side="left", padx=(0, 2))
        self.scope_all_rb = ttk.Radiobutton(
            scope_frame, text="All", value="all", variable=self.replace_scope_var,
            command=self._on_replace_scope_changed, style="Action.TRadiobutton"
        )
        self.scope_all_rb.pack(side="left")

        nav_frame = ttk.Frame(act, style="Action.TFrame")
        nav_frame.grid(row=1, column=0, sticky="we", pady=(10, 0))
        nav_frame.columnconfigure(0, weight=1)
        nav_frame.columnconfigure(1, weight=1)
        ttk.Label(nav_frame, text="Result Navigator", style="ActionHeading.TLabel").grid(
            row=0, column=0, columnspan=3, sticky="w", pady=(0, 4)
        )
        ttk.Label(nav_frame, text="File", style="ActionMini.TLabel").grid(row=1, column=0, padx=(0, 8), sticky="w")
        ttk.Label(nav_frame, text="Mapping", style="ActionMini.TLabel").grid(row=1, column=1, padx=(0, 8), sticky="w")
        self.file_jump_combo = ttk.Combobox(nav_frame, textvariable=self.file_jump_var, state="readonly", width=24)
        self.file_jump_combo.grid(row=2, column=0, padx=(0, 8), pady=(2, 0), sticky="we")
        self.file_jump_combo.bind("<<ComboboxSelected>>", self.on_file_jump_selected)
        self.mapping_jump_combo = ttk.Combobox(
            nav_frame, textvariable=self.mapping_jump_var, state="readonly", width=22
        )
        self.mapping_jump_combo.grid(row=2, column=1, padx=(0, 8), pady=(2, 0), sticky="we")
        self.mapping_jump_combo.bind("<<ComboboxSelected>>", self.on_mapping_jump_selected)
        self.file_jump_btn = ttk.Button(nav_frame, text="Jump", command=self.jump_to_selected_file, width=7)
        self.file_jump_btn.grid(row=2, column=2, pady=(2, 0), sticky="e")

        io_options_frame = ttk.Frame(act_bottom, style="Action.TFrame")
        io_options_frame.pack(side="left", fill="x", expand=True)
        ttk.Label(io_options_frame, text="Encoding", style="ActionMuted.TLabel").pack(side="left", padx=(0, 5))
        self.encoding_combo = ttk.Combobox(
            io_options_frame,
            textvariable=self.encoding_var,
            values=self.ENCODING_OPTIONS,
            state="readonly",
            width=13,
        )
        self.encoding_combo.pack(side="left", padx=(0, 14))
        self.encoding_combo.bind("<<ComboboxSelected>>", self.on_encoding_changed)

        ttk.Label(io_options_frame, text="Backup", style="ActionMuted.TLabel").pack(side="left", padx=(0, 5))
        self.backup_policy_combo = ttk.Combobox(
            io_options_frame,
            textvariable=self.backup_policy_var,
            values=self.BACKUP_OPTIONS,
            state="readonly",
            width=16,
        )
        self.backup_policy_combo.pack(side="left")

        btn_row_right = ttk.Frame(act_bottom, style="Action.TFrame")
        btn_row_right.pack(side="right")

        self.copy_preview_btn = ttk.Button(btn_row_right, text="Copy Preview", command=self.copy_preview)
        self.copy_preview_btn.pack(side="left", padx=(0, 8))

        self.undo_btn = ttk.Button(btn_row_right, text="Undo", command=self.undo_replace)
        self.undo_btn.state(["disabled"])
        self.undo_btn.pack(side="left", padx=(0, 8))

        self.cancel_btn = ttk.Button(btn_row_right, text="Cancel", style="Danger.TButton", command=self.cancel_replace)
        self.cancel_btn.pack(side="left", padx=(0, 8))
        self.cancel_btn.state(["disabled"])

        self.replace_btn = ttk.Button(btn_row_right, text="Apply", style="Accent.TButton", command=self.start_replace)
        self.replace_btn.pack(side="left")
        self.replace_btn.state(["disabled"])

        self.preview_status_label = ttk.Label(prev_frame, text="", style="Status.TLabel")
        self.preview_status_label.grid(row=5, column=0, sticky="we", pady=(0, 5))

        self.paned.add(prev_frame, weight=60)

        # 4) 로그
        log_frame = ttk.Frame(container, padding=(12, 10), style="Panel.TFrame")
        log_frame.grid(row=2, column=0, sticky="nsew", pady=(10, 0))
        log_frame.rowconfigure(1, weight=1)
        log_frame.columnconfigure(0, weight=1)
        ttk.Label(log_frame, text="Activity Log", style="Section.TLabel").grid(row=0, column=0, sticky="w")

        self.log_area = tk.Text(log_frame, wrap=tk.NONE, height=6, font=self.MONO_FONT, state="disabled")
        self._style_text_widget(self.log_area)
        self.log_area.grid(row=1, column=0, sticky="nsew", pady=(8, 0))

        self.hsb_log = ttk.Scrollbar(log_frame, orient="horizontal", command=self.log_area.xview)
        self.hsb_log.grid(row=2, column=0, sticky="we")
        self.vsb_log = ttk.Scrollbar(log_frame, orient="vertical", command=self.log_area.yview)
        self.vsb_log.grid(row=1, column=1, sticky="ns", pady=(8, 0))
        self.log_area.config(yscrollcommand=self.vsb_log.set, xscrollcommand=self.hsb_log.set)

        # 진행 바
        status_frame = ttk.Frame(container, padding=(12, 9), style="StatusBar.TFrame")
        status_frame.grid(row=3, column=0, sticky="we", pady=(10, 0))
        status_frame.columnconfigure(0, weight=1)
        self.replace_status_label = ttk.Label(status_frame, text="Ready.", style="StatusBar.TLabel")
        self.replace_status_label.grid(row=0, column=0, sticky="we", padx=(0, 12))
        self.progress = ttk.Progressbar(status_frame, mode="determinate", length=260)
        self.progress.grid(row=0, column=1, sticky="we")

        # 스크롤바 자동 숨김
        for widget, vsb, hsb in [
            (self.file_listbox, self.vsb_file, self.hsb_file),
            (self.map_text,     self.vsb_map,  self.hsb_map),
            (self.src_listbox,  self.vsb_src,  None),
            (self.preview_text, self.vsb_preview, self.hsb_preview),
            (self.log_area,     self.vsb_log,  self.hsb_log)
        ]:
            widget.bind("<Configure>", lambda e, w=widget, v=vsb, h=hsb: self._check_scrollbars(w, v, h))

        # 세션 로드
        self.load_session()
        self.update_src_list()
        self._set_file_shortcuts([])
        self._refresh_action_state()

    # ────────────────────── 유틸/레이아웃 ────────────────────── #
    def _on_paned_configure(self, e):
        if not self._sashes_initialized and self.paned.winfo_width() > 0:
            w = self.paned.winfo_width()
            self.paned.sashpos(0, int(w * 0.25))
            self.paned.sashpos(1, int(w * 0.40))
            self._sashes_initialized = True

    def _check_scrollbars(self, widget, vsb, hsb):
        if vsb:
            f, l = widget.yview()
            vsb.grid() if f > 0.0 or l < 1.0 else vsb.grid_remove()
        if hsb:
            f, l = widget.xview()
            hsb.grid() if f > 0.0 or l < 1.0 else hsb.grid_remove()

    def _normalize_encoding_mode(self, mode: str | None) -> str:
        if mode in self.ENCODING_OPTIONS:
            return mode
        return self.ENCODING_AUTO

    def _normalize_backup_policy(self, policy: str | None) -> str:
        if policy in self.BACKUP_OPTIONS:
            return policy
        return self.BACKUP_SIDECAR

    def _decode_file_bytes(self, path: str, raw: bytes) -> tuple[str, str]:
        mode = self._normalize_encoding_mode(self.encoding_mode)
        if mode != self.ENCODING_AUTO:
            codec = self.ENCODING_CODECS[mode]
            try:
                return raw.decode(codec), codec
            except UnicodeDecodeError as ex:
                raise OSError(f"Failed to decode with {mode}: {path}") from ex

        if raw.startswith(self.UTF8_BOM):
            try:
                return raw.decode("utf-8-sig"), "utf-8-sig"
            except UnicodeDecodeError:
                pass

        for codec in ("utf-8", "cp949", "euc-kr"):
            try:
                return raw.decode(codec), codec
            except UnicodeDecodeError:
                continue
        raise OSError(f"Failed to auto-detect encoding: {path}")

    def _read_file_with_encoding(self, path: str) -> tuple[str, str]:
        try:
            raw = Path(path).read_bytes()
            return self._decode_file_bytes(path, raw)
        except OSError:
            raise
        except Exception as ex:
            raise OSError(f"Failed to read file: {path}") from ex

    def _get_file_text(self, path: str) -> str:
        if path in self.file_cache:
            return self.file_cache[path]
        txt, encoding = self._read_file_with_encoding(path)
        self.file_cache[path] = txt
        self.file_encoding_cache[path] = encoding
        return txt

    def _get_file_encoding(self, path: str) -> str:
        encoding = self.file_encoding_cache.get(path)
        if encoding:
            return encoding
        self._get_file_text(path)
        return self.file_encoding_cache[path]

    def _open_text_reader(self, path: str):
        encoding = self._get_file_encoding(path)
        return open(path, "r", encoding=encoding, errors="strict", newline="", buffering=1 << 20)

    def _write_file_text(self, path: str, text: str, encoding: str):
        with open(path, "w", encoding=encoding, errors="strict", newline="") as fh:
            fh.write(text)

    def _clear_cached_file_derivatives(self, path: str | None = None):
        if path is None:
            self.file_lower_cache.clear()
            return
        self.file_lower_cache.pop(path, None)

    def _get_file_lower_text(self, path: str, text: str) -> str:
        cached = self.file_lower_cache.get(path)
        if cached is not None and len(cached) == len(text):
            return cached
        lowered = text.lower()
        self.file_lower_cache[path] = lowered
        return lowered

    @staticmethod
    def _normalize_file_path(raw: str) -> str:
        s = str(raw).strip().strip("{}")
        if not s:
            return ""
        if s.lower().startswith("file://"):
            u = urlparse(s)
            p = unquote(u.path)
            if re.match(r"^/[A-Za-z]:", p):
                p = p[1:]
            if u.netloc and not re.match(r"^[A-Za-z]:", p):
                p = f"//{u.netloc}{p}"
            s = p
        return os.path.normpath(s)

    def _add_files(self, paths, source="files", log_result=True):
        if not paths:
            return 0, 0
        existing = set(self.file_listbox.get(0, tk.END))
        added = 0
        skipped_dup = 0
        for raw in paths:
            p = self._normalize_file_path(raw)
            if not p:
                continue
            if p in existing:
                skipped_dup += 1
                continue
            existing.add(p)
            self.file_listbox.insert(tk.END, p)
            added += 1

        if log_result:
            self.log(f"{source}: added {added}, skipped duplicates {skipped_dup}")
        return added, skipped_dup

    def _get_preview_files(self):
        selected = self.file_listbox.curselection()
        if selected:
            return [self.file_listbox.get(i) for i in selected]
        return [self.file_listbox.get(i) for i in range(self.file_listbox.size())]

    def _get_replace_files(self):
        if self.replace_scope_var.get() == "selected":
            return [self.file_listbox.get(i) for i in self.file_listbox.curselection()]
        return [self.file_listbox.get(i) for i in range(self.file_listbox.size())]

    def _normalize_mapping_mode_token(self, token: str) -> str:
        return token.strip().lower().replace("_", "-").replace(" ", "-")

    def _parse_mapping_row(self, line: str) -> tuple[str, str, str] | None:
        parts = next(csv.reader([line], skipinitialspace=True), [])
        if not parts:
            return None

        src = parts[0].strip()
        if not src:
            return None

        if len(parts) == 1:
            return src, "", self.MAP_MODE_PREVIEW

        dst = parts[1].strip()
        if len(parts) > 2:
            mode_token = self._normalize_mapping_mode_token(parts[2])
            if mode_token in self.DELETE_LINE_MODE_ALIASES:
                return src, "", self.MAP_MODE_DELETE_LINE
            if mode_token:
                return src, dst, self.MAP_MODE_INVALID

        if dst:
            return src, dst, self.MAP_MODE_REPLACE
        return src, "", self.MAP_MODE_DELETE_WORD

    def _autocomplete_delete_line_mode(self):
        insert = self.map_text.index(tk.INSERT)
        line_start = self.map_text.index(f"{insert} linestart")
        before_cursor = self.map_text.get(line_start, insert)
        marker = before_cursor.rfind(",,")
        if marker == -1:
            return

        src_part = before_cursor[:marker].strip()
        typed_mode = before_cursor[marker + 2:]
        if not src_part or "," in typed_mode:
            return
        if not re.fullmatch(r"[A-Za-z_-]*", typed_mode):
            return

        normalized_mode = self._normalize_mapping_mode_token(typed_mode)
        completion = self.MAP_MODE_DELETE_LINE
        if normalized_mode == completion or not completion.startswith(normalized_mode):
            return

        mode_start = f"{line_start}+{marker + 2}c"
        self.map_text.delete(mode_start, insert)
        self.map_text.insert(mode_start, completion)

        keep_len = len(typed_mode)
        sel_start = f"{mode_start}+{keep_len}c"
        sel_end = f"{mode_start}+{len(completion)}c"
        self.map_text.mark_set(tk.INSERT, sel_end)
        self.map_text.tag_remove(tk.SEL, "1.0", tk.END)
        if self.map_text.compare(sel_start, "<", sel_end):
            self.map_text.tag_add(tk.SEL, sel_start, sel_end)
        self.map_text.see(sel_end)

    def _mapping_src(self, mapping) -> str:
        return mapping[0] if mapping else ""

    def _mapping_dst(self, mapping) -> str:
        return mapping[1] if len(mapping) > 1 else ""

    def _mapping_mode(self, mapping) -> str:
        if len(mapping) > 2:
            return mapping[2]
        return self.MAP_MODE_REPLACE if self._mapping_dst(mapping) else self.MAP_MODE_DELETE_WORD

    def _mapping_is_effective(self, mapping) -> bool:
        mode = self._mapping_mode(mapping)
        return bool(self._mapping_src(mapping)) and mode not in (self.MAP_MODE_PREVIEW, self.MAP_MODE_INVALID)

    def _mapping_preview_dst(self, mapping) -> str:
        mode = self._mapping_mode(mapping)
        if mode == self.MAP_MODE_DELETE_LINE:
            return "[delete line]"
        return self._mapping_dst(mapping)

    def _format_mapping_list_label(self, mapping) -> str:
        src = self._mapping_src(mapping)
        dst = self._mapping_dst(mapping)
        mode = self._mapping_mode(mapping)
        if mode == self.MAP_MODE_DELETE_LINE:
            return f"{src} (delete line)"
        if mode == self.MAP_MODE_DELETE_WORD:
            return f"{src} (delete word)"
        if mode == self.MAP_MODE_INVALID:
            return f"{src} (invalid mode)"
        if dst:
            return f"{src} -> {dst}"
        return src

    def _format_mapping_summary_label(self, mapping) -> str:
        src = self._mapping_src(mapping)
        mode = self._mapping_mode(mapping)
        if mode == self.MAP_MODE_DELETE_LINE:
            return f"{src}[line]"
        if mode == self.MAP_MODE_DELETE_WORD:
            return f"{src}[delete]"
        return src

    def _format_mapping_nav_label(self, index: int, mapping, count: int) -> str:
        label = self._format_mapping_list_label(mapping)
        if len(label) > 44:
            label = label[:41] + "..."
        return f"{index}. {label} ({count})"

    def _format_mapping_log_label(self, mapping) -> str:
        src = self._mapping_src(mapping)
        dst = self._mapping_dst(mapping)
        mode = self._mapping_mode(mapping)
        if mode == self.MAP_MODE_DELETE_LINE:
            return f"delete lines containing '{src}'"
        if mode == self.MAP_MODE_DELETE_WORD:
            return f"delete '{src}'"
        return f"'{src}' -> '{dst}'"

    def _get_effective_replace_pairs(self):
        return [mapping for mapping in self.mapping_pairs if self._mapping_is_effective(mapping)]

    def _set_preview_output(self, text: str):
        self.preview_text.config(state="normal")
        self.preview_text.delete("1.0", tk.END)
        if text:
            self.preview_text.insert("1.0", text)
        self.preview_text.config(state="disabled")
        self._check_scrollbars(self.preview_text, self.vsb_preview, self.hsb_preview)

    def _make_delete_line_selection_key(self, file_path: str, mapping, line_no: int) -> tuple[str, str, int]:
        return (os.path.normcase(os.path.abspath(file_path)), self._mapping_src(mapping), int(line_no))

    def _find_preview_file_for_header(self, basename: str, files: list[str], cursor: int) -> tuple[str | None, int]:
        for i in range(cursor + 1, len(files)):
            if os.path.basename(files[i]) == basename:
                return files[i], i
        for i, path in enumerate(files):
            if os.path.basename(path) == basename:
                return path, i
        return None, cursor

    def _rebuild_delete_line_preview_index(self, files, targets, text, ranges, line_starts):
        self._pv_delete_line_line_keys = {}
        delete_line_targets = {
            (self._mapping_src(mapping), self._mapping_preview_dst(mapping)): mapping
            for mapping in targets
            if self._mapping_mode(mapping) == self.MAP_MODE_DELETE_LINE
        }
        if not delete_line_targets or not text or not ranges:
            return

        header_re = re.compile(r"^([^:\r\n]+): '(.*)' -> '(.*)'$")
        line_re = re.compile(r"^\s+L(\d+):")
        line_candidates: dict[int, tuple[str, str, int]] = {}
        current_file = None
        current_mapping = None
        cursor = -1

        for preview_line_no, line in enumerate(text.splitlines(), start=1):
            hm = header_re.match(line.rstrip("\r\n"))
            if hm:
                basename, src, dst = hm.group(1), hm.group(2), hm.group(3)
                current_mapping = delete_line_targets.get((src, dst))
                if current_mapping:
                    current_file, cursor = self._find_preview_file_for_header(basename, files, cursor)
                else:
                    current_file = None
                continue

            if not current_file or not current_mapping:
                continue
            lm = line_re.match(line)
            if not lm:
                continue
            actual_line_no = int(lm.group(1))
            line_candidates[preview_line_no] = self._make_delete_line_selection_key(
                current_file, current_mapping, actual_line_no
            )

        for start, _ in ranges:
            preview_line_no = bisect.bisect_right(line_starts, start)
            key = line_candidates.get(preview_line_no)
            if key:
                self._pv_delete_line_line_keys[preview_line_no] = key

    def _delete_line_selection_counts(self) -> tuple[int, int]:
        keys = set(self._pv_delete_line_line_keys.values())
        total = len(keys)
        selected = sum(1 for key in keys if self.delete_line_selection_overrides.get(key, True))
        return selected, total

    def _apply_delete_line_selection_tags(self):
        self.preview_text.tag_remove("delete_line_selected", "1.0", tk.END)
        self.preview_text.tag_remove("delete_line_unselected", "1.0", tk.END)
        for preview_line_no, key in self._pv_delete_line_line_keys.items():
            tag = (
                "delete_line_selected"
                if self.delete_line_selection_overrides.get(key, True)
                else "delete_line_unselected"
            )
            self.preview_text.tag_add(tag, f"{preview_line_no}.0", f"{preview_line_no}.end")
        self.preview_text.tag_raise("highlight_src")

    def on_preview_click(self, event):
        try:
            preview_line_no = int(self.preview_text.index(f"@{event.x},{event.y}").split(".")[0])
        except Exception:
            return None

        key = self._pv_delete_line_line_keys.get(preview_line_no)
        if not key:
            return None

        selected = self.delete_line_selection_overrides.get(key, True)
        self.delete_line_selection_overrides[key] = not selected
        self._apply_delete_line_selection_tags()
        selected_count, total_count = self._delete_line_selection_counts()
        self.preview_status_label.config(
            text=f"Delete-line selection: {selected_count}/{total_count} lines selected. Click rows to toggle."
        )
        return "break"

    def _set_file_shortcuts(self, items: list[tuple[str, list[tuple[str, int | None]]]]):
        self._pv_jump_nav = {file_label: dict(mapping_items) for file_label, mapping_items in items}
        values = [file_label for file_label, _ in items]
        self.file_jump_combo["values"] = values
        if values:
            self.file_jump_combo.current(0)
        else:
            self.file_jump_var.set("")
        self._refresh_mapping_jump_values()
        self._refresh_file_jump_state()

    def _refresh_file_jump_state(self):
        has_file_values = bool(self.file_jump_combo.cget("values"))
        has_mapping_values = bool(self.mapping_jump_combo.cget("values"))
        if self.is_replacing or not has_file_values:
            self.file_jump_combo.state(["disabled"])
        else:
            self.file_jump_combo.state(["!disabled"])
        if self.is_replacing or not has_mapping_values:
            self.mapping_jump_combo.state(["disabled"])
        else:
            self.mapping_jump_combo.state(["!disabled"])
        if self.is_replacing or not (has_file_values and has_mapping_values):
            self.file_jump_btn.state(["disabled"])
        else:
            self.file_jump_btn.state(["!disabled"])

    def on_file_jump_selected(self, event=None):
        self._refresh_mapping_jump_values()

    def _refresh_mapping_jump_values(self):
        file_key = self.file_jump_var.get().strip()
        mapping_map = self._pv_jump_nav.get(file_key, {})
        values = list(mapping_map.keys())
        self.mapping_jump_combo["values"] = values
        if values:
            self.mapping_jump_combo.current(0)
        else:
            self.mapping_jump_var.set("")
        self._refresh_file_jump_state()

    def on_mapping_jump_selected(self, event=None):
        self.jump_to_selected_file()

    def jump_to_selected_file(self):
        file_key = self.file_jump_var.get().strip()
        map_key = self.mapping_jump_var.get().strip()
        if not file_key or not map_key:
            return
        off = self._pv_jump_nav.get(file_key, {}).get(map_key)
        if off is None:
            self.preview_status_label.config(text="No result lines for the selected mapping in this file.")
            return
        idx = f"1.0+{off}c"
        self.preview_text.see(idx)
        self.preview_text.mark_set(tk.INSERT, idx)
        self.preview_text.focus_set()
        self._schedule_visible_highlight(immediate=True)
        self.preview_status_label.config(text=f"Jumped to: {file_key} / {map_key}")

    def _set_replace_running(self, running: bool):
        self.is_replacing = running
        list_state = tk.DISABLED if running else tk.NORMAL
        text_state = tk.DISABLED if running else tk.NORMAL
        self.file_listbox.config(state=list_state)
        self.map_text.config(state=text_state)
        self.src_listbox.config(state=list_state)
        self.context_lines_entry.config(state=list_state)

        if running:
            self.regex_check.state(["disabled"])
            self.case_check.state(["disabled"])
            self.scope_selected_rb.state(["disabled"])
            self.scope_all_rb.state(["disabled"])
            self.context_lines_down_btn.state(["disabled"])
            self.context_lines_up_btn.state(["disabled"])
            self.context_line_mode_combo.state(["disabled"])
            self.context_chars_scale.state(["disabled"])
            self.browse_btn.state(["disabled"])
            self.clear_btn.state(["disabled"])
            self.encoding_combo.state(["disabled"])
            self.backup_policy_combo.state(["disabled"])
            self.copy_preview_btn.state(["disabled"])
            self.cancel_btn.state(["!disabled"])
        else:
            self.regex_check.state(["!disabled"])
            self.case_check.state(["!disabled"])
            self.scope_selected_rb.state(["!disabled"])
            self.scope_all_rb.state(["!disabled"])
            self.context_lines_down_btn.state(["!disabled"])
            self.context_lines_up_btn.state(["!disabled"])
            self.context_line_mode_combo.state(["!disabled"])
            self.context_chars_scale.state(["!disabled"])
            self.browse_btn.state(["!disabled"])
            self.clear_btn.state(["!disabled"])
            self.encoding_combo.state(["!disabled"])
            self.backup_policy_combo.state(["!disabled"])
            self.copy_preview_btn.state(["!disabled"])
            self.cancel_btn.state(["disabled"])

        self._refresh_file_jump_state()
        self._refresh_action_state()

    def _refresh_action_state(self):
        can_replace = (
            (not self.is_replacing)
            and bool(self._get_replace_files())
            and bool(self._get_effective_replace_pairs())
        )
        if can_replace:
            self.replace_btn.state(["!disabled"])
        else:
            self.replace_btn.state(["disabled"])

        can_undo = (not self.is_replacing) and bool(self.last_replaced)
        if can_undo:
            self.undo_btn.state(["!disabled"])
        else:
            self.undo_btn.state(["disabled"])

    def on_file_selection_changed(self, event=None):
        self.schedule_preview()
        self._refresh_action_state()

    def on_mode_option_changed(self):
        self._highlight_mapping()
        self.schedule_preview()
        self._refresh_action_state()

    def on_encoding_changed(self, event=None):
        self.encoding_mode = self._normalize_encoding_mode(self.encoding_var.get())
        self.encoding_var.set(self.encoding_mode)
        self.file_cache.clear()
        self.file_encoding_cache.clear()
        self._clear_cached_file_derivatives()
        self.schedule_preview()

    def on_context_chars_changed(self, *_):
        self.context_chars_label.config(text=str(self.context_chars_var.get()))

    def _validate_context_lines(self, value: str) -> bool:
        if not value.isdigit() or len(value) > 2:
            return False
        return 0 <= int(value) <= 30

    def _clamp_context_lines(self):
        try:
            value = int(self.context_lines_var.get())
        except (tk.TclError, ValueError):
            value = 0
        self.context_lines_var.set(max(0, min(30, value)))
        self.schedule_preview()

    def _adjust_context_lines(self, delta: int):
        if self.is_replacing:
            return
        try:
            value = int(self.context_lines_var.get())
        except (tk.TclError, ValueError):
            value = 0
        self.context_lines_var.set(max(0, min(30, value + delta)))
        self.schedule_preview()

    def _normalize_context_line_mode(self, mode: str | None) -> str:
        if mode in self.CONTEXT_LINE_MODE_OPTIONS:
            return mode
        return self.CONTEXT_LINE_MODE_BOTH

    def _get_context_line_visibility(self, mode: str | None = None) -> tuple[bool, bool]:
        mode = self._normalize_context_line_mode(
            self.context_line_mode_var.get() if mode is None else mode
        )
        show_above = mode != self.CONTEXT_LINE_MODE_BELOW
        show_below = mode != self.CONTEXT_LINE_MODE_ABOVE
        return show_above, show_below

    def on_context_line_mode_changed(self, event=None):
        self.context_line_mode_var.set(self._normalize_context_line_mode(self.context_line_mode_var.get()))
        self.schedule_preview()

    def _on_replace_scope_changed(self):
        self._refresh_action_state()

    # ────────────────────── 이벤트 ────────────────────── #
    def show_mapping_help(self):
        messagebox.showinfo(
            "Mapping examples",
            "Mapping 입력 예시\n\n"
            "foo,bar\n"
            "  foo를 bar로 치환합니다.\n\n"
            "foo,\n"
            "  매칭된 foo 텍스트를 삭제합니다.\n\n"
            "foo,,delete-line\n"
            "  foo가 포함된 라인 전체를 삭제합니다.\n\n"
            "참고\n"
            "- source가 비어 있으면 무시됩니다.\n"
            "- source만 있는 줄은 preview 전용입니다.\n"
            "- ,,를 입력하면 delete-line이 자동완성됩니다.\n"
            "- delete-line 매치는 Preview에서 기본 선택됩니다. 해당 줄을 클릭하면 적용 여부를 토글합니다.\n"
            "- 쉼표나 앞뒤 공백이 필요하면 CSV 따옴표를 사용하세요.\n\n"
            "Regex Mode 예시\n\n"
            "foo\\w*,bar\n"
            "  foo로 시작하는 단어를 치환합니다. 예: foo, foobar.\n\n"
            "\\w*foo,bar\n"
            "  foo로 끝나는 단어를 치환합니다. 예: myfoo.\n\n"
            "fo.*o,bar\n"
            "  fo로 시작하고 임의의 문자열 뒤 o로 끝나는 텍스트를 치환합니다.\n\n"
            "^foo.*,,delete-line\n"
            "  foo로 시작하는 라인을 삭제합니다.\n\n"
            ".*foo$,,delete-line\n"
            "  foo로 끝나는 라인을 삭제합니다.\n\n"
            "Regex 기호\n"
            "- . : 임의의 문자 1개\n"
            "- * : 앞 패턴이 0번 이상 반복\n"
            "- \\w : 영문자, 숫자, 밑줄\n"
            "- ^ : 시작 위치\n"
            "- $ : 끝 위치"
        )

    def on_browse(self):
        files = filedialog.askopenfilenames(filetypes=[("All Files", "*.*"), ("Text Files", "*.txt")])
        self._add_files(files, source="Browse Files")
        self.update_src_list()

    def on_clear(self):
        self.file_listbox.delete(0, tk.END)
        self.file_cache.clear()
        self.file_encoding_cache.clear()
        self._clear_cached_file_derivatives()
        self.delete_line_selection_overrides.clear()
        self.log("File list cleared")
        self.update_src_list()

    def delete_selected(self, event):
        for i in reversed(self.file_listbox.curselection()):
            removed = self.file_listbox.get(i)
            self.file_listbox.delete(i)
            self.file_cache.pop(removed, None)
            self.file_encoding_cache.pop(removed, None)
            self._clear_cached_file_derivatives(removed)
            file_key = os.path.normcase(os.path.abspath(removed))
            self.delete_line_selection_overrides = {
                key: selected
                for key, selected in self.delete_line_selection_overrides.items()
                if key[0] != file_key
            }
            self.log(f"File removed: {os.path.basename(removed)}")
        self.update_src_list()
        return "break"

    def on_files_dropped(self, event):
        dropped = self.master.tk.splitlist(event.data)
        self._add_files(dropped, source="Drop Files")
        self.update_src_list()

    def on_mapping_modified(self, event):
        if self.map_text.edit_modified():
            self.map_text.edit_modified(False)
            self.delete_line_selection_overrides.clear()
            self._highlight_mapping()
            self.update_src_list()

    def on_mapping_key_release(self, event):
        if event.keysym in {
            "BackSpace",
            "Delete",
            "Left",
            "Right",
            "Up",
            "Down",
            "Home",
            "End",
            "Prior",
            "Next",
            "Escape",
            "Return",
        }:
            return
        if not event.char:
            return
        self._autocomplete_delete_line_mode()

    def accept_mapping_autocomplete(self, event=None):
        ranges = self.map_text.tag_ranges(tk.SEL)
        if not ranges:
            return None
        self.map_text.mark_set(tk.INSERT, ranges[-1])
        self.map_text.tag_remove(tk.SEL, "1.0", tk.END)
        return "break"

    def _highlight_mapping(self):
        self.map_text.tag_remove("dup", "1.0", tk.END)
        self.map_text.tag_remove("same", "1.0", tk.END)
        self.map_text.tag_remove("csv_err", "1.0", tk.END)
        self.map_text.tag_remove("regex_err", "1.0", tk.END)
        self.map_text.tag_remove("mode_err", "1.0", tk.END)
        lines = self.map_text.get("1.0", "end-1c").splitlines()
        src_line_map: dict[str, list[int]] = {}
        duplicate_lines: set[int] = set()
        same_lines: list[int] = []
        csv_err_lines: list[int] = []
        regex_err_lines: list[int] = []
        mode_err_lines: list[int] = []
        regex = self.regex_var.get()
        flags = (0 if self.case_var.get() else re.IGNORECASE)

        for i, ln in enumerate(lines, start=1):
            stripped = ln.strip()
            if not stripped or stripped.startswith("#"):
                continue
            try:
                mapping = self._parse_mapping_row(ln)
            except csv.Error:
                csv_err_lines.append(i)
                self.map_text.tag_add("csv_err", f"{i}.0", f"{i}.end")
                continue

            if not mapping:
                continue

            src = self._mapping_src(mapping)
            dst = self._mapping_dst(mapping)
            mode = self._mapping_mode(mapping)
            if mode == self.MAP_MODE_INVALID:
                mode_err_lines.append(i)
                self.map_text.tag_add("mode_err", f"{i}.0", f"{i}.end")
            if src:
                src_line_map.setdefault(src, []).append(i)
                if regex:
                    try:
                        re.compile(src, flags)
                    except re.error:
                        regex_err_lines.append(i)
                        self.map_text.tag_add("regex_err", f"{i}.0", f"{i}.end")
            if mode == self.MAP_MODE_REPLACE and src and dst and src == dst:
                same_lines.append(i)
                self.map_text.tag_add("same", f"{i}.0", f"{i}.end")

        for line_list in src_line_map.values():
            if len(line_list) > 1:
                for i in line_list:
                    duplicate_lines.add(i)
                    self.map_text.tag_add("dup", f"{i}.0", f"{i}.end")

        def short_lines(nums):
            if not nums:
                return ""
            ordered = sorted(set(nums))
            shown = ordered[:8]
            tail = "..." if len(ordered) > 8 else ""
            return ",".join(str(n) for n in shown) + tail

        issues = []
        if duplicate_lines:
            issues.append(f"duplicate src lines [{short_lines(duplicate_lines)}]")
        if same_lines:
            issues.append(f"same src/dst lines [{short_lines(same_lines)}]")
        if csv_err_lines:
            issues.append(f"CSV parse error lines [{short_lines(csv_err_lines)}]")
        if regex_err_lines:
            issues.append(f"invalid regex lines [{short_lines(regex_err_lines)}]")
        if mode_err_lines:
            issues.append(f"invalid mode lines [{short_lines(mode_err_lines)}]")

        if issues:
            self.mapping_issue_var.set("Mapping issues: " + " | ".join(issues))
        else:
            self.mapping_issue_var.set("Mapping issues: none")

    def load_session(self):
        if SESSION_FILE.exists():
            try:
                data = json.loads(SESSION_FILE.read_text(encoding="utf-8"))
                self._add_files(data.get("files", []), source="Session", log_result=False)
                self.map_text.insert("1.0", data.get("mapping", ""))
                loaded_context_lines = int(data.get("context_lines", 0))
                self.context_lines_var.set(max(0, min(30, loaded_context_lines)))
                self.context_chars_var.set(int(data.get("context_chars", self.CONTEXT_CHARS_MAX)))
                self.context_line_mode_var.set(
                    self._normalize_context_line_mode(data.get("context_line_mode", self.CONTEXT_LINE_MODE_BOTH))
                )
                self.encoding_mode = self._normalize_encoding_mode(data.get("encoding_mode", self.ENCODING_AUTO))
                self.encoding_var.set(self.encoding_mode)
                self.backup_policy_var.set(
                    self._normalize_backup_policy(data.get("backup_policy", self.BACKUP_SIDECAR))
                )
                self._highlight_mapping()
            except Exception:
                pass

    def save_session(self):
        data = {
            "files": list(self.file_listbox.get(0, tk.END)),
            "mapping": self.map_text.get("1.0", tk.END).rstrip("\n"),
            "context_lines": int(self.context_lines_var.get()),
            "context_chars": int(self.context_chars_var.get()),
            "context_line_mode": self._normalize_context_line_mode(self.context_line_mode_var.get()),
            "encoding_mode": self._normalize_encoding_mode(self.encoding_var.get()),
            "backup_policy": self._normalize_backup_policy(self.backup_policy_var.get()),
        }
        try:
            SESSION_FILE.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception:
            pass

    def on_close(self):
        self.save_session()
        self.master.destroy()

    def update_src_list(self):
        prev_sel = self.src_listbox.curselection()
        self.mapping_pairs.clear()
        for ln in self.map_text.get("1.0", "end-1c").splitlines():
            stripped = ln.strip()
            if not stripped or stripped.startswith("#"):
                continue
            try:
                mapping = self._parse_mapping_row(ln)
            except csv.Error:
                continue
            if mapping:
                self.mapping_pairs.append(mapping)
        self.src_listbox.delete(0, tk.END)
        self.src_listbox.insert(tk.END, "All mappings")
        for mapping in self.mapping_pairs:
            self.src_listbox.insert(tk.END, self._format_mapping_list_label(mapping))
        if prev_sel and prev_sel[0] < self.src_listbox.size():
            self.src_listbox.selection_set(prev_sel[0])
        else:
            self.src_listbox.selection_set(0)
        self.schedule_preview()
        self._refresh_action_state()

    # ────────────────────── 프리뷰 (백그라운드 계산 + 한 번에 insert) ────────────────────── #
    def update_result(self):
        self.preview_seq += 1
        seq = self.preview_seq

        files = self._get_preview_files()
        if not files or not self.mapping_pairs:
            self._pv_text = None
            self._pv_src_ranges = []
            self._pv_src_starts = []
            self._pv_line_starts = []
            self._pv_delete_line_line_keys = {}
            self._set_file_shortcuts([])
            self._set_preview_output("No preview available. Add files and mappings.\n")
            self.preview_status_label.config(text="Preview idle.")
            return
        files = files[:self.MAX_PREVIEW_FILES]

        idx_sel = self.src_listbox.curselection()
        idx = idx_sel[0] if idx_sel else 0
        regex = self.regex_var.get()
        case = self.case_var.get()
        flags = (0 if case else re.IGNORECASE)  # 미리보기 전용
        ctx_chars = self.context_chars_var.get()
        ctx_lines = self.context_lines_var.get()
        show_above, show_below = self._get_context_line_visibility()
        if ctx_lines <= 0:
            show_above = False
            show_below = False
        targets = self.mapping_pairs if idx == 0 else [self.mapping_pairs[idx - 1]]
        if not targets:
            self._set_file_shortcuts([])
            self._set_preview_output("No preview target selected.\n")
            self.preview_status_label.config(text="Preview idle.")
            return

        self.preview_status_label.config(text="Searching...")
        self._set_file_shortcuts([])
        self._pv_delete_line_line_keys = {}
        self._set_preview_output("Rendering preview...\n")

        if self.preview_thread and self.preview_thread.is_alive():
            pass  # 기존 작업은 seq 불일치로 폐기

        def worker():
            try:
                text_out, src_ranges, truncated_by_matches = self._build_preview_grouped_text_and_ranges(
                    files, targets, regex, case, flags, ctx_lines, ctx_chars, show_above, show_below, seq
                )
                match_count = len(src_ranges)
                text_out, src_ranges, truncated_by_size = self._truncate_preview_payload(text_out, src_ranges)
                text_out, src_ranges, file_shortcuts = self._add_file_summary_and_shortcuts(
                    files, targets, text_out, src_ranges
                )
                line_starts = self._compute_line_starts(text_out)
            except Exception as e:
                text_out, src_ranges, line_starts = f"[Preview error] {e}\n", [], [0]
                match_count = 0
                truncated_by_matches = False
                truncated_by_size = False
                file_shortcuts = []

            def apply_if_current():
                if seq != self.preview_seq:
                    return
                # 결과 저장
                self._pv_text = text_out
                self._pv_src_ranges = src_ranges
                self._pv_src_starts = [a for a, _ in src_ranges]
                self._pv_line_starts = line_starts
                self._rebuild_delete_line_preview_index(files, targets, text_out, src_ranges, line_starts)

                # UI 반영 (한 번에 insert)
                self._set_preview_output(text_out)
                self._apply_delete_line_selection_tags()
                self._set_file_shortcuts(file_shortcuts)
                status = f"Done. {match_count} matches (grouped; visible highlighting)."
                if truncated_by_matches or truncated_by_size:
                    status += " Preview truncated."
                selected_count, total_count = self._delete_line_selection_counts()
                if total_count:
                    status += f" Delete-line selected: {selected_count}/{total_count}. Click rows to toggle."
                self.preview_status_label.config(text=status)

                # 첫 하이라이트 도색
                self._schedule_visible_highlight(immediate=True)

            self.master.after(0, apply_if_current)

        self.preview_thread = threading.Thread(target=worker, daemon=True)
        self.preview_thread.start()

    def _truncate_preview_payload(self, text: str, ranges: list[tuple[int, int]]):
        max_chars = self.MAX_PREVIEW_TEXT_CHARS
        if len(text) <= max_chars:
            return text, ranges, False

        cut = text.rfind("\n", 0, max_chars)
        if cut <= 0:
            cut = max_chars
        note = "\n[Preview truncated: output too large]\n"
        clipped_text = text[:cut] + note

        clipped_ranges = []
        for a, b in ranges:
            if a >= cut:
                break
            if b <= cut:
                clipped_ranges.append((a, b))
            elif b > cut:
                clipped_ranges.append((a, cut))
        return clipped_text, clipped_ranges, True

    def _build_preview_summary(self, targets, counts, capped):
        parts = []
        for i, mapping in enumerate(targets):
            suffix = "+" if i < len(capped) and capped[i] else ""
            parts.append(f"{self._format_mapping_summary_label(mapping)}:{counts[i]}{suffix}")
        head = "Summary: " + ", ".join(parts)
        if any(capped):
            return head + "\n(+ means more matches exist)\n\n"
        return head + "\n\n"

    @staticmethod
    def _split_preview_summary_block(text: str):
        if not text.startswith("Summary: "):
            return "", text
        cut = text.find("\n\n")
        if cut == -1:
            return "", text
        head_len = cut + 2
        return text[:head_len], text[head_len:]

    def _build_multi_literal_small_target_fast(
        self, files, targets, case, ctx_lines, ctx_chars, show_above, show_below, L, colon_sp, nl, arrow, seq
    ):
        N = len(targets)
        per_target_limit = max(1, self.MAX_PREVIEW_MATCHES // max(1, N))
        blocks = [""] * N
        ranges_per_t = [[] for _ in range(N)]
        shown_total = [0] * N
        capped = [False] * N
        truncated = False

        for k, mapping in enumerate(targets):
            if seq != self.preview_seq:
                break
            s = self._mapping_src(mapping)
            if not s:
                continue
            t_text, t_ranges, t_trunc = self._build_single_literal(
                files, mapping, case, ctx_lines, ctx_chars, show_above, show_below, L, colon_sp, nl, arrow, seq,
                max_matches_limit=per_target_limit
            )
            _, block = self._split_preview_summary_block(t_text)
            shift = len(t_text) - len(block)
            if shift:
                adj = []
                for a, b in t_ranges:
                    aa = a - shift
                    bb = b - shift
                    if bb > 0:
                        adj.append((max(0, aa), bb))
                t_ranges = adj
            blocks[k] = block
            ranges_per_t[k] = t_ranges
            shown_total[k] = len(t_ranges)
            capped[k] = shown_total[k] >= per_target_limit
            truncated = truncated or t_trunc

        summary = self._build_preview_summary(targets, shown_total, capped)
        combined = [summary]
        combined_ranges = []
        offset = len(summary)
        for k in range(N):
            block = blocks[k]
            if not block:
                continue
            combined.append(block)
            for a, b in ranges_per_t[k]:
                combined_ranges.append((a + offset, b + offset))
            offset += len(block)
        return ("".join(combined), combined_ranges, truncated or any(capped))

    def _add_file_summary_and_shortcuts(self, files, targets, text, ranges):
        if not files:
            return text, ranges, []

        header_re = re.compile(r"^([^:\r\n]+): '(.*)' -> '(.*)'$")
        count_re = re.compile(r"^Preview matches:\s*(\d+)\+?$")

        # (basename, src, dst, header_offset, file_match_count)
        sections: list[tuple[str, str, str, int, int]] = []
        current_base = None
        current_src = None
        current_dst = None
        current_offset = None
        offset = 0
        for line in text.splitlines(True):
            stripped = line.rstrip("\r\n")
            hm = header_re.match(stripped)
            if hm:
                current_base = hm.group(1)
                current_src = hm.group(2)
                current_dst = hm.group(3)
                current_offset = offset
            else:
                cm = count_re.match(stripped.strip())
                if (
                    cm
                    and current_base is not None
                    and current_src is not None
                    and current_dst is not None
                    and current_offset is not None
                ):
                    sections.append((current_base, current_src, current_dst, current_offset, int(cm.group(1))))
                    current_base = None
                    current_src = None
                    current_dst = None
                    current_offset = None
            offset += len(line)

        file_bases = [os.path.basename(f) for f in files]
        counts_per_file = [0] * len(files)
        counts_per_file_by_target = [[0] * len(targets) for _ in files]
        first_offsets_per_file: list[int | None] = [None] * len(files)
        first_offsets_per_file_target: list[list[int | None]] = [[None] * len(targets) for _ in files]
        target_key_to_idx: dict[tuple[str, str], int] = {}
        for ti, mapping in enumerate(targets):
            target_key_to_idx.setdefault((self._mapping_src(mapping), self._mapping_preview_dst(mapping)), ti)
        cursor = -1

        for base, src, dst, hdr_off, mcnt in sections:
            idx = None
            for i in range(cursor + 1, len(file_bases)):
                if file_bases[i] == base:
                    idx = i
                    break
            if idx is None:
                for i in range(len(file_bases)):
                    if file_bases[i] == base:
                        idx = i
                        break
            if idx is None:
                continue
            counts_per_file[idx] += mcnt
            t_idx = target_key_to_idx.get((src, dst))
            if t_idx is None:
                for j, mapping in enumerate(targets):
                    if self._mapping_src(mapping) == src:
                        t_idx = j
                        break
            if t_idx is not None:
                counts_per_file_by_target[idx][t_idx] += mcnt
                if first_offsets_per_file_target[idx][t_idx] is None:
                    first_offsets_per_file_target[idx][t_idx] = hdr_off
            if first_offsets_per_file[idx] is None:
                first_offsets_per_file[idx] = hdr_off
            cursor = idx

        prefix = ""
        if len(files) > 1:
            lines = ["Files Summary (all selected input files):"]
            detail_limit = 12
            for i, f in enumerate(files, start=1):
                base = os.path.basename(f)
                total = counts_per_file[i - 1]
                if targets:
                    shown = min(len(targets), detail_limit)
                    detail = [
                        f"{self._format_mapping_summary_label(targets[j])}:{counts_per_file_by_target[i - 1][j]}"
                        for j in range(shown)
                    ]
                    if len(targets) > detail_limit:
                        detail.append(f"...+{len(targets) - detail_limit}")
                    lines.append(f"  [{i}] {base}: {total} matches ({', '.join(detail)})")
                else:
                    lines.append(f"  [{i}] {base}: {total} matches")
            lines.append("Use 'Result Navigator' to jump by file/mapping.")
            lines.append("")
            prefix = "\n".join(lines) + "\n"

        shift = len(prefix)
        if shift:
            text = prefix + text
            ranges = [(a + shift, b + shift) for a, b in ranges]

        nav_items: list[tuple[str, list[tuple[str, int | None]]]] = []
        for i, f in enumerate(files, start=1):
            base = os.path.basename(f)
            cnt = counts_per_file[i - 1]
            file_label = f"{i}. {base} ({cnt})"
            mapping_items: list[tuple[str, int | None]] = []
            off = first_offsets_per_file[i - 1]
            mapping_items.append(("All mappings", (off + shift) if off is not None else None))
            for j, mapping in enumerate(targets):
                mcnt = counts_per_file_by_target[i - 1][j]
                map_label = self._format_mapping_nav_label(j + 1, mapping, mcnt)
                moff = first_offsets_per_file_target[i - 1][j]
                mapping_items.append((map_label, (moff + shift) if moff is not None else None))
            nav_items.append((file_label, mapping_items))

        return text, ranges, nav_items

    # === 핵심: 단어별 섹션 분리 + 고속 경로(리터럴 다중 패턴은 합성 정규식) ===
    def _build_preview_grouped_text_and_ranges(
        self, files, targets, regex, case, flags, ctx_lines, ctx_chars, show_above, show_below, seq
    ):
        """
        각 타겟(단어)마다 별도의 버퍼에 결과를 쌓고, 마지막에 섹션 순서대로 이어 붙여 반환.
        반환: (combined_text, combined_src_ranges)
        """
        # 상수 로컬화
        L = "  L"; colon_sp = ": "; nl = "\n"; arrow = " -> "

        # 1) 단일 타겟 + 리터럴 + 개행 없음: 초고속 경로 (그대로 사용)
        if (
            len(targets) == 1
            and not regex
            and "\n" not in self._mapping_src(targets[0])
            and "\r" not in self._mapping_src(targets[0])
        ):
            text, ranges, truncated = self._build_single_literal(
                files, targets[0], case, ctx_lines, ctx_chars, show_above, show_below, L, colon_sp, nl, arrow, seq
            )
            return text, ranges, truncated

        # 2) 다중 타겟이고 모두 리터럴(+개행없음)인 경우: 합성 정규식 한 번으로 전부 찾기
        all_literal = (not regex) and all(
            ("\n" not in self._mapping_src(mapping) and "\r" not in self._mapping_src(mapping))
            for mapping in targets
        )
        if all_literal and targets:
            # 소수 타겟(예: 2~6개)은 단일 고속 경로를 타겟별로 재사용하는 편이 훨씬 빠름.
            if len(targets) <= 6:
                return self._build_multi_literal_small_target_fast(
                    files, targets, case, ctx_lines, ctx_chars, show_above, show_below, L, colon_sp, nl, arrow, seq
                )

            # 그룹 이름 g0, g1, ...
            parts = []
            for i, mapping in enumerate(targets):
                s = self._mapping_src(mapping)
                if s == "":
                    continue  # 빈 패턴은 스킵
                parts.append(f"(?P<g{i}>{re.escape(s)})")
            if not parts:
                return "", [], False
            patt = re.compile("|".join(parts), flags)

            # 섹션별 버퍼/오프셋/범위
            N = len(targets)
            bufs = [io.StringIO() for _ in range(N)]
            pos = [0] * N
            ranges_per_t = [[] for _ in range(N)]
            per_target_limit = max(1, self.MAX_PREVIEW_MATCHES // max(1, N))
            shown_total = [0] * N
            capped = [False] * N
            stop_early = False
            truncated = False

            for f in files:
                if seq != self.preview_seq or stop_early:
                    break
                basename = os.path.basename(f)
                # 파일별 헤더/카운트/후행라인 관리(타겟별)
                printed_header = [False] * N
                cnt = [0] * N
                post_remain = [0] * N
                last_printed_line = [None] * N

                # 선행 문맥 라인 저장(공유)
                prev_lines = deque(maxlen=max(0, ctx_lines)) if show_above else None

                fh = self._open_text_reader(f)

                with fh:
                    for ln_no, line in enumerate(fh, 1):
                        if seq != self.preview_seq or stop_early:
                            break
                        line = line.rstrip("\r\n")

                        # 후행 문맥: 타겟별로 출력
                        if show_below:
                            s1 = f"{L}{ln_no}{colon_sp}{line}{nl}"
                            for k in range(N):
                                if post_remain[k] > 0:
                                    prev_ln = last_printed_line[k]
                                    if prev_ln is not None and ln_no > prev_ln + 1:
                                        bufs[k].write(nl); pos[k] += len(nl)
                                    bufs[k].write(s1); pos[k] += len(s1)
                                    last_printed_line[k] = ln_no
                                    post_remain[k] -= 1

                        # 매치 탐색(합성 패턴 1회)
                        for m in patt.finditer(line if case else line):
                            # 어떤 타겟이 맞았는지
                            g = m.lastgroup
                            if not g: 
                                continue
                            k = int(g[1:])  # g0 -> 0
                            mapping = targets[k]
                            s = self._mapping_src(mapping)
                            d = self._mapping_preview_dst(mapping)
                            if capped[k]:
                                continue
                            # 파일 헤더(해당 타겟에 대해 이 파일에서 최초)
                            if not printed_header[k]:
                                h = f"{basename}: '{s}' -> '{d}'{nl}"
                                bufs[k].write(h); pos[k] += len(h)
                                printed_header[k] = True

                            # 선행 문맥 (타겟별 섹션에 출력)
                            if show_above and prev_lines:
                                base_ln = ln_no - len(prev_lines)
                                for i, pl in enumerate(prev_lines, start=base_ln):
                                    prev_ln = last_printed_line[k]
                                    if prev_ln is not None and i > prev_ln + 1:
                                        bufs[k].write(nl); pos[k] += len(nl)
                                    s2 = f"{L}{i}{colon_sp}{pl}{nl}"
                                    bufs[k].write(s2); pos[k] += len(s2)
                                    last_printed_line[k] = i

                            # 매치 라인
                            pre = line[max(0, m.start()-ctx_chars):m.start()]
                            snippet = line[m.start():m.end()]
                            post = line[m.end():m.end()+ctx_chars]

                            prev_ln = last_printed_line[k]
                            if ctx_lines and prev_ln is not None and ln_no > prev_ln + 1:
                                bufs[k].write(nl); pos[k] += len(nl)
                            head = f"{L}{ln_no}{colon_sp}"
                            bufs[k].write(head); pos[k] += len(head)
                            if pre:
                                bufs[k].write(pre); pos[k] += len(pre)

                            a = pos[k]
                            if snippet:
                                bufs[k].write(snippet); pos[k] += len(snippet)
                            b = pos[k]
                            ranges_per_t[k].append((a, b))

                            if post:
                                bufs[k].write(post); pos[k] += len(post)

                            if d:
                                bufs[k].write(arrow); pos[k] += len(arrow)
                                if pre:
                                    bufs[k].write(pre); pos[k] += len(pre)
                                bufs[k].write(d); pos[k] += len(d)
                                if post:
                                    bufs[k].write(post); pos[k] += len(post)

                            bufs[k].write(nl); pos[k] += 1
                            last_printed_line[k] = ln_no
                            cnt[k] += 1
                            shown_total[k] += 1
                            if show_below:
                                post_remain[k] = max(post_remain[k], ctx_lines)
                            if shown_total[k] >= per_target_limit:
                                capped[k] = True

                        if all(capped):
                            stop_early = True
                            truncated = True
                            break

                        if show_above:
                            prev_lines.append(line)

                # 파일별 summary
                for k in range(N):
                    if printed_header[k]:
                        tail = f"  Preview matches: {cnt[k]}{nl}{nl}"
                        bufs[k].write(tail); pos[k] += len(tail)

            # 섹션 순서대로 병합
            summary = self._build_preview_summary(targets, shown_total, capped)
            combined = [summary]
            combined_ranges = []
            offset = len(summary)
            for k in range(N):
                block = bufs[k].getvalue()
                if not block:
                    continue
                combined.append(block)
                # 범위 오프셋 보정
                for a, b in ranges_per_t[k]:
                    combined_ranges.append((a + offset, b + offset))
                offset += len(block)

            return ("".join(combined), combined_ranges, truncated or any(capped))

        # 3) 일반 경로(정규식 포함): 라인 1패스 + 타겟별 버퍼에 분배
        compiled = [
            (
                re.compile(self._mapping_src(mapping) if regex else re.escape(self._mapping_src(mapping)), flags),
                self._mapping_src(mapping),
                self._mapping_preview_dst(mapping),
            )
            for mapping in targets
        ]

        N = len(targets)
        bufs = [io.StringIO() for _ in range(N)]
        pos = [0] * N
        ranges_per_t = [[] for _ in range(N)]
        per_target_limit = max(1, self.MAX_PREVIEW_MATCHES // max(1, N))
        shown_total = [0] * N
        capped = [False] * N
        stop_early = False
        truncated = False

        for f in files:
            if seq != self.preview_seq or stop_early:
                break
            basename = os.path.basename(f)
            printed_header = [False] * N
            cnt = [0] * N
            post_remain = [0] * N
            last_printed_line = [None] * N
            prev_lines = deque(maxlen=max(0, ctx_lines)) if show_above else None

            fh = self._open_text_reader(f)

            with fh:
                for ln_no, line in enumerate(fh, 1):
                    if seq != self.preview_seq or stop_early:
                        break
                    line = line.rstrip("\r\n")

                    # 후행 문맥
                    if show_below:
                        s1 = f"{L}{ln_no}{colon_sp}{line}{nl}"
                        for k in range(N):
                            if post_remain[k] > 0:
                                prev_ln = last_printed_line[k]
                                if prev_ln is not None and ln_no > prev_ln + 1:
                                    bufs[k].write(nl); pos[k] += len(nl)
                                bufs[k].write(s1); pos[k] += len(s1)
                                last_printed_line[k] = ln_no
                                post_remain[k] -= 1

                    matched_any = False
                    for k, (patt, s, d) in enumerate(compiled):
                        if capped[k]:
                            continue
                        for m in patt.finditer(line):
                            if not printed_header[k]:
                                h = f"{basename}: '{s}' -> '{d}'{nl}"
                                bufs[k].write(h); pos[k] += len(h)
                                printed_header[k] = True

                            if show_above and prev_lines:
                                base_ln = ln_no - len(prev_lines)
                                for i, pl in enumerate(prev_lines, start=base_ln):
                                    prev_ln = last_printed_line[k]
                                    if prev_ln is not None and i > prev_ln + 1:
                                        bufs[k].write(nl); pos[k] += len(nl)
                                    s2 = f"{L}{i}{colon_sp}{pl}{nl}"
                                    bufs[k].write(s2); pos[k] += len(s2)
                                    last_printed_line[k] = i

                            pre = line[max(0, m.start()-ctx_chars):m.start()]
                            snippet = m.group()
                            post = line[m.end():m.end()+ctx_chars]

                            prev_ln = last_printed_line[k]
                            if ctx_lines and prev_ln is not None and ln_no > prev_ln + 1:
                                bufs[k].write(nl); pos[k] += len(nl)
                            head = f"{L}{ln_no}{colon_sp}"
                            bufs[k].write(head); pos[k] += len(head)
                            if pre:
                                bufs[k].write(pre); pos[k] += len(pre)

                            a = pos[k]
                            if snippet:
                                bufs[k].write(snippet); pos[k] += len(snippet)
                            b = pos[k]
                            ranges_per_t[k].append((a, b))

                            if post:
                                bufs[k].write(post); pos[k] += len(post)

                            if d:
                                bufs[k].write(arrow); pos[k] += len(arrow)
                                if pre:
                                    bufs[k].write(pre); pos[k] += len(pre)
                                bufs[k].write(d); pos[k] += len(d)
                                if post:
                                    bufs[k].write(post); pos[k] += len(post)

                            bufs[k].write(nl); pos[k] += 1
                            last_printed_line[k] = ln_no
                            cnt[k] += 1
                            shown_total[k] += 1
                            matched_any = True
                            if shown_total[k] >= per_target_limit:
                                capped[k] = True
                                break

                    if all(capped):
                        stop_early = True
                        truncated = True
                        break

                    if matched_any and show_below:
                        for k in range(N):
                            if printed_header[k]:  # 매치가 있었던 타겟만
                                post_remain[k] = max(post_remain[k], ctx_lines)

                    if show_above:
                        prev_lines.append(line)

            for k in range(N):
                if printed_header[k]:
                    tail = f"  Preview matches: {cnt[k]}{nl}{nl}"
                    bufs[k].write(tail); pos[k] += len(tail)

        # 섹션 병합
        summary = self._build_preview_summary(targets, shown_total, capped)
        combined = [summary]
        combined_ranges = []
        offset = len(summary)
        for k in range(N):
            block = bufs[k].getvalue()
            if not block:
                continue
            combined.append(block)
            for a, b in ranges_per_t[k]:
                combined_ranges.append((a + offset, b + offset))
            offset += len(block)

        return ("".join(combined), combined_ranges, truncated or any(capped))

    def _build_single_literal_no_line_context(
        self, files, target, case, ctx_chars, L, colon_sp, nl, arrow, seq, max_matches_limit=None
    ):
        s = self._mapping_src(target)
        d = self._mapping_preview_dst(target)
        s_find = s if case else s.lower()
        s_len = len(s)
        step = s_len if s_len else 1
        header_tmpl = "{}: '{}' -> '{}'\n"

        out = io.StringIO()
        write = out.write
        ranges = []
        pos = 0
        max_matches = max_matches_limit if max_matches_limit is not None else self.MAX_PREVIEW_MATCHES
        build_char_limit = self.MAX_PREVIEW_TEXT_CHARS + 32768
        shown_total = 0
        stop_early = False
        truncated = False

        for f in files:
            if seq != self.preview_seq or stop_early:
                break

            txt = self._get_file_text(f)
            hay = txt if case else self._get_file_lower_text(f, txt)
            txt_len = len(txt)
            line_no = 1
            line_start = 0
            scan_pos = 0

            header_printed = False
            printed = 0
            start = 0
            basename = os.path.basename(f)

            while True:
                if seq != self.preview_seq or stop_early:
                    break
                pos_found = hay.find(s_find, start)
                if pos_found == -1:
                    break

                if pos_found > scan_pos:
                    crossed = txt.count("\n", scan_pos, pos_found)
                    if crossed:
                        line_no += crossed
                        last_nl = txt.rfind("\n", scan_pos, pos_found)
                        line_start = last_nl + 1
                    scan_pos = pos_found

                line_end = txt.find("\n", pos_found)
                if line_end == -1:
                    line_end = txt_len
                if line_end > line_start and txt[line_end - 1] == "\r":
                    line_end -= 1

                if not header_printed:
                    h = header_tmpl.format(basename, s, d)
                    write(h); pos += len(h)
                    header_printed = True

                pre_a = max(line_start, pos_found - ctx_chars)
                post_a = pos_found + s_len
                post_b = min(line_end, post_a + ctx_chars)
                pre = txt[pre_a:pos_found]
                snippet = txt[pos_found:post_a]
                post = txt[post_a:post_b]

                head = f"{L}{line_no}{colon_sp}"
                write(head); pos += len(head)
                if pre:
                    write(pre); pos += len(pre)

                a = pos
                if snippet:
                    write(snippet); pos += len(snippet)
                b = pos
                ranges.append((a, b))

                if post:
                    write(post); pos += len(post)

                if d:
                    write(arrow); pos += len(arrow)
                    if pre:
                        write(pre); pos += len(pre)
                    write(d); pos += len(d)
                    if post:
                        write(post); pos += len(post)

                write(nl); pos += 1

                printed += 1
                shown_total += 1
                if shown_total >= max_matches or pos >= build_char_limit:
                    stop_early = True
                    truncated = True
                    break
                start = pos_found + step
                scan_pos = start

            if header_printed:
                tail = f"  Preview matches: {printed}{nl}{nl}"
                write(tail); pos += len(tail)

        capped = shown_total >= max_matches
        summary = self._build_preview_summary([target], [shown_total], [capped])
        summary_len = len(summary)
        shifted_ranges = [(a + summary_len, b + summary_len) for a, b in ranges]
        return summary + out.getvalue(), shifted_ranges, truncated or capped

    def _build_single_literal_with_line_context(
        self, files, target, case, ctx_lines, ctx_chars, show_above, show_below,
        L, colon_sp, nl, arrow, seq, max_matches_limit=None
    ):
        s = self._mapping_src(target)
        d = self._mapping_preview_dst(target)
        s_find = s if case else s.lower()
        s_len = len(s)
        step = s_len if s_len else 1
        header_tmpl = "{}: '{}' -> '{}'\n"

        out = io.StringIO()
        write = out.write
        ranges = []
        pos = 0
        max_matches = max_matches_limit if max_matches_limit is not None else self.MAX_PREVIEW_MATCHES
        build_char_limit = self.MAX_PREVIEW_TEXT_CHARS + 32768
        shown_total = 0
        stop_early = False
        truncated = False

        for f in files:
            if seq != self.preview_seq or stop_early:
                break

            txt = self._get_file_text(f)
            hay = txt if case else self._get_file_lower_text(f, txt)
            txt_len = len(txt)
            basename = os.path.basename(f)

            header_printed = False
            printed = 0
            last_printed_line = None
            post_until_line = 0
            post_next_line = 0
            post_next_start = 0

            def write_full_line(line_no: int, start_off: int):
                nonlocal pos, last_printed_line
                if start_off >= txt_len:
                    return start_off, False
                raw_end = txt.find("\n", start_off)
                if raw_end == -1:
                    raw_end = txt_len
                end = raw_end
                if end > start_off and txt[end - 1] == "\r":
                    end -= 1
                if last_printed_line is not None and line_no > last_printed_line + 1:
                    write(nl); pos += len(nl)
                s1 = f"{L}{line_no}{colon_sp}{txt[start_off:end]}{nl}"
                write(s1); pos += len(s1)
                last_printed_line = line_no
                next_start = raw_end + 1 if raw_end < txt_len else txt_len + 1
                return next_start, True

            def flush_post_until(limit_line: int):
                nonlocal post_next_line, post_next_start
                if (not show_below) or post_next_line == 0 or post_next_line > limit_line:
                    return
                while post_next_line <= limit_line:
                    post_next_start, ok = write_full_line(post_next_line, post_next_start)
                    if not ok:
                        post_next_line = 0
                        post_next_start = txt_len + 1
                        break
                    post_next_line += 1

            line_no = 1
            line_start = 0
            scan_pos = 0
            start = 0

            grp_line_no = -1
            grp_line_start = 0
            grp_line_end = 0
            grp_line_raw_end = 0
            grp_matches: list[int] = []

            def process_group():
                nonlocal header_printed, printed, shown_total, stop_early, truncated, pos
                nonlocal grp_line_no, grp_line_start, grp_line_end, grp_line_raw_end
                nonlocal post_until_line, post_next_line, post_next_start, last_printed_line

                if not grp_matches:
                    return

                if show_below:
                    flush_post_until(min(post_until_line, grp_line_no))

                for pos_found in grp_matches:
                    if not header_printed:
                        h = header_tmpl.format(basename, s, d)
                        write(h); pos += len(h)
                        header_printed = True

                    if show_above:
                        prev_meta = []
                        prev_no = grp_line_no
                        prev_start = grp_line_start
                        for _ in range(ctx_lines):
                            if prev_no <= 1 or prev_start <= 0:
                                break
                            raw_end = prev_start - 1
                            prev_end = raw_end
                            if prev_end > 0 and txt[prev_end - 1] == "\r":
                                prev_end -= 1
                            prev_nl = txt.rfind("\n", 0, raw_end)
                            prev_start = prev_nl + 1 if prev_nl != -1 else 0
                            prev_no -= 1
                            prev_meta.append((prev_no, prev_start, prev_end))

                        for pno, pstart, pend in reversed(prev_meta):
                            if last_printed_line is not None and pno > last_printed_line + 1:
                                write(nl); pos += len(nl)
                            s2 = f"{L}{pno}{colon_sp}{txt[pstart:pend]}{nl}"
                            write(s2); pos += len(s2)
                            last_printed_line = pno

                    pre_a = max(grp_line_start, pos_found - ctx_chars)
                    post_a = pos_found + s_len
                    post_b = min(grp_line_end, post_a + ctx_chars)
                    pre = txt[pre_a:pos_found]
                    snippet = txt[pos_found:post_a]
                    post = txt[post_a:post_b]

                    if last_printed_line is not None and grp_line_no > last_printed_line + 1:
                        write(nl); pos += len(nl)
                    head = f"{L}{grp_line_no}{colon_sp}"
                    write(head); pos += len(head)
                    if pre:
                        write(pre); pos += len(pre)

                    a = pos
                    if snippet:
                        write(snippet); pos += len(snippet)
                    b = pos
                    ranges.append((a, b))

                    if post:
                        write(post); pos += len(post)

                    if d:
                        write(arrow); pos += len(arrow)
                        if pre:
                            write(pre); pos += len(pre)
                        write(d); pos += len(d)
                        if post:
                            write(post); pos += len(post)

                    write(nl); pos += 1
                    last_printed_line = grp_line_no

                    printed += 1
                    shown_total += 1
                    if show_below:
                        post_until_line = max(post_until_line, grp_line_no + ctx_lines)
                        if post_next_line == 0 or post_next_line < grp_line_no + 1:
                            post_next_line = grp_line_no + 1
                            post_next_start = grp_line_raw_end + 1 if grp_line_raw_end < txt_len else txt_len + 1

                    if shown_total >= max_matches or pos >= build_char_limit:
                        stop_early = True
                        truncated = True
                        break

            while True:
                if seq != self.preview_seq or stop_early:
                    break
                pos_found = hay.find(s_find, start)
                if pos_found == -1:
                    break

                if pos_found > scan_pos:
                    crossed = txt.count("\n", scan_pos, pos_found)
                    if crossed:
                        line_no += crossed
                        last_nl = txt.rfind("\n", scan_pos, pos_found)
                        line_start = last_nl + 1
                    scan_pos = pos_found

                line_raw_end = txt.find("\n", pos_found)
                if line_raw_end == -1:
                    line_raw_end = txt_len
                line_end = line_raw_end
                if line_end > line_start and txt[line_end - 1] == "\r":
                    line_end -= 1

                if grp_line_no == -1:
                    grp_line_no = line_no
                    grp_line_start = line_start
                    grp_line_end = line_end
                    grp_line_raw_end = line_raw_end
                elif line_no != grp_line_no:
                    process_group()
                    grp_matches.clear()
                    if stop_early:
                        break
                    grp_line_no = line_no
                    grp_line_start = line_start
                    grp_line_end = line_end
                    grp_line_raw_end = line_raw_end

                grp_matches.append(pos_found)
                start = pos_found + step
                scan_pos = start

            if not stop_early and grp_line_no != -1 and grp_matches:
                process_group()
                grp_matches.clear()

            if not stop_early and seq == self.preview_seq and show_below:
                flush_post_until(post_until_line)

            if header_printed:
                tail = f"  Preview matches: {printed}{nl}{nl}"
                write(tail); pos += len(tail)

        capped = shown_total >= max_matches
        summary = self._build_preview_summary([target], [shown_total], [capped])
        summary_len = len(summary)
        shifted_ranges = [(a + summary_len, b + summary_len) for a, b in ranges]
        return summary + out.getvalue(), shifted_ranges, truncated or capped

    def _build_single_literal(
        self, files, target, case, ctx_lines, ctx_chars, show_above, show_below,
        L, colon_sp, nl, arrow, seq, max_matches_limit=None
    ):
        """단일 리터럴 고속 경로(그대로)."""
        s = self._mapping_src(target)
        d = self._mapping_preview_dst(target)
        s_find = s if case else s.lower()
        s_len = len(s)
        if s and ("\n" not in s and "\r" not in s):
            if ctx_lines == 0:
                return self._build_single_literal_no_line_context(
                    files, target, case, ctx_chars, L, colon_sp, nl, arrow, seq, max_matches_limit
                )
            return self._build_single_literal_with_line_context(
                files, target, case, ctx_lines, ctx_chars, show_above, show_below,
                L, colon_sp, nl, arrow, seq, max_matches_limit
            )
        header_tmpl = "{}: '{}' -> '{}'\n"

        out = io.StringIO()
        write = out.write
        ranges = []
        pos = 0
        max_matches = max_matches_limit if max_matches_limit is not None else self.MAX_PREVIEW_MATCHES
        build_char_limit = self.MAX_PREVIEW_TEXT_CHARS + 32768
        shown_total = 0
        stop_early = False
        truncated = False

        for f in files:
            if seq != self.preview_seq or stop_early:
                break
            header_printed = False
            printed = 0
            prev_lines = deque(maxlen=max(0, ctx_lines)) if show_above else None
            post_remain = 0
            last_printed_line = None

            fh = self._open_text_reader(f)

            basename = os.path.basename(f)
            with fh:
                for ln_no, line in enumerate(fh, 1):
                    if seq != self.preview_seq or stop_early:
                        break
                    line = line.rstrip("\r\n")
                    hay = line if case else line.lower()

                    if show_below and post_remain > 0:
                        if last_printed_line is not None and ln_no > last_printed_line + 1:
                            write(nl); pos += len(nl)
                        s1 = f"{L}{ln_no}{colon_sp}{line}{nl}"
                        write(s1); pos += len(s1)
                        last_printed_line = ln_no
                        post_remain -= 1

                    start = 0
                    while True:
                        pos_found = hay.find(s_find, start)
                        if pos_found == -1:
                            break

                        if not header_printed:
                            h = header_tmpl.format(basename, s, d)
                            write(h); pos += len(h)
                            header_printed = True

                        if show_above and prev_lines:
                            base_ln = ln_no - len(prev_lines)
                            for i, pl in enumerate(prev_lines, start=base_ln):
                                if last_printed_line is not None and i > last_printed_line + 1:
                                    write(nl); pos += len(nl)
                                s2 = f"{L}{i}{colon_sp}{pl}{nl}"
                                write(s2); pos += len(s2)
                                last_printed_line = i

                        pre = line[max(0, pos_found - ctx_chars):pos_found]
                        snippet = line[pos_found:pos_found + s_len]
                        post = line[pos_found + s_len: pos_found + s_len + ctx_chars]

                        if ctx_lines and last_printed_line is not None and ln_no > last_printed_line + 1:
                            write(nl); pos += len(nl)
                        head = f"{L}{ln_no}{colon_sp}"
                        write(head); pos += len(head)
                        if pre:
                            write(pre); pos += len(pre)

                        a = pos
                        if snippet:
                            write(snippet); pos += len(snippet)
                        b = pos
                        ranges.append((a, b))

                        if post:
                            write(post); pos += len(post)

                        if d:
                            write(arrow); pos += len(arrow)
                            if pre:
                                write(pre); pos += len(pre)
                            write(d); pos += len(d)
                            if post:
                                write(post); pos += len(post)

                        write(nl); pos += 1
                        last_printed_line = ln_no

                        if show_below:
                            post_remain = max(post_remain, ctx_lines)
                        printed += 1
                        shown_total += 1
                        if shown_total >= max_matches or pos >= build_char_limit:
                            stop_early = True
                            truncated = True
                            break
                        start = pos_found + (s_len if s_len else 1)

                    if show_above:
                        prev_lines.append(line)

            if header_printed:
                tail = f"  Preview matches: {printed}{nl}{nl}"
                write(tail); pos += len(tail)

        capped = shown_total >= max_matches
        summary = self._build_preview_summary([target], [shown_total], [capped])
        summary_len = len(summary)
        shifted_ranges = [(a + summary_len, b + summary_len) for a, b in ranges]
        return summary + out.getvalue(), shifted_ranges, truncated or capped

    @staticmethod
    def _compute_line_starts(s: str) -> list[int]:
        starts = [0]
        i = -1
        while True:
            i = s.find("\n", i + 1)
            if i == -1:
                break
            starts.append(i + 1)
        return starts

    # ────────────────────── 보이는 영역만 하이라이트 ────────────────────── #
    def _on_preview_yview(self, first, last):
        self.vsb_preview.set(first, last)
        self._schedule_visible_highlight()

    def _schedule_visible_highlight(self, immediate: bool = False):
        if self.hilite_after_id:
            self.master.after_cancel(self.hilite_after_id)
            self.hilite_after_id = None
        if immediate:
            self._apply_visible_highlight()
        else:
            self.hilite_after_id = self.master.after(self.HILITE_DEBOUNCE_MS, self._apply_visible_highlight)

    def _apply_visible_highlight(self):
        if not self._pv_text or not self._pv_src_ranges or not self._pv_line_starts:
            return

        top_idx = self.preview_text.index("@0,0")
        bot_idx = self.preview_text.index(f"@0,{self.preview_text.winfo_height()}")
        try:
            top_line = int(top_idx.split(".")[0])
            bot_line = int(bot_idx.split(".")[0])
        except Exception:
            return

        ls = self._pv_line_starts
        if top_line < 1:
            top_line = 1
        if bot_line < 1:
            bot_line = 1
        vis_a = ls[top_line - 1] if top_line - 1 < len(ls) else 0
        vis_b = ls[bot_line] if bot_line < len(ls) else len(self._pv_text)

        self.preview_text.tag_remove("highlight_src", f"1.0+{vis_a}c", f"1.0+{vis_b}c")

        starts = self._pv_src_starts
        ranges = self._pv_src_ranges
        if not starts:
            return

        L = bisect.bisect_left(starts, vis_a)
        i = max(0, L - 5)
        while i > 0 and ranges[i][1] > vis_a:
            i -= 1
        args = []
        append = args.append
        end_limit = vis_b
        i2 = i
        while i2 < len(ranges):
            a, b = ranges[i2]
            if a >= end_limit:
                break
            if b > vis_a:
                append(f"1.0+{a}c"); append(f"1.0+{b}c")
            i2 += 1

        if args:
            CHUNK = 2000
            for k in range(0, len(args), CHUNK):
                chunk = args[k:k+CHUNK]
                self.preview_text.tag_add("highlight_src", *chunk)

    # ────────────────────── 치환 ────────────────────── #
    def _compile_patterns_for_replace(self, pairs, regex: bool, flags: int):
        compiled = []
        line_flags = flags & ~re.DOTALL
        for mapping in pairs:
            s = self._mapping_src(mapping)
            d = self._mapping_dst(mapping)
            mode = self._mapping_mode(mapping)
            patt_flags = line_flags if mode == self.MAP_MODE_DELETE_LINE else flags
            patt = re.compile(s if regex else re.escape(s), patt_flags)
            if mode == self.MAP_MODE_DELETE_LINE:
                repl = None
            elif (not regex) and ("\\" not in d):
                repl = d
            else:
                repl = (lambda rep: (lambda m: rep))(d)
            compiled.append((mode, patt, repl, mapping))
        return compiled

    def _delete_lines_matching(self, text: str, pattern, file_path: str, mapping) -> tuple[str, int]:
        kept = []
        removed = 0
        for line_no, line in enumerate(text.splitlines(True), start=1):
            searchable = line.rstrip("\r\n")
            key = self._make_delete_line_selection_key(file_path, mapping, line_no)
            if pattern.search(searchable) and self.delete_line_selection_overrides.get(key, True):
                removed += 1
            else:
                kept.append(line)
        return "".join(kept), removed

    def _make_backup_run_id(self) -> str:
        return f"{time.strftime('%Y%m%d-%H%M%S')}-{int((time.time() % 1) * 1000):03d}"

    def _backup_policy_description(self, policy: str) -> str:
        policy = self._normalize_backup_policy(policy)
        if policy == self.BACKUP_NONE:
            return "Backups will not be created. Undo is unavailable for this run."
        if policy == self.BACKUP_TIMESTAMPED:
            return "Timestamped .bak files will be created next to each source file."
        if policy == self.BACKUP_FOLDER:
            return f"Backups will be stored in {self.BACKUP_DIR_NAME} folders."
        return "Backup files (*.bak) will be created next to each source file."

    def _make_backup_path(self, file_path: str, policy: str, run_id: str) -> str | None:
        policy = self._normalize_backup_policy(policy)
        if policy == self.BACKUP_NONE:
            return None
        src = Path(file_path)
        if policy == self.BACKUP_TIMESTAMPED:
            return str(src.with_name(f"{src.name}.{run_id}.bak"))
        if policy == self.BACKUP_FOLDER:
            return str(src.parent / self.BACKUP_DIR_NAME / run_id / src.name)
        return file_path + ".bak"

    def _create_backup(self, file_path: str, policy: str, run_id: str) -> str | None:
        backup_path = self._make_backup_path(file_path, policy, run_id)
        if backup_path is None:
            return None
        Path(backup_path).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(file_path, backup_path)
        return backup_path

    def start_replace(self):
        if self.is_replacing:
            return

        files = self._get_replace_files()
        pairs = self._get_effective_replace_pairs()
        if not files or not pairs:
            messagebox.showerror("Error", "Provide mappings and files.")
            return

        regex = self.regex_var.get()
        case = self.case_var.get()
        flags = re.DOTALL | (0 if case else re.IGNORECASE)

        if regex:
            for i, mapping in enumerate(pairs, 1):
                s = self._mapping_src(mapping)
                patt_flags = (flags & ~re.DOTALL) if self._mapping_mode(mapping) == self.MAP_MODE_DELETE_LINE else flags
                try:
                    re.compile(s, patt_flags)
                except re.error as ex:
                    messagebox.showerror("Regex Error", f"Invalid regex in mapping #{i}:\n{s}\n\n{ex}")
                    return

        scope_label = "selected files" if self.replace_scope_var.get() == "selected" else "all files"
        delete_line_count = sum(1 for mapping in pairs if self._mapping_mode(mapping) == self.MAP_MODE_DELETE_LINE)
        delete_word_count = sum(1 for mapping in pairs if self._mapping_mode(mapping) == self.MAP_MODE_DELETE_WORD)
        replace_count = len(pairs) - delete_line_count - delete_word_count
        operation_bits = []
        if replace_count:
            operation_bits.append(f"{replace_count} replace")
        if delete_word_count:
            operation_bits.append(f"{delete_word_count} word delete")
        if delete_line_count:
            operation_bits.append(f"{delete_line_count} line delete")
        operation_label = ", ".join(operation_bits)
        backup_policy = self._normalize_backup_policy(self.backup_policy_var.get())
        confirm_message = (
            f"Apply {len(pairs)} mapping(s) ({operation_label}) in {len(files)} {scope_label}?\n"
            f"{self._backup_policy_description(backup_policy)}\n"
            "Files will be saved with the encoding used when they were read."
        )
        if not messagebox.askokcancel("Confirm Replace", confirm_message):
            return

        self.progress.config(maximum=len(files), value=0)
        self.replace_status_label.config(text=f"Running updates in {len(files)} file(s)...")
        self.replace_cancel_event.clear()
        self._set_replace_running(True)
        backup_run_id = self._make_backup_run_id()
        self.replace_thread = threading.Thread(
            target=self.run_replace, args=(files, pairs, regex, case, flags, backup_policy, backup_run_id), daemon=True
        )
        self.replace_thread.start()

    def cancel_replace(self):
        if not self.is_replacing:
            return
        self.replace_cancel_event.set()
        self.cancel_btn.state(["disabled"])
        self.replace_status_label.config(text="Cancel requested. Finishing current file...")

    def run_replace(self, files, pairs, regex, case, flags, backup_policy, backup_run_id):
        self.last_replaced.clear()
        self.last_backup_paths.clear()
        self.last_file_encodings.clear()
        self.total_replacements = 0
        self.file_mapping_changes.clear()

        use_literal_case_sensitive_fastpath = (
            (not regex)
            and case
            and all(self._mapping_mode(mapping) != self.MAP_MODE_DELETE_LINE for mapping in pairs)
        )
        compiled = [] if use_literal_case_sensitive_fastpath else self._compile_patterns_for_replace(pairs, regex, flags)
        cancelled = False
        processed = 0

        for i, f in enumerate(files, 1):
            if self.replace_cancel_event.is_set():
                cancelled = True
                break
            processed = i
            try:
                txt = self._get_file_text(f)
                new = txt
                fm = set()
                file_replacements = 0
                if use_literal_case_sensitive_fastpath:
                    for mapping in pairs:
                        s = self._mapping_src(mapping)
                        d = self._mapping_dst(mapping)
                        cnt = new.count(s)
                        if cnt:
                            new = new.replace(s, d)
                            file_replacements += cnt
                            fm.add(mapping)
                else:
                    for mode, patt, repl, mapping in compiled:
                        if mode == self.MAP_MODE_DELETE_LINE:
                            new, cnt = self._delete_lines_matching(new, patt, f, mapping)
                        else:
                            new, cnt = patt.subn(repl, new)
                        if cnt:
                            file_replacements += cnt
                            fm.add(mapping)
                if new != txt:
                    encoding = self._get_file_encoding(f)
                    backup_path = self._create_backup(f, backup_policy, backup_run_id)
                    self._write_file_text(f, new, encoding)
                    self.file_cache[f] = new
                    self.file_encoding_cache[f] = encoding
                    self._clear_cached_file_derivatives(f)
                    if backup_path:
                        self.last_replaced.append(f)
                        self.last_backup_paths[f] = backup_path
                        self.last_file_encodings[f] = encoding
                    self.file_mapping_changes[f] = fm
                    self.total_replacements += file_replacements
                status = f"{i}/{len(files)} {os.path.basename(f)}"
            except Exception as ex:
                status = f"Error {os.path.basename(f)}: {ex}"
            self.master.after(0, self.update_progress, status, i)

        self.master.after(0, self.reset_after_complete, cancelled, processed, len(files))

    def update_progress(self, status, value):
        self.replace_status_label.config(text=status)
        self.progress["value"] = value

    def reset_after_complete(self, cancelled=False, processed=0, total=0):
        if cancelled:
            self.progress["value"] = processed
            self.replace_status_label.config(text=f"Cancelled at {processed}/{total} files.")
            self.log(f"Cancelled at {processed}/{total} files.")
        else:
            self.progress["value"] = self.progress["maximum"]
            self.replace_status_label.config(
                text=f"Completed. {len(self.file_mapping_changes)} files changed, {self.total_replacements} changes."
            )
            desc = ", ".join(
                self._format_mapping_log_label(mapping)
                for f in self.file_mapping_changes
                for mapping in self.file_mapping_changes[f]
            ) or "(none)"
            self.log(
                f"Completed: {len(self.file_mapping_changes)} files, {self.total_replacements} changes. "
                f"Mappings: {desc}"
            )

        self._set_replace_running(False)

    def undo_replace(self):
        if self.is_replacing:
            return
        if not self.last_replaced:
            self.replace_status_label.config(text="No replacement history to restore.")
            return

        for f in self.last_replaced:
            bak = self.last_backup_paths.get(f, f + ".bak")
            if os.path.exists(bak):
                shutil.copy2(bak, f)
                encoding = self.last_file_encodings.get(f)
                if encoding:
                    txt = Path(f).read_bytes().decode(encoding)
                else:
                    txt, encoding = self._read_file_with_encoding(f)
                self.file_cache[f] = txt
                self.file_encoding_cache[f] = encoding
                self._clear_cached_file_derivatives(f)
            fm = self.file_mapping_changes.get(f, set())
            desc = ", ".join(self._format_mapping_log_label(mapping) for mapping in fm)
            self.log(f"Restored {os.path.basename(f)}; Mappings: {desc}")

        self.last_replaced.clear()
        self.last_backup_paths.clear()
        self.last_file_encodings.clear()
        self.file_mapping_changes.clear()
        self.total_replacements = 0
        self.replace_status_label.config(text="Undo completed.")
        self._refresh_action_state()

    def copy_preview(self):
        txt = self.preview_text.get("1.0", tk.END)
        self.master.clipboard_clear()
        self.master.clipboard_append(txt)
        self.log("Preview copied to clipboard")
        self.preview_status_label.config(text="Preview copied to clipboard.")

    def log(self, message):
        ts = time.strftime("%H:%M:%S")
        self.log_area.configure(state="normal")
        self.log_area.insert(tk.END, f"{ts} - {message}\n")
        self.log_area.configure(state="disabled")
        self.log_area.see(tk.END)


if __name__ == "__main__":
    if DND_TYPE == 'tkinterdnd2':
        root = TkinterDnD.Tk()
    else:
        root = tk.Tk()
    if DND_TYPE == 'tkdnd':
        TkDND(root)
    WordReplacerGUI(root)
    root.mainloop()
