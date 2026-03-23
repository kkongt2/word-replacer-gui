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

    def schedule_preview(self):
        if self.preview_after_id:
            self.master.after_cancel(self.preview_after_id)
        self.preview_after_id = self.master.after(self.DEBOUNCE_MS, self.update_result)

    def __init__(self, master):
        self.master = master
        master.title("Word Replacement Tool")
        master.geometry("1000x800")
        master.minsize(900, 640)
        master.configure(bg="#2e3440")
        master.protocol("WM_DELETE_WINDOW", self.on_close)

        # ── 상태 ──
        self.preview_after_id = None
        self.hilite_after_id = None
        self.preview_seq = 0
        self.preview_thread = None
        self.replace_thread = None
        self.replace_cancel_event = threading.Event()
        self.is_replacing = False
        self.mapping_pairs: list[tuple[str, str]] = []
        self.last_replaced: list[str] = []
        self.total_replacements = 0
        self.file_mapping_changes: dict[str, set[tuple[str, str]]] = {}
        self.file_cache: dict[str, str] = {}
        self.file_lower_cache: dict[str, str] = {}
        self.replace_scope_var = tk.StringVar(value="all")

        # 프리뷰 결과(텍스트/매치구간/라인시작오프셋)
        self._pv_text: str | None = None
        self._pv_src_ranges: list[tuple[int, int]] = []  # (start_off, end_off) in combined text
        self._pv_src_starts: list[int] = []              # starts for bisect
        self._pv_line_starts: list[int] = []             # 각 라인의 시작 문자 오프셋
        self._pv_jump_nav: dict[str, dict[str, int | None]] = {}

        self.context_chars_var = tk.IntVar(value=self.CONTEXT_CHARS_MAX)
        self.context_lines_var = tk.IntVar(value=0)
        self.mapping_issue_var = tk.StringVar(value="Mapping issues: none")
        self.file_jump_var = tk.StringVar(value="")
        self.mapping_jump_var = tk.StringVar(value="")

        # ── 스타일 ──
        style = ttk.Style(master)
        style.theme_use('clam')
        style.configure('TFrame', background='#2e3440')
        style.configure('TLabel', background='#2e3440', foreground='#ECEFF4', font=('Segoe UI', 10))
        style.configure('TButton', background='#3B4252', foreground='#ECEFF4')
        style.map('TButton', background=[('active', '#4C566A')])
        style.configure('Accent.TButton', background='#4CAF50', foreground='#FFFFFF', font=('Segoe UI', 10, 'bold'))
        style.map('Accent.TButton', background=[('active', '#43A047')])
        style.configure('TCheckbutton', background='#2e3440', foreground='#ECEFF4')
        style.configure('TRadiobutton', background='#2e3440', foreground='#ECEFF4')
        style.configure('Horizontal.TScale', troughcolor='#4C566A', background='#88C0D0')
        style.configure('Vertical.TScrollbar', background='#3B4252', troughcolor='#2e3440', arrowcolor='#ECEFF4')
        style.configure('TPanedwindow', background='#2e3440')
        style.configure('TProgressbar', troughcolor='#000000', background='#4CAF50')
        style.configure('Navigator.TLabelframe', background='#2e3440', bordercolor='#4C566A', borderwidth=1)
        style.configure(
            'Navigator.TLabelframe.Label',
            background='#2e3440', foreground='#88C0D0', font=('Segoe UI', 9, 'bold')
        )

        # ── 레이아웃 ──
        container = ttk.Frame(master, padding=12)
        container.pack(fill=tk.BOTH, expand=True)
        container.rowconfigure(0, weight=3)
        container.rowconfigure(1, weight=1)
        container.rowconfigure(2, weight=0)
        container.rowconfigure(3, weight=0)
        container.columnconfigure(0, weight=1)

        self.paned = ttk.Panedwindow(container, orient=tk.HORIZONTAL)
        self.paned.grid(row=0, column=0, sticky="nsew", pady=(0, 10))
        self._sashes_initialized = False
        self.paned.bind("<Configure>", self._on_paned_configure)

        # 1) 파일 리스트
        file_frame = ttk.Frame(self.paned)
        file_frame.columnconfigure(0, weight=1)
        ttk.Label(file_frame, text="Input Text Files:").grid(row=0, column=0, sticky="w")

        self.file_listbox = tk.Listbox(
            file_frame, selectmode="extended",
            bg="#3B4252", fg="#ECEFF4", selectbackground="#81A1C1", bd=1, relief="solid")
        self.file_listbox.grid(row=1, column=0, sticky="nsew", pady=(5, 0))
        self.file_listbox.bind("<Delete>", self.delete_selected)
        self.file_listbox.bind("<<ListboxSelect>>", self.on_file_selection_changed)

        self.hsb_file = ttk.Scrollbar(file_frame, orient="horizontal", command=self.file_listbox.xview)
        self.hsb_file.grid(row=2, column=0, sticky="we")
        self.vsb_file = ttk.Scrollbar(file_frame, orient="vertical", command=self.file_listbox.yview)
        self.vsb_file.grid(row=1, column=1, sticky="ns", pady=(5, 0))
        self.file_listbox.config(xscrollcommand=self.hsb_file.set, yscrollcommand=self.vsb_file.set)

        if DND_TYPE == 'tkinterdnd2':
            self.file_listbox.drop_target_register(DND_FILES)
            self.file_listbox.dnd_bind('<<Drop>>', self.on_files_dropped)
        elif DND_TYPE == 'tkdnd':
            TkDND(master).bindtarget(self.file_listbox, self.on_files_dropped, 'text/uri-list')

        btn_frame = ttk.Frame(file_frame)
        btn_frame.grid(row=3, column=0, sticky="w", pady=6)
        self.browse_btn = ttk.Button(btn_frame, text="Browse Files", command=self.on_browse)
        self.browse_btn.pack(side="left", padx=5)
        self.clear_btn = ttk.Button(btn_frame, text="Clear List", command=self.on_clear)
        self.clear_btn.pack(side="left", padx=5)
        if DND_TYPE is None:
            dnd_text = "Drag & drop unavailable. Install tkinterdnd2/tkdnd to enable."
        else:
            dnd_text = "Drag & drop enabled."
        self.dnd_hint_label = ttk.Label(file_frame, text=dnd_text, foreground="#88C0D0")
        self.dnd_hint_label.grid(row=4, column=0, sticky="w", pady=(0, 4))

        file_frame.rowconfigure(1, weight=1)
        self.paned.add(file_frame, weight=25)

        # 2) 매핑 창
        map_frame = ttk.Frame(self.paned)
        map_frame.rowconfigure(1, weight=1)
        map_frame.columnconfigure(0, weight=1)
        ttk.Label(map_frame, text="Mapping (src,dst per line):").grid(row=0, column=0, sticky="w")

        self.map_text = tk.Text(map_frame, wrap=tk.NONE, font=("Consolas", 11),
                                bg="#3B4252", fg="#ECEFF4", insertbackground="#ECEFF4", bd=0)
        self.map_text.grid(row=1, column=0, sticky="nsew", pady=(5, 0))

        self.vsb_map = ttk.Scrollbar(map_frame, orient="vertical", command=self.map_text.yview)
        self.vsb_map.grid(row=1, column=1, sticky="ns", pady=(5, 0))
        self.hsb_map = ttk.Scrollbar(map_frame, orient="horizontal", command=self.map_text.xview)
        self.hsb_map.grid(row=2, column=0, sticky="we")
        self.map_text.config(yscrollcommand=self.vsb_map.set, xscrollcommand=self.hsb_map.set)

        self.map_text.tag_configure("dup", background="#BF616A", foreground="#ECEFF4")
        self.map_text.tag_configure("same", background="#7E57C2", foreground="#ECEFF4")
        self.map_text.tag_configure("csv_err", underline=True, foreground="#BF616A")
        self.map_text.tag_configure("regex_err", underline=True, foreground="#EBCB8B")
        self.map_text.bind("<<Modified>>", self.on_mapping_modified)

        opts = ttk.Frame(map_frame)
        opts.grid(row=3, column=0, columnspan=2, sticky="w", pady=(4, 0))
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
            foreground="#EBCB8B"
        )
        self.mapping_issue_label.grid(row=4, column=0, columnspan=2, sticky="we", pady=(4, 0))

        self.paned.add(map_frame, weight=15)

        # 3) 프리뷰 & 컨트롤
        prev_frame = ttk.Frame(self.paned)
        prev_frame.rowconfigure(2, weight=1)
        prev_frame.columnconfigure(0, weight=1)
        ttk.Label(prev_frame, text="Preview Matches:").grid(row=0, column=0, sticky="w")

        self.src_listbox = tk.Listbox(prev_frame, height=5,
                                      bg="#3B4252", fg="#ECEFF4", selectbackground="#81A1C1")
        self.src_listbox.grid(row=1, column=0, sticky="we", pady=(5, 0))
        self.src_listbox.bind("<<ListboxSelect>>", lambda e: self.schedule_preview())
        self.vsb_src = ttk.Scrollbar(prev_frame, orient="vertical", command=self.src_listbox.yview)
        self.vsb_src.grid(row=1, column=1, sticky="ns", pady=(5, 0))
        self.src_listbox.config(yscrollcommand=self.vsb_src.set)

        self.preview_text = tk.Text(prev_frame, wrap=tk.NONE, font=("Consolas", 11),
                                    bg="#3B4252", fg="#ECEFF4", bd=0, state="disabled")
        self.preview_text.grid(row=2, column=0, sticky="nsew", pady=(5, 0))

        # 하이라이트 태그: src만 (속도 이유)
        self.preview_text.tag_configure("highlight_src", background="#ebcb8b", foreground="#2e3440")

        # 스크롤바
        self.vsb_preview = ttk.Scrollbar(prev_frame, orient="vertical", command=self.preview_text.yview)
        self.vsb_preview.grid(row=2, column=1, sticky="ns", pady=(5, 0))
        self.hsb_preview = ttk.Scrollbar(prev_frame, orient="horizontal", command=self.preview_text.xview)
        self.hsb_preview.grid(row=3, column=0, sticky="we")

        # yview 변경을 감지해 보이는 영역만 하이라이트
        self.preview_text.config(yscrollcommand=self._on_preview_yview, xscrollcommand=self.hsb_preview.set)
        self.preview_text.bind("<Configure>", lambda e: self._schedule_visible_highlight())

        act = ttk.Frame(prev_frame)
        act.grid(row=4, column=0, sticky="we", pady=6)
        act_top = ttk.Frame(act)
        act_top.pack(fill="x")
        act_bottom = ttk.Frame(act)
        act_bottom.pack(fill="x", pady=(6, 0))

        ttk.Label(act_top, text="Context lines:", background="#2e3440", foreground="#ECEFF4").pack(
            side="left", padx=(0, 5))
        self.context_lines_spinbox = tk.Spinbox(act_top, from_=0, to=30, textvariable=self.context_lines_var,
                                                width=3, command=self.schedule_preview)
        self.context_lines_spinbox.pack(side="left", padx=(0, 10))
        self.context_lines_spinbox.bind("<KeyRelease>", lambda e: self.schedule_preview())

        ttk.Label(act_top, text="Context chars:", background="#2e3440", foreground="#ECEFF4").pack(
            side="left", padx=(0, 5))
        self.context_chars_scale = ttk.Scale(act_top, from_=0, to=self.CONTEXT_CHARS_MAX, variable=self.context_chars_var,
                                             orient=tk.HORIZONTAL, length=120,
                                             command=lambda v: self.schedule_preview())
        self.context_chars_scale.pack(side="left", padx=(0, 4))
        self.context_chars_label = ttk.Label(act_top, text=str(self.context_chars_var.get()))
        self.context_chars_label.pack(side="left", padx=(0, 12))
        self.context_chars_var.trace_add("write", self.on_context_chars_changed)

        scope_frame = ttk.Frame(act_top)
        scope_frame.pack(side="left", padx=(0, 12))
        ttk.Label(scope_frame, text="Replace scope:").pack(side="left", padx=(0, 4))
        self.scope_selected_rb = ttk.Radiobutton(
            scope_frame, text="Selected", value="selected", variable=self.replace_scope_var,
            command=self._on_replace_scope_changed
        )
        self.scope_selected_rb.pack(side="left", padx=(0, 2))
        self.scope_all_rb = ttk.Radiobutton(
            scope_frame, text="All", value="all", variable=self.replace_scope_var,
            command=self._on_replace_scope_changed
        )
        self.scope_all_rb.pack(side="left")

        nav_frame = ttk.Labelframe(act_top, text="Result Navigator", style="Navigator.TLabelframe")
        nav_frame.pack(side="left", padx=(6, 10))
        ttk.Label(nav_frame, text="File").grid(row=0, column=0, padx=(6, 4), pady=(2, 0), sticky="w")
        ttk.Label(nav_frame, text="Mapping").grid(row=0, column=1, padx=(6, 4), pady=(2, 0), sticky="w")
        self.file_jump_combo = ttk.Combobox(nav_frame, textvariable=self.file_jump_var, state="readonly", width=24)
        self.file_jump_combo.grid(row=1, column=0, padx=(6, 4), pady=(0, 6), sticky="we")
        self.file_jump_combo.bind("<<ComboboxSelected>>", self.on_file_jump_selected)
        self.mapping_jump_combo = ttk.Combobox(
            nav_frame, textvariable=self.mapping_jump_var, state="readonly", width=22
        )
        self.mapping_jump_combo.grid(row=1, column=1, padx=(6, 4), pady=(0, 6), sticky="we")
        self.mapping_jump_combo.bind("<<ComboboxSelected>>", self.on_mapping_jump_selected)
        self.file_jump_btn = ttk.Button(nav_frame, text="Go", command=self.jump_to_selected_file, width=5)
        self.file_jump_btn.grid(row=1, column=2, padx=(4, 6), pady=(0, 6))

        btn_row_right = ttk.Frame(act_bottom)
        btn_row_right.pack(side="left")

        self.replace_btn = ttk.Button(btn_row_right, text="Replace", style="Accent.TButton", command=self.start_replace)
        self.replace_btn.pack(side="left", padx=5)
        self.replace_btn.state(["disabled"])

        self.cancel_btn = ttk.Button(btn_row_right, text="Cancel", command=self.cancel_replace)
        self.cancel_btn.pack(side="left", padx=5)
        self.cancel_btn.state(["disabled"])

        self.undo_btn = ttk.Button(btn_row_right, text="Undo", command=self.undo_replace)
        self.undo_btn.state(["disabled"])
        self.undo_btn.pack(side="left", padx=5)

        self.copy_preview_btn = ttk.Button(btn_row_right, text="Copy Preview", command=self.copy_preview)
        self.copy_preview_btn.pack(side="left", padx=5)

        self.preview_status_label = ttk.Label(prev_frame, text="", background="#2e3440", foreground="#ECEFF4")
        self.preview_status_label.grid(row=5, column=0, sticky="we", pady=(0, 5))

        self.paned.add(prev_frame, weight=60)

        # 4) 로그
        log_frame = ttk.Frame(container)
        log_frame.grid(row=1, column=0, sticky="nsew", pady=(10, 0))
        ttk.Label(log_frame, text="Log Viewer:").pack(anchor="w")

        self.log_area = tk.Text(log_frame, wrap=tk.NONE, height=6,
                                bg="#3B4252", fg="#ECEFF4", bd=0, state="disabled")
        self.log_area.pack(fill=tk.BOTH, expand=True, side="left")

        self.hsb_log = ttk.Scrollbar(log_frame, orient="horizontal", command=self.log_area.xview)
        self.hsb_log.pack(fill="x", side="bottom")
        self.vsb_log = ttk.Scrollbar(log_frame, orient="vertical", command=self.log_area.yview)
        self.vsb_log.pack(fill="y", side="right")
        self.log_area.config(yscrollcommand=self.vsb_log.set, xscrollcommand=self.hsb_log.set)

        # 진행 바
        self.replace_status_label = ttk.Label(container, text="Ready.", background="#2e3440", foreground="#ECEFF4")
        self.replace_status_label.grid(row=2, column=0, sticky="we")
        self.progress = ttk.Progressbar(container, mode="determinate")
        self.progress.grid(row=3, column=0, sticky="we", pady=(5, 0))

        # 스크롤바 자동 숨김
        for widget, vsb, hsb in [
            (self.file_listbox, self.vsb_file, self.hsb_file),
            (self.map_text,     self.vsb_map,  self.hsb_map),
            (self.src_listbox,  self.vsb_src,  None),
            (self.preview_text, self.vsb_preview, self.hsb_preview)
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

    def _get_file_text(self, path: str) -> str:
        if path in self.file_cache:
            return self.file_cache[path]
        txt = None
        for enc, errs in (("utf-8", "strict"), ("cp949", "strict"), ("euc-kr", "ignore"), ("utf-8", "ignore")):
            try:
                txt = Path(path).read_text(encoding=enc, errors=errs)
                break
            except Exception:
                txt = None
        if txt is None:
            raise OSError(f"Failed to read file: {path}")
        self.file_cache[path] = txt
        return txt

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

    def _get_effective_replace_pairs(self):
        return [(s, d) for (s, d) in self.mapping_pairs if s and d]

    def _set_preview_output(self, text: str):
        self.preview_text.config(state="normal")
        self.preview_text.delete("1.0", tk.END)
        if text:
            self.preview_text.insert("1.0", text)
        self.preview_text.config(state="disabled")
        self._check_scrollbars(self.preview_text, self.vsb_preview, self.hsb_preview)

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
        self.context_lines_spinbox.config(state=list_state)

        if running:
            self.regex_check.state(["disabled"])
            self.case_check.state(["disabled"])
            self.scope_selected_rb.state(["disabled"])
            self.scope_all_rb.state(["disabled"])
            self.context_chars_scale.state(["disabled"])
            self.browse_btn.state(["disabled"])
            self.clear_btn.state(["disabled"])
            self.copy_preview_btn.state(["disabled"])
            self.cancel_btn.state(["!disabled"])
        else:
            self.regex_check.state(["!disabled"])
            self.case_check.state(["!disabled"])
            self.scope_selected_rb.state(["!disabled"])
            self.scope_all_rb.state(["!disabled"])
            self.context_chars_scale.state(["!disabled"])
            self.browse_btn.state(["!disabled"])
            self.clear_btn.state(["!disabled"])
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

    def on_context_chars_changed(self, *_):
        self.context_chars_label.config(text=str(self.context_chars_var.get()))

    def _on_replace_scope_changed(self):
        self._refresh_action_state()

    # ────────────────────── 이벤트 ────────────────────── #
    def on_browse(self):
        files = filedialog.askopenfilenames(filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")])
        self._add_files(files, source="Browse Files")
        self.update_src_list()

    def on_clear(self):
        self.file_listbox.delete(0, tk.END)
        self.file_cache.clear()
        self._clear_cached_file_derivatives()
        self.log("File list cleared")
        self.update_src_list()

    def delete_selected(self, event):
        for i in reversed(self.file_listbox.curselection()):
            removed = self.file_listbox.get(i)
            self.file_listbox.delete(i)
            self.file_cache.pop(removed, None)
            self._clear_cached_file_derivatives(removed)
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
            self._highlight_mapping()
            self.update_src_list()

    def _highlight_mapping(self):
        self.map_text.tag_remove("dup", "1.0", tk.END)
        self.map_text.tag_remove("same", "1.0", tk.END)
        self.map_text.tag_remove("csv_err", "1.0", tk.END)
        self.map_text.tag_remove("regex_err", "1.0", tk.END)
        lines = self.map_text.get("1.0", "end-1c").splitlines()
        src_line_map: dict[str, list[int]] = {}
        duplicate_lines: set[int] = set()
        same_lines: list[int] = []
        csv_err_lines: list[int] = []
        regex_err_lines: list[int] = []
        regex = self.regex_var.get()
        flags = (0 if self.case_var.get() else re.IGNORECASE)

        for i, ln in enumerate(lines, start=1):
            stripped = ln.strip()
            if not stripped or stripped.startswith("#"):
                continue
            try:
                parts = next(csv.reader([ln], skipinitialspace=True), [])
            except csv.Error:
                csv_err_lines.append(i)
                self.map_text.tag_add("csv_err", f"{i}.0", f"{i}.end")
                continue

            if not parts:
                continue

            src = parts[0].strip()
            dst = parts[1].strip() if len(parts) > 1 else ""
            if src:
                src_line_map.setdefault(src, []).append(i)
                if regex:
                    try:
                        re.compile(src, flags)
                    except re.error:
                        regex_err_lines.append(i)
                        self.map_text.tag_add("regex_err", f"{i}.0", f"{i}.end")
            if src and dst and src == dst:
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
                self._highlight_mapping()
            except Exception:
                pass

    def save_session(self):
        data = {"files": list(self.file_listbox.get(0, tk.END)),
                "mapping": self.map_text.get("1.0", tk.END).rstrip("\n")}
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
                parts = next(csv.reader([ln], skipinitialspace=True), [])
            except csv.Error:
                continue
            if parts:
                src = parts[0].strip()
                if not src:
                    continue
                self.mapping_pairs.append((src, parts[1].strip() if len(parts) > 1 else ""))
        self.src_listbox.delete(0, tk.END)
        self.src_listbox.insert(tk.END, "All src words")
        for s, _ in self.mapping_pairs:
            self.src_listbox.insert(tk.END, s)
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
        targets = self.mapping_pairs if idx == 0 else [self.mapping_pairs[idx - 1]]
        if not targets:
            self._set_file_shortcuts([])
            self._set_preview_output("No preview target selected.\n")
            self.preview_status_label.config(text="Preview idle.")
            return

        self.preview_status_label.config(text="Searching...")
        self._set_file_shortcuts([])
        self._set_preview_output("Rendering preview...\n")

        if self.preview_thread and self.preview_thread.is_alive():
            pass  # 기존 작업은 seq 불일치로 폐기

        def worker():
            try:
                text_out, src_ranges, truncated_by_matches = self._build_preview_grouped_text_and_ranges(
                    files, targets, regex, case, flags, ctx_lines, ctx_chars, seq
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

                # UI 반영 (한 번에 insert)
                self._set_preview_output(text_out)
                self._set_file_shortcuts(file_shortcuts)
                status = f"Done. {match_count} matches (grouped; visible highlighting)."
                if truncated_by_matches or truncated_by_size:
                    status += " Preview truncated."
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
        for i, (src, _) in enumerate(targets):
            suffix = "+" if i < len(capped) and capped[i] else ""
            parts.append(f"{src}:{counts[i]}{suffix}")
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
        self, files, targets, case, ctx_lines, ctx_chars, L, colon_sp, nl, arrow, seq
    ):
        N = len(targets)
        per_target_limit = max(1, self.MAX_PREVIEW_MATCHES // max(1, N))
        blocks = [""] * N
        ranges_per_t = [[] for _ in range(N)]
        shown_total = [0] * N
        capped = [False] * N
        truncated = False

        for k, (s, d) in enumerate(targets):
            if seq != self.preview_seq:
                break
            if not s:
                continue
            t_text, t_ranges, t_trunc = self._build_single_literal(
                files, (s, d), case, ctx_lines, ctx_chars, L, colon_sp, nl, arrow, seq,
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
        for ti, (s, d) in enumerate(targets):
            target_key_to_idx.setdefault((s, d), ti)
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
                for j, (s, _) in enumerate(targets):
                    if s == src:
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
                        f"{targets[j][0]}:{counts_per_file_by_target[i - 1][j]}"
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
            for j, (src, dst) in enumerate(targets):
                mcnt = counts_per_file_by_target[i - 1][j]
                src_disp = src if len(src) <= 28 else (src[:25] + "...")
                if dst:
                    dst_disp = dst if len(dst) <= 14 else (dst[:11] + "...")
                    map_label = f"{j+1}. {src_disp} -> {dst_disp} ({mcnt})"
                else:
                    map_label = f"{j+1}. {src_disp} ({mcnt})"
                moff = first_offsets_per_file_target[i - 1][j]
                mapping_items.append((map_label, (moff + shift) if moff is not None else None))
            nav_items.append((file_label, mapping_items))

        return text, ranges, nav_items

    # === 핵심: 단어별 섹션 분리 + 고속 경로(리터럴 다중 패턴은 합성 정규식) ===
    def _build_preview_grouped_text_and_ranges(self, files, targets, regex, case, flags, ctx_lines, ctx_chars, seq):
        """
        각 타겟(단어)마다 별도의 버퍼에 결과를 쌓고, 마지막에 섹션 순서대로 이어 붙여 반환.
        반환: (combined_text, combined_src_ranges)
        """
        # 상수 로컬화
        L = "  L"; colon_sp = ": "; nl = "\n"; arrow = " -> "

        # 1) 단일 타겟 + 리터럴 + 개행 없음: 초고속 경로 (그대로 사용)
        if len(targets) == 1 and not regex and ("\n" not in targets[0][0] and "\r" not in targets[0][0]):
            text, ranges, truncated = self._build_single_literal(
                files, targets[0], case, ctx_lines, ctx_chars, L, colon_sp, nl, arrow, seq
            )
            return text, ranges, truncated

        # 2) 다중 타겟이고 모두 리터럴(+개행없음)인 경우: 합성 정규식 한 번으로 전부 찾기
        all_literal = (not regex) and all(("\n" not in s and "\r" not in s) for s, _ in targets)
        if all_literal and targets:
            # 소수 타겟(예: 2~6개)은 단일 고속 경로를 타겟별로 재사용하는 편이 훨씬 빠름.
            if len(targets) <= 6:
                return self._build_multi_literal_small_target_fast(
                    files, targets, case, ctx_lines, ctx_chars, L, colon_sp, nl, arrow, seq
                )

            # 그룹 이름 g0, g1, ...
            parts = []
            for i, (s, _) in enumerate(targets):
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
                prev_lines = deque(maxlen=max(0, ctx_lines))

                fh = None
                for enc in ("utf-8", "cp949", "euc-kr"):
                    try:
                        fh = open(f, "r", encoding=enc, errors="ignore", newline="", buffering=1<<20)
                        break
                    except Exception:
                        fh = None; continue
                if fh is None:
                    fh = open(f, "r", encoding="utf-8", errors="ignore", newline="", buffering=1<<20)

                with fh:
                    for ln_no, line in enumerate(fh, 1):
                        if seq != self.preview_seq or stop_early:
                            break
                        line = line.rstrip("\r\n")

                        # 후행 문맥: 타겟별로 출력
                        if ctx_lines:
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
                            s, d = targets[k]
                            if capped[k]:
                                continue
                            # 파일 헤더(해당 타겟에 대해 이 파일에서 최초)
                            if not printed_header[k]:
                                h = f"{basename}: '{s}' -> '{d}'{nl}"
                                bufs[k].write(h); pos[k] += len(h)
                                printed_header[k] = True

                            # 선행 문맥 (타겟별 섹션에 출력)
                            if ctx_lines and prev_lines:
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
                            post_remain[k] = max(post_remain[k], ctx_lines)
                            if shown_total[k] >= per_target_limit:
                                capped[k] = True

                        if all(capped):
                            stop_early = True
                            truncated = True
                            break

                        if ctx_lines:
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
        compiled = [ (re.compile(s if regex else re.escape(s), flags), s, d)
                     for (s, d) in targets ]

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
            prev_lines = deque(maxlen=max(0, ctx_lines))

            fh = None
            for enc in ("utf-8", "cp949", "euc-kr"):
                try:
                    fh = open(f, "r", encoding=enc, errors="ignore", newline="", buffering=1<<20)
                    break
                except Exception:
                    fh = None; continue
            if fh is None:
                fh = open(f, "r", encoding="utf-8", errors="ignore", newline="", buffering=1<<20)

            with fh:
                for ln_no, line in enumerate(fh, 1):
                    if seq != self.preview_seq or stop_early:
                        break
                    line = line.rstrip("\r\n")

                    # 후행 문맥
                    if ctx_lines:
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

                            if ctx_lines and prev_lines:
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

                    if matched_any:
                        for k in range(N):
                            if printed_header[k]:  # 매치가 있었던 타겟만
                                post_remain[k] = max(post_remain[k], ctx_lines)

                    if ctx_lines:
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
        s, d = target
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
        summary = self._build_preview_summary([(s, d)], [shown_total], [capped])
        summary_len = len(summary)
        shifted_ranges = [(a + summary_len, b + summary_len) for a, b in ranges]
        return summary + out.getvalue(), shifted_ranges, truncated or capped

    def _build_single_literal_with_line_context(
        self, files, target, case, ctx_lines, ctx_chars, L, colon_sp, nl, arrow, seq, max_matches_limit=None
    ):
        s, d = target
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
                if post_next_line == 0 or post_next_line > limit_line:
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

                flush_post_until(min(post_until_line, grp_line_no))

                for pos_found in grp_matches:
                    if not header_printed:
                        h = header_tmpl.format(basename, s, d)
                        write(h); pos += len(h)
                        header_printed = True

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

            if not stop_early and seq == self.preview_seq:
                flush_post_until(post_until_line)

            if header_printed:
                tail = f"  Preview matches: {printed}{nl}{nl}"
                write(tail); pos += len(tail)

        capped = shown_total >= max_matches
        summary = self._build_preview_summary([(s, d)], [shown_total], [capped])
        summary_len = len(summary)
        shifted_ranges = [(a + summary_len, b + summary_len) for a, b in ranges]
        return summary + out.getvalue(), shifted_ranges, truncated or capped

    def _build_single_literal(
        self, files, target, case, ctx_lines, ctx_chars, L, colon_sp, nl, arrow, seq, max_matches_limit=None
    ):
        """단일 리터럴 고속 경로(그대로)."""
        s, d = target
        s_find = s if case else s.lower()
        s_len = len(s)
        if s and ("\n" not in s and "\r" not in s):
            if ctx_lines == 0:
                return self._build_single_literal_no_line_context(
                    files, target, case, ctx_chars, L, colon_sp, nl, arrow, seq, max_matches_limit
                )
            return self._build_single_literal_with_line_context(
                files, target, case, ctx_lines, ctx_chars, L, colon_sp, nl, arrow, seq, max_matches_limit
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
            prev_lines = deque(maxlen=max(0, ctx_lines))
            post_remain = 0
            last_printed_line = None

            fh = None
            for enc in ("utf-8", "cp949", "euc-kr"):
                try:
                    fh = open(f, "r", encoding=enc, errors="ignore", newline="", buffering=1<<20)
                    break
                except Exception:
                    fh = None; continue
            if fh is None:
                fh = open(f, "r", encoding="utf-8", errors="ignore", newline="", buffering=1<<20)

            basename = os.path.basename(f)
            with fh:
                for ln_no, line in enumerate(fh, 1):
                    if seq != self.preview_seq or stop_early:
                        break
                    line = line.rstrip("\r\n")
                    hay = line if case else line.lower()

                    if post_remain > 0:
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

                        if ctx_lines and prev_lines:
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

                        post_remain = max(post_remain, ctx_lines)
                        printed += 1
                        shown_total += 1
                        if shown_total >= max_matches or pos >= build_char_limit:
                            stop_early = True
                            truncated = True
                            break
                        start = pos_found + (s_len if s_len else 1)

                    if ctx_lines:
                        prev_lines.append(line)

            if header_printed:
                tail = f"  Preview matches: {printed}{nl}{nl}"
                write(tail); pos += len(tail)

        capped = shown_total >= max_matches
        summary = self._build_preview_summary([(s, d)], [shown_total], [capped])
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
        for s, d in pairs:
            patt = re.compile(s if regex else re.escape(s), flags)
            if (not regex) and ("\\" not in d):
                repl = d
            else:
                repl = (lambda rep: (lambda m: rep))(d)
            compiled.append((patt, repl, s, d))
        return compiled

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
            for i, (s, _) in enumerate(pairs, 1):
                try:
                    re.compile(s, flags)
                except re.error as ex:
                    messagebox.showerror("Regex Error", f"Invalid regex in mapping #{i}:\n{s}\n\n{ex}")
                    return

        scope_label = "selected files" if self.replace_scope_var.get() == "selected" else "all files"
        confirm_message = (
            f"Replace {len(pairs)} mapping(s) in {len(files)} {scope_label}?\n"
            "Backup files (*.bak) will be created next to each source file."
        )
        if not messagebox.askokcancel("Confirm Replace", confirm_message):
            return

        self.progress.config(maximum=len(files), value=0)
        self.replace_status_label.config(text=f"Running replacement in {len(files)} file(s)...")
        self.replace_cancel_event.clear()
        self._set_replace_running(True)
        self.replace_thread = threading.Thread(
            target=self.run_replace, args=(files, pairs, regex, case, flags), daemon=True
        )
        self.replace_thread.start()

    def cancel_replace(self):
        if not self.is_replacing:
            return
        self.replace_cancel_event.set()
        self.cancel_btn.state(["disabled"])
        self.replace_status_label.config(text="Cancel requested. Finishing current file...")

    def run_replace(self, files, pairs, regex, case, flags):
        self.last_replaced.clear()
        self.total_replacements = 0
        self.file_mapping_changes.clear()

        use_literal_case_sensitive_fastpath = (not regex) and case
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
                if use_literal_case_sensitive_fastpath:
                    for s, d in pairs:
                        cnt = new.count(s)
                        if cnt:
                            new = new.replace(s, d)
                            self.total_replacements += cnt
                            fm.add((s, d))
                else:
                    for patt, repl, s, d in compiled:
                        new, cnt = patt.subn(repl, new)
                        if cnt:
                            self.total_replacements += cnt
                            fm.add((s, d))
                if new != txt:
                    bak = f + ".bak"
                    shutil.copy(f, bak)
                    Path(f).write_text(new, encoding="utf-8")
                    self.file_cache[f] = new
                    self._clear_cached_file_derivatives(f)
                    self.last_replaced.append(f)
                    self.file_mapping_changes[f] = fm
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
                text=f"Completed. {len(self.file_mapping_changes)} files changed, {self.total_replacements} replacements."
            )
            desc = ", ".join(
                f"'{s}' -> '{d}'" for f in self.file_mapping_changes for s, d in self.file_mapping_changes[f]
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
            bak = f + ".bak"
            if os.path.exists(bak):
                shutil.copy(bak, f)
                try:
                    self.file_cache[f] = Path(f).read_text(encoding="utf-8")
                except UnicodeDecodeError:
                    self.file_cache[f] = Path(f).read_text(encoding="euc-kr", errors="ignore")
                self._clear_cached_file_derivatives(f)
            fm = self.file_mapping_changes.get(f, set())
            desc = ", ".join(f"'{d}' -> '{s}'" for s, d in fm)
            self.log(f"Restored {os.path.basename(f)}; Mappings: {desc}")

        self.last_replaced.clear()
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
