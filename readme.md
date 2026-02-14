# word-replacer-gui

A desktop GUI tool for batch text replacement across multiple files.

This project is built with Python + Tkinter and provides safe replace workflows with preview, backup, cancel, and undo.

## Recommended Repository Names

- `word-replacer-gui` (recommended)
- `bulk-word-replacer`
- `tk-word-replace-tool`
- `text-mapping-replacer`
- `safe-batch-replace`
- `replaceword-desktop`

## Key Features

- Multi-file replacement with `src,dst` mapping input
- Preview with match highlighting
- Replace scope: `All` (default) or `Selected`
- Regex mode and case-sensitive mode
- Context controls for preview (`Context lines`, `Context chars`)
- Safety flow:
  - Confirmation dialog before replace
  - `.bak` backup creation per changed file
  - Undo from backups
  - Cancel running replace
- Mapping validation UI:
  - Duplicate source highlighting
  - Same `src == dst` highlighting
  - CSV parse error lines
  - Invalid regex lines (when Regex mode is enabled)
- Session persistence (`word_replacer_session.json`)

## Requirements

- Python 3.10+
- Tkinter (usually bundled with Python on Windows)
- Optional for drag-and-drop:
  - `tkinterdnd2` (preferred), or
  - `tkdnd`

## Run

```bash
python word-replacer-gui.py
```

## Mapping Format

Enter one mapping per line in the mapping editor:

```text
source_text,target_text
```

Examples:

```text
foo,bar
"hello world","HELLO_WORLD"
# comment lines are ignored
```

Notes:

- Empty source values are ignored.
- Replace operation uses mappings that have both `src` and `dst`.

## Usage

1. Add input text files (`Browse Files` or drag-and-drop when enabled).
2. Enter mapping lines in `src,dst` format.
3. Choose options:
   - `Regex Mode`
   - `Case Sensitive`
   - `Replace scope` (`All` / `Selected`)
4. Review matches in the preview panel.
5. Click `Replace` and confirm.
6. Use `Cancel` to stop an ongoing run (current file finishes first).
7. Use `Undo` to restore from `.bak` backups.

## Safety and Recovery

- Before any write, each modified file is copied to `<filename>.bak`.
- `Undo` restores from the created `.bak` files.
- Only files with actual content changes are rewritten.

## Project Files

- `word-replacer-gui.py`: main GUI application
- `word_replacer_session.json`: saved UI session state
- `*.bak`: backup files created during replace

