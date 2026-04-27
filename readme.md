# Batch Text Transformer

A desktop GUI tool for batch text replacement, deletion, and line filtering across multiple files.

This project is built with Python + Tkinter and provides safe replace workflows with preview, backup, cancel, and undo.


## Key Features

- Multi-file replacement with `src,dst` mapping input
- Delete matched words with `src,`
- Delete lines containing a match with `src,,delete-line`
- Preview with match highlighting
- Replace scope: `All` (default) or `Selected`
- Regex mode and case-sensitive mode
- Encoding selection: `Auto detect`, `UTF-8`, `UTF-8 BOM`, `CP949`, `EUC-KR`
- Files are saved with the same encoding used when they were read
- Context controls for preview (`Context lines`, `Context chars`)
- Safety flow:
  - Confirmation dialog before replace
  - Configurable backup policy per run
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
python batch-text-transformer.py
```

## Mapping Format

Enter one mapping per line in the mapping editor:

```text
source_text,target_text
```

Examples:

```text
foo,bar
foo,
foo,,delete-line
"hello world","HELLO_WORLD"
# comment lines are ignored
```

Notes:

- Empty source values are ignored.
- `src,dst` replaces `src` with `dst`.
- `src,` deletes the matched text.
- `src,,delete-line` deletes each line containing `src`.
- A line with only `src` is preview-only and is not applied during replace.
- `delete-line` matches are selected by default in Preview. Click a highlighted delete-line row to toggle whether that line is applied.

## Usage

1. Add input text files (`Browse Files` or drag-and-drop when enabled).
2. Enter mapping lines for replace or delete operations.
3. Choose options:
   - `Regex Mode`
   - `Case Sensitive`
   - `Replace scope` (`All` / `Selected`)
   - `Encoding`
   - `Backup`
4. Review matches in the preview panel.
5. Click `Apply` and confirm.
6. Use `Cancel` to stop an ongoing run (current file finishes first).
7. Use `Undo` to restore from backups when the selected backup policy created them.

## Safety and Recovery

- Backup policies:
  - `Sidecar .bak`: overwrite/create `<filename>.bak` next to each changed file.
  - `Timestamped .bak`: create `<filename>.<timestamp>.bak` next to each changed file.
  - `Backup folder`: create backups under `_word_replacer_backups/<timestamp>/`.
  - `No backup`: skip backup creation and disable undo for that run.
- `Undo` restores from the backup files created by the last run.
- Only files with actual content changes are rewritten.
- Auto encoding detection checks UTF-8 BOM, UTF-8, CP949, and EUC-KR, then writes changed files using the detected codec.

## Project Files

- `batch-text-transformer.py`: main GUI application
- `word_replacer_session.json`: saved UI session state
- `*.bak`, `_word_replacer_backups/`: backup files created during replace

