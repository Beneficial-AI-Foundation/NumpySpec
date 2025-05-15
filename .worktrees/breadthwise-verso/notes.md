## OCR strategy scratchpad

- Implemented parametric `ocr_pdf_to_text` that supports `start_page`, `end_page`, concurrency.
- CLI (`pdf_pipeline.py`) now takes `--pages` (default 1-100).
- `Justfile` ocr recipe now allows `pages` arg.
- Parallel OCR via `ThreadPoolExecutor`; Tesseract releases GIL so threads help.
- Future plan: loop over chunks of 100 pages, append to single txt or separate files then cat.
