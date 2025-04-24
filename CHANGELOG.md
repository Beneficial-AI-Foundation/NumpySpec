# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2025-04-14

### Added

- Initial project structure with `lakefile.toml`, `Main.lean`, and `GaussianSpec.lean`.
- `mathlib` dependency.
- Specification `gaussianElimination_is_left_inverse` stating Gaussian elimination yields a left inverse.
- Placeholder `gaussianElimination` function.
- Imported `LeanSearchClient` in `Main.lean`.

### Changed

- Updated `lean-toolchain` to `leanprover/lean4:v4.19.0-rc3` for `mathlib` compatibility.
- Refined `lakefile.toml` configuration.

### Removed

- Default `IO.println` in `Main.lean`.

## [0.0.1] - 2024-07-19

### Added

- Initial README.md, CHANGELOG.md, LICENSE, .gitignore, lean-toolchain.

## [0.2.0] - 2025-04-15

### Added
- MorphCloud-driven Lean agent in `src/gaussianspec/agent.py` for compositional feedback loop:
  - Drives Lean code edits, builds, and parses feedback.
  - Uses morphcloud SDK (ready for orchestration).
  - Pure functional idioms, data-oriented design, type signatures.
  - Example usage for future MorphCloud integration.

## [0.2.1] - 2025-04-15

### Added
- Pure functional OCR preprocessing step to agent pipeline:
  - Uses pdf2image and pytesseract to OCR textbook PDF.
  - Caches OCR result as .txt file, skipping if already present.
  - Composable and documented; integrated as preproc in agent pipeline.

## [0.3.0] - 2025-04-15

### Added
- Modular subagent classes in `src/gaussianspec/subagents.py`:
  - `OCRSubagent`, `LeanEditSubagent`, `LeanBuildSubagent`, `FeedbackParseSubagent`.
  - Each is a pure dataclass with a `run()` method and clear feedback/result type.
  - Enables compositional, forkable, feedback-driven agent pipelines.
- Updated dependencies (`uv.lock`, `pyproject.toml`) for subagent support.

## [0.4.0] - 2025-05-01

### Added
- Reinforcement‑learning scaffolding (`LeanEnv`, `EditLibrary`) in `src/gaussianspec/rl_env.py`.
  Provides Gymnasium‑compatible environment exposing Lean build feedback.
- Exported in package root for easy import `from gaussianspec import LeanEnv`.
- Added dependencies: `pantograph>=0.3.0` (Lean REPL orchestration) and `gymnasium>=0.29.1`.

## [0.4.1] - 2025-05-20

### Added

- Multi‑backend OCR with automatic fallback in `agent.py`:
  - New `auto` mode tries **OpenAI Vision (GPT‑4o‑mini) → Google Gemini → local Tesseract**.
  - Copyright / policy refusal detection falls back to next provider.
  - `pdf_pipeline` CLI exposes `--method auto|openai|gemini|tesseract` (default `auto`).
  - Helper functions `_openai_ocr_images`, `_ocr_refused`.

### Changed

- Added `openai>=1.30.0` dependency in `pyproject.toml`.

### Fixed

- Type‑checker false positive for `txt_path.write_text` by asserting text not‑None.

## [Unreleased]

- Added runtime guard for optional local Tesseract backend in `agent.py`, removing unconditional `pytesseract` import to fix linter when dependency is absent.

- **Breaking** `ocr_pdf_to_text` now accepts a `strip_right_px` argument that crops a fixed
  number of pixels from the right margin before OCR.  CLI `pdf_pipeline` exposes
  `--strip-right` flag.  Useful for textbooks like *Numerical Recipes* whose sample
  page column interferes with OCR accuracy.

## [0.4.2] - PLACEHOLDER_DATE

### Added

- Verbose, batched OCR with `tqdm` progress bar in `agent.py`.
- Parallel page-level OCR using `ThreadPoolExecutor` with `as_completed` preserving page order.
- Added `tqdm>=4.66.4` dependency to `pyproject.toml`.

### Changed

- `ocr_pdf_to_text` now shows a live progress bar and can process pages concurrently even when using non-Tesseract providers (which release the GIL internally).
