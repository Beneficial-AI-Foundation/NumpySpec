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
