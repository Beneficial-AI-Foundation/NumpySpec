# Roadmap / Progress Tracker

> Updated: <!--TIMESTAMP-->
> Updated: 2025-04-30:02:49 UTC

## Core migration to MorphCloud + Pantograph

- [ ] Default all pipelines and RL env to remote Pantograph compile
- [ ] Remove mandatory Lean toolchain from local dev docs
- [x] Add health-check CI hitting /expr_type on server mock
- [ ] Pre-compute lake cache in snapshot to speed warm-up

## Multi-agent architecture

- [ ] Share single `

## OCR & Cropping Integration (done)

- [x] Integrate `PDFCropSubagent` into `pdf_pipeline.py` so OCR runs on cropped PDF.
- [x] Regenerate pipeline mermaid diagram in `pipeline.md`.

## Translation MVP (first page only)

- [ ] Implement `TranslatePageSubagent` that:
  - Accepts `txt_path` and `page_num`.
  - Emits `Verso` Lean prose or comments for the specified page.
- [ ] Extend `pdf_pipeline` with `--translate-first-page` flag to trigger subagent after OCR.
- [ ] Write failing unit test in `tests/test_translate.py` asserting first page translation exists.

## Immediate Next Actions (v0.2.0)

### Lean core spec
- [ ] Replace the placeholder `gaussianElimination` implementation with a row-operation-based routine.
- [ ] Prove `gaussianElimination_is_left_inverse` (use `Matrix.mul_inv_cancel`).
- [ ] Add a Lean regression test on a `2 × 2` numeric example.

### Verso book pipeline
- [ ] Create `generated/versobook/` Lake project (Verso dependency, `Book/Main.lean`).
- [ ] Implement `build_book_agents.py` to populate `Book/Chapter2.lean` from OCR.
- [ ] Add `just build-book` and `just refresh-book` recipes. Test them to ensure they worked.

### Pantograph remote build
- [ ] Default all runner scripts to `LeanRemoteBuildSubagent` with local fallback.
- [ ] Pre-warm mathlib cache in the Morph snapshot.

### OCR / translation
- [x] `PDFCropSubagent` integrated.
- [x] `TranslatePageSubagent` implemented & unit-tested.
- [ ] Wire `--translate-first-page` flag in `pdf_pipeline.py`.

### CI & linting
- [ ] Add Ruff to dev dependencies and enforce `ruff check .` in CI.
- [ ] CI job compiling root project and Verso book via Pantograph mock.

### Documentation & metadata
- [ ] Update `CHANGELOG.md` after each bullet lands.
- [ ] Fix the broken bullet under *Multi-agent architecture*.
- [ ] Tick completed tasks in `README.md` and `roadmap.md`.

### Nice-to-haves
- [ ] Auto-generate Lean examples from Verso prose and compile in CI.
- [ ] Regression test ensuring page ordering preservation in translation workflow.