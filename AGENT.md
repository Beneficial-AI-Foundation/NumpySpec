# AGENT.md - GaussianSpec Project

## Overview
GaussianSpec is a cloud-native Lean 4 research playground for formal specification of Gaussian elimination. It uses Pantograph Lean 4 server on Morph Cloud for millisecond-latency verification.

## Project Structure
- `src/gaussianspec/` - Python modules for agents, OCR, and RL
- `tests/` - Python test files  
- `GaussianSpec.lean` - Main Lean specification file
- `generated/` - Dynamically generated Lean files (OCR-derived)
- `textbook/` - PDF textbook for OCR processing
- `lakefile.toml` - Lean package configuration
- `pyproject.toml` - Python package configuration

## Dependencies & Setup
- Python ≥ 3.12 with `uv` package manager
- Lean 4 (nightly-2025-04-23) via elan
- MorphCloud SDK for remote compilation

**Quick setup:**
```bash
just sync  # Install all Python dependencies
```

**Bootstrap full environment:**
```bash
just bootstrap  # Install Rust, elan, uv
```

## Build Commands

### Python/Testing
- `just test` - Run pytest test suite
- `uv run -m pytest -q` - Run tests directly
- `uv run ruff check --fix .` - Lint with Ruff
- `uv run ruff format .` - Format code

### Lean Compilation
- `just build-local` - Build local Lean package (`lake build`)
- `just build-all` - Build all including generated files (`lake build` + `lake build generated`)
- `lake build Generated` - Build dynamically generated Lean files

### Cloud Pipeline
- `just pipeline` - Run end-to-end OCR → edit → remote compile loop
- `just pipeline --pdf <pdf> --lean-file <file> --edit "<edit>"` - Custom pipeline

### OCR Processing
- `just ocr` - OCR textbook pages 1-149
- `just ocr-all` - OCR entire PDF in chunks
- `uv run -m gaussianspec.pdf_pipeline <pdf>` - Direct OCR pipeline

### RL Training
- `just train` - Train PPO on LeanEnv for 1k steps
- `just train steps=5000` - Train for custom number of steps

## Code Style & Conventions
- Uses Ruff for Python linting and formatting
- Lean code follows mathlib4 conventions
- Git hooks available via `just install-hooks`
- Type hints required for Python code

## Testing Framework
- Uses pytest for Python tests
- Test files in `tests/` directory
- Run with `just test` or `uv run -m pytest`
- Specific test modules:
  - `test_spec_verifier.py` - Specification verification tests
  - `test_hf_utils.py` - Hugging Face utilities tests
  - `test_translate.py` - Translation tests

## Agent System
Modular subagent architecture in `src/gaussianspec/subagents.py`:
- `OCRSubagent` - PDF to text conversion
- `LeanEditSubagent` - Lean file editing
- `LeanBuildSubagent` - Local Lean builds
- `LeanRemoteBuildSubagent` - Remote Pantograph builds
- `FeedbackParseSubagent` - Parse Lean output

### LLM-based Generation (NEW)
- `LLMCodeSpecGenerator` - Two-stage LLM pipeline for Lean generation
- `LLMCodeSpecSubagent` - Subagent wrapper for LLM generation
- Pipeline: Python input → Lean code → Lean specification
- Uses nvidia/Nemotron-Research-Reasoning-Qwen-1.5B by default
- Debug mode: `--debug` saves full LLM communications for troubleshooting
- Improved content cleaning: Filters out thinking text, preserves only Lean code/specs

## Main Entry Points
- `uv run -m gaussianspec.pipeline` - Main pipeline
- `uv run -m gaussianspec.pdf_pipeline` - OCR pipeline
- `uv run src/gaussianspec/rl_trainer.py` - RL training
- `python scripts/run_llm_pipeline.py` - LLM-based Lean generation pipeline
  - Add `--debug` flag to save full LLM communications
  - Example: `python scripts/run_llm_pipeline.py --input example_input.py --debug`
- `gaussianspec` - CLI entry point (after installation)

## Development Workflow
1. Edit Lean specifications in `GaussianSpec.lean`
2. Use `just pipeline` for cloud compilation
3. Run `just test` for Python tests
4. Use `just build-local` for local Lean builds
5. OCR processing with `just ocr` for textbook integration
