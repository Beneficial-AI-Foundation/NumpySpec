# GaussianSpec

GaussianSpec is a **cloud-native Lean 4 research playground**: all compilation and
goal-state introspection are off-loaded to a **Pantograph Lean 4 server running
on Morph Cloud**.  This enables millisecond-latency, horizontally scalable
verification for RL agents while keeping the repo light-weight.

## Overview

This project aims to formally specify that Gaussian elimination, when applied to a nonsingular square matrix `A`, produces its left inverse.

The core specification is found in `GaussianSpec.lean`:

- `gaussianElimination`: A (currently sorried) function representing the Gaussian elimination algorithm.
- `gaussianElimination_is_left_inverse`: A theorem stating that `gaussianElimination A * A = 1` for a nonsingular matrix `A`.

## Dependencies

Local machine only needs:

* Python ≥ 3.12 with [`uv`](https://github.com/astral-sh/uv) (see `Justfile`).
* [`morphcloud` SDK](https://pypi.org/project/morphcloud/) ≥ 0.1.67 (auto-installed via `uv sync`).

All Lean toolchain bits (elan ± mathlib) live inside the Morph Cloud snapshot;
you **do not** need Lean installed locally to run the pipeline.

## Local build (optional)

If you really want to compile locally you still can.  **Important**: the
pipeline produces Lean files under the `Generated` namespace (e.g.
`generated/Spec/Chunk0001_0050.lean`).  These files are *not* part of the
default `lake build` target, so you must request them explicitly or build all
targets:

```bash
# Build the root package (default)
just build-local              # → `lake build`

# Additionally build everything under the `Generated` namespace
lake build Generated           # or `lake build Generated.*` for a sub-tree

# Convenience — build both in one step
just build-all
```

The new `build-all` recipe is defined in the `Justfile` and simply calls
`lake build` followed by `lake build Generated`.  For day-to-day work we still
recommend the cloud pipeline (next section) but the local path is useful when
working offline.

## Cloud pipeline quick-start

Run the end-to-end OCR → edit → remote-compile loop:

```bash
just pipeline --remote \
    --pdf textbook/Numerical_Recipes_in_C.pdf \
    --lean-file GaussianSpec.lean \
    --edit "theorem t : 1 = 1 := by rfl"
```

First run provisions an *Infinibranch* snapshot (≈ 5 min).  Subsequent runs
reuse the warmed snapshot/instance.

## Automated multi-agent loop

### Key stages

1. OCR (`OCRSubagent`) – multi-backend (OpenAI Vision → Gemini → Tesseract)
2. Edit (`LeanEditSubagent`) – templatized edits
3. **Remote compile (`LeanRemoteBuildSubagent`)** – Pantograph HTTP POST
4. Feedback parse → RL reward / next action

## Roadmap

See `plan.md` for an up-to-date progress tracker.

## Usage

The primary goal is library development and formal proof. You can explore the definitions and theorems within the Lean environment.

## Contributing

Contributions are welcome! Please focus on:

1. Implementing the `gaussianElimination` function based on standard algorithms or `mathlib` components.
2. Proving the `gaussianElimination_is_left_inverse` theorem.
3. Adding further specifications or related matrix properties.

## License

This project is licensed under the Apache-2.0 license - see the LICENSE file for details.

## TODO

- [ ] Implement `gaussianElimination` function.
- [ ] Prove `gaussianElimination_is_left_inverse`.
- [ ] Consider specifying properties related to row echelon form.

## Automated Agent Feedback Loop

This project includes a MorphCloud-driven Lean agent (`src/gaussianspec/agent.py`) that automates the feedback loop for Lean code development:

- Drives Lean code edits, builds, and parses feedback for the Gaussian elimination spec.
- Uses the [morphcloud](https://pypi.org/project/morphcloud/) SDK for orchestration (ready for cloud/VM integration).
- Compositional, pure functional design: all logic is broken into small, typed units for easy extension.
- Example usage included; ready for integration with MorphCloud and `.cursorrules` for meta-programmatic Lean development.

The agent pipeline now includes a pure functional OCR preprocessing step:

- Automatically OCRs the textbook PDF (`textbook/Numerical_Recipes_in_C.pdf`) to a cached `.txt` file before running Lean code.
- Uses `pdf2image` and `pytesseract` for robust PDF-to-text conversion.
- Skips OCR if the `.txt` file already exists (caching for reproducibility and speed).
- The OCR step is fully composable and can be reused or extended in other pipelines.

To use or extend the agent:

1. Edit `src/gaussianspec/agent.py` to add new edit strategies or feedback parsing.
2. Run the agent as a script or import its functions in your own orchestration code.
3. The agent can be extended to drive Lean code via MorphCloud VMs, automate theorem search, and more.

## Modular Subagent Architecture (v0.3.0)

The agent system is now built from modular, composable subagents, each with a clear goal and feedback interface. See `src/gaussianspec/subagents.py` for details.

**Subagents:**
- `OCRSubagent`: OCRs a PDF to text, with caching and error feedback.
- `LeanEditSubagent`: Applies edits to Lean files, reporting success or error.
- `LeanBuildSubagent`: Runs `lake build` and returns build output and status.
- `FeedbackParseSubagent`: Parses Lean build output for actionable feedback.

Each subagent is a pure dataclass with a `run()` method and a result type. Subagents can be composed into pipelines, forked for retries or escalation, and orchestrated for robust, feedback-driven development.

**Example composition:**
- OCR textbook → edit Lean file → build → parse feedback → (repeat or escalate)

This enables fine-grained automation, traceability, and easy extension for new tasks or agent types.
