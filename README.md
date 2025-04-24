# GaussianSpec

A Lean 4 project specifying and proving properties of Gaussian elimination.

## Overview

This project aims to formally specify that Gaussian elimination, when applied to a nonsingular square matrix `A`, produces its left inverse.

The core specification is found in `GaussianSpec.lean`:

- `gaussianElimination`: A (currently sorried) function representing the Gaussian elimination algorithm.
- `gaussianElimination_is_left_inverse`: A theorem stating that `gaussianElimination A * A = 1` for a nonsingular matrix `A`.

## Dependencies

- Lean 4 (version specified in `lean-toolchain`)
- `mathlib`

## Building

```bash
lake build
```

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
