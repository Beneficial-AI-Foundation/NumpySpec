"""Concrete pipeline orchestrating subagents for a single run.

Usage (from project root):

    uv run -m gaussianspec.pipeline --pdf textbook/your.pdf --lean-file GaussianSpec.lean

This minimal implementation will be refactored once verified.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from dataclasses import dataclass
from typing import Optional

from gaussianspec.subagents import (
    OCRSubagent,
    LeanEditSubagent,
    LeanBuildSubagent,
    FeedbackParseSubagent,
)


@dataclass
class PipelineArgs:
    project_root: Path
    pdf_path: Path
    lean_file: Path
    edit: str = "-- edit by pipeline"


def run_pipeline(args: PipelineArgs) -> None:
    # OCR step
    ocr_res = OCRSubagent(pdf_path=args.pdf_path).run()
    if not ocr_res.success:
        print(f"OCR failed: {ocr_res.error}")
        return
    print(f"OCR completed -> {ocr_res.txt_path}")

    # Lean edit step
    edit_res = LeanEditSubagent(file=args.lean_file, edit=args.edit).run()
    if not edit_res.success:
        print(f"Edit failed: {edit_res.error}")
        return
    print(f"Edit applied to {edit_res.file}")

    # Build step
    build_res = LeanBuildSubagent(project_root=args.project_root).run()
    print("Build finished")

    # Feedback parse step
    parse_res = FeedbackParseSubagent(output=build_res.output).run()
    if parse_res.is_success:
        print("Build success! 🎉")
    else:
        print(f"Build failed -> {parse_res.message}")

    # Print raw build output for inspection (trimmed)
    print("\n--- Raw build output (first 100 lines) ---")
    lines = build_res.output.splitlines()[:100]
    print("\n".join(lines))


def _cli() -> None:
    parser = argparse.ArgumentParser(description="Run concrete Lean agent pipeline")
    parser.add_argument("--pdf", required=True, help="Path to PDF textbook")
    parser.add_argument("--lean-file", required=True, help="Lean file to edit")
    parser.add_argument(
        "--project-root", default=".", help="Project root for lake build"
    )
    parser.add_argument(
        "--edit",
        default="-- edit by pipeline",
        help="Lean code snippet to append (default: comment)",
    )
    ns = parser.parse_args()
    run_pipeline(
        PipelineArgs(
            project_root=Path(ns.project_root).resolve(),
            pdf_path=Path(ns.pdf).resolve(),
            lean_file=Path(ns.lean_file).resolve(),
            edit=ns.edit,
        )
    )


if __name__ == "__main__":
    _cli()
