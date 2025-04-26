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
    OCRResult,
    LeanEditSubagent,
    LeanEditResult,
    LeanBuildSubagent,
    LeanBuildResult,
    FeedbackParseSubagent,
    FeedbackParseResult,
)


@dataclass
class PipelineArgs:
    project_root: Path
    pdf_path: Path
    lean_file: Path
    edit: str = "-- edit by pipeline"


@dataclass
class PipelineResult:
    """Aggregated results of a single pipeline run so downstream agents can reuse them."""

    ocr: OCRResult
    edit: LeanEditResult
    build: LeanBuildResult
    parse: FeedbackParseResult


def run_pipeline(args: PipelineArgs) -> PipelineResult:
    """Run the end-to-end OCR→edit→build pipeline and *return* all intermediate
    artefacts so that other agents (e.g. RL loops, orchestrators) can inspect
    them programmatically.
    """

    # OCR step
    ocr_res = OCRSubagent(pdf_path=args.pdf_path).run()
    if not ocr_res.success:
        # Even on failure we still return a PipelineResult for debuggability
        return PipelineResult(
            ocr=ocr_res,
            edit=LeanEditResult(
                file=args.lean_file, success=False, error="skipped due to OCR failure"
            ),
            build=LeanBuildResult(success=False, output=""),
            parse=FeedbackParseResult(
                message=ocr_res.error or "OCR failed", is_success=False
            ),
        )

    # Lean edit step
    edit_res = LeanEditSubagent(file=args.lean_file, edit=args.edit).run()

    # Build step (only attempted if edit succeeded)
    build_res: LeanBuildResult
    if edit_res.success:
        build_res = LeanBuildSubagent(project_root=args.project_root).run()
    else:
        build_res = LeanBuildResult(success=False, output="skipped due to edit failure")

    # Parse Lean build feedback for actionable message
    parse_res = FeedbackParseSubagent(output=build_res.output).run()

    # Side-effect: pretty console log for human operators. Downstream automation
    # should rely on the returned PipelineResult instead.
    _pretty_print_pipeline(ocr_res, edit_res, build_res, parse_res)

    return PipelineResult(ocr=ocr_res, edit=edit_res, build=build_res, parse=parse_res)


def _pretty_print_pipeline(
    ocr: OCRResult,
    edit: LeanEditResult,
    build: LeanBuildResult,
    parse: FeedbackParseResult,
) -> None:
    """Human-friendly summary of pipeline stages (non-essential side effect)."""

    if ocr.success:
        print(f"OCR completed   -> {ocr.txt_path}")
    else:
        print(f"OCR failed      -> {ocr.error}")

    if edit.success:
        print(f"Edit applied    -> {edit.file}")
    else:
        print(f"Edit failed     -> {edit.error}")

    print("Build finished  ->", "OK" if build.success else "FAILED")
    if parse.is_success:
        print("Build status    -> success 🎉")
    else:
        print(f"Build status    -> {parse.message}")

    # Trimmed build output for quick inspection
    print("\n--- Raw build output (first 100 lines) ---")
    lines = build.output.splitlines()[:100]
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
    result = run_pipeline(
        PipelineArgs(
            project_root=Path(ns.project_root).resolve(),
            pdf_path=Path(ns.pdf).resolve(),
            lean_file=Path(ns.lean_file).resolve(),
            edit=ns.edit,
        )
    )

    # Return code is derived from build success so shell scripts can react.
    import sys

    sys.exit(0 if result.build.success else 1)


if __name__ == "__main__":
    _cli()
