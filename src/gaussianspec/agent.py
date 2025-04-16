"""
MorphCloud-driven Lean agent for Gaussian elimination spec development.
- Drives Lean code edits, builds, and feedback loop.
- Uses morphcloud for orchestration.
- Uses subprocess for Lean build and feedback.
- Designed for compositional, functional extension.
"""

from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterator, Sequence, Any
import subprocess
import morphcloud
from pdf2image import convert_from_path
import pytesseract


# --- Types ---
@dataclass(frozen=True)
class LeanEdit:
    file: Path
    edit: str
    description: str


@dataclass(frozen=True)
class BuildResult:
    success: bool
    output: str


# --- Core functions ---
def run_lake_build(project_root: Path) -> BuildResult:
    """Run `lake build` and return result."""
    proc = subprocess.run(
        ["lake", "build"], cwd=project_root, capture_output=True, text=True
    )
    return BuildResult(success=proc.returncode == 0, output=proc.stdout + proc.stderr)


def apply_lean_edit(edit: LeanEdit) -> None:
    """Apply an edit to a Lean file."""
    with edit.file.open("a") as f:
        f.write("\n" + edit.edit)


def parse_build_feedback(output: str) -> str:
    """Extract error or success message from build output."""
    # Simple heuristic: return first error or 'success'
    for line in output.splitlines():
        if "error:" in line:
            return line
    return "success"


# --- OCR Preprocessing ---
def ocr_pdf_to_text(
    pdf_path: Path, txt_path: Path | None = None, lang: str = "eng"
) -> Path:
    """
    OCR the given PDF to a text file. If the text file exists, return it (cache).
    Args:
        pdf_path: Path to the PDF file.
        txt_path: Path to output text file (default: pdf_path.with_suffix('.txt'))
        lang: Language for OCR (default: 'eng')
    Returns:
        Path to the text file with OCR result.
    """
    if txt_path is None:
        txt_path = pdf_path.with_suffix(".txt")
    if txt_path.exists():
        return txt_path
    images = convert_from_path(str(pdf_path))
    text = "\n".join(pytesseract.image_to_string(img, lang=lang) for img in images)
    txt_path.write_text(text)
    return txt_path


# --- Agent loop ---
def agent_loop(
    project_root: Path,
    edits: Sequence[LeanEdit],
    build_fn: Callable[[Path], BuildResult] = run_lake_build,
    edit_fn: Callable[[LeanEdit], None] = apply_lean_edit,
    feedback_fn: Callable[[str], str] = parse_build_feedback,
) -> Iterator[str]:
    """Drive Lean code edits and builds, yielding feedback after each step."""
    for edit in edits:
        edit_fn(edit)
        result = build_fn(project_root)
        feedback = feedback_fn(result.output)
        yield feedback


# --- Pipeline composition ---
def agent_pipeline(
    project_root: Path,
    pdf_path: Path,
    edits: Sequence[LeanEdit],
    ocr_fn: Callable[[Path], Path] = lambda pdf: ocr_pdf_to_text(pdf),
    build_fn: Callable[[Path], BuildResult] = run_lake_build,
    edit_fn: Callable[[LeanEdit], None] = apply_lean_edit,
    feedback_fn: Callable[[str], str] = parse_build_feedback,
) -> Iterator[str]:
    """
    Full agent pipeline: OCR textbook, then run Lean edit/build/feedback loop.
    Yields feedback after each Lean step.
    """
    ocr_txt = ocr_fn(pdf_path)
    yield f"OCR complete: {ocr_txt}"
    yield from agent_loop(project_root, edits, build_fn, edit_fn, feedback_fn)
h

# --- Example usage (to be replaced by MorphCloud orchestration) ---
if __name__ == "__main__":
    root = Path(__file__).parent.parent.parent
    edits = [
        LeanEdit(
            file=root / "GaussianSpec.lean",
            edit="-- Example edit by agent",
            description="Add a comment for testing.",
        )
    ]
    for feedback in agent_loop(root, edits):
        print("Agent feedback:", feedback)
