from __future__ import annotations
"""PDF → OCR → Lean skeleton pipeline.

Example usage:
    uv run -m gaussianspec.pdf_pipeline path/to/textbook.pdf --out-dir generated

This will:
1. OCR the PDF to `out_dir/textbook.txt` (cached).
2. Create `out_dir/Spec/Spec.lean` with the OCR text inside a comment block so
   it can be inspected in Lean.
"""

import argparse
from pathlib import Path
from textwrap import indent

from .agent import ocr_pdf_to_text


def create_lean_file(txt_path: Path, out_dir: Path) -> Path:
    """Write a Lean file embedding the OCR text as a block comment."""
    out_dir.mkdir(parents=True, exist_ok=True)
    lean_path = out_dir / "Spec.lean"
    content = txt_path.read_text()
    lean_text = "/-\n" + indent(content, " ") + "\n-/\n"
    lean_text += "\n-- TODO: parse the OCR text into Lean definitions\n"
    lean_path.write_text(lean_text)
    return lean_path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("pdf", type=Path, help="Path to input PDF")
    parser.add_argument("--out-dir", type=Path, default=Path("generated"), help="Output directory")
    args = parser.parse_args()

    txt_path = ocr_pdf_to_text(args.pdf, args.out_dir / (args.pdf.stem + ".txt"))
    lean_file = create_lean_file(txt_path, args.out_dir / "Spec")
    print(f"OCR text written to {txt_path}")
    print(f"Lean skeleton written to {lean_file}")


if __name__ == "__main__":
    main() 