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
    parser.add_argument(
        "--out-dir", type=Path, default=Path("generated"), help="Output directory"
    )
    parser.add_argument(
        "--pages",
        type=str,
        default="1-100",
        help="Page range like 1-100 or 50- for till end",
    )
    parser.add_argument(
        "--method",
        type=str,
        choices=["auto", "openai", "gemini", "tesseract"],
        default="auto",
        help="OCR backend to use",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Process the entire PDF in chunks (see --chunk-size) instead of a single range",
    )
    parser.add_argument(
        "--chunk-size",
        type=int,
        default=50,
        help="Number of pages per chunk when using --all",
    )
    args = parser.parse_args()

    # Ensure base output directory exists
    args.out_dir.mkdir(parents=True, exist_ok=True)

    if args.all:
        from pdf2image import pdfinfo_from_path

        info = pdfinfo_from_path(str(args.pdf))
        total_pages = int(info["Pages"])

        spec_dir = args.out_dir / "Spec"
        spec_dir.mkdir(parents=True, exist_ok=True)

        chunk_files: list[Path] = []
        for start_page in range(1, total_pages + 1, args.chunk_size):
            end_page = min(start_page + args.chunk_size - 1, total_pages)

            txt_path = ocr_pdf_to_text(
                args.pdf,
                args.out_dir / (args.pdf.stem + f"_{start_page}-{end_page}.txt"),
                start_page=start_page,
                end_page=end_page,
                method=args.method,
            )

            chunk_lean = create_lean_file(
                txt_path, spec_dir / f"Chunk{start_page:04d}_{end_page:04d}"
            )
            chunk_files.append(chunk_lean)
            print(f"Chunk {start_page}-{end_page}: {txt_path} -> {chunk_lean}")

        # Create root Spec.lean that imports chunks
        root_spec = spec_dir / "Spec.lean"
        with root_spec.open("w") as f:
            for cf in chunk_files:
                # Build Lean module name relative to generated directory
                # e.g. if cf is generated/Spec/Chunk0001_0050.lean -> generated.Spec.Chunk0001_0050
                mod_name = (
                    cf.relative_to(args.out_dir.parent)
                    .with_suffix("")
                    .as_posix()
                    .replace("/", ".")
                )
                f.write(f"import {mod_name}\n")

        print(f"Root Spec file written to {root_spec}")
    else:
        # Single range logic (existing)
        if "-" in args.pages:
            start_s, end_s = args.pages.split("-", 1)
            start_page = int(start_s) if start_s else 1
            end_page = int(end_s) if end_s else None
        else:
            start_page = int(args.pages)
            end_page = start_page

        txt_path = ocr_pdf_to_text(
            args.pdf,
            args.out_dir / (args.pdf.stem + f"_{start_page}-{end_page}.txt"),
            start_page=start_page,
            end_page=end_page,
            method=args.method,
        )
        lean_file = create_lean_file(txt_path, args.out_dir / "Spec")
        print(f"OCR text written to {txt_path}")
        print(f"Lean skeleton written to {lean_file}")


if __name__ == "__main__":
    main()
