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
    """Write a Lean file embedding the OCR text as a block comment and parse it into Lean definitions."""
    out_dir.mkdir(parents=True, exist_ok=True)
    lean_path = out_dir / "Spec.lean"
    content = txt_path.read_text()
    
    lean_text = "/-\n" + indent(content, " ") + "\n-/\n\n"
    
    lean_definitions = parse_ocr_to_lean(content)
    lean_text += lean_definitions
    
    lean_path.write_text(lean_text)
    return lean_path


def parse_ocr_to_lean(ocr_text: str) -> str:
    """Parse OCR text into Lean definitions.
    
    Extracts mathematical definitions, theorems, and algorithms from OCR text
    and converts them into Lean syntax.
    """
    lines = ocr_text.split('\n')
    
    lean_defs = []
    
    in_definition = False
    current_def = []
    definition_name = ""
    
    for line in lines:
        if not line.strip():
            continue
            
        if "definition" in line.lower() or "theorem" in line.lower() or "algorithm" in line.lower():
            if in_definition:
                lean_defs.append(format_lean_definition(definition_name, current_def))
            
            in_definition = True
            current_def = [line]
            
            words = line.split()
            if len(words) > 1:
                definition_name = words[1].strip(":.,()")
            else:
                definition_name = "unnamed"
        
        elif in_definition:
            current_def.append(line)
            
            if line.strip().endswith(".") or line.strip().endswith(":"):
                lean_defs.append(format_lean_definition(definition_name, current_def))
                in_definition = False
                current_def = []
    
    if in_definition:
        lean_defs.append(format_lean_definition(definition_name, current_def))
    
    if not lean_defs:
        lean_defs.append("-- No formal definitions detected in OCR text\n")
        lean_defs.append("-- Example of how a definition might look:\n")
        lean_defs.append("def gaussianElimination (A : Matrix n n ℝ) : Matrix n n ℝ :=\n  sorry\n")
        lean_defs.append("\n-- Example of how a theorem might look:\n")
        lean_defs.append("theorem gaussianElimination_is_left_inverse (A : Matrix n n ℝ) (h : IsNonsingular A) :\n  gaussianElimination A * A = 1 :=\n  sorry\n")
    
    return "\n".join(lean_defs)


def format_lean_definition(name: str, lines: list[str]) -> str:
    """Format extracted definition into Lean syntax."""
    comment = "-- Original text:\n" + "\n".join(f"-- {line}" for line in lines)
    
    first_line = lines[0].lower()
    
    if "definition" in first_line:
        lean_def = f"\ndef {name} : sorry :=\n  sorry"
    elif "theorem" in first_line:
        lean_def = f"\ntheorem {name} : sorry :=\n  sorry"
    elif "algorithm" in first_line:
        lean_def = f"\ndef {name} : sorry :=\n  sorry -- Implemented from algorithm"
    else:
        lean_def = f"\n-- Extracted content: {name}\n-- TODO: Convert to formal Lean definition"
    
    return f"{comment}\n{lean_def}\n"


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
        "--strip-right",
        type=int,
        default=0,
        help="Crop this many pixels from the right margin of each page before OCR",
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

    # Sanitize common mistakes coming from shell/just variable expansion, e.g.
    # when `pages="pages=1-2"` leaks through.
    if isinstance(args.pages, str) and args.pages.startswith("pages="):
        args.pages = args.pages[len("pages=") :]

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
                strip_right_px=args.strip_right,
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
            strip_right_px=args.strip_right,
        )
        lean_file = create_lean_file(txt_path, args.out_dir / "Spec")
        print(f"OCR text written to {txt_path}")
        print(f"Lean skeleton written to {lean_file}")


if __name__ == "__main__":
    main()
