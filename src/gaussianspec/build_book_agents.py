from __future__ import annotations

"""Agent driver that converts Chapter 2 OCR into a Verso book.

Usage (from project root):
    uv run src/gaussianspec/build_book_agents.py

This will:
1. Ensure `generated/versobook` is a Lake project with Verso dependency.
2. Read the first few lines of Chapter 2 OCR text and write a minimal
   `Book/Chapter2.lean` file that compiles through Verso.
3. Print next-step hints for incremental ingestion.
"""

from pathlib import Path
from textwrap import indent, dedent
from gaussianspec.subagents import LakeProjectInitSubagent

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

GENERATED_DIR = Path("generated")
VERSOBOOK_DIR = GENERATED_DIR / "versobook"
OCR_TEXT_PATH = GENERATED_DIR / "Numerical_Recipes_in_C_1-149.txt"
CHAPTER_FILE = VERSOBOOK_DIR / "Book" / "Chapter2.lean"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def read_chapter2_intro(max_lines: int = 20) -> str:
    """Return the first *max_lines* of Chapter 2 from the OCR txt file."""
    if not OCR_TEXT_PATH.exists():
        raise FileNotFoundError(f"OCR text not found: {OCR_TEXT_PATH}")

    # A naive heuristic: Chapter 2 starts at the first line containing 'Chapter 2'.
    lines = OCR_TEXT_PATH.read_text().splitlines()
    start_idx = next((i for i, ln in enumerate(lines) if "Chapter 2" in ln), None)
    if start_idx is None:
        start_idx = 0  # fallback to beginning

    end_idx = min(start_idx + max_lines, len(lines))
    excerpt = "\n".join(lines[start_idx:end_idx])
    return excerpt.strip()


# ---------------------------------------------------------------------------
# Main driver
# ---------------------------------------------------------------------------


def main() -> None:
    # 1. Initialize Lake project if needed
    init_result = LakeProjectInitSubagent(VERSOBOOK_DIR).run()
    if not init_result.success:
        raise RuntimeError(f"Failed to init Lake project: {init_result.error}")

    # 2. Build the Chapter2 file if absent
    excerpt = read_chapter2_intro(max_lines=25)

    chapter_source = (
        dedent(
            f"""
        import Verso

        #doc (Manual) "Solution of Linear Equations" =>

        """
        )
        + "\n"
        + indent(excerpt, "")
        + "\n"
    )

    CHAPTER_FILE.parent.mkdir(parents=True, exist_ok=True)
    CHAPTER_FILE.write_text(chapter_source)

    try:
        print("Wrote", CHAPTER_FILE.resolve().relative_to(Path.cwd().resolve()))
    except ValueError:
        # Fallback to absolute path if relative fails (e.g. differing mount points)
        print("Wrote", CHAPTER_FILE.resolve())
    print("You can now run: just build-book")


if __name__ == "__main__":
    main()
