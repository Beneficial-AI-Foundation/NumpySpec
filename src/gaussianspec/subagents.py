"""
Subagents for compositional, feedback-driven Lean agent system.
Each subagent is a pure dataclass with a run() method and clear feedback.
Created: 2025-04-15T21:11 UTC
"""

from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Optional
from pdf2image import convert_from_path
import pytesseract
import subprocess


# --- OCR Subagent ---
@dataclass(frozen=True)
class OCRResult:
    txt_path: Path
    success: bool
    error: Optional[str] = None


@dataclass(frozen=True)
class OCRSubagent:
    pdf_path: Path
    txt_path: Optional[Path] = None
    lang: str = "eng"

    def run(self) -> OCRResult:
        """Run OCR on the PDF, cache result, return feedback."""
        txt_path = self.txt_path or self.pdf_path.with_suffix(".txt")
        if txt_path.exists():
            return OCRResult(txt_path, True)
        try:
            images = convert_from_path(str(self.pdf_path))
            text = "\n".join(
                pytesseract.image_to_string(img, lang=self.lang) for img in images
            )
            txt_path.write_text(text)
            return OCRResult(txt_path, True)
        except Exception as e:
            return OCRResult(txt_path, False, str(e))


# --- Lean Edit Subagent ---
@dataclass(frozen=True)
class LeanEditResult:
    file: Path
    success: bool
    error: Optional[str] = None


@dataclass(frozen=True)
class LeanEditSubagent:
    file: Path
    edit: str

    def run(self) -> LeanEditResult:
        """Apply an edit to a Lean file."""
        try:
            with self.file.open("a") as f:
                f.write("\n" + self.edit)
            return LeanEditResult(self.file, True)
        except Exception as e:
            return LeanEditResult(self.file, False, str(e))


# --- Lean Build Subagent ---
@dataclass(frozen=True)
class LeanBuildResult:
    success: bool
    output: str


@dataclass(frozen=True)
class LeanBuildSubagent:
    project_root: Path

    def run(self) -> LeanBuildResult:
        """Run `lake build` and return result."""
        proc = subprocess.run(
            ["lake", "build"], cwd=self.project_root, capture_output=True, text=True
        )
        return LeanBuildResult(proc.returncode == 0, proc.stdout + proc.stderr)


# --- Feedback Parse Subagent ---
@dataclass(frozen=True)
class FeedbackParseResult:
    message: str
    is_success: bool


@dataclass(frozen=True)
class FeedbackParseSubagent:
    output: str

    def run(self) -> FeedbackParseResult:
        """Parse Lean build output for actionable feedback."""
        for line in self.output.splitlines():
            if "error:" in line:
                return FeedbackParseResult(line, False)
        return FeedbackParseResult("success", True)
