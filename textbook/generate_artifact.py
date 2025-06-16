"""Generate a demonstration artifact for OCR text parsing.

This script creates a side-by-side comparison of OCR text and its translation to Lean.
"""

from pathlib import Path
import sys
import os

sys.path.insert(0, str(Path(__file__).parent.parent))

from gaussianspec.pdf_pipeline import create_lean_file, parse_ocr_to_lean

def generate_artifact():
    """Generate a demonstration artifact showing OCR text parsing."""
    ocr_text_path = Path("textbook/sample_ocr_text.txt")
    output_dir = Path("textbook/demo_output")
    artifact_path = Path("textbook/ocr_parsing_demo.md")
    
    if not ocr_text_path.exists():
        print(f"Error: OCR text file not found at {ocr_text_path}")
        return
    
    ocr_text = ocr_text_path.read_text()
    
    lean_file_path = create_lean_file(ocr_text_path, output_dir)
    lean_content = lean_file_path.read_text()
    
    artifact_content = "# OCR Text Parsing Demonstration\n\n"
    artifact_content += "This file demonstrates the OCR text parsing functionality implemented in `pdf_pipeline.py`. "
    artifact_content += "It shows a side-by-side comparison of the original OCR text and the generated Lean definitions.\n\n"
    
    artifact_content += "## Original OCR Text\n\n"
    artifact_content += "```\n" + ocr_text + "\n```\n\n"
    
    artifact_content += "## Generated Lean Definitions\n\n"
    artifact_content += "```lean\n" + lean_content + "\n```\n\n"
    
    artifact_content += "## Explanation\n\n"
    artifact_content += "The parser identifies definitions, theorems, and algorithms in the OCR text and converts them into Lean syntax. "
    artifact_content += "Each extracted definition includes:\n\n"
    artifact_content += "1. The original text as a comment\n"
    artifact_content += "2. A Lean definition with appropriate syntax\n\n"
    
    artifact_content += "This implementation provides a basic foundation that can be extended with more sophisticated parsing logic in the future.\n"
    
    artifact_path.write_text(artifact_content)
    print(f"Artifact generated at {artifact_path}")
    
    return artifact_path

if __name__ == "__main__":
    generate_artifact()
