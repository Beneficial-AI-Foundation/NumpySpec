#!/usr/bin/env python3
"""
Script to run the LLM-based Lean code and spec generation pipeline.

Usage:
    python scripts/run_llm_pipeline.py --input <python_file> --output <output_dir>
    python scripts/run_llm_pipeline.py --input example_input.py --output generated/
"""

import argparse
import sys
from pathlib import Path

# Add src to path to import gaussianspec modules
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from gaussianspec.llm_generator import LLMCodeSpecSubagent


def main():
    parser = argparse.ArgumentParser(description="Run LLM-based Lean generation pipeline")
    parser.add_argument(
        "--input", 
        type=Path, 
        required=True,
        help="Input Python file to process"
    )
    parser.add_argument(
        "--output", 
        type=Path, 
        default=Path("generated"),
        help="Output directory for generated Lean files"
    )
    parser.add_argument(
        "--model", 
        type=str, 
        default="nvidia/Nemotron-Research-Reasoning-Qwen-1.5B",
        help="HuggingFace model to use for generation"
    )
    parser.add_argument(
        "--debug", 
        action="store_true",
        help="Save full LLM communications for debugging"
    )
    
    args = parser.parse_args()
    
    if not args.input.exists():
        print(f"Error: Input file {args.input} does not exist")
        sys.exit(1)
    
    # Read Python input
    python_input = args.input.read_text()
    
    print(f"Processing {args.input} with model {args.model}")
    print(f"Output directory: {args.output}")
    if args.debug:
        print("Debug mode enabled - full LLM communications will be saved")
    
    # Run the LLM generation pipeline
    subagent = LLMCodeSpecSubagent(
        python_input=python_input,
        model_name=args.model,
        output_dir=args.output,
        debug_save_responses=args.debug
    )
    
    code_result, spec_result = subagent.run()
    
    print("\n=== Code Generation Results ===")
    if code_result.success:
        print("✓ Lean code generation successful")
        print(f"Generated code:\n{code_result.lean_code}")
        
        code_file = args.output / "generated_code.lean"
        print(f"Saved to: {code_file}")
    else:
        print(f"✗ Lean code generation failed: {code_result.error}")
    
    print("\n=== Spec Generation Results ===")
    if spec_result.success:
        print("✓ Lean spec generation successful")
        print(f"Generated spec:\n{spec_result.lean_spec}")
        
        spec_file = args.output / "generated_spec.lean"
        print(f"Saved to: {spec_file}")
    else:
        print(f"✗ Lean spec generation failed: {spec_result.error}")

if __name__ == "__main__":
    main()
