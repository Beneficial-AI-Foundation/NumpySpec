#!/usr/bin/env python3
"""Verify that Lean implementations and specifications are aligned for numpy constants."""

import json
import sys
from pathlib import Path
import tempfile

# Add the src directory to the Python path so we can import gaussianspec modules
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from gaussianspec.spec_verifier import verify_specs_from_json, SpecEvaluation


def load_constants_data(constants_dir: Path, json_filename: str = "data.json") -> list:
    """Load constants from the JSON file and read their corresponding files.
    
    Parameters
    ----------
    constants_dir : Path
        Directory containing the constants JSON and associated files
    json_filename : str
        Name of the JSON file containing constant definitions
        
    Returns
    -------
    list
        List of dictionaries with docstring, python, lean_function, and lean_spec
    """
    json_path = constants_dir / json_filename
    if not json_path.exists():
        raise FileNotFoundError(f"Constants file not found: {json_path}")
    
    with open(json_path, 'r') as f:
        constants_data = json.load(f)
    
    # Convert to the format expected by verify_specs_from_json
    spec_data = []
    
    for const_name, const_info in constants_data.items():
        try:
            # Read Python file
            python_file = constants_dir / const_info['python']
            if python_file.exists():
                python_code = python_file.read_text()
            else:
                print(f"Warning: Python file not found: {python_file}")
                python_code = "# File not found"
            
            # Read Lean implementation file
            lean_file = constants_dir / const_info['lean']
            if lean_file.exists():
                lean_code = lean_file.read_text()
            else:
                print(f"Warning: Lean file not found: {lean_file}")
                lean_code = "-- File not found"
            
            # Read Lean spec file
            spec_file = constants_dir / const_info['spec']
            if spec_file.exists():
                spec_code = spec_file.read_text()
            else:
                print(f"Warning: Spec file not found: {spec_file}")
                spec_code = "-- File not found"
            
            spec_data.append({
                'docstring': f"{const_name}: {const_info['doc']}",
                'python': python_code,
                'lean_function': lean_code,
                'lean_spec': spec_code
            })
        except Exception as e:
            print(f"Error processing {const_name}: {e}")
    
    return spec_data


def verify_constants(constants_dir: Path, json_filename: str = "data.json") -> list[SpecEvaluation]:
    """Verify all constants in the given directory.
    
    Parameters
    ----------
    constants_dir : Path
        Directory containing the constants JSON and associated files
    json_filename : str
        Name of the JSON file containing constant definitions
        
    Returns
    -------
    list[SpecEvaluation]
        Results of verifying each constant
    """
    # Load and prepare data
    spec_data = load_constants_data(constants_dir, json_filename)
    
    # Write to temporary JSON file for verify_specs_from_json
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as tmp:
        json.dump(spec_data, tmp, indent=2)
        tmp_path = Path(tmp.name)
    
    try:
        # Verify specs
        results = verify_specs_from_json(tmp_path)
    finally:
        # Clean up temp file
        tmp_path.unlink()
    
    return results


def main():
    """Main entry point for the verifier script."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Verify numpy constants Lean specifications')
    parser.add_argument('constants_dir', type=Path, 
                       help='Directory containing constants JSON and files')
    parser.add_argument('--json-file', default='data.json',
                       help='Name of the JSON file (default: data.json)')
    parser.add_argument('--verbose', action='store_true',
                       help='Show detailed output including build logs')
    
    args = parser.parse_args()
    
    if not args.constants_dir.exists():
        print(f"Error: Directory does not exist: {args.constants_dir}")
        sys.exit(1)
    
    print(f"Verifying constants in: {args.constants_dir}")
    print(f"Using JSON file: {args.json_file}")
    print("-" * 60)
    
    # Run verification
    results = verify_constants(args.constants_dir, args.json_file)
    
    # Display results
    success_count = sum(1 for r in results if r.success)
    total_count = len(results)
    
    for i, result in enumerate(results):
        status = "✓ PASS" if result.success else "✗ FAIL"
        const_name = result.docstring.split(":")[0] if ":" in result.docstring else f"Constant {i+1}"
        print(f"{status} - {const_name}")
        
        if not result.success or args.verbose:
            # Show truncated log for failures, full log if verbose
            log_lines = result.log.strip().split('\n')
            if not args.verbose and len(log_lines) > 10:
                print("  Log (truncated):")
                for line in log_lines[:5]:
                    print(f"    {line}")
                print("    ...")
                for line in log_lines[-5:]:
                    print(f"    {line}")
            else:
                print("  Log:")
                for line in log_lines:
                    print(f"    {line}")
            print()
    
    print("-" * 60)
    print(f"Summary: {success_count}/{total_count} specs verified successfully")
    
    # Exit with non-zero code if any failures
    sys.exit(0 if success_count == total_count else 1)


if __name__ == "__main__":
    main() 