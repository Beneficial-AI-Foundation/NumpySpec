#!/usr/bin/env python3
"""Local-only verifier for numpy constants that doesn't require remote API."""

import json
import sys
import re
import subprocess
import tempfile
from pathlib import Path

# Add the src directory to the Python path so we can import gaussianspec modules
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from gaussianspec.spec_verifier import SpecEvaluation
from gaussianspec.subagents import LeanBuildResult


def load_and_process_constants(constants_dir: Path, json_filename: str = "data.json") -> list[dict]:
    """Load constants and process their files to handle relative imports."""
    json_path = constants_dir / json_filename
    if not json_path.exists():
        raise FileNotFoundError(f"Constants file not found: {json_path}")
    
    with open(json_path, 'r') as f:
        constants_data = json.load(f)
    
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
            
            # Read Lean spec file and process imports
            spec_file = constants_dir / const_info['spec']
            if spec_file.exists():
                spec_code = spec_file.read_text()
                # Remove relative imports since we'll include the implementation directly
                spec_code = remove_relative_imports(spec_code)
            else:
                print(f"Warning: Spec file not found: {spec_file}")
                spec_code = "-- File not found"
            
            spec_data.append({
                'docstring': f"{const_name}: {const_info['doc'][:100]}...",
                'python': python_code,
                'lean_function': lean_code,
                'lean_spec': spec_code,
                'constant_name': const_name
            })
        except Exception as e:
            print(f"Error processing {const_name}: {e}")
    
    return spec_data


def remove_relative_imports(lean_code: str) -> str:
    """Remove relative imports from Lean code since we combine files."""
    lines = lean_code.split('\n')
    filtered_lines = []
    
    for line in lines:
        # Skip lines that are relative imports
        if re.match(r'\s*import\s+\./', line.strip()):
            continue
        filtered_lines.append(line)
    
    return '\n'.join(filtered_lines)


def verify_lean_constant_local(lean_fn: str, lean_spec: str, constant_name: str) -> LeanBuildResult:
    """Compile a single constant's Lean function and spec using local lake build."""
    
    with tempfile.TemporaryDirectory() as tmpdir:
        project_dir = Path(tmpdir) / "lean_project"
        project_dir.mkdir()
        
        # Create basic lakefile.toml
        lakefile_content = """[package]
name = "test_constants"
version = "0.1.0"

[[lean_lib]]
name = "TestConstants"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
"""
        (project_dir / "lakefile.toml").write_text(lakefile_content)
        
        # Create the Lean source file
        lean_source = f"""import Mathlib

{lean_fn}

{lean_spec}
"""
        
        lean_lib_dir = project_dir / "TestConstants"
        lean_lib_dir.mkdir()
        
        lean_file = lean_lib_dir / f"{constant_name.replace('.', '_').replace('-', '_')}.lean"
        lean_file.write_text(lean_source)
        
        print(f"  Building {constant_name} with local lake build...")
        print(f"  Project directory: {project_dir}")

        # exit(0)
        
        # Run lake build
        try:
            proc = subprocess.run(
                ["lake", "build"], 
                cwd=project_dir, 
                capture_output=True, 
                text=True,
                timeout=30 # 5 minute timeout
            )

            print(proc.stdout)
            print(proc.stderr)
            
            output = proc.stdout + proc.stderr
            success = proc.returncode == 0
            
            return LeanBuildResult(success, output)
            
        except subprocess.TimeoutExpired:
            return LeanBuildResult(False, "Build timed out after 5 minutes")
        except Exception as e:
            return LeanBuildResult(False, f"Build failed with exception: {e}")


def verify_lean_constant_simple(lean_fn: str, lean_spec: str, constant_name: str) -> LeanBuildResult:
    """Simple verification by checking Lean syntax without full mathlib build."""
    
    with tempfile.TemporaryDirectory() as tmpdir:
        # Create a simple Lean file to check syntax
        lean_source = f"""{lean_fn}

{lean_spec}
"""
        
        lean_file = Path(tmpdir) / f"{constant_name.replace('.', '_')}.lean"
        lean_file.write_text(lean_source)
        
        print(f"  Checking {constant_name} Lean syntax...")
        
        # Use lean --check to verify syntax without building
        try:
            proc = subprocess.run(
                ["lean", "--check", str(lean_file)], 
                capture_output=True, 
                text=True,
                timeout=30
            )
            
            output = proc.stdout + proc.stderr
            success = proc.returncode == 0
            
            if success:
                output = "Lean syntax check passed"
            
            return LeanBuildResult(success, output)
            
        except subprocess.TimeoutExpired:
            return LeanBuildResult(False, "Syntax check timed out")
        except FileNotFoundError:
            return LeanBuildResult(False, "Lean executable not found. Please install Lean 4.")
        except Exception as e:
            return LeanBuildResult(False, f"Syntax check failed: {e}")


def verify_constants_local(constants_dir: Path, json_filename: str = "data.json", use_full_build: bool = False) -> list[SpecEvaluation]:
    """Local verification that handles numpy constants without remote API."""
    
    # Load and process data
    spec_data = load_and_process_constants(constants_dir, json_filename)
    
    results = []
    
    for item in spec_data:
        const_name = item['constant_name']
        doc = item['docstring']
        py_code = item['python']
        lean_fn = item['lean_function']
        lean_spec = item['lean_spec']
        
        print(f"\n🔍 Verifying {const_name}...")
        
        # Validate Python syntax first
        try:
            compile(py_code, f"<{const_name}.py>", "exec")
            print(f"  ✓ Python syntax valid")
        except SyntaxError as e:
            print(f"  ✗ Python syntax error: {e}")
            results.append(SpecEvaluation(doc, False, f"Invalid Python syntax: {e}"))
            continue
        
        # Verify Lean code
        try:
            if use_full_build:
                build_result = verify_lean_constant_local(lean_fn, lean_spec, const_name)
            else:
                build_result = verify_lean_constant_simple(lean_fn, lean_spec, const_name)
            
            if build_result.success:
                print(f"  ✓ Lean verification successful")
                results.append(SpecEvaluation(doc, True, build_result.output))
            else:
                print(f"  ✗ Lean verification failed")
                results.append(SpecEvaluation(doc, False, build_result.output))
                
        except Exception as e:
            print(f"  ✗ Verification error: {e}")
            results.append(SpecEvaluation(doc, False, f"Verification error: {e}"))
    
    return results


def main():
    """Main entry point for the local constants verifier."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Local numpy constants Lean specifications verifier')
    parser.add_argument('constants_dir', type=Path, 
                       help='Directory containing constants JSON and files')
    parser.add_argument('--json-file', default='data.json',
                       help='Name of the JSON file (default: data.json)')
    parser.add_argument('--verbose', action='store_true',
                       help='Show detailed output including build logs')
    parser.add_argument('--dry-run', action='store_true',
                       help='Parse files but skip actual Lean compilation')
    parser.add_argument('--full-build', action='store_true',
                       help='Use full lake build instead of syntax check only')
    parser.add_argument('--syntax-only', action='store_true',
                       help='Only check Lean syntax, don\'t attempt full compilation')
    
    args = parser.parse_args()
    
    if not args.constants_dir.exists():
        print(f"Error: Directory does not exist: {args.constants_dir}")
        sys.exit(1)
    
    print(f"🏠 Local Numpy Constants Verifier")
    print(f"Directory: {args.constants_dir}")
    print(f"JSON file: {args.json_file}")
    if args.full_build:
        print("Mode: Full lake build (requires mathlib)")
    else:
        print("Mode: Syntax check only")
    print("-" * 70)
    
    if args.dry_run:
        print("DRY RUN MODE - Parsing files only")
        spec_data = load_and_process_constants(args.constants_dir, args.json_file)
        print(f"\nParsed {len(spec_data)} constants:")
        for item in spec_data:
            print(f"  - {item['constant_name']}")
        return
    
    # Run verification
    results = verify_constants_local(args.constants_dir, args.json_file, args.full_build)
    
    # Display results
    print("\n" + "=" * 70)
    print("VERIFICATION RESULTS")
    print("=" * 70)
    
    success_count = 0
    total_count = len(results)
    
    for i, result in enumerate(results):
        if result.success:
            success_count += 1
            status = "✅ PASS"
        else:
            status = "❌ FAIL"
        
        # Extract constant name from docstring
        const_name = result.docstring.split(":")[0] if ":" in result.docstring else f"Constant {i+1}"
        print(f"\n{status} - {const_name}")
        
        if not result.success or args.verbose:
            # Show build log
            log_lines = result.log.strip().split('\n') if result.log else ["No log available"]
            
            if not args.verbose and len(log_lines) > 10:
                print("  Build log (truncated):")
                for line in log_lines[:5]:
                    print(f"    {line}")
                print("    ... (use --verbose for full log)")
                if len(log_lines) > 5:
                    for line in log_lines[-3:]:
                        print(f"    {line}")
            else:
                print("  Build log:")
                for line in log_lines:
                    print(f"    {line}")
    
    print("\n" + "=" * 70)
    print(f"SUMMARY: {success_count}/{total_count} constants verified successfully")
    
    if success_count == total_count:
        print("🎉 All constants passed verification!")
        exit_code = 0
    else:
        print(f"❌ {total_count - success_count} constants failed verification")
        exit_code = 1
    
    sys.exit(exit_code)


if __name__ == "__main__":
    main()
