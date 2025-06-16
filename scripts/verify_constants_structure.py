#!/usr/bin/env python3
"""Simple structure verifier for numpy constants that doesn't require Lean compilation."""

import json
import sys
import re
from pathlib import Path

def load_and_analyze_constants(constants_dir: Path, json_filename: str = "data.json") -> list[dict]:
    """Load constants and analyze their structure."""
    json_path = constants_dir / json_filename
    if not json_path.exists():
        raise FileNotFoundError(f"Constants file not found: {json_path}")
    
    with open(json_path, 'r') as f:
        constants_data = json.load(f)
    
    results = []
    
    for const_name, const_info in constants_data.items():
        result = {
            'name': const_name,
            'success': True,
            'issues': []
        }
        
        # Check Python file
        python_file = constants_dir / const_info['python']
        if python_file.exists():
            python_code = python_file.read_text()
            result['python_exists'] = True
            
            # Basic Python syntax check
            try:
                compile(python_code, str(python_file), "exec")
                result['python_syntax_valid'] = True
            except SyntaxError as e:
                result['python_syntax_valid'] = False
                result['issues'].append(f"Python syntax error: {e}")
                result['success'] = False
        else:
            result['python_exists'] = False
            result['issues'].append(f"Python file not found: {python_file}")
            result['success'] = False
        
        # Check Lean implementation file
        lean_file = constants_dir / const_info['lean']
        if lean_file.exists():
            lean_code = lean_file.read_text()
            result['lean_exists'] = True
            result['lean_analysis'] = analyze_lean_structure(lean_code, const_name, 'implementation')
            if not result['lean_analysis']['valid']:
                result['issues'].extend(result['lean_analysis']['issues'])
                result['success'] = False
        else:
            result['lean_exists'] = False
            result['issues'].append(f"Lean file not found: {lean_file}")
            result['success'] = False
        
        # Check Lean spec file
        spec_file = constants_dir / const_info['spec']
        if spec_file.exists():
            spec_code = spec_file.read_text()
            result['spec_exists'] = True
            result['spec_analysis'] = analyze_lean_structure(spec_code, const_name, 'specification')
            if not result['spec_analysis']['valid']:
                result['issues'].extend(result['spec_analysis']['issues'])
                result['success'] = False
        else:
            result['spec_exists'] = False
            result['issues'].append(f"Spec file not found: {spec_file}")
            result['success'] = False
        
        results.append(result)
    
    return results


def analyze_lean_structure(lean_code: str, const_name: str, file_type: str) -> dict:
    """Analyze the structure of a Lean file."""
    analysis = {
        'valid': True,
        'issues': [],
        'has_namespace': False,
        'has_definition': False,
        'has_theorem_or_lemma': False
    }
    
    lines = lean_code.split('\n')
    
    # Check for namespace
    for line in lines:
        if re.match(r'\s*namespace\s+\w+', line.strip()):
            analysis['has_namespace'] = True
            break
    
    # Check for definitions
    for line in lines:
        if re.match(r'\s*(def|noncomputable\s+def)\s+\w+', line.strip()):
            analysis['has_definition'] = True
            break
    
    # Check for theorems/lemmas (for spec files)
    for line in lines:
        if re.match(r'\s*(theorem|lemma|noncomputable\s+lemma|noncomputable\s+theorem)\s+\w+', line.strip()):
            analysis['has_theorem_or_lemma'] = True
            break
    
    # Validate based on file type
    if file_type == 'implementation':
        if not analysis['has_namespace']:
            analysis['issues'].append("Implementation should have a namespace")
            analysis['valid'] = False
        if not analysis['has_definition']:
            analysis['issues'].append("Implementation should have a definition")
            analysis['valid'] = False
    elif file_type == 'specification':
        if not analysis['has_theorem_or_lemma']:
            analysis['issues'].append("Specification should have a theorem or lemma")
            analysis['valid'] = False
    
    # Check for basic syntax issues
    if lean_code.count('(') != lean_code.count(')'):
        analysis['issues'].append("Unmatched parentheses")
        analysis['valid'] = False
    
    if lean_code.count('{') != lean_code.count('}'):
        analysis['issues'].append("Unmatched braces")
        analysis['valid'] = False
    
    return analysis


def main():
    """Main entry point for the structure verifier."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Structure verifier for numpy constants')
    parser.add_argument('constants_dir', type=Path, 
                       help='Directory containing constants JSON and files')
    parser.add_argument('--json-file', default='data.json',
                       help='Name of the JSON file (default: data.json)')
    parser.add_argument('--verbose', action='store_true',
                       help='Show detailed analysis')
    
    args = parser.parse_args()
    
    if not args.constants_dir.exists():
        print(f"Error: Directory does not exist: {args.constants_dir}")
        sys.exit(1)
    
    print(f"📋 Numpy Constants Structure Verifier")
    print(f"Directory: {args.constants_dir}")
    print(f"JSON file: {args.json_file}")
    print("-" * 70)
    
    # Run analysis
    results = load_and_analyze_constants(args.constants_dir, args.json_file)
    
    # Display results
    success_count = 0
    total_count = len(results)
    
    for result in results:
        if result['success']:
            success_count += 1
            status = "✅ PASS"
        else:
            status = "❌ FAIL"
        
        print(f"\n{status} - {result['name']}")
        
        if args.verbose or not result['success']:
            print(f"  Files exist: Python={result.get('python_exists', False)}, "
                  f"Lean={result.get('lean_exists', False)}, "
                  f"Spec={result.get('spec_exists', False)}")
            
            if result.get('python_exists'):
                print(f"  Python syntax: {'✓' if result.get('python_syntax_valid', False) else '✗'}")
            
            if result.get('lean_exists'):
                lean_analysis = result.get('lean_analysis', {})
                print(f"  Lean impl: namespace={'✓' if lean_analysis.get('has_namespace') else '✗'}, "
                      f"definition={'✓' if lean_analysis.get('has_definition') else '✗'}")
            
            if result.get('spec_exists'):
                spec_analysis = result.get('spec_analysis', {})
                print(f"  Lean spec: theorem/lemma={'✓' if spec_analysis.get('has_theorem_or_lemma') else '✗'}")
            
            if result['issues']:
                print("  Issues:")
                for issue in result['issues']:
                    print(f"    - {issue}")
    
    print("\n" + "=" * 70)
    print(f"SUMMARY: {success_count}/{total_count} constants have valid structure")
    
    if success_count == total_count:
        print("🎉 All constants have valid structure!")
        print("\nNote: This verifies file structure and basic syntax only.")
        print("For full verification, Lean compilation with mathlib is required.")
        exit_code = 0
    else:
        print(f"❌ {total_count - success_count} constants have structural issues")
        exit_code = 1
    
    sys.exit(exit_code)


if __name__ == "__main__":
    main()
