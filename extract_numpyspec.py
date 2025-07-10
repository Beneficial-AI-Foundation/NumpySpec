#!/usr/bin/env python3
"""
Extract NumpySpec declarations for lean-explore indexing.
This is a simplified version that extracts basic information from NumpySpec Lean files.
"""

import json
import os
import re
from pathlib import Path

def extract_lean_declarations(file_path):
    """Extract declarations from a Lean file."""
    declarations = []
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except:
        return declarations
    
    # Extract module name from path
    module_name = str(file_path).replace('/', '.').replace('.lean', '')
    if module_name.startswith('.'):
        module_name = module_name[1:]
    
    # Find all def, theorem, lemma, structure, inductive declarations
    patterns = [
        (r'^(def|abbrev)\s+(\w+)', 'definition', 2),
        (r'^theorem\s+(\w+)', 'theorem', 1),
        (r'^lemma\s+(\w+)', 'theorem', 1),
        (r'^structure\s+(\w+)', 'structure', 1),
        (r'^inductive\s+(\w+)', 'inductive', 1),
        (r'^class\s+(\w+)', 'class', 1),
    ]
    
    lines = content.split('\n')
    for i, line in enumerate(lines):
        for pattern, decl_type, name_group in patterns:
            match = re.match(pattern, line)
            if match:
                try:
                    name = match.group(name_group)
                    full_name = f"NumpySpec.{name}"
                    
                    # Extract docstring if present
                    docstring = None
                    if i > 0 and lines[i-1].strip().startswith('/-!'):
                        # Multi-line docstring
                        doc_lines = []
                        j = i - 1
                        while j >= 0 and not lines[j].strip().endswith('-/'):
                            doc_lines.append(lines[j])
                            j -= 1
                        if j >= 0:
                            doc_lines.append(lines[j])
                        docstring = '\n'.join(reversed(doc_lines))
                    elif i > 0 and lines[i-1].strip().startswith('/--'):
                        # Single line docstring
                        docstring = lines[i-1].strip()
                    
                    declaration = {
                        'lean_name': full_name,
                        'decl_type': decl_type,
                        'module_name': module_name,
                        'source_file': str(file_path),
                        'range_start_line': i + 1,
                        'is_protected': False,
                        'is_deprecated': False,
                        'attributes': []
                    }
                    
                    if docstring:
                        declaration['docstring'] = docstring.strip('/-! ').strip()
                    
                    declarations.append(declaration)
                except Exception as e:
                    print(f"Error processing {file_path} line {i}: {e}")
                    continue
    
    return declarations

def main():
    """Main extraction function."""
    all_declarations = []
    
    # Find all Lean files in NumpySpec
    for root, dirs, files in os.walk('NumpySpec'):
        # Skip hidden directories
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        
        for file in files:
            if file.endswith('.lean'):
                file_path = Path(root) / file
                print(f"Extracting from {file_path}")
                declarations = extract_lean_declarations(file_path)
                all_declarations.extend(declarations)
    
    # Also extract from root NumpySpec.lean
    if Path('NumpySpec.lean').exists():
        print("Extracting from NumpySpec.lean")
        declarations = extract_lean_declarations(Path('NumpySpec.lean'))
        all_declarations.extend(declarations)
    
    # Write to JSONL format
    output_file = 'numpyspec_declarations.jsonl'
    with open(output_file, 'w', encoding='utf-8') as f:
        for decl in all_declarations:
            f.write(json.dumps(decl) + '\n')
    
    print(f"\nExtracted {len(all_declarations)} declarations to {output_file}")
    
    # Also create a summary
    by_type = {}
    for decl in all_declarations:
        decl_type = decl['decl_type']
        if decl_type not in by_type:
            by_type[decl_type] = 0
        by_type[decl_type] += 1
    
    print("\nSummary by declaration type:")
    for decl_type, count in sorted(by_type.items()):
        print(f"  {decl_type}: {count}")

if __name__ == "__main__":
    main()