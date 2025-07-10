#!/usr/bin/env python3
"""
Script to convert NumPy JSON documentation files to Lean files with JSON-formatted docstrings.
"""

import json
import os
from pathlib import Path
import re

def extract_module_path(name):
    """
    Extract the module path from a numpy function name.
    
    Examples:
    - numpy.sin -> sin.lean
    - numpy.fft.ifftshift -> fft/ifftshift.lean
    - numpy.polynomial.chebyshev.chebint -> polynomial/chebyshev/chebint.lean
    - numpy.binary_repr -> bitwise_operations/binary_repr.lean
    """
    # Remove numpy. prefix
    if name.startswith("numpy."):
        name = name[6:]
    
    # Split by dots
    parts = name.split(".")
    
    # The last part is the function name
    func_name = parts[-1]
    
    # The rest forms the directory structure
    if len(parts) > 1:
        dirs = parts[:-1]
        return "/".join(dirs) + "/" + func_name + ".lean"
    else:
        return func_name + ".lean"

def json_to_lean_docstring(func_data):
    """Convert a function data dict to a JSON-formatted Lean docstring."""
    # Create a clean JSON representation with proper formatting
    json_str = json.dumps(func_data, indent=2, ensure_ascii=False)
    
    # Escape any backticks in the JSON string
    json_str = json_str.replace('`', '\\`')
    
    # Create the Lean docstring
    return f"/-!\n{json_str}\n-/"

def create_lean_file_content(func_data):
    """Create the content for a Lean file with JSON docstring."""
    docstring = json_to_lean_docstring(func_data)
    
    # Extract function name for potential future use
    func_name = func_data["name"]
    lean_name = func_name.split(".")[-1]
    
    # For now, just create a file with the docstring and a placeholder
    content = f"""{docstring}

-- TODO: Implement {lean_name}
"""
    
    return content

def process_json_file(json_path, output_base_dir):
    """Process a single JSON file and create corresponding Lean files."""
    with open(json_path, 'r') as f:
        data = json.load(f)
    
    # Handle different JSON structures
    functions = []
    
    if isinstance(data, list):
        # Direct list of functions
        functions = data
    elif isinstance(data, dict):
        if "functions" in data:
            # Dictionary with functions key
            functions = data["functions"]
        else:
            # Dictionary with category keys (like array_creation_operations.json)
            for category, func_list in data.items():
                if isinstance(func_list, list):
                    functions.extend(func_list)
    
    if not functions:
        print(f"Skipping {json_path}: No functions found")
        return []
    
    # Get the category from the JSON file path
    rel_path = os.path.relpath(json_path, "web_utils/full_numpy")
    category_dir = os.path.dirname(rel_path)
    
    created_files = []
    
    for func_data in functions:
        if not isinstance(func_data, dict) or "name" not in func_data:
            continue
        
        # Determine the output path
        module_path = extract_module_path(func_data["name"])
        
        # For functions in specific categories (like bitwise_operations),
        # ensure they go to the right directory
        if category_dir and not module_path.startswith(category_dir):
            # Special handling for top-level functions in category files
            if "/" not in module_path:
                module_path = category_dir + "/" + module_path
        
        output_path = os.path.join(output_base_dir, module_path)
        
        # Create directory if needed
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        
        # Create Lean file content
        content = create_lean_file_content(func_data)
        
        # Write the file
        with open(output_path, 'w') as f:
            f.write(content)
        
        created_files.append(output_path)
    
    return created_files

def main():
    """Main function to process all JSON files."""
    input_dir = "web_utils/full_numpy"
    output_dir = "NumpySpec"
    
    # Find all JSON files
    json_files = list(Path(input_dir).rglob("*.json"))
    
    # Skip the summary file
    json_files = [f for f in json_files if f.name != "numpy_operations_summary.json"]
    
    print(f"Found {len(json_files)} JSON files to process")
    
    all_created_files = []
    
    for json_file in json_files:
        print(f"\nProcessing {json_file}")
        created_files = process_json_file(json_file, output_dir)
        if created_files:
            all_created_files.extend(created_files)
            print(f"  Created {len(created_files)} Lean files")
    
    print(f"\nTotal files created: {len(all_created_files)}")
    
    # Print a sample of created files
    print("\nSample of created files:")
    for f in all_created_files[:10]:
        print(f"  {f}")

if __name__ == "__main__":
    main()