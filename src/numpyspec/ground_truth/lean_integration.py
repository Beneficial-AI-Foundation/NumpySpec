"""Integration utilities for using ground truth data with Lean."""

import json
from pathlib import Path
from typing import Dict, List, Any
import numpy as np


def numpy_to_lean_value(value: Any, indent: int = 0) -> str:
    """Convert NumPy values to Lean syntax.
    
    Args:
        value: The value to convert (scalar, array, etc.)
        indent: Indentation level for pretty printing
    
    Returns:
        String representation in Lean syntax
    """
    ind = "  " * indent
    
    if isinstance(value, dict) and value.get("type") == "ndarray":
        # Convert ndarray representation
        data = value["data"]
        shape = value["shape"]
        dtype = value["dtype"]
        
        if len(shape) == 0:
            # Scalar
            return str(data)
        elif len(shape) == 1:
            # 1D array
            elements = ", ".join(str(x) for x in data)
            return f"#[{elements}]"
        else:
            # Multi-dimensional array
            # For now, just flatten
            elements = ", ".join(str(x) for x in np.array(data).flatten())
            return f"#[{elements}] -- shape: {shape}"
    
    elif isinstance(value, (int, float)):
        if np.isnan(value):
            return "Float.nan"
        elif np.isinf(value):
            return "Float.inf" if value > 0 else "(-Float.inf)"
        else:
            return str(value)
    
    elif isinstance(value, list):
        elements = ", ".join(numpy_to_lean_value(v) for v in value)
        return f"#[{elements}]"
    
    elif isinstance(value, dict):
        # General dictionary
        pairs = []
        for k, v in value.items():
            pairs.append(f'("{k}", {numpy_to_lean_value(v, indent + 1)})')
        return f"[{', '.join(pairs)}]"
    
    else:
        return repr(value)


def generate_lean_test_case(test_case: Dict[str, Any]) -> str:
    """Generate Lean test code from a ground truth test case.
    
    Args:
        test_case: Dictionary containing test case data
    
    Returns:
        Lean code as a string
    """
    operation = test_case["operation"]
    inputs = test_case["inputs"]
    output = test_case["output"]
    
    # Generate test name
    test_name = f"test_{operation}_ground_truth"
    
    # Generate Lean code
    code = f"""/-- Ground truth test for {operation} --/
def {test_name} : IO Unit := do
"""
    
    # Add input setup
    for name, value in inputs.items():
        lean_value = numpy_to_lean_value(value)
        code += f"  let {name} := {lean_value}\n"
    
    # Add expected output
    lean_output = numpy_to_lean_value(output)
    code += f"  let expected := {lean_output}\n"
    
    # Add actual computation (placeholder)
    if len(inputs) == 1:
        input_name = list(inputs.keys())[0]
        code += f"  let actual := NumpySpec.{operation} {input_name}\n"
    else:
        input_names = " ".join(inputs.keys())
        code += f"  let actual := NumpySpec.{operation} {input_names}\n"
    
    # Add assertion
    code += """  if actual == expected then
    IO.println "✓ Test passed"
  else
    IO.println s!"✗ Test failed: expected {expected}, got {actual}"
"""
    
    return code


def generate_lean_test_file(
    spec_path: Path,
    output_path: Path,
    max_tests: int = 5
) -> None:
    """Generate a Lean test file from ground truth specification.
    
    Args:
        spec_path: Path to the ground truth JSON file
        output_path: Path for the output Lean file
        max_tests: Maximum number of tests to include
    """
    with open(spec_path) as f:
        spec = json.load(f)
    
    operation = spec["name"]
    description = spec["description"]
    test_cases = spec["test_cases"][:max_tests]
    
    # Generate Lean file content
    content = f"""/-
Automatically generated ground truth tests for {operation}
{description}

Generated from: {spec_path.name}
-/

import NumpySpec

namespace NumpySpec.GroundTruthTests.{operation.capitalize()}

"""
    
    # Add individual test cases
    for i, test_case in enumerate(test_cases):
        if test_case.get("output") is not None:  # Skip error cases
            test_code = generate_lean_test_case(test_case)
            content += test_code + "\n"
    
    # Add test runner
    content += f"""
/-- Run all ground truth tests for {operation} --/
def runAllTests : IO Unit := do
"""
    
    for i in range(len(test_cases)):
        if test_cases[i].get("output") is not None:
            content += f"  test_{operation}_ground_truth\n"
    
    content += f"\nend NumpySpec.GroundTruthTests.{operation.capitalize()}\n"
    
    # Write to file
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        f.write(content)
    
    print(f"Generated Lean test file: {output_path}")


def generate_all_lean_tests(
    ground_truth_dir: Path,
    output_dir: Path
) -> None:
    """Generate Lean test files for all ground truth data.
    
    Args:
        ground_truth_dir: Directory containing ground truth JSON files
        output_dir: Directory for output Lean files
    """
    for json_file in ground_truth_dir.glob("*_ground_truth.json"):
        if json_file.name == "ground_truth_summary.json":
            continue
        
        operation = json_file.stem.replace("_ground_truth", "")
        output_file = output_dir / f"Test_{operation.capitalize()}_GroundTruth.lean"
        
        try:
            generate_lean_test_file(json_file, output_file)
        except Exception as e:
            print(f"Error processing {json_file}: {e}")


if __name__ == "__main__":
    # Example usage
    from .generator import GroundTruthGenerator
    
    # Generate some ground truth data
    generator = GroundTruthGenerator()
    abs_spec = generator.generate_unary_operation_tests("abs", np.abs)
    output_path = generator.save_spec(abs_spec)
    
    # Generate Lean test file
    lean_output = Path("NumpySpec/Tests/Test_Abs_GroundTruth.lean")
    generate_lean_test_file(output_path, lean_output)
    
    print(f"\nExample Lean test generated at: {lean_output}")
