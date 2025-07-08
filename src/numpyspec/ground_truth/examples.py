"""Examples of generating ground truth data from NumPy."""

import numpy as np
from pathlib import Path
from .generator import GroundTruthGenerator
from .formats import GroundTruthData, OperationSpec


def generate_matrix_operation_examples():
    """Generate ground truth for matrix operations."""
    generator = GroundTruthGenerator()
    
    # Matrix multiplication (matmul)
    matmul_inputs = [
        # 2D x 2D
        (np.array([[1, 2], [3, 4]]), np.array([[5, 6], [7, 8]])),
        (np.array([[1.0, 2.0], [3.0, 4.0]]), np.array([[2.0, 0.0], [1.0, 2.0]])),
        
        # 1D x 1D (dot product)
        (np.array([1, 2, 3]), np.array([4, 5, 6])),
        
        # 2D x 1D
        (np.array([[1, 2], [3, 4]]), np.array([5, 6])),
        
        # Identity matrix
        (np.eye(3), np.array([[1], [2], [3]])),
    ]
    
    matmul_spec = generator.generate_binary_operation_tests(
        "matmul",
        np.matmul,
        test_inputs=matmul_inputs,
        description="Matrix multiplication"
    )
    generator.save_spec(matmul_spec)
    
    # Dot product
    dot_spec = generator.generate_binary_operation_tests(
        "dot",
        np.dot,
        test_inputs=matmul_inputs,  # Similar inputs work for dot
        description="Dot product"
    )
    generator.save_spec(dot_spec)
    
    return {"matmul": matmul_spec, "dot": dot_spec}


def generate_statistical_operation_examples():
    """Generate ground truth for statistical operations."""
    generator = GroundTruthGenerator()
    
    # Sum
    sum_spec = generator.generate_reduction_operation_tests(
        "sum",
        np.sum,
        description="Sum of array elements"
    )
    generator.save_spec(sum_spec)
    
    # Mean
    mean_spec = generator.generate_reduction_operation_tests(
        "mean",
        np.mean,
        description="Mean of array elements"
    )
    generator.save_spec(mean_spec)
    
    # Standard deviation
    std_spec = generator.generate_reduction_operation_tests(
        "std",
        np.std,
        description="Standard deviation"
    )
    generator.save_spec(std_spec)
    
    # Variance
    var_spec = generator.generate_reduction_operation_tests(
        "var",
        np.var,
        description="Variance"
    )
    generator.save_spec(var_spec)
    
    return {
        "sum": sum_spec,
        "mean": mean_spec,
        "std": std_spec,
        "var": var_spec,
    }


def generate_array_manipulation_examples():
    """Generate ground truth for array manipulation operations."""
    generator = GroundTruthGenerator()
    
    # Reshape
    reshape_spec = OperationSpec(
        name="reshape",
        numpy_func="numpy.reshape",
        description="Reshape array"
    )
    
    reshape_tests = [
        # 1D to 2D
        (np.array([1, 2, 3, 4, 5, 6]), (2, 3)),
        (np.array([1, 2, 3, 4, 5, 6]), (3, 2)),
        (np.array([1, 2, 3, 4, 5, 6]), (6, 1)),
        (np.array([1, 2, 3, 4, 5, 6]), (1, 6)),
        
        # 2D to 1D
        (np.array([[1, 2, 3], [4, 5, 6]]), (-1,)),
        (np.array([[1, 2], [3, 4], [5, 6]]), (6,)),
        
        # 2D to 2D
        (np.array([[1, 2, 3], [4, 5, 6]]), (3, 2)),
        
        # Using -1 for auto dimension
        (np.array([1, 2, 3, 4, 5, 6]), (2, -1)),
        (np.array([1, 2, 3, 4, 5, 6]), (-1, 3)),
    ]
    
    for arr, new_shape in reshape_tests:
        try:
            output = np.reshape(arr, new_shape)
            test_case = GroundTruthData(
                operation="reshape",
                inputs={"array": arr, "shape": new_shape},
                output=output,
                dtype=str(output.dtype),
                shape=output.shape,
            )
            reshape_spec.test_cases.append(test_case)
        except Exception as e:
            test_case = GroundTruthData(
                operation="reshape",
                inputs={"array": arr, "shape": new_shape},
                output=None,
                metadata={"error": str(e), "error_type": type(e).__name__},
            )
            reshape_spec.test_cases.append(test_case)
    
    generator.save_spec(reshape_spec)
    
    # Transpose
    transpose_spec = OperationSpec(
        name="transpose",
        numpy_func="numpy.transpose",
        description="Transpose array"
    )
    
    transpose_tests = [
        np.array([[1, 2, 3], [4, 5, 6]]),
        np.array([[[1, 2], [3, 4]], [[5, 6], [7, 8]]]),
        np.array([1, 2, 3]),  # 1D array (no change)
    ]
    
    for arr in transpose_tests:
        output = np.transpose(arr)
        test_case = GroundTruthData(
            operation="transpose",
            inputs={"array": arr},
            output=output,
            dtype=str(output.dtype),
            shape=output.shape,
        )
        transpose_spec.test_cases.append(test_case)
    
    generator.save_spec(transpose_spec)
    
    return {"reshape": reshape_spec, "transpose": transpose_spec}


def generate_comparison_operation_examples():
    """Generate ground truth for comparison operations."""
    generator = GroundTruthGenerator()
    
    # All
    all_spec = generator.generate_reduction_operation_tests(
        "all",
        np.all,
        test_inputs=[
            np.array([True, True, True]),
            np.array([True, False, True]),
            np.array([False, False, False]),
            np.array([[True, True], [True, True]]),
            np.array([[True, False], [True, True]]),
            np.array([1, 2, 3]),  # Non-zero values are True
            np.array([1, 0, 3]),  # Zero is False
        ],
        description="Test whether all array elements are True"
    )
    generator.save_spec(all_spec)
    
    # Any
    any_spec = generator.generate_reduction_operation_tests(
        "any",
        np.any,
        test_inputs=[
            np.array([True, True, True]),
            np.array([True, False, True]),
            np.array([False, False, False]),
            np.array([[False, False], [False, False]]),
            np.array([[True, False], [False, False]]),
            np.array([0, 0, 0]),  # All zeros are False
            np.array([0, 1, 0]),  # Non-zero is True
        ],
        description="Test whether any array element is True"
    )
    generator.save_spec(any_spec)
    
    return {"all": all_spec, "any": any_spec}


def generate_all_examples():
    """Generate all example ground truth data."""
    generator = GroundTruthGenerator()
    
    print("Generating basic operations...")
    basic_ops = generator.generate_basic_operations()
    print(f"Generated {len(basic_ops)} basic operations")
    
    print("\nGenerating matrix operations...")
    matrix_ops = generate_matrix_operation_examples()
    print(f"Generated {len(matrix_ops)} matrix operations")
    
    print("\nGenerating statistical operations...")
    stat_ops = generate_statistical_operation_examples()
    print(f"Generated {len(stat_ops)} statistical operations")
    
    print("\nGenerating array manipulation operations...")
    manip_ops = generate_array_manipulation_examples()
    print(f"Generated {len(manip_ops)} array manipulation operations")
    
    print("\nGenerating comparison operations...")
    comp_ops = generate_comparison_operation_examples()
    print(f"Generated {len(comp_ops)} comparison operations")
    
    # Create summary
    all_ops = {**basic_ops, **matrix_ops, **stat_ops, **manip_ops, **comp_ops}
    
    summary = {
        "total_operations": len(all_ops),
        "total_test_cases": sum(len(op.test_cases) for op in all_ops.values()),
        "operations": list(all_ops.keys()),
        "output_directory": str(generator.output_dir),
    }
    
    # Save summary
    summary_path = generator.output_dir / "ground_truth_summary.json"
    with open(summary_path, "w") as f:
        import json
        json.dump(summary, f, indent=2)
    
    print(f"\nSummary saved to: {summary_path}")
    print(f"Total operations: {summary['total_operations']}")
    print(f"Total test cases: {summary['total_test_cases']}")
    
    return all_ops


if __name__ == "__main__":
    generate_all_examples()
