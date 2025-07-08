#!/usr/bin/env python3
"""Generate ground truth data from NumPy operations.

This script uses NumPy itself to generate test data pairs that serve as
lightweight specifications for the Lean implementation.
"""

import argparse
import sys
from pathlib import Path

# Add src to path for imports
sys.path.insert(0, str(Path(__file__).parent / "src"))

from numpyspec.ground_truth.generator import GroundTruthGenerator
from numpyspec.ground_truth.examples import (
    generate_all_examples,
    generate_matrix_operation_examples,
    generate_statistical_operation_examples,
    generate_array_manipulation_examples,
    generate_comparison_operation_examples,
)


def main():
    parser = argparse.ArgumentParser(
        description="Generate ground truth data from NumPy operations"
    )
    parser.add_argument(
        "--category",
        choices=["all", "basic", "matrix", "statistical", "manipulation", "comparison"],
        default="all",
        help="Category of operations to generate",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        help="Output directory for generated data",
    )
    parser.add_argument(
        "--operation",
        help="Generate data for a specific operation (e.g., 'add', 'matmul')",
    )
    
    args = parser.parse_args()
    
    # Create generator
    generator = GroundTruthGenerator(output_dir=args.output_dir)
    
    print(f"Generating ground truth data...")
    print(f"Output directory: {generator.output_dir}")
    
    if args.operation:
        # Generate for specific operation
        import numpy as np
        
        # Map operation names to numpy functions
        operation_map = {
            # Basic operations
            "abs": np.abs,
            "negative": np.negative,
            "sign": np.sign,
            "sqrt": np.sqrt,
            "square": np.square,
            "exp": np.exp,
            "log": np.log,
            "sin": np.sin,
            "cos": np.cos,
            "add": np.add,
            "subtract": np.subtract,
            "multiply": np.multiply,
            "divide": np.divide,
            "power": np.power,
            "maximum": np.maximum,
            "minimum": np.minimum,
            # Matrix operations
            "matmul": np.matmul,
            "dot": np.dot,
            # Statistical operations
            "sum": np.sum,
            "mean": np.mean,
            "std": np.std,
            "var": np.var,
            # Comparison operations
            "all": np.all,
            "any": np.any,
        }
        
        if args.operation not in operation_map:
            print(f"Error: Unknown operation '{args.operation}'")
            print(f"Available operations: {', '.join(sorted(operation_map.keys()))}")
            return 1
        
        func = operation_map[args.operation]
        
        # Determine operation type
        if args.operation in ["abs", "negative", "sign", "sqrt", "square", "exp", "log", "sin", "cos"]:
            spec = generator.generate_unary_operation_tests(args.operation, func)
        elif args.operation in ["add", "subtract", "multiply", "divide", "power", "maximum", "minimum", "matmul", "dot"]:
            spec = generator.generate_binary_operation_tests(args.operation, func)
        elif args.operation in ["sum", "mean", "std", "var", "all", "any"]:
            spec = generator.generate_reduction_operation_tests(args.operation, func)
        else:
            print(f"Error: Don't know how to generate tests for '{args.operation}'")
            return 1
        
        output_path = generator.save_spec(spec)
        print(f"Generated {len(spec.test_cases)} test cases for {args.operation}")
        print(f"Saved to: {output_path}")
    
    elif args.category == "all":
        generate_all_examples()
    elif args.category == "basic":
        ops = generator.generate_basic_operations()
        print(f"Generated {len(ops)} basic operations")
    elif args.category == "matrix":
        ops = generate_matrix_operation_examples()
        print(f"Generated {len(ops)} matrix operations")
    elif args.category == "statistical":
        ops = generate_statistical_operation_examples()
        print(f"Generated {len(ops)} statistical operations")
    elif args.category == "manipulation":
        ops = generate_array_manipulation_examples()
        print(f"Generated {len(ops)} array manipulation operations")
    elif args.category == "comparison":
        ops = generate_comparison_operation_examples()
        print(f"Generated {len(ops)} comparison operations")
    
    print("\nDone!")
    return 0


if __name__ == "__main__":
    sys.exit(main())
