"""Ground truth data generator for NumPy operations."""

import numpy as np
from typing import Any, Callable, Dict, List, Optional, Tuple, Union
import json
import os
from pathlib import Path

from .formats import GroundTruthData, OperationSpec


class GroundTruthGenerator:
    """Generator for NumPy ground truth test data."""
    
    def __init__(self, output_dir: Optional[Path] = None):
        """Initialize the generator.
        
        Args:
            output_dir: Directory to save generated data. Defaults to src/numpyspec/data/ground_truth/
        """
        if output_dir is None:
            output_dir = Path(__file__).parent.parent / "data" / "ground_truth"
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
    
    def generate_unary_operation_tests(
        self,
        operation_name: str,
        numpy_func: Callable,
        test_inputs: Optional[List[np.ndarray]] = None,
        description: str = "",
    ) -> OperationSpec:
        """Generate test cases for unary operations (single input).
        
        Args:
            operation_name: Name of the operation (e.g., "abs", "sin")
            numpy_func: The numpy function to test
            test_inputs: List of test input arrays. If None, uses default set.
            description: Description of the operation
        
        Returns:
            OperationSpec with generated test cases
        """
        if test_inputs is None:
            test_inputs = self._get_default_unary_test_inputs()
        
        spec = OperationSpec(
            name=operation_name,
            numpy_func=f"numpy.{operation_name}",
            description=description or f"NumPy {operation_name} operation",
        )
        
        for input_arr in test_inputs:
            try:
                output = numpy_func(input_arr)
                test_case = GroundTruthData(
                    operation=operation_name,
                    inputs={"x": input_arr},
                    output=output,
                    dtype=str(output.dtype) if hasattr(output, "dtype") else None,
                    shape=output.shape if hasattr(output, "shape") else None,
                )
                spec.test_cases.append(test_case)
            except Exception as e:
                # Record error cases too
                test_case = GroundTruthData(
                    operation=operation_name,
                    inputs={"x": input_arr},
                    output=None,
                    metadata={"error": str(e), "error_type": type(e).__name__},
                )
                spec.test_cases.append(test_case)
        
        return spec
    
    def generate_binary_operation_tests(
        self,
        operation_name: str,
        numpy_func: Callable,
        test_inputs: Optional[List[Tuple[np.ndarray, np.ndarray]]] = None,
        description: str = "",
    ) -> OperationSpec:
        """Generate test cases for binary operations (two inputs).
        
        Args:
            operation_name: Name of the operation (e.g., "add", "multiply")
            numpy_func: The numpy function to test
            test_inputs: List of test input pairs. If None, uses default set.
            description: Description of the operation
        
        Returns:
            OperationSpec with generated test cases
        """
        if test_inputs is None:
            test_inputs = self._get_default_binary_test_inputs()
        
        spec = OperationSpec(
            name=operation_name,
            numpy_func=f"numpy.{operation_name}",
            description=description or f"NumPy {operation_name} operation",
        )
        
        for x, y in test_inputs:
            try:
                output = numpy_func(x, y)
                test_case = GroundTruthData(
                    operation=operation_name,
                    inputs={"x": x, "y": y},
                    output=output,
                    dtype=str(output.dtype) if hasattr(output, "dtype") else None,
                    shape=output.shape if hasattr(output, "shape") else None,
                )
                spec.test_cases.append(test_case)
            except Exception as e:
                # Record error cases too
                test_case = GroundTruthData(
                    operation=operation_name,
                    inputs={"x": x, "y": y},
                    output=None,
                    metadata={"error": str(e), "error_type": type(e).__name__},
                )
                spec.test_cases.append(test_case)
        
        return spec
    
    def _get_default_unary_test_inputs(self) -> List[np.ndarray]:
        """Get default test inputs for unary operations."""
        return [
            # Scalars
            np.array(0.0),
            np.array(1.0),
            np.array(-1.0),
            np.array(2.5),
            np.array(-3.7),
            
            # 1D arrays
            np.array([1, 2, 3]),
            np.array([-1, 0, 1]),
            np.array([0.5, 1.5, 2.5]),
            np.array([-2.0, -1.0, 0.0, 1.0, 2.0]),
            
            # 2D arrays
            np.array([[1, 2], [3, 4]]),
            np.array([[-1, 0], [1, 2]]),
            np.array([[0.5, 1.5], [2.5, 3.5]]),
            
            # Special values
            np.array([np.inf, -np.inf, np.nan]),
            np.array([[np.inf, 1], [-np.inf, np.nan]]),
            
            # Different dtypes
            np.array([1, 2, 3], dtype=np.int32),
            np.array([1.0, 2.0, 3.0], dtype=np.float32),
            np.array([1.0, 2.0, 3.0], dtype=np.float64),
        ]
    
    def _get_default_binary_test_inputs(self) -> List[Tuple[np.ndarray, np.ndarray]]:
        """Get default test input pairs for binary operations."""
        pairs = []
        
        # Scalar operations
        pairs.extend([
            (np.array(1.0), np.array(2.0)),
            (np.array(0.0), np.array(1.0)),
            (np.array(-1.0), np.array(1.0)),
            (np.array(2.5), np.array(0.5)),
        ])
        
        # Element-wise operations (same shape)
        pairs.extend([
            (np.array([1, 2, 3]), np.array([4, 5, 6])),
            (np.array([[1, 2], [3, 4]]), np.array([[5, 6], [7, 8]])),
        ])
        
        # Broadcasting tests
        pairs.extend([
            # Scalar with array
            (np.array(2.0), np.array([1, 2, 3])),
            (np.array([1, 2, 3]), np.array(2.0)),
            
            # 1D with 2D
            (np.array([1, 2]), np.array([[1, 2], [3, 4]])),
            (np.array([[1], [2]]), np.array([3, 4])),
        ])
        
        # Special values
        pairs.extend([
            (np.array([1, 2, np.inf]), np.array([3, np.nan, -np.inf])),
        ])
        
        return pairs
    
    def save_spec(self, spec: OperationSpec, filename: Optional[str] = None) -> Path:
        """Save operation specification to JSON file.
        
        Args:
            spec: The operation specification to save
            filename: Output filename. If None, uses operation name.
        
        Returns:
            Path to saved file
        """
        if filename is None:
            filename = f"{spec.name}_ground_truth.json"
        
        output_path = self.output_dir / filename
        with open(output_path, "w") as f:
            f.write(spec.to_json())
        
        return output_path
    
    def generate_basic_operations(self) -> Dict[str, OperationSpec]:
        """Generate ground truth for basic NumPy operations.
        
        Returns:
            Dictionary mapping operation names to their specifications
        """
        operations = {}
        
        # Unary operations
        unary_ops = [
            ("abs", np.abs, "Absolute value"),
            ("negative", np.negative, "Numerical negative"),
            ("sign", np.sign, "Sign of number"),
            ("sqrt", np.sqrt, "Square root"),
            ("square", np.square, "Square"),
            ("exp", np.exp, "Exponential"),
            ("log", np.log, "Natural logarithm"),
            ("sin", np.sin, "Sine"),
            ("cos", np.cos, "Cosine"),
        ]
        
        for name, func, desc in unary_ops:
            spec = self.generate_unary_operation_tests(name, func, description=desc)
            operations[name] = spec
            self.save_spec(spec)
        
        # Binary operations
        binary_ops = [
            ("add", np.add, "Addition"),
            ("subtract", np.subtract, "Subtraction"),
            ("multiply", np.multiply, "Multiplication"),
            ("divide", np.divide, "Division"),
            ("power", np.power, "Power"),
            ("maximum", np.maximum, "Element-wise maximum"),
            ("minimum", np.minimum, "Element-wise minimum"),
        ]
        
        for name, func, desc in binary_ops:
            spec = self.generate_binary_operation_tests(name, func, description=desc)
            operations[name] = spec
            self.save_spec(spec)
        
        return operations
    
    def generate_reduction_operation_tests(
        self,
        operation_name: str,
        numpy_func: Callable,
        test_inputs: Optional[List[np.ndarray]] = None,
        test_axes: Optional[List[Union[None, int, Tuple[int, ...]]]] = None,
        description: str = "",
    ) -> OperationSpec:
        """Generate test cases for reduction operations (sum, mean, etc.).
        
        Args:
            operation_name: Name of the operation
            numpy_func: The numpy function to test
            test_inputs: List of test input arrays
            test_axes: List of axis parameters to test
            description: Description of the operation
        
        Returns:
            OperationSpec with generated test cases
        """
        if test_inputs is None:
            test_inputs = self._get_default_reduction_test_inputs()
        if test_axes is None:
            test_axes = [None, 0, 1, -1, (0, 1)]
        
        spec = OperationSpec(
            name=operation_name,
            numpy_func=f"numpy.{operation_name}",
            description=description or f"NumPy {operation_name} reduction operation",
        )
        
        for input_arr in test_inputs:
            for axis in test_axes:
                # Skip invalid axis for the array shape
                if axis is not None:
                    if isinstance(axis, int):
                        if abs(axis) > input_arr.ndim:
                            continue
                    elif isinstance(axis, tuple):
                        if any(abs(ax) > input_arr.ndim for ax in axis):
                            continue
                
                try:
                    output = numpy_func(input_arr, axis=axis)
                    test_case = GroundTruthData(
                        operation=operation_name,
                        inputs={"array": input_arr, "axis": axis},
                        output=output,
                        dtype=str(output.dtype) if hasattr(output, "dtype") else None,
                        shape=output.shape if hasattr(output, "shape") else None,
                    )
                    spec.test_cases.append(test_case)
                except Exception as e:
                    test_case = GroundTruthData(
                        operation=operation_name,
                        inputs={"array": input_arr, "axis": axis},
                        output=None,
                        metadata={"error": str(e), "error_type": type(e).__name__},
                    )
                    spec.test_cases.append(test_case)
        
        return spec
    
    def _get_default_reduction_test_inputs(self) -> List[np.ndarray]:
        """Get default test inputs for reduction operations."""
        return [
            # 1D arrays
            np.array([1, 2, 3, 4, 5]),
            np.array([1.0, 2.5, 3.0]),
            np.array([-2, -1, 0, 1, 2]),
            
            # 2D arrays
            np.array([[1, 2, 3], [4, 5, 6]]),
            np.array([[1.0, 2.0], [3.0, 4.0], [5.0, 6.0]]),
            
            # 3D arrays
            np.array([[[1, 2], [3, 4]], [[5, 6], [7, 8]]]),
            
            # Arrays with special values
            np.array([1, 2, np.nan, 4]),
            np.array([[np.inf, 1], [2, -np.inf]]),
            
            # Empty and single element
            np.array([42]),
            np.array([[1]]),
        ]
