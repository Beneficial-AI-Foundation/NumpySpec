"""Tests for ground truth data generation."""

import numpy as np
import pytest
import json
import tempfile
from pathlib import Path

from numpyspec.ground_truth.generator import GroundTruthGenerator
from numpyspec.ground_truth.formats import GroundTruthData, OperationSpec


class TestGroundTruthData:
    """Test the GroundTruthData class."""
    
    def test_basic_creation(self):
        """Test creating basic ground truth data."""
        data = GroundTruthData(
            operation="add",
            inputs={"x": 1, "y": 2},
            output=3,
            dtype="int64",
            shape=(),
        )
        
        assert data.operation == "add"
        assert data.inputs == {"x": 1, "y": 2}
        assert data.output == 3
        assert data.dtype == "int64"
        assert data.shape == ()
    
    def test_numpy_array_serialization(self):
        """Test serialization of numpy arrays."""
        arr = np.array([1, 2, 3])
        data = GroundTruthData(
            operation="identity",
            inputs={"x": arr},
            output=arr,
        )
        
        serialized = data.to_dict()
        
        # Check input serialization
        assert serialized["inputs"]["x"]["type"] == "ndarray"
        assert serialized["inputs"]["x"]["data"] == [1, 2, 3]
        assert serialized["inputs"]["x"]["shape"] == (3,)
        
        # Check output serialization
        assert serialized["output"]["type"] == "ndarray"
        assert serialized["output"]["data"] == [1, 2, 3]
    
    def test_special_values_serialization(self):
        """Test serialization of special numpy values."""
        data = GroundTruthData(
            operation="special",
            inputs={"x": np.array([np.inf, -np.inf, np.nan])},
            output=np.array([1.0, 2.0]),
        )
        
        serialized = data.to_dict()
        input_data = serialized["inputs"]["x"]["data"]
        
        assert input_data[0] == float("inf")
        assert input_data[1] == float("-inf")
        assert input_data[2] != input_data[2]  # NaN != NaN


class TestOperationSpec:
    """Test the OperationSpec class."""
    
    def test_basic_creation(self):
        """Test creating operation specification."""
        spec = OperationSpec(
            name="add",
            numpy_func="numpy.add",
            description="Addition operation",
        )
        
        assert spec.name == "add"
        assert spec.numpy_func == "numpy.add"
        assert spec.description == "Addition operation"
        assert spec.test_cases == []
    
    def test_json_serialization(self):
        """Test JSON serialization of operation spec."""
        spec = OperationSpec(
            name="multiply",
            numpy_func="numpy.multiply",
            description="Multiplication",
        )
        
        # Add a test case
        spec.test_cases.append(
            GroundTruthData(
                operation="multiply",
                inputs={"x": 2, "y": 3},
                output=6,
            )
        )
        
        # Serialize to JSON
        json_str = spec.to_json()
        data = json.loads(json_str)
        
        assert data["name"] == "multiply"
        assert len(data["test_cases"]) == 1
        assert data["test_cases"][0]["output"] == 6
    
    def test_from_dict(self):
        """Test creating OperationSpec from dictionary."""
        data = {
            "name": "subtract",
            "numpy_func": "numpy.subtract",
            "description": "Subtraction",
            "test_cases": [
                {
                    "operation": "subtract",
                    "inputs": {"x": 5, "y": 3},
                    "output": 2,
                    "dtype": "int64",
                }
            ],
        }
        
        spec = OperationSpec.from_dict(data)
        
        assert spec.name == "subtract"
        assert len(spec.test_cases) == 1
        assert spec.test_cases[0].output == 2


class TestGroundTruthGenerator:
    """Test the GroundTruthGenerator class."""
    
    def test_generator_creation(self):
        """Test creating a generator."""
        with tempfile.TemporaryDirectory() as tmpdir:
            generator = GroundTruthGenerator(output_dir=Path(tmpdir))
            assert generator.output_dir == Path(tmpdir)
    
    def test_unary_operation_generation(self):
        """Test generating unary operation tests."""
        with tempfile.TemporaryDirectory() as tmpdir:
            generator = GroundTruthGenerator(output_dir=Path(tmpdir))
            
            # Generate tests for absolute value
            spec = generator.generate_unary_operation_tests(
                "abs",
                np.abs,
                test_inputs=[np.array([-1, 0, 1]), np.array([-2.5, 3.5])],
            )
            
            assert spec.name == "abs"
            assert len(spec.test_cases) == 2
            
            # Check first test case
            tc = spec.test_cases[0]
            np.testing.assert_array_equal(tc.output, np.array([1, 0, 1]))
    
    def test_binary_operation_generation(self):
        """Test generating binary operation tests."""
        with tempfile.TemporaryDirectory() as tmpdir:
            generator = GroundTruthGenerator(output_dir=Path(tmpdir))
            
            # Generate tests for addition
            spec = generator.generate_binary_operation_tests(
                "add",
                np.add,
                test_inputs=[
                    (np.array([1, 2]), np.array([3, 4])),
                    (np.array(5), np.array(10)),
                ],
            )
            
            assert spec.name == "add"
            assert len(spec.test_cases) == 2
            
            # Check results
            np.testing.assert_array_equal(
                spec.test_cases[0].output, np.array([4, 6])
            )
            assert spec.test_cases[1].output == 15
    
    def test_reduction_operation_generation(self):
        """Test generating reduction operation tests."""
        with tempfile.TemporaryDirectory() as tmpdir:
            generator = GroundTruthGenerator(output_dir=Path(tmpdir))
            
            # Generate tests for sum
            spec = generator.generate_reduction_operation_tests(
                "sum",
                np.sum,
                test_inputs=[np.array([[1, 2], [3, 4]])],
                test_axes=[None, 0, 1],
            )
            
            assert spec.name == "sum"
            assert len(spec.test_cases) == 3
            
            # Check results for different axes
            results = {tc.inputs["axis"]: tc.output for tc in spec.test_cases}
            
            assert results[None] == 10  # Sum all elements
            np.testing.assert_array_equal(results[0], np.array([4, 6]))  # Sum columns
            np.testing.assert_array_equal(results[1], np.array([3, 7]))  # Sum rows
    
    def test_error_handling(self):
        """Test that errors are properly recorded."""
        with tempfile.TemporaryDirectory() as tmpdir:
            generator = GroundTruthGenerator(output_dir=Path(tmpdir))
            
            # Generate tests that will cause errors
            spec = generator.generate_unary_operation_tests(
                "sqrt",
                np.sqrt,
                test_inputs=[np.array([-1, -2, -3])],  # Negative values for sqrt
            )
            
            assert len(spec.test_cases) == 1
            tc = spec.test_cases[0]
            
            # Should have recorded the operation (with NaN results, not error)
            assert np.all(np.isnan(tc.output))
    
    def test_save_spec(self):
        """Test saving specification to file."""
        with tempfile.TemporaryDirectory() as tmpdir:
            generator = GroundTruthGenerator(output_dir=Path(tmpdir))
            
            spec = OperationSpec(
                name="test_op",
                numpy_func="numpy.test",
                description="Test operation",
            )
            
            spec.test_cases.append(
                GroundTruthData(
                    operation="test_op",
                    inputs={"x": 42},
                    output=42,
                )
            )
            
            # Save the spec
            output_path = generator.save_spec(spec)
            
            assert output_path.exists()
            assert output_path.name == "test_op_ground_truth.json"
            
            # Load and verify
            with open(output_path) as f:
                data = json.load(f)
            
            assert data["name"] == "test_op"
            assert len(data["test_cases"]) == 1


def test_default_test_inputs():
    """Test that default test inputs are reasonable."""
    with tempfile.TemporaryDirectory() as tmpdir:
        generator = GroundTruthGenerator(output_dir=Path(tmpdir))
        
        # Test unary inputs
        unary_inputs = generator._get_default_unary_test_inputs()
        assert len(unary_inputs) > 0
        assert any(arr.ndim == 0 for arr in unary_inputs)  # Has scalars
        assert any(arr.ndim == 1 for arr in unary_inputs)  # Has 1D arrays
        assert any(arr.ndim == 2 for arr in unary_inputs)  # Has 2D arrays
        
        # Test binary inputs
        binary_inputs = generator._get_default_binary_test_inputs()
        assert len(binary_inputs) > 0
        assert all(len(pair) == 2 for pair in binary_inputs)
        
        # Test reduction inputs
        reduction_inputs = generator._get_default_reduction_test_inputs()
        assert len(reduction_inputs) > 0
        assert any(arr.ndim >= 2 for arr in reduction_inputs)  # Has multi-dim arrays
