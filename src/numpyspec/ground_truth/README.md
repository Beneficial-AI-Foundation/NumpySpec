# NumPy Ground Truth Generation

This module provides utilities for generating ground truth test data directly from NumPy operations. These data pairs serve as lightweight specifications that the Lean implementation should match.

## Motivation

Instead of manually writing expected outputs for tests, we use NumPy itself as the source of truth. This ensures:

1. **Accuracy**: The expected values come directly from NumPy's implementation
2. **Coverage**: Easy to generate tests for edge cases, special values, and various input shapes
3. **Consistency**: All test data follows the same format and structure
4. **Maintainability**: Adding new operations or test cases is straightforward

## Usage

### Command Line Interface

Generate ground truth data using the provided script:

```bash
# Generate all ground truth data
python generate_ground_truth.py

# Generate data for specific categories
python generate_ground_truth.py --category basic      # Basic arithmetic operations
python generate_ground_truth.py --category matrix     # Matrix operations
python generate_ground_truth.py --category statistical # Statistical operations

# Generate data for a specific operation
python generate_ground_truth.py --operation add
python generate_ground_truth.py --operation matmul

# Specify output directory
python generate_ground_truth.py --output-dir /path/to/output
```

### Programmatic Usage

```python
from numpyspec.ground_truth import GroundTruthGenerator
import numpy as np

# Create generator
generator = GroundTruthGenerator()

# Generate tests for unary operations
abs_spec = generator.generate_unary_operation_tests(
    "abs",
    np.abs,
    description="Absolute value"
)

# Generate tests for binary operations
add_spec = generator.generate_binary_operation_tests(
    "add",
    np.add,
    description="Addition"
)

# Generate tests for reduction operations
sum_spec = generator.generate_reduction_operation_tests(
    "sum",
    np.sum,
    description="Sum of array elements"
)

# Save to JSON
generator.save_spec(abs_spec)
```

## Data Format

The generated ground truth data is stored in JSON format with the following structure:

```json
{
  "name": "add",
  "numpy_func": "numpy.add",
  "description": "Addition",
  "test_cases": [
    {
      "operation": "add",
      "inputs": {
        "x": {"type": "ndarray", "data": [1, 2, 3], "dtype": "int64", "shape": [3]},
        "y": {"type": "ndarray", "data": [4, 5, 6], "dtype": "int64", "shape": [3]}
      },
      "output": {"type": "ndarray", "data": [5, 7, 9], "dtype": "int64", "shape": [3]},
      "dtype": "int64",
      "shape": [3]
    }
  ]
}
```

## Adding New Operations

To add ground truth for a new NumPy operation:

1. **For unary operations** (single input):
   ```python
   spec = generator.generate_unary_operation_tests(
       "operation_name",
       np.operation_name,
       test_inputs=[...],  # Optional custom inputs
       description="Operation description"
   )
   ```

2. **For binary operations** (two inputs):
   ```python
   spec = generator.generate_binary_operation_tests(
       "operation_name",
       np.operation_name,
       test_inputs=[...],  # Optional custom input pairs
       description="Operation description"
   )
   ```

3. **For reduction operations** (with axis parameter):
   ```python
   spec = generator.generate_reduction_operation_tests(
       "operation_name",
       np.operation_name,
       test_inputs=[...],  # Optional custom inputs
       test_axes=[None, 0, 1, -1],  # Axes to test
       description="Operation description"
   )
   ```

4. **For custom operations**, create the test cases manually:
   ```python
   from numpyspec.ground_truth import OperationSpec, GroundTruthData
   
   spec = OperationSpec(
       name="custom_op",
       numpy_func="numpy.custom_op",
       description="Custom operation"
   )
   
   # Add test cases
   for inputs in test_inputs:
       output = compute_output(inputs)
       test_case = GroundTruthData(
           operation="custom_op",
           inputs=inputs,
           output=output,
       )
       spec.test_cases.append(test_case)
   ```

## Default Test Inputs

The generator provides comprehensive default test inputs:

### Unary Operations
- Scalars: 0, 1, -1, 2.5, -3.7
- 1D arrays: Various sizes and values
- 2D arrays: Different shapes
- Special values: inf, -inf, nan
- Different dtypes: int32, float32, float64

### Binary Operations
- Scalar-scalar operations
- Element-wise operations (same shape)
- Broadcasting tests
- Special value combinations

### Reduction Operations
- Various array shapes (1D, 2D, 3D)
- Different axis parameters
- Arrays with special values
- Empty and single-element arrays

## Integration with Lean

The generated JSON files can be:

1. **Parsed in Lean** to create test cases automatically
2. **Used as specifications** to verify Lean implementations
3. **Converted to Lean syntax** for property-based testing
4. **Referenced in documentation** as examples

## Best Practices

1. **Generate tests for edge cases**: Include special values (inf, nan), empty arrays, and boundary conditions
2. **Test broadcasting**: Ensure operations work correctly with different input shapes
3. **Document properties**: Add mathematical properties (commutativity, associativity) to the operation spec
4. **Version control**: Commit generated ground truth data to track changes over time
5. **Validate against NumPy version**: Document which NumPy version was used for generation

## Extending the System

The ground truth generation system is designed to be extensible:

1. **Custom generators**: Subclass `GroundTruthGenerator` for specialized operations
2. **Additional formats**: Extend `GroundTruthData.to_dict()` for other serialization formats
3. **Property testing**: Add property verification alongside ground truth data
4. **Lean integration**: Create tools to automatically generate Lean test cases from JSON
