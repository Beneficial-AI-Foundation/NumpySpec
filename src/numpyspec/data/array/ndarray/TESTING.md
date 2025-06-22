# Testing Guide for LeanArrayLib and NDArray

## Quick Start

The project now has multiple ways to run tests:

### 1. Using Lake Scripts (Recommended)
```bash
# Run all tests
lake run test

# Run only LeanArrayLib tests
lake run test_lean

# Run only NDArray tests
lake run test_nd
```

### 2. Using Make
```bash
# Run all tests
make test

# Run specific tests
make test-lean    # LeanArrayLib only
make test-nd      # NDArray only

# Run tests directly without building executables
make test-direct
```

### 3. Direct Execution
```bash
# Build and run manually
lake build testexe ndtest
./.lake/build/bin/testexe
./.lake/build/bin/ndtest
```

### 4. Development Testing (Fastest)
```bash
# Run test files directly without building executables
lake env lean Test.lean
lake env lean NDArrayTest.lean
```

## Test Structure

### LeanArrayLib Tests (`Test.lean`)
- Basic encode/decode functionality
- Buffer operations
- Layout computations
- 1D array creation (limited by proof requirements)

### NDArray Tests (`NDArrayTest.lean`)
Comprehensive n-dimensional array testing:
- **1D Arrays**: vectors with basic operations
- **2D Arrays**: matrices with element access and operations
- **3D Arrays**: tensors with slicing patterns
- **4D Arrays**: ML-style batch processing (batch × height × width × channels)
- **5D Arrays**: high-dimensional data structures
- **Edge Cases**: scalars, single elements, empty dimensions
- **Reshaping**: dimension transformation with size preservation

## Why the Error Occurred

The original error `unknown script test` happened because:
1. `lake run` expects **scripts** defined in the lakefile, not executables
2. The original `lakefile.toml` only defined executables, not scripts
3. Lake executables need a `main` function to be buildable

## Solution Implemented

1. **Converted to `lakefile.lean`**: More flexible than TOML for defining scripts
2. **Added `main` functions**: Both test files now have proper entry points
3. **Created test scripts**: `lake run test` now works as expected
4. **Alternative methods**: Makefile and direct execution options

## Adding New Tests

To add new tests:

1. **For unit tests**: Add to existing test files
2. **For new test suites**: 
   ```lean
   -- MyNewTest.lean
   def myTestSuite : IO Unit := do
     IO.println "Running my tests..."
     -- test code here
   
   def main : IO Unit := myTestSuite
   ```

3. **Update lakefile.lean**:
   ```lean
   lean_exe mynewtest where
     root := `MyNewTest
   ```

4. **Update test script**:
   ```lean
   script test do
     -- ... existing code ...
     -- Add your new test
     let newResult ← IO.Process.output {
       cmd := "./.lake/build/bin/mynewtest"
     }
     IO.print newResult.stdout
   ```

## Continuous Testing

For development, you can watch for changes and auto-run tests:

```bash
# Using fswatch (install with: brew install fswatch)
fswatch -o *.lean | xargs -n1 -I{} make test-direct

# Using entr (install with: brew install entr)
ls *.lean | entr -c make test-direct
```

## Test Output

All tests provide clear output:
- Shape information for all dimensions
- Element access verification  
- Operation results
- Edge case handling
- Success/failure status

## Future Improvements

Consider adding:
- Property-based testing with Lean's `Plausible`
- Performance benchmarks
- Formal verification of test properties
- CI/CD integration with GitHub Actions