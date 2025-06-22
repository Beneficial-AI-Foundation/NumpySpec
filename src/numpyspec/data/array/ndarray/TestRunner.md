# Running Tests for LeanArrayLib and NDArray

## Method 1: Direct Execution with Lake

### Build and run specific test executables:

```bash
# For LeanArrayLib tests
lake build test
./.lake/build/bin/test

# For NDArray tests  
lake build ndtest
./.lake/build/bin/ndtest

# Build all executables
lake build
```

## Method 2: Using Lake Scripts

Add scripts to your lakefile for convenient test execution.

### Option A: Convert lakefile.toml to lakefile.lean

Create `lakefile.lean` with test scripts:

```lean
import Lake
open Lake DSL

package leanArrayLib where
  version := "0.1.0"
  leanOptions := #[
    ⟨`linter.missingDocs, true⟩
  ]

lean_lib LeanArrayLib
lean_lib NDArray

@[default_target]
lean_exe leanarraylib where
  root := `Main

lean_exe test where
  root := `Test

lean_exe ndtest where
  root := `NDArrayTest

-- Test scripts
script test do
  IO.println "Running all tests..."
  -- Run LeanArrayLib tests
  IO.println "\n=== LeanArrayLib Tests ==="
  let testResult ← IO.Process.run {
    cmd := "./.lake/build/bin/test"
  }
  IO.print testResult
  
  -- Run NDArray tests
  IO.println "\n=== NDArray Tests ==="
  let ndtestResult ← IO.Process.run {
    cmd := "./.lake/build/bin/ndtest"
  }
  IO.print ndtestResult
  
  return 0

script test_lean do
  IO.println "Running LeanArrayLib tests..."
  let result ← IO.Process.run {
    cmd := "./.lake/build/bin/test"
  }
  IO.print result
  return 0

script test_nd do
  IO.println "Running NDArray tests..."
  let result ← IO.Process.run {
    cmd := "./.lake/build/bin/ndtest"
  }
  IO.print result
  return 0
```

### Option B: Use a Makefile

Create a `Makefile`:

```makefile
.PHONY: test test-lean test-nd build clean

build:
	lake build

test: build
	@echo "=== Running All Tests ==="
	@echo "\n--- LeanArrayLib Tests ---"
	@./.lake/build/bin/test
	@echo "\n--- NDArray Tests ---"
	@./.lake/build/bin/ndtest

test-lean: build
	@echo "=== Running LeanArrayLib Tests ==="
	@./.lake/build/bin/test

test-nd: build
	@echo "=== Running NDArray Tests ==="
	@./.lake/build/bin/ndtest

clean:
	lake clean
```

## Method 3: Using Shell Scripts

Create `run_tests.sh`:

```bash
#!/bin/bash
set -e

echo "Building project..."
lake build

echo -e "\n=== Running LeanArrayLib Tests ==="
./.lake/build/bin/test

echo -e "\n=== Running NDArray Tests ==="
./.lake/build/bin/ndtest

echo -e "\nAll tests completed!"
```

## Method 4: Direct Lean Evaluation

For quick testing during development:

```bash
# Run test file directly without building executable
lake env lean Test.lean
lake env lean NDArrayTest.lean
```

## Recommended Approach

For your project, I recommend Method 2 Option A (converting to lakefile.lean) because:
1. It integrates well with Lake's ecosystem
2. Allows `lake run test` to work as expected
3. Provides flexibility for different test configurations
4. Maintains all build configuration in one place

To use it:
1. Convert lakefile.toml to lakefile.lean (shown above)
2. Run `lake run test` to execute all tests
3. Run `lake run test_lean` or `lake run test_nd` for specific tests