# Pipeline for Generating Lean 4 Specifications from NumPy Documentation

## Overview

This document provides a systematic process for generating Vector-based Lean 4 specifications with Hoare triple syntax from NumPy function documentation and source code. The pipeline produces formal specifications that capture the mathematical properties of NumPy operations.

## Essential Concepts

### 1. Hoare Triple Syntax in Lean 4

The new syntax uses special brackets for pre/post conditions:
```lean
⦃⌜precondition⌝⦄ function ⦃⇓result => postcondition⦄
```

- `⦃⌜...⌝⦄` - Precondition wrapped in special brackets
- `⦃⇓result => ...⦄` - Postcondition with bound result variable
- Always end theorems with `:= by sorry` during specification phase

### 2. Array to Vector Transformation Rules

| Array Pattern | Vector Pattern |
|--------------|----------------|
| `Array T` | `Vector T n` |
| `a : Array Int` | `{n : Nat} (a : Vector Int n)` |
| `(h : a.size = b.size)` | Remove (enforced by type) |
| `a.size > 0` | Use `Vector T (n + 1)` |
| `∀ i (hi : i < a.size)` | `∀ i : Fin n` |
| `a[i]'hi` | `a.get i` |
| `∃ hr : res.size = a.size` | Remove (types match) |

## Complete Examples

### Example 1: Binary Operation (Addition)

**Array Version:**
```lean
def add (a b : Array Int): Id (Array Int) :=
  sorry

theorem add_spec (a b : Array Int) (h : a.size = b.size) :
    ⦃⌜a.size = b.size⌝⦄
    add a b
    ⦃⇓r => ∃ hr : r.size = a.size, ∀ i (hi : i < r.size), r[i] = a[i] + b[i]⦄ := by
  sorry
```

**Vector Version:**
```lean
def add {n : Nat} (a b : Vector Int n) : Id (Vector Int n) :=
  sorry

theorem add_spec {n : Nat} (a b : Vector Int n) :
    ⦃⌜True⌝⦄
    add a b
    ⦃⇓r => ∀ i : Fin n, r.get i = a.get i + b.get i⦄ := by
  sorry
```

### Example 2: Unary Operation Requiring Non-empty (Maximum)

**Array Version:**
```lean
def max (a : Array Int) : Id Int :=
  sorry

theorem max_spec (a : Array Int) (h : a.size > 0) :
    ⦃⌜a.size > 0⌝⦄
    max a
    ⦃⇓res => ∃ i : Nat, ∃ hi : i < a.size, res = a[i]'hi ∧
             ∀ j : Nat, ∀ hj : j < a.size, a[j]'hj ≤ res⦄ := by
  sorry
```

**Vector Version:**
```lean
def max {n : Nat} (a : Vector Int (n + 1)) : Id Int :=
  sorry

theorem max_spec {n : Nat} (a : Vector Int (n + 1)) :
    ⦃⌜True⌝⦄
    max a
    ⦃⇓res => ∃ i : Fin (n + 1), res = a.get i ∧
             ∀ j : Fin (n + 1), a.get j ≤ res⦄ := by
  sorry
```

## Step-by-Step Workflow

### 1. Initial Setup
```bash
mkdir -p DafnySpecs/dfy_syntax_from_doc
```

### 2. File-by-File Conversion Process

For each file:

1. **Read the original Array version**
   ```lean
   -- Identify: function signature, preconditions, postconditions
   ```

2. **Create the Vector version header**
   ```lean
   import Std.Do.Triple
   import Std.Tactic.Do
   
   open Std.Do
   ```

3. **Transform the function signature**
   - Add `{n : Nat}` parameter for vector size
   - Replace `Array T` with `Vector T n`
   - For non-empty requirements, use `Vector T (n + 1)`
   - Remove size equality parameters

4. **Transform the specification**
   - Simplify preconditions (usually to `⌜True⌝`)
   - Remove existential size proofs
   - Replace index types with `Fin n`
   - Use `.get` for element access

5. **Compile and verify**
   ```bash
   lake build  # Check for compilation errors
   ```

### 3. Common Patterns

#### Binary Operations (Equal Size)
```lean
def op {n : Nat} (a b : Vector T n) : Id (Vector R n) :=
  sorry

theorem op_spec {n : Nat} (a b : Vector T n) :
    ⦃⌜True⌝⦄
    op a b
    ⦃⇓r => ∀ i : Fin n, r.get i = f (a.get i) (b.get i)⦄ := by
  sorry
```

#### Operations with Non-zero Preconditions
```lean
def divide {n : Nat} (a b : Vector Int n) : Id (Vector Int n) :=
  sorry

theorem divide_spec {n : Nat} (a b : Vector Int n) 
    (h_nonzero : ∀ i : Fin n, b.get i ≠ 0) :
    ⦃⌜∀ i : Fin n, b.get i ≠ 0⌝⦄
    divide a b
    ⦃⇓r => ∀ i : Fin n, r.get i = a.get i / b.get i⦄ := by
  sorry
```

#### Index-returning Operations
```lean
def argmax {n : Nat} (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry

theorem argmax_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    argmax a
    ⦃⇓idx => a.get idx = max a ∧ 
            ∀ j : Fin (n + 1), j < idx → a.get j < a.get idx⦄ := by
  sorry
```

## Critical Success Factors

### 1. Type-Level Size Management
- Use implicit `{n : Nat}` parameters
- Let Lean infer sizes when possible
- Use `(n + 1)` pattern for non-empty constraints

### 2. Proof Simplification
- Vector types eliminate size equality proofs
- `Fin n` eliminates bounds checking proofs
- Focus specifications on actual behavior, not size management

### 3. Compilation Verification
- **Always** check compilation after each file
- Fix errors immediately before proceeding
- Common fixes:
  - Missing parentheses around array accesses
  - Incorrect proof term transformations
  - Type mismatches in index operations

### 4. Special Cases

#### 2D Arrays
```lean
-- Use Vector of Vectors
def flatten {rows cols : Nat} 
    (mat : Vector (Vector Int cols) rows) : 
    Id (Vector Int (rows * cols)) :=
  sorry
```

#### Dynamic Size Computation
```lean
-- Add size as parameter with constraint
def arange {n : Nat} (start stop step : Float) : Id (Vector Float n) :=
  sorry

theorem arange_spec {n : Nat} (start stop step : Float) 
    (h_size : n = ((stop - start)/step).floor.toUInt64.toNat) :
    ⦃⌜n = ((stop - start)/step).floor.toUInt64.toNat⌝⦄
    arange start stop step
    ⦃⇓v => v.get ⟨0, sorry⟩ = start ∧ ...⦄ := by
  sorry
```

## Common Pitfalls and Solutions

1. **Forgetting to wrap array accesses in parentheses**
   - Wrong: `a[i]'proof + b[i]'proof`
   - Right: `(a[i]'proof) + (b[i]'proof)`

2. **Using wrong index types**
   - Wrong: `∀ i : Nat, i < n → ...`
   - Right: `∀ i : Fin n, ...`

3. **Keeping unnecessary size proofs**
   - Wrong: `∃ hr : r.size = a.size, ...`
   - Right: Just use the postcondition directly

4. **Complex index proof terms**
   - Wrong: `a[i]'(hr ▸ h ▸ hi)`
   - Right: `a.get i` (with Vectors)

## Automation Strategy

When converting many files:

1. Start with 2-3 manual conversions to establish patterns
2. Create sub-agents for batches of similar files
3. Group files by operation type:
   - Binary operations (add, multiply, compare)
   - Unary operations (abs, sign, square)
   - Reductions (sum, max, argmax)
   - Special operations (reshape, flatten)

## Final Checklist

- [ ] All imports are correct
- [ ] Return type uses `Id` monad
- [ ] Specification uses ⦃⌜...⌝⦄ syntax
- [ ] Postcondition binds result with ⇓
- [ ] All array accesses use `.get`
- [ ] Indices use `Fin n` type
- [ ] File compiles with only `sorry` warnings
- [ ] No unnecessary size equality proofs
- [ ] The file could pass the lean4 compiler, you can use mcp tool to check the file.

## Input Format

The input will be a JSON object containing:
```json
{
  "name": "numpy.function_name",
  "description": "Brief description",
  "url": "https://numpy.org/doc/stable/...",
  "doc": "Full documentation string with parameters and returns",
  "code": "Python implementation"
}
```

## Output Format

Generate a Lean 4 specification file with:
1. Required imports
2. Function definition with `sorry` implementation
3. Specification theorem using Hoare triple syntax
4. Save to: `DafnySpecs/dfy_syntax_from_doc/Numpy_FunctionName.lean`

## Generation Process

### Step 1: Parse the Documentation

From the `doc` field, extract:
- **Parameters**: Types and constraints
- **Returns**: Type and properties
- **Behavior**: What the function computes

### Step 2: Determine Lean Types

| NumPy Type | Lean Type | Notes |
|------------|-----------|-------|
| `array_like` | `Vector T n` | Use implicit `{n : Nat}` |
| `ndarray of ints` | `Vector Int n` | |
| `ndarray of floats` | `Vector Float n` | |
| `int` (index) | `Fin n` | Type-safe index |
| `axis` parameter | Omit for now | Focus on 1D |

### Step 3: Identify Preconditions

Common preconditions to check for:
- Non-empty array: Use `(h : n > 0)` parameter or `Vector T (n + 1)`
- Value constraints: e.g., `∀ i : Fin n, v.get i ≠ 0`
- Size relationships: Handled by type system with Vectors

### Step 4: Generate the Specification

Template:
```lean
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- [Description from doc] -/
def functionName {n : Nat} (params...) : Id ReturnType :=
  sorry

/-- Specification: [describe what function does] -/
theorem functionName_spec {n : Nat} (params...) (preconditions...) :
    ⦃⌜precondition_formula⌝⦄
    functionName params
    ⦃⇓result => postcondition_formula⦄ := by
  sorry
```

## Complete Example: numpy.argmax

**Input:**
```json
{
  "name": "numpy.argmax",
  "description": "Returns the indices of the maximum values along an axis.",
  "doc": "numpy.argmax(a, axis=None, out=None, *, keepdims=<no value>)\n\nReturns the indices of the maximum values along an axis.\n\nParameters:\n- a : array_like\n  Input array.\n- axis : int, optional\n  By default, the index is into the flattened array.\n\nReturns:\n- index_array : ndarray of ints\n  Array of indices into the array.",
  "code": "..."
}
```

**Output:**
```lean
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns the index of the maximum value in a vector (first occurrence) -/
def argmax {n : Nat} (arr : Vector Float n) (h : n > 0) : Id (Fin n) :=
  sorry

/-- Specification: argmax returns the index of the first maximum element -/
theorem argmax_spec {n : Nat} (arr : Vector Float n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    argmax arr h
    ⦃⇓ret => (∀ i : Fin n, i < ret → arr.get ret > arr.get i) ∧
             (∀ i : Fin n, ret < i → arr.get ret ≥ arr.get i)⦄ := by
  sorry
```

Save as: `DafnySpecs/dfy_syntax_from_doc/Numpy_Argmax.lean`

## Specification Patterns by Function Type

### 1. Element-wise Operations (add, multiply, abs)
```lean
def op {n : Nat} (a b : Vector T n) : Id (Vector T n) :=
  sorry

theorem op_spec {n : Nat} (a b : Vector T n) :
    ⦃⌜True⌝⦄
    op a b
    ⦃⇓r => ∀ i : Fin n, r.get i = f (a.get i) (b.get i)⦄ := by
  sorry
```

### 2. Reduction Operations (sum, max, min)
```lean
def reduce {n : Nat} (arr : Vector T (n + 1)) : Id T :=
  sorry

theorem reduce_spec {n : Nat} (arr : Vector T (n + 1)) :
    ⦃⌜True⌝⦄
    reduce arr
    ⦃⇓res => property_of_result⦄ := by
  sorry
```

### 3. Index-returning Operations (argmax, argmin)
```lean
def argop {n : Nat} (arr : Vector T n) (h : n > 0) : Id (Fin n) :=
  sorry

theorem argop_spec {n : Nat} (arr : Vector T n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    argop arr h
    ⦃⇓idx => property_of_index⦄ := by
  sorry
```

### 4. Array Generation (zeros, ones, arange)
```lean
def generate (n : Nat) (params...) : Id (Vector T n) :=
  sorry

theorem generate_spec (n : Nat) (params...) :
    ⦃⌜constraints_on_params⌝⦄
    generate n params
    ⦃⇓arr => ∀ i : Fin n, arr.get i = formula⦄ := by
  sorry
```

## Key Decisions When Generating

1. **Parameter Selection**: 
   - Ignore `axis`, `out`, `keepdims` for 1D specifications
   - Focus on core mathematical behavior

2. **Type Selection**:
   - Use `Float` for general numeric operations
   - Use `Int` for index operations
   - Use `Bool` for comparison results

3. **Precondition Extraction**:
   - "non-empty" → `(h : n > 0)` or `Vector T (n + 1)`
   - "positive values" → `∀ i : Fin n, arr.get i > 0`
   - Division operations → non-zero divisors

4. **Postcondition Formulation**:
   - Express the mathematical property precisely
   - Use `∀ i : Fin n` for element-wise properties
   - Use `∃ i : Fin n` for existence properties

## File Naming Convention

For NumPy function `numpy.function_name`:
- File: `Numpy_FunctionName.lean`
- Location: `DafnySpecs/dfy_syntax_from_doc/`
- Examples:
  - `numpy.argmax` → `Numpy_Argmax.lean`
  - `numpy.array_equal` → `Numpy_ArrayEqual.lean`
  - `numpy.dot` → `Numpy_Dot.lean`

## Generation Prompt Template

"Given the NumPy function documentation below, generate a Lean 4 specification using Vector types and Hoare triple syntax. Extract the core mathematical behavior from the documentation, determine appropriate preconditions, and express the postcondition precisely. Save the output to `DafnySpecs/dfy_syntax_from_doc/Numpy_[FunctionName].lean`. Focus on 1D array behavior and ignore parameters like axis, out, and keepdims."

## Checklist for Generated Specifications

- [ ] Imports are present: `Std.Do.Triple` and `Std.Tactic.Do`
- [ ] Function name follows Lean conventions (camelCase)
- [ ] Appropriate use of `{n : Nat}` for vector sizes
- [ ] Preconditions correctly extracted from documentation
- [ ] Postcondition captures the mathematical property
- [ ] File saved with correct naming convention
- [ ] All functions end with `:= sorry`
- [ ] All theorems end with `:= by sorry`