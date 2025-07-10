# NumpySpec `add` Function Definition and Specification

## Overview
The `add` function in NumpySpec has been defined but not yet fully implemented. Here's what exists:

## Location 1: Main Implementation (NumpySpec/Numpy_Add.lean)

### Definition
```lean
def numpy_add {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
```

- Takes two vectors of the same length `n`
- Returns a vector of the same length
- Currently unimplemented (marked with `sorry`)

### Specification
```lean
theorem numpy_add_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_add x1 x2
    ⦃⇓result => ∀ i : Fin n, result.get i = x1.get i + x2.get i⦄ := by
  sorry
```

The specification states:
- **Precondition**: `True` (no special preconditions)
- **Postcondition**: For all indices i, `result[i] = x1[i] + x2[i]`

## Location 2: Documentation/Spec File (NumpySpec/mathematical_functions/add.lean)

This file contains the NumPy documentation and Python implementation reference:
- **Description**: "Add arguments element-wise"
- **NumPy signature**: `numpy.add(x1, x2, /, out=None, *, where=True, casting='same_kind', order='K', dtype=None, subok=True)`
- **Python implementation notes**: Uses universal function (ufunc) with broadcasting support

## Current Status
- The function signature is defined
- The specification (theorem) is written
- The implementation is not complete (both definition and proof use `sorry`)
- The current Lean implementation is simplified compared to NumPy (no broadcasting, output parameters, or type casting)

## Next Steps for Implementation
To complete the implementation, you would need to:
1. Replace the `sorry` in the definition with actual element-wise addition
2. Prove the specification theorem
3. Consider extending to support more NumPy features like broadcasting