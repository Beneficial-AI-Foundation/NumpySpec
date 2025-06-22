import StdArrayOperation

/-
# Test cases for Array Operations

This file demonstrates the array operations defined in StdArrayOperation.Basic
-/

-- Test element-wise addition
def test_add : IO Unit := do
  let a : Array Nat := #[1, 2, 3, 4]
  let b : Array Nat := #[5, 6, 7, 8]
  let c := a.add b
  IO.println s!"Addition: {a} + {b} = {c}"

-- Test element-wise subtraction
def test_sub : IO Unit := do
  let a : Array Nat := #[10, 20, 30, 40]
  let b : Array Nat := #[5, 10, 15, 20]
  let c := a.sub b
  IO.println s!"Subtraction: {a} - {b} = {c}"

-- Test element-wise multiplication
def test_mul : IO Unit := do
  let a : Array Nat := #[2, 3, 4, 5]
  let b : Array Nat := #[10, 20, 30, 40]
  let c := a.mul b
  IO.println s!"Multiplication: {a} * {b} = {c}"

-- Test element-wise division and modulo
def test_divMod : IO Unit := do
  let a : Array Nat := #[20, 35, 47, 62]
  let b : Array Nat := #[3, 5, 6, 8]
  let (divs, mods) := a.divMod b
  IO.println s!"DivMod: {a} divMod {b} = (divs: {divs}, mods: {mods})"

-- Test zeros creation
def test_zeros : IO Unit := do
  let z : Array Nat := Array.zeros 5
  IO.println s!"Zeros(5): {z}"

-- Test scalar multiplication
def test_scalarMul : IO Unit := do
  let a : Array Nat := #[1, 2, 3, 4]
  let c := a.scalarMul 10
  IO.println s!"Scalar multiplication: 10 * {a} = {c}"

-- Test negation with integers
def test_neg : IO Unit := do
  let a : Array Int := #[1, -2, 3, -4]
  let c := a.neg
  IO.println s!"Negation: -{a} = {c}"

-- Test with floating point numbers
def test_float : IO Unit := do
  let a : Array Float := #[1.5, 2.5, 3.5]
  let b : Array Float := #[0.5, 1.5, 2.5]
  let c := a.add b
  IO.println s!"Float addition: {a} + {b} = {c}"

-- Test size mismatch handling (will panic)
def test_size_mismatch : IO Unit := do
  let a : Array Nat := #[1, 2, 3]
  let b : Array Nat := #[4, 5]
  try
    let c := a.add b  -- This should panic
    IO.println s!"This shouldn't print: {c}"
  catch e =>
    IO.println s!"Caught expected error: {e}"

-- Main test runner
def main : IO Unit := do
  IO.println "Running Array Operation Tests..."
  IO.println "================================"

  test_add
  test_sub
  test_mul
  test_divMod
  test_zeros
  test_scalarMul
  test_neg
  test_float

  IO.println "\nTesting error handling..."
  test_size_mismatch

  IO.println "\nAll tests completed!"
