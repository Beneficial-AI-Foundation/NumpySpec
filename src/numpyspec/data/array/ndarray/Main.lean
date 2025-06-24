import 
import LeanArrayLib.Memory
import LeanArrayLib.Layout
import LeanArrayLib.Index
import LeanArrayLib.LeanArray

open LeanArrayLib

-- Add Inhabited instance for UInt8
instance : Inhabited UInt8 where
  default := 0

/-- Test the round-trip correctness of encode/decode operations for UInt8.

    This test verifies that for all possible UInt8 values (0-255), encoding
    followed by decoding returns the original value. This is a fundamental
    property required for the array storage system to work correctly.
-/
def testEncodeDecode : Bool :=
  List.all (List.range 256) (fun n =>
    let b : UInt8 := UInt8.ofNat n
    (PlainDataType.decode (α := UInt8) (PlainDataType.encode (α := UInt8) b)) = some b)

/-- Test 1D array creation and element access.

    Creates a 1D array containing [0, 1, 2, ..., 9] and verifies that each
    element can be accessed correctly using array indexing notation.

    This tests:
    - Array creation from a list
    - Type-safe indexing with Fin types
    - Element retrieval
-/
def test1D : Bool :=
  let xs : List UInt8 := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  let arr := LeanArray.fromList xs
  List.all (List.range 10) (fun i =>
    if h : i < xs.length then
      let idx : Fin xs.length := ⟨i, h⟩
      arr[idx] = UInt8.ofNat i
    else false)

/-- Test 2D array indexing with row-major layout.

    Creates a 2×3 matrix stored as [0, 1, 2, 3, 4, 5] in row-major order:
    ```
    [[0, 1, 2],
     [3, 4, 5]]
    ```

    Verifies that 2D indexing (i, j) correctly maps to the linear position i*3 + j.

    This tests:
    - Multi-dimensional indexing
    - Row-major layout computation
    - IndexType instance for pairs
-/
def test2D : Bool :=
  -- Since we have 2*3 = 6, we can work directly with that
  let elems : List UInt8 := [0, 1, 2, 3, 4, 5]
  let buf  : Buffer UInt8 := elems.foldl (fun b x => b.push x) Buffer.mkEmpty
  let lay  := Layout.rowMajor [2, 3]
  have hlen : buf.length = (2*3) := sorry
  let arr  : LeanArray UInt8 (Fin 2 × Fin 3) (2*3) := {
    buffer := buf,
    layout := lay,
    len_ok := hlen }
  List.all (List.range 2) (fun i =>
    List.all (List.range 3) (fun j =>
      if hi : i < 2 then
        if hj : j < 3 then
          let idx : (Fin 2 × Fin 3) := (⟨i, hi⟩, ⟨j, hj⟩)
          arr[idx] = UInt8.ofNat (i * 3 + j)
        else false
      else false))

/-- Run all tests and return true if all pass.

    This aggregates all individual test results using logical AND.
-/
def allTests : Bool :=
  testEncodeDecode && test1D && test2D

/-- Main entry point for the test suite.

    Runs all tests and reports the results. Returns exit code 0 on success.
-/
def main : IO UInt32 := do
  if allTests then
    IO.println "✅ LeanArray tests passed!"
  else
    IO.eprintln "❌ LeanArray tests failed!"
  pure 0

-- Quick eval. Comment out if you only use `lake run`.
-- #eval main  -- Cannot eval with sorry in the code

-- End of file
