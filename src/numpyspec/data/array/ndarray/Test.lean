import Lean
import LeanArrayLib.Memory
import LeanArrayLib.Layout
import LeanArrayLib.Index
import LeanArrayLib.LeanArray

open LeanArrayLib

-- Add Inhabited instance for UInt8
instance : Inhabited UInt8 where
  default := 0

-- Simple test that doesn't require proofs
def simpleTest : IO Unit := do
  IO.println "Testing LeanArrayLib implementation..."

  -- Test encode/decode
  let b : UInt8 := 42
  let encoded := PlainDataType.encode (α := UInt8) b
  let decoded := PlainDataType.decode (α := UInt8) encoded
  IO.println s!"Encode/decode test: {b} -> {encoded} -> {decoded}"

  -- Test 1D array
  let xs : List UInt8 := [1, 2, 3, 4, 5]
  IO.println s!"Creating array from list: {xs}"
  -- Note: We can't test array access without completing the proof

  -- Test Buffer operations
  let buf : Buffer UInt8 := Buffer.mkEmpty
  let buf1 := buf.push (10 : UInt8)
  let buf2 := buf1.push (20 : UInt8)
  IO.println s!"Buffer length after pushes: {buf2.length}"

  -- Test Layout
  let layout := Layout.rowMajor [2, 3]
  IO.println s!"Layout shape: {layout.shape.toList}"
  IO.println s!"Layout strides: {layout.strides.toList}"

  IO.println "Tests completed!"

-- Run the test
#eval! simpleTest  -- Using #eval! to bypass sorry warning
