import Lean
import LeanArrayLib.Memory
import LeanArrayLib.Layout
import LeanArrayLib.Index

open LeanArrayLib

-- Add Inhabited instance for UInt8
instance : Inhabited UInt8 where
  default := 0

-- Simple test without array access that requires proofs
def main : IO Unit := do
  IO.println "Testing LeanArrayLib basic functionality..."

  -- Test 1: PlainDataType encode/decode
  let testVals : List UInt8 := [0, 42, 127, 255]
  let allPassed := testVals.all fun v =>
    match PlainDataType.decode (α := UInt8) (PlainDataType.encode (α := UInt8) v) with
    | some decoded => decoded == v
    | none => false

  if allPassed then
    IO.println "✅ Encode/decode tests passed!"
  else
    IO.println "❌ Encode/decode tests failed!"

  -- Test 2: Buffer operations
  let buf0 : Buffer UInt8 := Buffer.mkEmpty
  let buf1 := buf0.push 10
  let buf2 := buf1.push 20
  let buf3 := buf2.push 30

  IO.println s!"Buffer lengths: {buf0.length}, {buf1.length}, {buf2.length}, {buf3.length}"

  -- Test 3: Layout computation
  let shapes := [[2, 3], [3, 4], [2, 2, 2]]
  for shape in shapes do
    let layout := Layout.rowMajor shape
    IO.println s!"Shape {shape} -> strides {layout.strides.toList}"

  IO.println "Basic tests completed!"

#eval main
