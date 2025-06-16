import Lean
import LeanArrayLib.Memory
import LeanArrayLib.Layout
import LeanArrayLib.Index
import LeanArrayLib.LeanArray

open LeanArrayLib

/-- Test 0: round‑trip correctness of `encode`/`decode` for `UInt8`. -/
def testEncodeDecode : Bool :=
  List.all (List.range 256) (fun n =>
    let b : UInt8 := UInt8.ofNat n
    (PlainDataType.decode (α := UInt8) (PlainDataType.encode (α := UInt8) b)) = some b)

/-- Test 1: 1‑D array creation and element access. -/
def test1D : Bool :=
  let xs : List UInt8 := (List.range 10).map fun n => UInt8.ofNat n
  let arr := LeanArray.fromList xs
  List.all (List.range 10) (fun i =>
    arr[Fin.ofNat (m := 10) i] = UInt8.ofNat i)

/-- Test 2: 2‑D (row‑major) indexing: 2×3 matrix stored 0‥5. -/
def test2D : Bool :=
  let elems : List UInt8 := (List.range 6).map fun n => UInt8.ofNat n
  let buf  : Buffer UInt8 := elems.foldl (fun b x => b.push x) (Buffer.mkEmpty 6)
  let lay  := Layout.mkRowMajor #[2, 3]
  have hlen : buf.length = 6 := by
    simp [Buffer.length, PlainDataType.byteSize]
  let arr  : LeanArray UInt8 (Fin 2 × Fin 3) := {
    buffer := buf,
    layout := lay,
    h_size := by
      simpa using hlen }
  List.all (List.range 2) (fun i =>
    List.all (List.range 3) (fun j =>
      let idx : (Fin 2 × Fin 3) := (⟨i, by decide⟩, ⟨j, by decide⟩)
      arr[idx] = UInt8.ofNat (i * 3 + j)))

/-- Aggregate all boolean tests. -/
def allTests : Bool :=
  testEncodeDecode && test1D && test2D

/-- Entry point. -/
def main : IO UInt32 := do
  if allTests then
    IO.println "✅ LeanArray tests passed!"
  else
    IO.eprintln "❌ LeanArray tests failed!"
  pure 0

/-- Quick eval. Comment out if you only use `lake run`. -/
#eval main
