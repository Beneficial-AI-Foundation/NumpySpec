import Lean
import LeanArrayLib.Memory
import LeanArrayLib.Layout
import LeanArrayLib.Index

namespace LeanArrayLib

/-- High‑level array.  `n` is implicit via `IndexType`. -/
structure LeanArray (α : Type) (I : Type) [PlainDataType α]
  [IndexType I n] where
  buffer : Buffer α
  layout : Layout      -- for future use
  len_ok : buffer.length = n

namespace LeanArray

/-- Build 1‑D array from list. -/
@[inline] def fromList (xs : List UInt8) : LeanArray UInt8 (Fin xs.length) :=
  let buf := xs.foldl (fun b x => b.push x) Buffer.empty
  { buffer := buf,
    layout := Layout.rowMajor [xs.length],
    len_ok := by simp [Buffer.length, Buffer.empty] }

/-- Access element. -/
@[inline] def get {α I n} [PlainDataType α] [IndexType I n]
    (arr : LeanArray α I) (idx : I) : α :=
  let lin : Fin n := IndexType.toLinear idx
  -- `len_ok` ensures bounds
  unsafe_cast (arr.buffer.readUnsafe lin)
where
  unsafe unsafe_cast [PlainDataType α] (x : α) : α := x

instance {α I n} [PlainDataType α] [IndexType I n] :
    GetElem (LeanArray α I) I α (λ _ _ => True) where
  getElem a i _ := a.get i

end LeanArray
end LeanArrayLib
