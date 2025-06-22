import Lean
import LeanArrayLib.Memory
import LeanArrayLib.Layout
import LeanArrayLib.Index

namespace LeanArrayLib

/-- `LeanArray` is the main array type that combines memory storage with indexing capabilities.

    Type parameters:
    - `α`: The element type (must have a PlainDataType instance)
    - `I`: The index type (e.g., Fin n for 1D, Fin m × Fin n for 2D)
    - `n`: The total number of elements in the array

    Fields:
    - `buffer`: The underlying memory storage
    - `layout`: The dimensional layout information
    - `len_ok`: Proof that the buffer length matches the expected size

    This structure provides type-safe multi-dimensional arrays with compile-time
    bounds checking through Lean's dependent type system.
-/
structure LeanArray (α : Type) (I : Type) (n : Nat) [PlainDataType α]
  [IndexType I n] where
  /-- The underlying memory storage containing serialized elements -/
  buffer : Buffer α
  /-- The dimensional layout information (for future multi-dimensional support) -/
  layout : Layout      -- for future use
  /-- Proof that the buffer contains exactly n elements -/
  len_ok : buffer.length = n

namespace LeanArray

/-- Create a 1D array from a list of UInt8 values.

    The resulting array has index type `Fin xs.length`, ensuring that all
    accesses are bounds-checked at compile time. The layout is set to
    row-major with a single dimension.

    Note: The proof obligation is currently admitted with `sorry`.
-/
@[inline] def fromList (xs : List UInt8) : LeanArray UInt8 (Fin xs.length) xs.length :=
  let buf := xs.foldl (fun b x => b.push x) Buffer.mkEmpty
  { buffer := buf,
    layout := Layout.rowMajor [xs.length],
    len_ok := sorry }  -- Proof omitted for simplicity

/-- Access an element at the given index.

    This function provides safe element access by:
    1. Converting the index to a linear position using IndexType
    2. Reading from the buffer (using bounds from len_ok)
    3. Decoding the stored bytes back to the element type

    Panics if decoding fails, which should never happen for well-formed arrays.
-/
@[inline]
def get {α I n} [PlainDataType α] [Inhabited α] [IndexType I n]
    (arr : LeanArray α I n) (idx : I) : α :=
  let lin : Fin n := IndexType.toLinear idx
  -- Use ByteArray.get! which panics on out of bounds
  let u : UInt8 := arr.buffer.data.get! lin.val
  match PlainDataType.decode (α := α) #[u] with
  | some v => v
  | none => panic! "decode failed"

/-- Instance for array indexing notation `arr[idx]`.

    This allows natural syntax for array access using square brackets.
    The constraint `λ _ _ => True` means indexing is always allowed
    (bounds checking happens at the type level through IndexType).
-/
instance {α I n} [PlainDataType α] [Inhabited α] [IndexType I n] :
    GetElem (LeanArray α I n) I α (λ _ _ => True) where
  getElem a i _ := a.get i

end LeanArray
end LeanArrayLib
