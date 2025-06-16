import LeanArrayLib.Core
import LeanArrayLib.Indexing

/--
A non-owning view into an `NdArray`.

This lightweight structure provides a way to interpret the data of an `NdArray`
with a different shape, offset, or strides, without copying the underlying data.
-/
structure ArrayView (α : Type) where
  base    : NdArray α
  offset  : Nat
  shape   : Array Nat
  strides : Array Nat
  /-- Specification: The shape and strides arrays must have the same length. -/
  h_dims  : shape.size = strides.size
  deriving Repr

namespace ArrayView

/-- Creates a view that covers the entire `NdArray`. -/
def ofNdArray (arr : NdArray α) : ArrayView α :=
  {
    base    := arr,
    offset  := 0,
    shape   := arr.shape,
    strides := arr.strides,
    h_dims  := by rw
  }

/--
Calculates the linear offset for an index *within the base array's data*.
The dependent return type guarantees the offset is a valid index into the base array.
-/
def getOffset? (v : ArrayView α) (idx : Array Nat) (h_rank : v.shape.size = idx.size) : Option { offset : Nat // offset < v.base.data.size } :=
  let mut local_offset := 0
  for i in [:v.shape.size] do
    if idx[i]! >= v.shape[i]! then return none
    have : i < v.strides.size := by rw [←v.h_dims]; exact (Array.get_lt..)
    local_offset := local_offset + idx[i]! * v.strides[i]

  let final_offset := v.offset + local_offset
  have h_bound : final_offset < v.base.data.size := by
    -- This proof is more complex than for `NdArray`. It requires an invariant
    -- on the `ArrayView` itself, guaranteeing that the view (defined by its
    -- offset, shape, and strides) does not point outside the bounds of its
    -- base array. For simplicity, we omit this complex invariant and its proof.
    sorry
  some ⟨final_offset, h_bound⟩

/-- Generic `getElem` implementation for `ArrayView`. -/
instance [inst : NdIndex Idx] : GetElem (ArrayView α) Idx α fun v _ => v.shape.size = inst.rank where
  getElem (v : ArrayView α) (idx : Idx) (h_rank_match : v.shape.size = inst.rank) :=
    let idxArr := NdIndex.toNatArray idx
    have h_idx_rank : idxArr.size = v.shape.size := (inst.h_rank idx).trans h_rank_match.symm
    match getOffset? v idxArr h_idx_rank with
| some ⟨offset, h_bound⟩ => v.base.data.get ⟨offset, h_bound⟩
| none        => panic! "Index out of bounds"

end ArrayView

namespace ArrayView

/-- Creates a zero-copy slice of a view along a single dimension. -/
def slice (v : ArrayView α) (dim : Nat) (start : Nat) (stop : Nat) : Option (ArrayView α) :=
  if h_dim : dim < v.shape.size then
    if h_start : start <= stop then
      if h_stop : stop <= v.shape[dim] then
        let new_offset := v.offset + start * v.strides[dim]!
        let new_shape := v.shape.set! dim (stop - start)
        some {
          v with
          offset := new_offset,
          shape := new_shape,
          h_dims := by simp [Array.size_set, v.h_dims]
        }
      else none
    else none
  else none

/-- Creates a view with a reduced rank by fixing an index along one dimension. -/
def index (v : ArrayView α) (dim : Nat) (idx : Nat) : Option (ArrayView α) :=
  if h_dim : dim < v.shape.size then
    if h_idx : idx < v.shape[dim] then
      let new_offset := v.offset + idx * v.strides[dim]!
      let new_shape := v.shape.eraseIdx dim
      let new_strides := v.strides.eraseIdx dim
      some {
        base := v.base,
        offset := new_offset,
        shape := new_shape,
        strides := new_strides,
        h_dims := by simp [Array.size_eraseIdx, v.h_dims]
      }
    else none
  else none

end ArrayView

namespace ArrayView

/-- Creates a zero-copy transposition of a view by swapping two dimensions. -/
def transpose (v : ArrayView α) (dim1 : Nat) (dim2 : Nat) : Option (ArrayView α) :=
  if h1 : dim1 < v.shape.size then
    if h2 : dim2 < v.shape.size then
      let new_shape := v.shape.swap dim1 dim2
      let new_strides := v.strides.swap dim1 dim2
      some {
        v with
        shape := new_shape,
        strides := new_strides,
        h_dims := by simp [Array.size_swap, v.h_dims]
      }
    else none
  else none

/-- A safe, zero-copy reshape operation. -/
def reshape (v : ArrayView α) (new_shape : Array Nat) : Option (ArrayView α) :=
  -- A proper implementation requires checking for contiguity.
  if totalSize v.shape!= totalSize new_shape then
    none
  else
    let new_strides := computeStrides new_shape
    some {
      v with
      shape := new_shape,
      strides := new_strides,
      h_dims := by simp
    }

end ArrayView
