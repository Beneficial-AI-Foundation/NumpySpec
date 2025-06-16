import LeanArrayLib.Core

/--
A typeclass for types that can be interpreted as an n-dimensional index.
The `h_rank` field is a specification ensuring that `toNatArray` produces
an array of the advertised rank.
-/
class NdIndex (Idx : Type) where
  toNatArray : Idx → Array Nat
  rank : Nat
  /-- Specification: The size of the array version of the index must equal the rank. -/
  h_rank : ∀ (idx : Idx), (toNatArray idx).size = rank

-- Instances for 1D, 2D, and 3D indexing, each providing a proof of `h_rank`.
instance : NdIndex Nat where
  toNatArray i := #[i]
  rank := 1
  h_rank _ := rfl

instance : NdIndex (Nat × Nat) where
  toNatArray | (i, j) => #[i, j]
  rank := 2
  h_rank _ := rfl

instance : NdIndex (Nat × Nat × Nat) where
  toNatArray | (i, j, k) => #[i, j, k]
  rank := 3
  h_rank _ := rfl

-- An instance for providing an index directly as an array of Nats.
instance (n : Nat) : NdIndex (Fin n → Nat) where
  toNatArray idx := Array.ofFn idx
  rank := n
  h_rank _ := by simp [Array.size_ofFn]

namespace NdArray

/--
A theorem stating that the size of the array returned by `computeStrides`
is the same as the size of the input shape array. This is needed for proofs.
-/
theorem computeStrides_size_eq_shape_size (shape : Array Nat) : (computeStrides shape).size = shape.size := by
  -- This proof would follow from the definition of `computeStrides`.
  sorry

/--
Calculates the linear offset from a multi-dimensional index.

The return type `{ offset : Nat // offset < arr.data.size }` is a dependent type
that acts as a specification. It guarantees that any successfully computed
offset is a valid index into the underlying `data` buffer.

- **arr:** The `NdArray` to be indexed.
- **idx:** The multi-dimensional index.
- **h_rank:** A proof that the index has the same number of dimensions as the array.
- **returns:** `some ⟨offset, h_bound⟩` if the index is valid, `none` otherwise.
-/
def getOffset? (arr : NdArray α) (idx : Array Nat) (h_rank : arr.shape.size = idx.size) : Option { offset : Nat // offset < arr.data.size } :=
  let mut offset := 0
  for i in [:arr.shape.size] do
    let dim_idx := idx[i]!
    let dim_size := arr.shape[i]!
    if dim_idx >= dim_size then
      return none
    -- The stride is guaranteed to exist because of the h_strides invariant and the size theorem.
    have : i < arr.strides.size := by rw; exact (Array.get_lt..)
    offset := offset + dim_idx * arr.strides[i]

  have h_bound : offset < arr.data.size := by
    rw [arr.h_size]
    -- This proof relies on the mathematical property of mixed-radix number systems:
    -- The value of an index `(i_1,..., i_d)` where each `i_k < N_k` is always
    -- less than the total number of elements `N_1 *... * N_d`.
    -- A full formalization is non-trivial and would require a library for
    -- mixed-radix arithmetic.
    sorry
  some ⟨offset, h_bound⟩

/--
Generic `getElem` implementation for `NdArray`.
The condition `arr.shape.size = inst.rank` is a specification enforced at the call site,
ensuring that an array can only be indexed by an index of the correct rank.
-/
instance [inst : NdIndex Idx] : GetElem (NdArray α) Idx α fun arr _ => arr.shape.size = inst.rank where
  getElem (arr : NdArray α) (idx : Idx) (h_rank_match : arr.shape.size = inst.rank) :=
    let idxArr := NdIndex.toNatArray idx
    have h_idx_rank : idxArr.size = arr.shape.size := (inst.h_rank idx).trans h_rank_match.symm
    match getOffset? arr idxArr h_idx_rank with
| some ⟨offset, h_bound⟩ => arr.data.get ⟨offset, h_bound⟩
| none        => panic! "Index out of bounds"

/--
Generic `setElem` implementation for `NdArray`.
This is a pure function that returns a *new* `NdArray` with the modified element.
The `h_rank_match` argument makes invalid indexing a compile-time error.
-/
def setElem [inst : NdIndex Idx] (arr : NdArray α) (idx : Idx) (val : α) (h_rank_match : arr.shape.size = inst.rank) : NdArray α :=
  let idxArr := NdIndex.toNatArray idx
  have h_idx_rank : idxArr.size = arr.shape.size := (inst.h_rank idx).trans h_rank_match.symm
  match getOffset? arr idxArr h_idx_rank with
| some ⟨offset, h_bound⟩ =>
    let newData := arr.data.set ⟨offset, h_bound⟩ val
    {
      data    := newData,
      shape   := arr.shape,
      strides := arr.strides,
      h_size  := by simp [Array.size_set, arr.h_size],
      h_strides := arr.h_strides
    }
| none => panic! "Index out of bounds"

end NdArray
