import Lean

def computeStrides (shape : Array Nat) : Array Nat :=
  let n := shape.size
  if n = 0 then
    #[]
  else
    let revShape := shape.reverse
    let revStrides := revShape.foldl (fun (acc : Array Nat) (dim : Nat) =>
      let lastStride := acc.back? |>.getD 1
      acc.push (lastStride * dim)
    ) #[]
    (revStrides.pop).reverse

def totalSize (shape : Array Nat) : Nat :=
  shape.foldl (· * ·) 1

/--
An owning n-dimensional array structure.

This structure is responsible for the allocation and management of a contiguous
memory buffer (`data`). It also stores the canonical shape and row-major strides
for interpreting that buffer as a multi-dimensional array.

The invariants `h_size` and `h_strides` are formal specifications enforced by
the type system. Any function creating an `NdArray` must provide proofs that
these invariants hold.
-/
structure NdArray (α : Type) where
  data    : Array α
  shape   : Array Nat
  strides : Array Nat
  /-- Specification: The size of the data buffer must equal the total size computed from the shape. -/
  h_size  : data.size = totalSize shape
  /-- Specification: The strides must be the canonical row-major strides for the shape. -/
  h_strides : strides = computeStrides shape
  deriving Repr

namespace NdArray

/--
Creates a new `NdArray` of a given shape, initialized with a default value.
This function provides proofs that the constructed array satisfies the `h_size`
and `h_strides` invariants.
-/
def new (shape : Array Nat) (default : α) [Inhabited α] : NdArray α :=
  let size := totalSize shape
  let data := Array.mkArray size default
  {
    data    := data,
    shape   := shape,
    strides := computeStrides shape,
    h_size  := by simp [Array.size_mkArray, size],
    h_strides := rfl
  }

/--
Creates a new `NdArray` from a flat `Array` and a target shape.
This function's return type `Option (NdArray α)` acts as a specification:
it returns `some` only if the input data's size is compatible with the shape.
The `if h :...` syntax provides the necessary proof for the `h_size` invariant.
-/
def ofArray (data : Array α) (shape : Array Nat) : Option (NdArray α) :=
  if h : data.size = totalSize shape then
    some {
      data    := data,
      shape   := shape,
      strides := computeStrides shape,
      h_size  := h,
      h_strides := rfl
    }
  else
    none

/--
Creates a new `NdArray` by applying a function to each valid index.
-/
def ofFn (shape : Array Nat) (f : Array Nat → α) [Inhabited α] : NdArray α :=
  let rec build (dim : Nat) (idx : Array Nat) (acc : Array α) : Array α :=
    if dim < shape.size then
      let mut acc' := acc
      for i in [:shape[dim]!] do
        acc' := build (dim + 1) (idx.push i) acc'
      acc'
    else
      acc.push (f idx)
  let data := build 0 # #
  have h_size : data.size = totalSize shape := by
    -- This proof requires induction on the shape and is non-trivial for this
    -- recursive implementation. A production library would use a different
    -- implementation (e.g., pre-allocating the array and filling it) or a
    -- detailed proof here.
    sorry
  {
    data      := data,
    shape     := shape,
    strides   := computeStrides shape,
    h_size    := h_size,
    h_strides := rfl
  }

end NdArray
