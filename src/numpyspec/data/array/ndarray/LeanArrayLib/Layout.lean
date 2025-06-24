namespace LeanArrayLib

/-- `Layout` describes the memory layout of a multi-dimensional array.

    It stores:
    - `shape`: The dimensions of the array (e.g., [2, 3] for a 2×3 matrix)
    - `strides`: The number of elements to skip in memory for each dimension

    This allows efficient indexing into multi-dimensional arrays stored in linear memory.
-/
structure Layout where
  /-- The dimensions of the array (e.g., [2, 3] for a 2×3 matrix) -/
  shape   : Array Nat
  /-- The number of elements to skip in memory for each dimension -/
  strides : Array Nat
-- TODO: A/B instruct it to use imperative style when copying known impls
/-- Compute row-major strides for a given shape.

    In row-major order, the rightmost dimension has stride 1, and each dimension
    to the left has a stride equal to the product of all dimensions to its right.

    For example:
    - Shape [2, 3] produces strides [3, 1]
    - Shape [2, 3, 4] produces strides [12, 4, 1]
-/
@[inline] def computeStrides (shape : Array Nat) : Array Nat :=
  let (out, _) := shape.foldr (fun d (acc,p) => (acc.push p, p * d)) (#[], 1)
  out.reverse -- reverse to get the rightmost dimension first

#eval computeStrides #[2, 3] = #[3, 1]

/-- Create a row-major layout from a list of dimensions.

    Row-major order means that when iterating through the array linearly,
    the rightmost index changes fastest. This is the standard layout used
    in C, Python (NumPy), and many other languages.
-/
@[inline] def Layout.rowMajor (dims : List Nat) : Layout :=
  let shp := dims.toArray
  { shape := shp, strides := computeStrides shp }

end LeanArrayLib
