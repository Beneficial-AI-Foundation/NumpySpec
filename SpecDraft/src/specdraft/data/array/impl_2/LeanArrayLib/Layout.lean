namespace LeanArrayLib

structure Layout where
  shape   : Array Nat
  strides : Array Nat

/-- Compute row‑major strides (rightmost dim stride = 1). -/
@[inline] def computeStrides (shape : Array Nat) : Array Nat :=
  let (out, _) := shape.foldr (fun d (acc,p) => (p :: acc, p * d)) ([], 1)
  out.toArray

@[inline] def Layout.rowMajor (dims : List Nat) : Layout :=
  let shp := dims.toArray
  { shape := shp, strides := computeStrides shp }

end LeanArrayLib
