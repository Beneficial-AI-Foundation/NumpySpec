namespace LeanArrayLib

/-- Map an index type to a linear `Fin n`. -/
class IndexType (I : Type) (n : Nat) where
  toLinear : I → Fin n

instance {n} : IndexType (Fin n) n where
  toLinear := id

/-- Pair index instance (row‑major).  Uses `Fin.ofNat` so no manual
    proof obligations. -/
instance {m n} : IndexType (Fin m × Fin n) (m*n) where
  toLinear | (i,j) => Fin.ofNat (i.val * n + j.val)

end LeanArrayLib
