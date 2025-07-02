/-
# NumPy Bitwise And Specification

Port of np_bitwise_and.dfy to Lean 4
-/

namespace DafnySpecs.BitwiseAnd

/-- Element-wise bitwise AND of two vectors -/
def bitwiseAnd {n : Nat} (a b : Vector Nat n) : Vector Nat n := Vector.zipWith (· &&& ·) a b

/-- Specification: The result has the same length as inputs -/
theorem bitwiseAnd_length {n : Nat} (a b : Vector Nat n) :
  (bitwiseAnd a b).size = n := rfl

/-- Specification: Each element is the bitwise AND of corresponding input elements -/
theorem bitwiseAnd_spec {n : Nat} (a b : Vector Nat n) :
  ∀ i : Fin n, (bitwiseAnd a b)[i] = a[i] &&& b[i] := by
    intro i
    simp [bitwiseAnd]

end DafnySpecs.BitwiseAnd
