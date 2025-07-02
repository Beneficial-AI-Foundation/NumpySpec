/-
# NumPy Bitwise Or Specification

Port of np_bitwise_or.dfy to Lean 4
-/

namespace DafnySpecs.BitwiseOr

/-- Element-wise bitwise OR of two vectors -/
def bitwiseOr {n : Nat} (a b : Vector Nat n) : Vector Nat n := Vector.zipWith (· ||| ·) a b

/-- Specification: The result has the same length as inputs -/
theorem bitwiseOr_length {n : Nat} (a b : Vector Nat n) :
  (bitwiseOr a b).size = n := rfl

/-- Specification: Each element is the bitwise OR of corresponding input elements -/
theorem bitwiseOr_spec {n : Nat} (a b : Vector Nat n) :
  ∀ i : Fin n, (bitwiseOr a b)[i] = a[i] ||| b[i] := by
    intro i
    simp [bitwiseOr]

end DafnySpecs.BitwiseOr