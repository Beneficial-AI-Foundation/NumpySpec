/-
# NumPy Floor Divide Specification

Port of np_floor_divide.dfy to Lean 4
-/

namespace DafnySpecs.FloorDivide

/-- Type constraint ensuring all elements are non-zero -/
abbrev NonZeroIntVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }

/-- Element-wise floor division of two vectors -/
def floorDivide {n : Nat} (a : Vector Int n) (b : NonZeroIntVector n) : Vector Int n :=
  Vector.zipWith (· / ·) a b.val

/-- Specification: The result has the same length as inputs -/
theorem floorDivide_length {n : Nat} (a : Vector Int n) (b : NonZeroIntVector n) :
  (floorDivide a b).size = n := rfl

/-- Specification: Each element is the floor division of corresponding input elements -/
theorem floorDivide_spec {n : Nat} (a : Vector Int n) (b : NonZeroIntVector n) :
  ∀ i : Fin n, (floorDivide a b)[i] = a[i] / (b.val[i]) := by
    simp [floorDivide]

end DafnySpecs.FloorDivide
