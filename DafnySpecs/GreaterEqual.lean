/-
# NumPy Greater Equal Specification

Port of np_greater_equal.dfy to Lean 4
-/

namespace DafnySpecs.GreaterEqual

/-- Element-wise greater than or equal comparison of two vectors -/
def greaterEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := Vector.zipWith (· ≥ ·) a b

/-- Specification: The result has the same length as inputs -/
theorem greaterEqual_length {n : Nat} (a b : Vector Int n) :
  (greaterEqual a b).size = n := rfl

/-- Specification: Each element is true iff corresponding element in a is >= element in b -/
theorem greaterEqual_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (greaterEqual a b)[i] = (a[i] ≥ b[i]) := by
    simp [greaterEqual]

end DafnySpecs.GreaterEqual
