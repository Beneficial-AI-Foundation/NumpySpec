/-
# NumPy Equal Specification

Port of np_equal.dfy to Lean 4
-/

namespace DafnySpecs.Equal

/-- Element-wise equality comparison of two vectors -/
def equal {n : Nat} (a b : Vector Int n) : Vector Bool n := Vector.zipWith (· = ·) a b

/-- Specification: The result has the same length as inputs -/
theorem equal_length {n : Nat} (a b : Vector Int n) :
  (equal a b).size = n := rfl

/-- Specification: Each element is true iff corresponding input elements are equal -/
theorem equal_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (equal a b)[i] = (a[i] = b[i]) := by
    intro i
    simp [equal]

end DafnySpecs.Equal