/-
# NumPy Less Specification

Port of np_less.dfy to Lean 4
-/

namespace DafnySpecs.Less

/-- Element-wise less-than comparison of two vectors -/
def less {n : Nat} (a b : Vector Int n) : Vector Bool n := Vector.zipWith (· < ·) a b

/-- Specification: The result has the same length as inputs -/
theorem less_length {n : Nat} (a b : Vector Int n) :
  (less a b).size = n := rfl

/-- Specification: Each element is true iff first input element is less than second -/
theorem less_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (less a b)[i] = (a[i] < b[i]) := by
    intro i
    simp [less]

end DafnySpecs.Less