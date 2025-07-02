/-
# NumPy Greater Specification

Port of np_greater.dfy to Lean 4
-/

namespace DafnySpecs.Greater

/-- Element-wise greater-than comparison of two vectors -/
def greater {n : Nat} (a b : Vector Int n) : Vector Bool n := Vector.zipWith (· > ·) a b

/-- Specification: The result has the same length as inputs -/
theorem greater_length {n : Nat} (a b : Vector Int n) :
  (greater a b).size = n := rfl

/-- Specification: Each element is true iff first input element is greater than second -/
theorem greater_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (greater a b)[i] = (a[i] > b[i]) := by
    intro i
    simp [greater]

end DafnySpecs.Greater