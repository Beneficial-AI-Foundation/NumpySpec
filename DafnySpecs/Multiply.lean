/-
# NumPy Multiply Specification

Port of np_multiply.dfy to Lean 4
-/

namespace DafnySpecs.Multiply

/-- Element-wise multiplication of two vectors -/
def multiply {n : Nat} (a b : Vector Int n) : Vector Int n := Vector.zipWith Int.mul a b

/-- Specification: The result has the same length as inputs -/
theorem multiply_length {n : Nat} (a b : Vector Int n) :
  (multiply a b).size = n := rfl

/-- Specification: Each element is the product of corresponding input elements -/
theorem multiply_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (multiply a b)[i] = a[i] * b[i] := by
    intro i
    simp [multiply]

end DafnySpecs.Multiply
