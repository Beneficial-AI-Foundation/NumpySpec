/-
# NumPy Add Specification

Port of np_add.dfy to Lean 4
-/

namespace DafnySpecs.Add

/-- Element-wise addition of two vectors -/
def add {n : Nat} (a b : Vector Int n) : Vector Int n := Vector.zipWith Int.add a b

/-- Specification: The result has the same length as inputs -/
theorem add_length {n : Nat} (a b : Vector Int n) :
  (add a b).size = n := rfl

/-- Specification: Each element is the sum of corresponding input elements -/
theorem add_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (add a b)[i] = a[i] + b[i] := by
    simp [add]


end DafnySpecs.Add
