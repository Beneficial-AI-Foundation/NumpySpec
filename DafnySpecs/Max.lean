/-
# NumPy Max Specification

Port of np_max.dfy to Lean 4
-/

namespace DafnySpecs.Max

/-- Find the maximum element in a non-empty vector -/
def max' {n : Nat} (h : 0 < n) (a : Vector Int n) : Int :=
  a.foldl Max.max a[0]

/-- Specification: The maximum exists in the vector -/
theorem max_exists {n : Nat} (h : 0 < n) (a : Vector Int n) :
  ∃ i : Fin n, max' h a = a[i] := by
  use 0, h
  simp [max']
  sorry -- This requires induction on the fold

/-- Specification: The maximum is greater than or equal to all elements -/
theorem max_spec {n : Nat} (h : 0 < n) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ max' h a := by
  intro i
  simp [max']
  sorry -- This requires properties of fold and max

end DafnySpecs.Max
