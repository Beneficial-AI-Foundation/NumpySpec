import Lean
/-
# NumPy Abs Specification

Port of np_abs.dfy to Lean 4
-/


namespace DafnySpecs.Abs

/-- Absolute value of an integer -/
def absInt (x : Int) : Int := sorry

/-- Element-wise absolute value of a vector -/
def abs {n : Nat} (a : Vector Int n) : Vector Int n := sorry

/-- Specification: The result has the same length as input -/
theorem abs_length {n : Nat} (a : Vector Int n) :
  (abs a).size = n := sorry

/-- Specification: Each element is the absolute value of the corresponding input element -/
theorem abs_spec {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n, (abs a)[i] = absInt (a[i]) := sorry

/-- Specification: All elements in the result are non-negative -/
theorem abs_nonnegative {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n, 0 ≤ (abs a)[i] := sorry

end DafnySpecs.Abs
