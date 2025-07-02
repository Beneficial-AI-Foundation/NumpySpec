/-
# NumPy Left Shift Specification

Port of np_left_shift.dfy to Lean 4
-/

namespace DafnySpecs.LeftShift

/-- Left shift operation for integers -/
def shiftLeftInt (x : Int) (n : Nat) : Int := sorry

/-- Element-wise left shift of integers by natural numbers -/
def leftShift {n : Nat} (a : Vector Int n) (b : Vector Nat n)
  : Vector Int n := sorry

/-- Specification: The result has the same length as inputs -/
theorem leftShift_length {n : Nat} (a : Vector Int n) (b : Vector Nat n)
  :
  (leftShift a b).size = n := sorry

/-- Specification: Each element is the left shift of corresponding input elements -/
theorem leftShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n)
  :
  ∀ i : Fin n, (leftShift a b)[i] = shiftLeftInt (a[i]) (b[i]) := sorry

end DafnySpecs.LeftShift
