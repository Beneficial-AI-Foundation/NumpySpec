/-
# NumPy Right Shift Specification

Port of np_right_shift.dfy to Lean 4
-/

namespace DafnySpecs.RightShift

/-- Right shift operation for integers (arithmetic shift) -/
def shiftRightInt (x : Int) (n : Nat) : Int :=
  if x ≥ 0 then
    Int.ofNat (x.natAbs >>> n)
  else
    -(Int.ofNat (((-x).natAbs - 1) >>> n + 1))

/-- Element-wise right shift of integers by natural numbers -/
def rightShift {n : Nat} (a : Vector Int n) (b : Vector Nat n) : Vector Int n :=
  Vector.zipWith shiftRightInt a b

/-- Specification: The result has the same length as inputs -/
theorem rightShift_length {n : Nat} (a : Vector Int n) (b : Vector Nat n) :
  (rightShift a b).size = n := rfl

/-- Specification: Each element is the right shift of corresponding input elements -/
theorem rightShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n)
  :
  ∀ i : Fin n, (rightShift a b)[i] = shiftRightInt (a[i]) (b[i]) := by
    intro i
    simp [rightShift]

end DafnySpecs.RightShift
