import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Element-wise floor division on two vectors -/
def floorDivide {n : Nat} (a b : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: floorDivide returns a vector with element-wise integer division -/
theorem floorDivide_spec {n : Nat} (a b : Vector Int n) 
    (h_nonzero : ∀ i : Fin n, b.get i ≠ 0) :
    ⦃⌜∀ i : Fin n, b.get i ≠ 0⌝⦄
    floorDivide a b
    ⦃⇓r => ∀ i : Fin n, r.get i = a.get i / b.get i⦄ := by
  sorry