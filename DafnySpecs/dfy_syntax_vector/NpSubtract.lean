import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Subtracts two vectors element-wise -/
def subtract {n : Nat} (a b : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: subtract returns a vector of the same size with element-wise differences -/
theorem subtract_spec {n : Nat} (a b : Vector Int n) :
    ⦃⌜True⌝⦄
    subtract a b
    ⦃⇓res => ∀ i : Fin n, res.get i = a.get i - b.get i⦄ := by
  sorry