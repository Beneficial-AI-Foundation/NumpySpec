import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Multiplies two vectors element-wise -/
def multiply {n : Nat} (a b : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: multiply returns a vector of the same size with element-wise products -/
theorem multiply_spec {n : Nat} (a b : Vector Int n) :
    ⦃⌜True⌝⦄
    multiply a b
    ⦃⇓res => ∀ i : Fin n, res.get i = a.get i * b.get i⦄ := by
  sorry