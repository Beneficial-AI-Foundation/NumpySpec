import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Adds two vectors element-wise -/
def add {n : Nat} (a b : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: add returns a vector with element-wise sums -/
theorem add_spec {n : Nat} (a b : Vector Int n) :
    ⦃⌜True⌝⦄
    add a b
    ⦃⇓r => ∀ i : Fin n, r.get i = a.get i + b.get i⦄ := by
  sorry