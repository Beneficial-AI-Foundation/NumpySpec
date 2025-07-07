import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Finds the maximum element in a vector -/
def max {n : Nat} (a : Vector Int (n + 1)) : Id Int :=
  sorry

/-- Specification: max returns the maximum element from a non-empty vector -/
theorem max_spec {n : Nat} (a : Vector Int (n + 1)) :
    ⦃⌜True⌝⦄
    max a
    ⦃⇓res => ∃ i : Fin (n + 1), res = a.get i ∧
             ∀ j : Fin (n + 1), a.get j ≤ res⦄ := by
  sorry