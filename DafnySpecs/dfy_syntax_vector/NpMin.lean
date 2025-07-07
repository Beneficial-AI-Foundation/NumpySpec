import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Finds the minimum element in a vector -/
def min {n : Nat} (a : Vector Int (n + 1)) : Id Int :=
  sorry

/-- Specification: min returns the minimum element from a non-empty vector -/
theorem min_spec {n : Nat} (a : Vector Int (n + 1)) :
    ⦃⌜True⌝⦄
    min a
    ⦃⇓res => ∃ i : Fin (n + 1), res = a.get i ∧
             ∀ j : Fin (n + 1), res ≤ a.get j⦄ := by
  sorry