import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Finds the minimum element in an array -/
def min (a : Array Int) : Id Int :=
  sorry

/-- Specification: min returns the minimum element from a non-empty array -/
theorem min_spec (a : Array Int) (h : a.size > 0) :
    ⦃⌜True⌝⦄
    min a
    ⦃⇓res => ∃ i : Nat, ∃ hi : i < a.size, res = a[i]'hi ∧
             ∀ j : Nat, ∀ hj : j < a.size, res ≤ a[j]'hj⦄ := by
  sorry