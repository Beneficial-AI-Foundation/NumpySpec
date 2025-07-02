import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Finds the maximum element in an array -/
def max (a : Array Int) : Id Int :=
  sorry

/-- Specification: max returns the maximum element from a non-empty array -/
theorem max_spec (a : Array Int) (h : a.size > 0) :
    ⦃⌜a.size > 0⌝⦄
    max a
    ⦃⇓res => ∃ i : Nat, ∃ hi : i < a.size, res = a[i]'hi ∧
             ∀ j : Nat, ∀ hj : j < a.size, a[j]'hj ≤ res⦄ := by
  sorry
