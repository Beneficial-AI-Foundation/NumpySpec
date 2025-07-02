import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Finds the maximum element in an array -/
def max (a : Array Int) : Id Int :=
  sorry

/-- Specification: max returns the maximum element from a non-empty array -/
theorem max_spec (a : Array Int) (h : a.size > 0) :
    ⦃⌜True⌝⦄
    max a
    ⦃⇓res => (∃ i (hi : i < a.size), res = a[i]'hi) ∧
             (∀ i (hi : i < a.size), a[i]'hi ≤ res)⦄ := by
  sorry