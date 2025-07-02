import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Adds two arrays element-wise -/
def add (a b : Array Int): Id (Array Int) :=
  sorry

/-- Specification: add returns an array of the same size with element-wise sums -/
theorem add_spec (a b : Array Int) (h : a.size = b.size) :
    ⦃⌜True⌝⦄
    add a b
    ⦃⌜⇓r => ∃ hr : r.size = a.size, ∀ i (hi : i < r.size), r[i] = a[i] + b[i]⦄ := by
  sorry
