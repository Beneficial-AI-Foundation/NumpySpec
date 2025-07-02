import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Subtracts two arrays element-wise -/
def subtract (a b : Array Int) : Id (Array Int) :=
  sorry

/-- Specification: subtract returns an array of the same size with element-wise differences -/
theorem subtract_spec (a b : Array Int) (h : a.size = b.size) :
    ⦃⌜a.size = b.size⌝⦄
    subtract a b
    ⦃⇓res => ∃ hr : res.size = a.size, ∀ i (hi : i < res.size), res[i]'hi = a[i]'(hr ▸ hi) - b[i]'(h ▸ hr ▸ hi)⦄ := by
  sorry