import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Compares two arrays element-wise for less than -/
def less (a b : Array Int) : Id (Array Bool) :=
  sorry

/-- Specification: less returns an array of booleans indicating element-wise comparison -/
theorem less_spec (a b : Array Int) (h : a.size = b.size) :
    ⦃⌜a.size = b.size⌝⦄
    less a b
    ⦃⇓res => ∃ hr : res.size = a.size, ∀ i (hi : i < res.size), res[i]'hi = (a[i]'(hr ▸ hi) < b[i]'(h ▸ hr ▸ hi))⦄ := by
  sorry