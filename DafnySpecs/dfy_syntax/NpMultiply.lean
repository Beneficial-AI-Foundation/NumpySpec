import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Multiplies two arrays element-wise -/
def multiply (a b : Array Int) : Id (Array Int) :=
  sorry

/-- Specification: multiply returns an array of the same size with element-wise products -/
theorem multiply_spec (a b : Array Int) (h : a.size = b.size) :
    ⦃⌜True⌝⦄
    multiply a b
    ⦃⇓res => ∃ hr : res.size = a.size, ∀ i (hi : i < res.size), res[i]'hi = a[i]'(hr ▸ hi) * b[i]'(h ▸ hr ▸ hi)⦄ := by
  sorry