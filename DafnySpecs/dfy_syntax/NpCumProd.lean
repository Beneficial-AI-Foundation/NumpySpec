import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Computes the cumulative product of array elements -/
def cumProd (a : Array Int) : Id (Array Int) :=
  sorry

/-- Specification: cumProd returns an array with cumulative products -/
theorem cumProd_spec (a : Array Int) (h : a.size > 0) :
    ⦃⌜a.size > 0⌝⦄
    cumProd a
    ⦃⇓res => ∃ hr : res.size = a.size,
             (∃ h0 : 0 < res.size, res[0]'h0 = a[0]'h) ∧
             (∀ i (hi : 1 ≤ i) (hi2 : i < a.size), 
               ∃ hir : i < res.size, ∃ hir1 : i-1 < res.size,
               res[i]'hir = res[i-1]'hir1 * a[i]'hi2)⦄ := by
  sorry