import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Element-wise floor division on two arrays -/
def floorDivide (a b : Array Int) : Id (Array Int) :=
  sorry

/-- Specification: floorDivide returns an array with element-wise integer division -/
theorem floorDivide_spec (a b : Array Int) 
    (h_size : a.size = b.size)
    (h_nonzero : ∀ i (hi : i < b.size), b[i] ≠ 0) :
    ⦃⌜a.size = b.size ∧ ∀ i (hi : i < b.size), b[i] ≠ 0⌝⦄
    floorDivide a b
    ⦃⇓r => ∃ hr : r.size = a.size,
           ∀ i (hi : i < r.size), r[i]'hi = a[i]'(hr ▸ hi) / b[i]'(h_size ▸ hr ▸ hi)⦄ := by
  sorry