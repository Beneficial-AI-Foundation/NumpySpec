import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Element-wise modulo operation on two arrays -/
def mod (a b : Array Int) : Id (Array Int) :=
  sorry

/-- Specification: mod returns an array with element-wise modulo -/
theorem mod_spec (a b : Array Int) 
    (h_size : a.size = b.size)
    (h_nonzero : ∀ i (hi : i < b.size), b[i] ≠ 0) :
    ⦃⌜a.size = b.size ∧ ∀ i (hi : i < b.size), b[i] ≠ 0⌝⦄
    mod a b
    ⦃⇓r => ∃ (hr : r.size = a.size), 
           ∀ i (hi : i < a.size), r[i]'(hr ▸ hi) = a[i] % b[i]'(h_size ▸ hi)⦄ := by
  sorry