import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns the sign of each element in an array -/
def sign (a : Array Int) : Id (Array Int) :=
  sorry

/-- Specification: sign returns an array with -1, 0, or 1 based on element signs -/
theorem sign_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    sign a
    ⦃⇓res => ∃ hr : res.size = a.size, 
             ∀ i (hi : i < res.size), 
               (a[i]'(hr ▸ hi) > 0 → res[i]'hi = 1) ∧
               (a[i]'(hr ▸ hi) = 0 → res[i]'hi = 0) ∧
               (a[i]'(hr ▸ hi) < 0 → res[i]'hi = -1)⦄ := by
  sorry