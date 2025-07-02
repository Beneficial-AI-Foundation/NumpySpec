import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns a copy of the given array -/
def copy (arr : Array Int) : Id (Array Int) :=
  sorry

/-- Specification: copy returns an array with the same length and elements -/
theorem copy_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    copy arr
    ⦃⇓ret => ∃ hr : ret.size = arr.size,
             ∀ i : Nat, ∀ hi : i < ret.size, ret[i]'hi = arr[i]'(hr ▸ hi)⦄ := by
  sorry