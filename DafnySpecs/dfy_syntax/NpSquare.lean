import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns the element-wise square of the input array -/
def square (arr : Array Int) : Id (Array Int) :=
  sorry

/-- Specification: square returns an array of the same size with squared elements -/
theorem square_spec (arr : Array Int) :
    ⦃⌜arr.size > 0⌝⦄
    square arr
    ⦃⇓ret => ∃ hr : ret.size = arr.size,
             ∀ i : Nat, ∀ hi : i < ret.size, ret[i]'hi = arr[i]'(hr ▸ hi) * arr[i]'(hr ▸ hi)⦄ := by
  sorry
