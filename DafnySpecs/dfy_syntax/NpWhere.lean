import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Return elements chosen from x or y depending on condition -/
def «where» (condition : Int → Bool) (arr : Array Int) (change : Int → Int) : Id (Array Int) :=
  sorry

/-- Specification: where returns an array of the same size with elements conditionally changed -/
theorem where_spec (condition : Int → Bool) (arr : Array Int) (change : Int → Int) 
    (h : arr.size > 0) :
    ⦃⌜arr.size > 0⌝⦄
    «where» condition arr change
    ⦃⇓r => ∃ (hr : r.size = arr.size), 
           ∀ i (hi : i < arr.size), 
             r[i]'(hr ▸ hi) = if condition arr[i] then change arr[i] else arr[i]⦄ := by
  sorry