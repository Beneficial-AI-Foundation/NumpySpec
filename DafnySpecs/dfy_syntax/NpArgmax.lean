import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns the index of the maximum value in an array (first occurrence) -/
def argmax (arr : Array Float) : Id Nat :=
  sorry

/-- Specification: argmax returns the index of the first maximum element -/
theorem argmax_spec (arr : Array Float) (h : arr.size > 0) :
    ⦃⌜arr.size > 0⌝⦄
    argmax arr
    ⦃⇓ret => ∃ hr : ret < arr.size,
             (∀ i (hi : i < ret), arr[ret]'hr > arr[i]'(by omega)) ∧
             (∀ i, ret < i → ∀ hi : i < arr.size, arr[ret]'hr ≥ arr[i]'hi)⦄ := by
  sorry