import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Creates a 2D array of zeros with the given shape -/
def zeros (shape : Array Nat) : Id (Array Int) :=
  sorry

/-- Specification: zeros returns an array of zeros with the specified dimensions -/
theorem zeros_spec (shape : Array Nat) (h1 : shape.size = 2) (h2 : shape[0]'(by simp [h1]) > 0) (h3 : shape[1]'(by simp [h1]) > 0) :
    ⦃⌜shape.size = 2 ∧ shape[0]'(by simp [h1]) > 0 ∧ shape[1]'(by simp [h1]) > 0⌝⦄
    zeros shape
    ⦃⇓ret => ∃ hr : ret.size = shape[0]'(by simp [h1]) * shape[1]'(by simp [h1]),
             ∀ i : Nat, ∀ hi : i < ret.size, ret[i]'hi = 0⦄ := by
  sorry