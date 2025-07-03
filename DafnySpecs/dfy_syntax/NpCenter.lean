import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Centers each string in an array within a string of specified width -/
def center (input : Array String) (width : Nat) : Id (Array String) :=
  sorry

/-- Specification: center returns an array with centered strings -/
theorem center_spec (input : Array String) (width : Nat) 
    (h : ∀ i (hi : i < input.size), (input[i]'hi).length ≥ 1) :
    ⦃⌜∀ i (hi : i < input.size), (input[i]'hi).length ≥ 1⌝⦄
    center input width
    ⦃⇓res => ∃ hr1 : res.size = input.size,
             ∀ i (hi : i < input.size), 
               if (input[i]'hi).length > width then 
                 (res[i]'(hr1 ▸ hi)).length = (input[i]'hi).length 
               else 
                 (res[i]'(hr1 ▸ hi)).length = width⦄ := by
  sorry