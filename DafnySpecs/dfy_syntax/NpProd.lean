import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Helper function to compute product of array elements from start to endPos -/
def ProdArray (a : Array Int) (start : Nat) (endPos : Nat) : Int :=
  sorry

/-- Computes the product of all elements in an array -/
def prod (a : Array Int) : Id Int :=
  sorry

/-- Specification: prod returns the product of all array elements -/
theorem prod_spec (a : Array Int) :
    ⦃⌜a.size > 0⌝⦄
    prod a
    ⦃⇓res => res = ProdArray a 0 a.size⦄ := by
  sorry
