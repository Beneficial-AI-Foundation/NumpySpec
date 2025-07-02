import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Helper function to compute sum of array elements from start to endPos -/
def SumArray (a : Array Int) (start : Nat) (endPos : Nat) : Int :=
  sorry

/-- Computes the sum of all elements in an array -/
def sum (a : Array Int) : Id Int :=
  sorry

/-- Specification: sum returns the sum of all array elements -/
theorem sum_spec (a : Array Int) :
    ⦃⌜ae⌝⦄
    sum a
    ⦃⇓res => res = SumArray a 0 a.size⦄ := by
  sorry
