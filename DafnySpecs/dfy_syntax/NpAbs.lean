import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Helper function for absolute value -/
def AbsInt (x : Int) : Int := if x < 0 then -x else x

/-- Computes the absolute value of each element in an array -/
def abs (a : Array Int) : Id (Array Int) :=
  sorry

/-- Specification: abs returns an array of the same size with absolute values -/
theorem abs_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    abs a
    ⦃⇓res => ∃ hr : res.size = a.size, 
             (∀ i (hi : i < res.size), res[i] = AbsInt (a[i]'(hr ▸ hi))) ∧
             (∀ i (hi : i < res.size), res[i] ≥ 0)⦄ := by
  sorry