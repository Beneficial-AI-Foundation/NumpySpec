import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns evenly spaced values within a given interval -/
def arange (start stop step : Float) : Id (Array Float) :=
  sorry

/-- Specification: arange returns an array of evenly spaced values -/
theorem arange_spec (start stop step : Float) 
    (h1 : if step < 0.0 then start > stop else start < stop)
    (h2 : step ≠ 0.0) :
    ⦃⌜(if step < 0.0 then start > stop else start < stop) ∧ step ≠ 0.0⌝⦄
    arange start stop step
    ⦃⇓ret => ∃ hr1 : ret.size = ((stop - start)/step).floor.toUInt64.toNat, 
             ∃ hr2 : ret.size > 0,
             ∃ hr3 : ret[0]'(by simp [hr2]) = start,
             ∀ i (hi : 1 ≤ i) (hi2 : i < ret.size), 
               ret[i]'hi2 - ret[i-1]'(by omega) = step⦄ := by
  sorry