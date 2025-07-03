import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns evenly spaced values within a given interval as a vector of known size -/
def arange (n : Nat) (start stop step : Float) : Id (Vector Float n) :=
  sorry

/-- Specification: arange returns a vector of evenly spaced values -/
theorem arange_spec (n : Nat) (start stop step : Float) 
    (h1 : if step < 0.0 then start > stop else start < stop)
    (h2 : step ≠ 0.0)
    (h3 : n = ((stop - start)/step).floor.toUInt64.toNat) :
    ⦃⌜(if step < 0.0 then start > stop else start < stop) ∧ step ≠ 0.0 ∧ 
      n = ((stop - start)/step).floor.toUInt64.toNat⌝⦄
    arange n start stop step
    ⦃⇓ret => (∀ h0 : 0 < n, ret.get ⟨0, h0⟩ = start) ∧
             ∀ i : Nat, ∀ hi : i + 1 < n, 
               ret.get ⟨i + 1, hi⟩ - ret.get ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ = step⦄ := by
  sorry