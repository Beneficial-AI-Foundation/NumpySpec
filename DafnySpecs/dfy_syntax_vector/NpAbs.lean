import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Helper function for absolute value -/
def AbsInt (x : Int) : Int := if x < 0 then -x else x

/-- Computes the absolute value of each element in a vector -/
def abs {n : Nat} (v : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: abs returns a vector of the same size with absolute values -/
theorem abs_spec {n : Nat} (v : Vector Int (n + 1)) :
    ⦃⌜True⌝⦄
    abs v
    ⦃⇓res => (∀ i : Fin (n + 1), res.get i = AbsInt (v.get i)) ∧
             (∀ i : Fin (n + 1), res.get i ≥ 0)⦄ := by
  sorry