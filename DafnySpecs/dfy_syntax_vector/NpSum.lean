import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Helper function to compute sum of vector elements from start to endPos -/
def SumVector {n : Nat} (v : Vector Int n) (start : Nat) (endPos : Nat) : Int :=
  sorry

/-- Computes the sum of all elements in a vector -/
def sum {n : Nat} (v : Vector Int n) : Id Int :=
  sorry

/-- Specification: sum returns the sum of all vector elements -/
theorem sum_spec {n : Nat} (v : Vector Int (n + 1)) :
    ⦃⌜True⌝⦄
    sum v
    ⦃⇓res => res = SumVector v 0 (n + 1)⦄ := by
  sorry