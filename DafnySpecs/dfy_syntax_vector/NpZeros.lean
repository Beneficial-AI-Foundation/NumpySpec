import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Creates a vector of zeros with the given size -/
def zeros (n : Nat) : Id (Vector Int n) :=
  sorry

/-- Specification: zeros returns a vector of zeros with the specified size -/
theorem zeros_spec (n : Nat) :
    ⦃⌜True⌝⦄
    zeros n
    ⦃⇓ret => ∀ i : Fin n, ret.get i = 0⦄ := by
  sorry