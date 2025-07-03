import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns a copy of the given vector -/
def copy {n : Nat} (v : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: copy returns a vector with the same length and elements -/
theorem copy_spec {n : Nat} (v : Vector Int n) :
    ⦃⌜True⌝⦄
    copy v
    ⦃⇓ret => ∀ i : Fin n, ret.get i = v.get i⦄ := by
  sorry