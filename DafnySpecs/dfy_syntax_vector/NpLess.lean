import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Compares two vectors element-wise for less than -/
def less {n : Nat} (a b : Vector Int n) : Id (Vector Bool n) :=
  sorry

/-- Specification: less returns a vector of booleans indicating element-wise comparison -/
theorem less_spec {n : Nat} (a b : Vector Int n) :
    ⦃⌜True⌝⦄
    less a b
    ⦃⇓res => ∀ i : Fin n, res.get i = (a.get i < b.get i)⦄ := by
  sorry