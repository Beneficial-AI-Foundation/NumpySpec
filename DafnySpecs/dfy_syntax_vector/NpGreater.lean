import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Compares two vectors element-wise for greater than -/
def greater {n : Nat} (a b : Vector Int n) : Id (Vector Bool n) :=
  sorry

/-- Specification: greater returns a vector of booleans indicating element-wise comparison -/
theorem greater_spec {n : Nat} (a b : Vector Int n) :
    ⦃⌜True⌝⦄
    greater a b
    ⦃⇓res => ∀ i : Fin n, res.get i = (a.get i > b.get i)⦄ := by
  sorry