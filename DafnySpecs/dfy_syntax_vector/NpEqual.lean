import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Compares two vectors element-wise for equality -/
def equal {n : Nat} (a b : Vector Int n) : Id (Vector Bool n) :=
  sorry

/-- Specification: equal returns a vector of booleans indicating element-wise equality -/
theorem equal_spec {n : Nat} (a b : Vector Int n) :
    ⦃⌜True⌝⦄
    equal a b
    ⦃⇓res => ∀ i : Fin n, res.get i = (a.get i = b.get i)⦄ := by
  sorry