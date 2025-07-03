import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns the sign of each element in a vector -/
def sign {n : Nat} (a : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: sign returns a vector with -1, 0, or 1 based on element signs -/
theorem sign_spec {n : Nat} (a : Vector Int n) :
    ⦃⌜True⌝⦄
    sign a
    ⦃⇓res => ∀ i : Fin n, 
             (a.get i > 0 → res.get i = 1) ∧
             (a.get i = 0 → res.get i = 0) ∧
             (a.get i < 0 → res.get i = -1)⦄ := by
  sorry