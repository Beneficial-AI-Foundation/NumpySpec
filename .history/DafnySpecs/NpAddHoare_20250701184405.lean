import Std.Do
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- *Specification only* (no implementation yet). -/
def vectorAdd {n : Nat} (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  return sorry

/-- Hoare-style contract for `vectorAdd`. -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  ⦃ spred(fun _ : Unit => True) ⦄ vectorAdd a b ⦃ fun (res : Vector Int n) (_ : Unit) =>
        spred(∀ i : Fin n, res.get i = a.get i + b.get i) ⦄ := by
  sorry
