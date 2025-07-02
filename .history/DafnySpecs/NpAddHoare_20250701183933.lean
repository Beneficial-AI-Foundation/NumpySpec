import Std.Do
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- *Specification only* (no implementation) -/
def vectorAdd {n : Nat} (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  return sorry      -- implementation goes here later

/-- Hoare-style contract for `vectorAdd`. -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  ⦃ spred(True) ⦄                     -- or:  ⦃ fun _ : Unit => True ⦄
    vectorAdd a b
  ⦃ fun res _ =>                     -- post-condition
        ∀ i : Fin n, res[i]! = a.get i + b.get i ⦄ := by
  sorry                               -- proof to be filled in
