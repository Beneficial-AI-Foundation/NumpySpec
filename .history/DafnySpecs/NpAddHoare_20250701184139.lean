import Std.Do               -- monad + notation
import Std.Do.Triple        -- Hoare-triple framework
import Std.Tactic.Do

open Std.Do

/-- Lift a propositional predicate to a state predicate. -/
def spred {σ} (p : Prop) : σ → Prop := fun _ ⇒ p

/-- *Specification only* (no implementation yet). -/
def vectorAdd {n : Nat} (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  return sorry

/-- Hoare-style contract for `vectorAdd`. -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  ⦃ spred True ⦄                                    -- pre-condition
    vectorAdd a b
  ⦃ fun (res : Vector Int n) =>                    -- post-condition
        ∀ i : Fin n, Vector.get res i =
                   Vector.get a   i + Vector.get b i ⦄ := by
  sorry
