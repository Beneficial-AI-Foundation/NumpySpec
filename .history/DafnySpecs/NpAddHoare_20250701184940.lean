import Std.Do               -- monad + notation
import Std.Do.Triple        -- Hoare-triple framework
import Std.Data.Vector      -- Vector API
import Std.Tactic.Do

open Std.Do

/-- Lift a plain `Prop` to an *Assertion* (state predicate). -/
def spred {σ} (p : Prop) : Assertion σ := fun _ => p

/-- *Specification only* (implementation will be supplied later). -/
def vectorAdd {n : Nat} (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  return sorry

/-- Hoare-style contract for `vectorAdd`. -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  ⦃ spred True ⦄
    vectorAdd a b
  ⦃ (⟨ fun (res : Vector Int n) (_ : Unit) =>
        ∀ i : Fin n,
          Vector.get res i = Vector.get a i + Vector.get b i ⟩) ⦄ := by
  sorry
