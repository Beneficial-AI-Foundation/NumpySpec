import Std.Do
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

def vectorAdd {n : Nat} (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  -- A possible implementation:
  let mut res := Vector.replicate n 0
  for i in [:n] do
    res := res.set i (a.get i + b.get i)
  return res

/-- Hoare-style contract -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  -- The precondition now correctly has the type Unit → Prop.
  ⦃ fun (_ : Unit) => True ⦄
    vectorAdd a b
  ⦃ fun (res : Vector Int n) (_ : Unit) =>
        ∀ i : Fin n, res.get i = a.get i + b.get i ⦄ := by
  -- The proof would go here, for example:
  rw [vectorAdd]
  simp_all
  sorry -- Proof outline depends on the full implementation details and available lemmas.
