import Std.Do
import Std.Tactic.Do
import Std.Do.Triple

/-- *Specification only* (implementation to be supplied later). -/
def vectorAdd {n : Nat} (a b : Vector Int n) :
    StateM Unit (Vector Int n) := do
  return sorry                           -- algorithm comes here

/-- Hoare-style contract for `vectorAdd`. -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  ⦃ fun _ : Unit => True) ⦄                -- Assertion `Unit → Prop`
    vectorAdd a b
  ⦃ (PostCond.mk                          -- wrap the λ in `PostCond`
        (fun (res : Vector Int n)
             (_ : PostShape.arg Unit PostShape.pure) =>
           ∀ i : Fin n,
             res.get i = a.get i + b.get i)) ⦄ := by
  sorry
