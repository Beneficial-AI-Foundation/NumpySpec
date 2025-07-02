import Std.Do               -- monad + notation
import Std.Do.Triple        -- Hoare-triple framework
import Std.Tactic.Do

open Std.Do

/-- *Specification only* (implementation will be added later). -/
def vectorAdd {n : Nat}
    (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  return sorry                  -- ← algorithm goes here

/-- Hoare-style contract for `vectorAdd`. -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  ⦃ (fun _ : Unit => True) ⦄                    -- pre-condition
    vectorAdd a b
  ⦃ (fun (res : Vector Int n) (_ : Unit) =>     -- post-condition
        ∀ i : Fin n,
          Vector.get res i = Vector.get a i + Vector.get b i) ⦄ := by
  sorry      
