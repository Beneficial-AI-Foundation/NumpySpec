import Std.Do
import Std.Tactic.Do
import Std.Do.Triple

/-- Trivial pre-condition: the state (here a `Unit`) can be anything. -/
def pre : Assertion Unit := fun _ => True

/-- Post-condition for `vectorAdd`. -/
def post {n : Nat} (a b : Vector Int n) :
    PostCond (Vector Int n) _ :=
  PostCond.mk
    (fun (res : Vector Int n) _ =>
        ∀ i : Fin n, res.get i = a.get i + b.get i)

/-! ### Code to be verified -/

/-- *Specification only* for element-wise addition on fixed-length vectors. -/
def vectorAdd {n : Nat}
    (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  return sorry                               -- implementation goes here

/-- Hoare-style contract for `vectorAdd`. -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
    Triple (vectorAdd a b) (pre) (post a b) := by
  sorry
