import Std.Do.Triple

open Std.Do

def vectorAdd {n : Nat} (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  return sorry          -- 无实现

/-- Hoare-style 合约 -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  ⦃ spred(a.size = b.size) ⦄
    vectorAdd a b
  ⦃ fun (res : Vector Int n) (_ : Unit) =>
        ∀ i : Fin n, res.get i = a.get i + b.get i ⦄ := by
  sorry
