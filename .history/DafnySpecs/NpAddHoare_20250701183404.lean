import Std.Do
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

def vectorAdd {n : Nat} (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  return sorry     -- 没有实现

/-- Hoare-style 合约 -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  ⦃ spred(True) ⦄              -- 前置条件：长度在类型里已保证，不必再写
    vectorAdd a b
  ⦃ fun (res : Vector Int n) =>
     spred(∀ i : Fin n, res.get i = a.get i + b.get i) ⦄ := by
  sorry
