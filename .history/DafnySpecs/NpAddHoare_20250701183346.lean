import Std.Do
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

def vectorAdd {n : Nat} (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  return sorry     -- 没有实现

/-- Hoare-style 合约 -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  ⦃ spred True ⦄              -- 前置条件：长度在类型里已保证，不必再写
    vectorAdd a b
  ⦃ fun (res : Vector Int n) (_ : Unit) =>   -- “显式 λ” 生成 SPred
        ∀ i : Fin n,                         -- 只要能索引 0 ≤ i < n
          res.get i = a.get i + b.get i ⦄ := by
  sorry
