import Std.Do
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

def vectorAdd (a b : Vector Int n) : StateM Unit (Vector Int n) := do
  return sorry   -- 仅规格，无实现

theorem vectorAdd_spec (a b : Vector Int n) :
  ⦃ spred(a.size = b.size) ⦄            -- 前置：长度相等
    vectorAdd a b
  ⦃ fun (res : Array Int) =>             -- 后置：用 spred
      spred(  res.size = a.size
            ∧ ∀ i : Nat, i < a.size →
                res.get! i = a.get! i + b.get! i) ⦄ := by
  sorry
