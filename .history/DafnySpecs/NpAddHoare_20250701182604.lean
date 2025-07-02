import Std.Do
import Std.Do.Triple
import Std.Tactic.Do
import Std.Data.Array.Basic

open Std.Do

def arrayAdd (a b : Array Int) : StateM Unit (Array Int) := do
  return sorry   -- 仅规格，无实现

theorem arrayAdd_spec (a b : Array Int) :
  ⦃ spred (a.size = b.size) ⦄            -- 前置：长度相等
    arrayAdd a b
  ⦃ fun (res : Array Int) =>             -- 后置：用 spred
      spred (  res.size = a.size
            ∧ ∀ i : Nat, i < a.size →
                res.get! i = a.get! i + b.get! i) ⦄ := by
  sorry
