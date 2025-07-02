import Std.Do.Triple

open Std.Do
set_option diagnostics true

def vectorAdd {n : Nat} (a b : Vector Int n) : Id (Vector Int n) :=
  pure sorry          -- 无实现

/-- Hoare-style 合约 -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  ⦃ fun _ : Vector Int n => a.size = b.size ⦄
    vectorAdd a b
  ⦃ fun (res : Vector Int n) (_ : Unit) =>
        ∀ i : Fin n, res.get i = a.get i + b.get i ⦄ := by
  sorry
