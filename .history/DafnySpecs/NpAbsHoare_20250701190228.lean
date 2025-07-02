import Std.Do.Triple

open Std.Do         -- 带来 Triple／Assertion／PostCond 等名字

/-- **待实现**：长度为 `n` 的向量逐点相加。 -/
def vectorAdd {n : Nat} (a b : Vector Int n) :
    StateM Unit (Vector Int n) := do
  return sorry

/-- 恒真前置条件。 -/
def pre : Assertion _ := fun _ => True

/-- `vectorAdd` 的后置条件。 -/
def post {n : Nat} (a b : Vector Int n) :
    PostCond (Vector Int n) _ :=
  { pred := fun res _ =>
      ∀ i : Fin n, res.get i = a.get i + b.get i }

/-- Hoare-style 规格。 -/
theorem vectorAdd_spec {n : Nat} (a b : Vector Int n) :
  Triple (vectorAdd a b) pre (post a b) := by
  sorry
