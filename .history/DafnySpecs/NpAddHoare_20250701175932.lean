import Std.Tactic.Do


open Std.Do

/--
  *Specification only* (no implementation) for element-wise addition on
  `Array Int`.

  **Pre-condition** `a.size = b.size`

  **Post-condition** `res.size = a.size ∧
                      ∀ i < a.size, res[i] = a[i] + b[i]`.
-/
def arrayAdd (a b : Array Int) : StateM Unit (Array Int) := do
  return sorry   -- implementation intentionally omitted

/-- Hoare-style contract for `arrayAdd`. -/
theorem arrayAdd_spec (a b : Array Int) :
  ⦃ spred(a.size = b.size) ⦄
    arrayAdd a b
  ⦃ fun (res : Array Int) =>
     res.size = a.size ∧ ∀ i : Fin (a.size), a.size → spred(res[i] = a[i]! + b[i]!)))) ⦄ := by
  sorry   -- proof placeholder
