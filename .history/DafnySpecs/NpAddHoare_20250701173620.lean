import Std.Do
import Std.Tactic.Do
import Std.Do.Triple
open Std.Do

/--
  *Specification only* (no implementation) for element-wise addition on
  `Array Int`.

  **Pre-condition** `a.size = b.size` – the two input arrays must agree in
  length.

  **Post-condition** `res.size = a.size ∧
                      ∀ i < a.size, res[i] = a[i] + b[i]`.

  The function body is left as `sorry`; only the contract matters here.
-/
def arrayAdd (a b : Array Int) : StateM Unit (Array Int) := do
  return sorry   -- ← implementation deliberately omitted

/-- Hoare-style contract for `arrayAdd`. -/
theorem arrayAdd_spec (a b : Array Int) :
  ⦃ spred (a.size = b.size) ⦄          -- pre
    arrayAdd a b
  ⦃ fun res => spred                   -- post
      (res.size = a.size ∧
       ∀ i : Nat, i < a.size →
         res.get! i = a.get! i + b.get! i) ⦄ := by
  sorry                                 -- proof placeholde
