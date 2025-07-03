import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns the element-wise square of the input vector -/
def square {n : Nat} (v : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: square returns a vector of the same size with squared elements -/
theorem square_spec {n : Nat} (v : Vector Int (n + 1)) :
    ⦃⌜True⌝⦄
    square v
    ⦃⇓ret => ∀ i : Fin (n + 1), ret.get i = v.get i * v.get i⦄ := by
  sorry