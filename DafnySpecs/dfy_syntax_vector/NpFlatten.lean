import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Flattens a 2D vector (represented as Vector of Vectors) into a 1D vector -/
def flatten2 {rows cols : Nat} (mat : Vector (Vector Int cols) rows) : Id (Vector Int (rows * cols)) :=
  sorry

/-- Specification: flatten2 returns a 1D vector with all elements from the 2D vector in row-major order -/
theorem flatten2_spec {rows cols : Nat} (mat : Vector (Vector Int cols) rows) 
    (h1 : rows > 0) 
    (h2 : cols > 0) :
    ⦃⌜rows > 0 ∧ cols > 0⌝⦄
    flatten2 mat
    ⦃⇓ret => ∀ (i : Fin rows) (j : Fin cols), 
             ∃ (idx : Fin (rows * cols)) (hidx : idx.val = i.val * cols + j.val),
             ret.get idx = (mat.get i).get j⦄ := by
  sorry