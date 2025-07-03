import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns the index of the maximum value in a vector (first occurrence) -/
def argmax {n : Nat} (arr : Vector Float n) (h : n > 0) : Id (Fin n) :=
  sorry

/-- Specification: argmax returns the index of the first maximum element -/
theorem argmax_spec {n : Nat} (arr : Vector Float n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    argmax arr h
    ⦃⇓ret => (∀ i : Fin n, i < ret → arr.get ret > arr.get i) ∧
             (∀ i : Fin n, ret < i → arr.get ret ≥ arr.get i)⦄ := by
  sorry