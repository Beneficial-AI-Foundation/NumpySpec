import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Computes the cumulative product of vector elements -/
def cumProd {n : Nat} (a : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: cumProd returns a vector with cumulative products -/
theorem cumProd_spec {n : Nat} (a : Vector Int n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    cumProd a
    ⦃⇓res => (res.get ⟨0, h⟩ = a.get ⟨0, h⟩) ∧
             (∀ i : Nat, ∀ hi : i + 1 < n, 
               res.get ⟨i + 1, hi⟩ = res.get ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ * 
                                      a.get ⟨i + 1, hi⟩)⦄ := by
  sorry