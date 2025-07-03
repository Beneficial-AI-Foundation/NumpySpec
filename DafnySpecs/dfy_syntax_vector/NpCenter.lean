import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Centers each string in a vector within a string of specified width -/
def center {n : Nat} (input : Vector String n) (width : Nat) : Id (Vector String n) :=
  sorry

/-- Specification: center returns a vector with centered strings -/
theorem center_spec {n : Nat} (input : Vector String n) (width : Nat) 
    (h : ∀ i : Fin n, (input.get i).length ≥ 1) :
    ⦃⌜∀ i : Fin n, (input.get i).length ≥ 1⌝⦄
    center input width
    ⦃⇓r => ∀ i : Fin n, 
           if (input.get i).length > width then 
             (r.get i).length = (input.get i).length 
           else 
             (r.get i).length = width⦄ := by
  sorry