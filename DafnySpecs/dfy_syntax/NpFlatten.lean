import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Flattens a 2D array into a 1D array -/
def flatten2 (mat : Array (Array Int)) : Id (Array Int) :=
  sorry

/-- Specification: flatten2 returns a 1D array with all elements from the 2D array -/
theorem flatten2_spec (mat : Array (Array Int)) 
    (h1 : mat.size > 0) 
    (h2 : ∀ i (hi : i < mat.size), (mat[i]'hi).size > 0)
    (h3 : ∀ i j (hi : i < mat.size) (hj : j < mat.size), (mat[i]'hi).size = (mat[j]'hj).size) :
    ⦃⌜mat.size > 0 ∧ (∀ i (hi : i < mat.size), (mat[i]'hi).size > 0) ∧ 
      (∀ i j (hi : i < mat.size) (hj : j < mat.size), (mat[i]'hi).size = (mat[j]'hj).size)⌝⦄
    flatten2 mat
    ⦃⇓ret => ∃ cols : Nat, ∃ h0 : 0 < mat.size, ∃ hcols : cols = (mat[0]'h0).size,
             ∃ hr : ret.size = mat.size * cols,
             ∀ i j (hi : i < mat.size) (hj : j < cols), 
               ∃ hidx : i * cols + j < ret.size,
               ∃ hjcols : j < (mat[i]'hi).size,
               ret[i * cols + j]'hidx = (mat[i]'hi)[j]'hjcols⦄ := by
  sorry