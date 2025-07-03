import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- 2D array type -/
structure Array2 (α : Type) where
  /-- The underlying 1D array storing elements in row-major order -/
  data : Array α
  /-- Number of rows -/
  rows : Nat
  /-- Number of columns -/
  cols : Nat
  /-- Invariant: data size equals rows * cols -/
  h_size : data.size = rows * cols

/-- Get element at position (i, j) in a 2D array -/
def Array2.get (arr : Array2 α) (i j : Nat) (hi : i < arr.rows) (hj : j < arr.cols) : α :=
  arr.data[i * arr.cols + j]'(by
    rw [arr.h_size]
    have h1 : i * arr.cols + j < i * arr.cols + arr.cols := Nat.add_lt_add_left hj _
    have h2 : i * arr.cols + arr.cols = (i + 1) * arr.cols := by 
      rw [←Nat.succ_mul, Nat.succ_eq_add_one]
    have h3 : (i + 1) * arr.cols ≤ arr.rows * arr.cols := 
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
    omega)

/-- Reshape a 1D array into a 2D array -/
def reshape (arr : Array Int) (shape : Array Int) : Id (Array2 Int) :=
  sorry

/-- Specification: reshape returns a 2D array with the specified dimensions -/
theorem reshape_spec (arr : Array Int) (shape : Array Int)
    (h_shape_len : shape.size = 2)
    (h_valid : ∀ i (hi : i < 2), shape[i] > 0 ∨ shape[i] = -1)
    (h_not_both_neg : ¬(shape[0] = -1 ∧ shape[1] = -1))
    (h_size : if shape[0] > 0 ∧ shape[1] > 0 then 
                shape[0] * shape[1] = arr.size
              else if shape[0] = -1 then 
                arr.size % shape[1] = 0
              else 
                arr.size % shape[0] = 0) :
    ⦃⌜shape.size = 2 ∧ 
      (∀ i (hi : i < 2), shape[i] > 0 ∨ shape[i] = -1) ∧
      ¬(shape[0] = -1 ∧ shape[1] = -1) ∧
      (if shape[0] > 0 ∧ shape[1] > 0 then 
         shape[0] * shape[1] = arr.size
       else if shape[0] = -1 then 
         arr.size % shape[1] = 0
       else 
         arr.size % shape[0] = 0)⌝⦄
    reshape arr shape
    ⦃⇓r => (if shape[0] > 0 then r.rows = shape[0].natAbs else r.rows = arr.size / shape[1].natAbs) ∧
           (if shape[1] > 0 then r.cols = shape[1].natAbs else r.cols = arr.size / shape[0].natAbs) ∧
           ∀ i (hi : i < arr.size), 
             have hr : i / r.cols < r.rows := sorry
             have hc : i % r.cols < r.cols := sorry
             r.get (i / r.cols) (i % r.cols) hr hc = arr[i]⦄ := by
  sorry