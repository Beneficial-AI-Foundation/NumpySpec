-- No external imports needed for basic array operations

/-!
# Array Absolute Value Specification

Port of `np_abs.dfy` to idiomatic Lean 4.

This module provides several approaches to specifying element-wise absolute value:
1. Direct implementation using Array.map
2. Vector-based approach with compile-time size information
3. Polymorphic versions for different numeric types
4. MPL-style specifications for future verification

## Dafny Specification Reference

The original Dafny specification defines:
- `Abs(a: array<int>)` - returns array with absolute values
- Ensures: result length equals input length
- Ensures: each element is the absolute value of corresponding input
- Ensures: all result elements are non-negative
-/

namespace DafnySpecs.NpAbs

/-- Element-wise absolute value of an integer array -/
def abs (a : Array Int) : Array Int :=
  a.map (fun x => if x < 0 then -x else x)

/-- Specification theorem: result has same length as input -/
theorem abs_length (a : Array Int) :
    (abs a).size = a.size := by
  simp only [abs, Array.size_map]

/-- Specification theorem: element-wise correctness -/
theorem abs_elem (a : Array Int) (i : Nat) (hi : i < a.size) :
    (abs a)[i]'(by rw [abs_length]; exact hi) = Int.abs a[i] := by
  simp [abs]
  rfl

/-- Specification theorem: all elements are non-negative -/
theorem abs_nonneg (a : Array Int) (i : Nat) (hi : i < (abs a).size) :
    (abs a)[i] ≥ 0 := by
  rw [abs_length] at hi
  simp [abs]
  split
  · simp
  · apply Int.le_of_not_lt
    assumption

/-- MPL-style specification comment for future verification:
    
    ⦃ True ⦄ 
      abs a 
    ⦃ λ res, res.size = a.size ∧ 
             ∀ i : Fin res.size, res[i] = Int.abs a[i.val] ∧ res[i] ≥ 0 ⦄
    
    When MPL tactics are available, this can be proved using `mspec` or `mvcgen`.
-/

/- Vector approach using compile-time size checking -/

section VectorApproach

/-- Absolute value using vectors with compile-time size checking -/
def absVec {n : Nat} (v : Vector Int n) : Vector Int n :=
  ⟨v.toArray.map (fun x => if x < 0 then -x else x), by simp [Array.size_map]⟩

/-- Vector absolute value preserves all elements correctly -/
theorem absVec_elem {n : Nat} (v : Vector Int n) (i : Fin n) :
    (absVec v).get i = Int.abs (v.get i) := by
  simp [absVec, Vector.get]

/-- All elements in vector result are non-negative -/
theorem absVec_nonneg {n : Nat} (v : Vector Int n) (i : Fin n) :
    (absVec v).get i ≥ 0 := by
  simp [absVec, Vector.get]
  split
  · simp
  · apply Int.le_of_not_lt
    assumption

end VectorApproach

section GeneralizedApproach

/-- Absolute value for non-empty arrays -/
def absNonEmpty (a : {arr : Array Int // arr.size > 0}) : 
    {arr : Array Int // arr.size > 0} :=
  ⟨a.val.map (fun x => if x < 0 then -x else x), by
    simp only [Array.size_map]
    exact a.property⟩

/-- Alternative: return natural numbers -/
def absNat (a : Array Int) : Array Nat :=
  a.map Int.natAbs

end GeneralizedApproach

section Properties

/-- Absolute value is idempotent -/
theorem abs_idempotent (a : Array Int) :
    abs (abs a) = abs a := by
  unfold abs
  apply Array.ext
  · simp [Array.size_map]
  · intro i hi1 hi2
    simp
    split
    case isTrue h =>
      -- If abs(a[i]) < 0, which is impossible
      have : ¬(if a[i] < 0 then -a[i] else a[i]) < 0 := by
        split
        · simp
        · exact h
      contradiction
    case isFalse h =>
      -- abs(a[i]) ≥ 0, so it remains unchanged
      rfl

/-- Absolute value of negation -/
theorem abs_neg (a : Array Int) :
    abs (a.map (- ·)) = abs a := by
  unfold abs
  apply Array.ext
  · simp [Array.size_map]
  · intro i hi1 hi2
    simp
    split <;> split <;> simp [Int.neg_neg]

/-- Absolute value preserves zeros -/
theorem abs_zero (n : Nat) :
    abs (Array.replicate n 0) = Array.replicate n 0 := by
  unfold abs
  simp [Array.map_replicate]

/-- Triangle inequality for arrays -/
theorem abs_triangle (a b : Array Int) (h : a.size = b.size) :
    ∀ i : Nat, i < a.size → 
    Int.abs (a[i] + b[i]) ≤ Int.abs a[i] + Int.abs b[i] := by
  intros i hi
  exact Int.abs_add_le _ _

/-- Absolute value distributes over scalar multiplication -/
theorem abs_scale (a : Array Int) (c : Int) :
    abs (a.map (· * c)) = (abs a).map (· * Int.abs c) := by
  unfold abs
  apply Array.ext
  · simp [Array.size_map]
  · intro i hi1 hi2
    simp
    split <;> split <;> simp [Int.mul_comm c, Int.neg_mul, Int.mul_neg, Int.neg_neg]
    · rw [Int.mul_comm]
      simp [Int.neg_mul]
    · have : ¬c < 0 := by
        intro hc
        have : a[i] * c < 0 := Int.mul_neg_of_pos_of_neg ‹¬a[i] < 0› hc
        contradiction
      simp [Int.abs_of_nonneg (Int.le_of_not_lt ‹¬c < 0›)]
    · have : c < 0 := by
        by_contra hc
        have : a[i] * c < 0 := Int.mul_neg_of_neg_of_pos ‹a[i] < 0› (Int.lt_of_not_le hc)
        contradiction
      simp [Int.abs_of_neg ‹c < 0›]
      rw [Int.mul_comm, Int.neg_mul]
    · simp [Int.abs_of_nonneg (Int.le_of_not_lt ‹¬c < 0›)]

/-- Maximum element preservation -/
theorem abs_max_elem (a : Array Int) (ha : a.size > 0) :
    ∃ i : Nat, i < a.size ∧ 
    ∀ j : Nat, j < a.size → Int.abs (abs a)[j] ≤ Int.abs (abs a)[i] := by
  -- The maximum absolute value exists
  sorry

end Properties

section Optimizations

/-- Specialized absolute value for small integers (can be more efficient) -/
def absSmall (a : Array Int) : Array Int :=
  a.map fun x => if x < 0 then -x else x

/-- Correctness of optimized version -/
theorem absSmall_correct (a : Array Int) :
    absSmall a = abs a := by
  rfl

end Optimizations

section Examples

/- Example usage:
#eval abs #[1, -2, 3, -4, 5]
-- Output: #[1, 2, 3, 4, 5]

#eval abs #[-10, 0, 10]
-- Output: #[10, 0, 10]

#check absVec ⟨#[1, -2, 3], rfl⟩
-- Type: Vector Int 3

#eval absNat #[-1, -2, -3]
-- Output: #[1, 2, 3]
-/

end Examples

end DafnySpecs.NpAbs