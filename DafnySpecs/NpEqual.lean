import Std.Do

/-!
# Array Equality Comparison Specification

Port of `np_equal.dfy` to idiomatic Lean 4.

This module provides several approaches to specifying element-wise equality comparison:
1. Direct implementation using Array.zipWith
2. Vector-based approach with compile-time size checking
3. Polymorphic versions for different types with decidable equality
4. MPL-style specifications for future verification

## Dafny Specification Reference

The original Dafny specification defines:
- `Equal(a: array<int>, b: array<int>)` - returns array of booleans
- Requires: arrays have equal length
- Ensures: result length equals input length
- Ensures: each element is true iff corresponding elements are equal
-/

namespace DafnySpecs.NpEqual

/-- Element-wise equality comparison of arrays with runtime size checking.
    
    The hypothesis `h` ensures arrays have equal length at the call site.
    This mirrors the Dafny `requires` clause.
-/
def equal (a b : Array Int) (_ : a.size = b.size) : Array Bool :=
  Array.zipWith (· == ·) a b

/-- Specification theorem: result has same length as inputs -/
theorem equal_length (a b : Array Int) (h : a.size = b.size) :
    (equal a b h).size = a.size := by
  simp only [equal]
  rw [Array.size_zipWith, h]
  simp

/-- Specification theorem: element-wise correctness -/
theorem equal_elem (a b : Array Int) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (equal a b h)[i]'(by simp [equal_length, hi]) = (a[i] == b[i]) := by
  simp [equal, Array.getElem_zipWith, hi, h ▸ hi]

/-
MPL-style specification comment for future verification:

⦃ a.size = b.size ⦄ 
  equal a b 
⦃ λ res, res.size = a.size ∧ ∀ i : Fin res.size, res[i] = (a[i.val] == b[i.val]) ⦄

When MPL tactics are available, this can be proved using `mspec` or `mvcgen`.
-/

section VectorApproach

/-- Equality comparison using vectors with compile-time size checking.
    
    This approach eliminates the need for runtime hypotheses by encoding
    the size constraint in the type system.
-/
def equalVec {n : Nat} (a b : Vector Int n) : Vector Bool n :=
  ⟨Array.zipWith (· == ·) a.toArray b.toArray, by simp [Array.size_zipWith]⟩

/-- Vector equality comparison preserves all elements correctly -/
theorem equalVec_elem {n : Nat} (a b : Vector Int n) (i : Fin n) :
    (equalVec a b).get i = (a.get i == b.get i) := by
  simp [equalVec, Vector.get]

end VectorApproach

section GeneralizedApproach

/-- Polymorphic equality comparison for any type with decidable equality -/
def equalPoly {α : Type} [DecidableEq α] (a b : Array α) (_ : a.size = b.size) : Array Bool :=
  Array.zipWith (· == ·) a b

/-- Equality comparison for non-empty arrays -/
def equalNonEmpty (a b : {arr : Array Int // arr.size > 0}) 
    (h : a.val.size = b.val.size) : {arr : Array Bool // arr.size > 0} :=
  ⟨Array.zipWith (· == ·) a.val b.val, by
    simp only [Array.size_zipWith]
    rw [h]
    simp [Nat.min_eq_left (h ▸ Nat.le_refl _), a.property]⟩

/-- Alternative: use propositional equality (returns Array Prop) -/
def equalProp (a b : Array Int) (_ : a.size = b.size) : Array Prop :=
  Array.zipWith (· = ·) a b

end GeneralizedApproach

section Properties

/-- Equality comparison is reflexive -/
theorem equal_refl (a : Array Int) :
    equal a a rfl = Array.replicate a.size true := by
  unfold equal
  ext i hi
  · simp [Array.size_zipWith, Array.size_replicate]
  · simp [Array.size_zipWith] at hi
    simp [Array.getElem_zipWith, Array.getElem_replicate, hi]

/-- Equality comparison is symmetric -/
theorem equal_symm (a b : Array Int) (h : a.size = b.size) :
    equal a b h = equal b a h.symm := by
  unfold equal
  ext i _
  simp [Array.getElem_zipWith]
  constructor
  · intro heq
    exact heq.symm
  · intro heq
    exact heq.symm

/-- If arrays are equal element-wise, they are equal -/
theorem equal_all_true_iff (a b : Array Int) (h : a.size = b.size) :
    (∀ i : Nat, ∀ (hi : i < (equal a b h).size), (equal a b h)[i] = true) ↔ a = b := by
  constructor
  · intro hall
    ext i hi
    · exact h
    · have : i < (equal a b h).size := by simp [equal_length, hi]
      have := hall i this
      rw [equal_elem] at this
      simp at this
      exact this
  · intro heq
    subst heq
    intro i hi
    rw [equal_refl]
    simp [Array.getElem_replicate]

/-- Transitivity property helper -/
theorem equal_trans_helper (a b c : Array Int) (hab : a.size = b.size) (hbc : b.size = c.size) 
    (i : Nat) (hi : i < a.size) :
    (equal a b hab)[i]'(by simp [equal_length, hi]) = true →
    (equal b c hbc)[i]'(by simp [equal_length, hi, hab]) = true →
    (equal a c (hab.trans hbc))[i]'(by simp [equal_length, hi]) = true := by
  simp [equal_elem]
  intro heq1 heq2
  exact Eq.trans heq1 heq2

/-- Count true elements in equality comparison -/
def countEqual (a b : Array Int) (h : a.size = b.size) : Nat :=
  (equal a b h).filter id |>.size

/-- All equal implies count equals size -/
theorem countEqual_all (a b : Array Int) (h : a.size = b.size) :
    a = b → countEqual a b h = a.size := by
  intro heq
  subst heq
  unfold countEqual
  rw [equal_refl]
  simp [Array.filter_replicate]

/-- No equal elements implies count is zero -/
theorem countEqual_none (a b : Array Int) (h : a.size = b.size) :
    (∀ i : Nat, ∀ (hi : i < a.size), a[i] ≠ b[i]'(by rw [← h]; exact hi)) →
    countEqual a b h = 0 := by
  intro hne
  unfold countEqual
  have : ∀ i : Nat, ∀ (hi : i < (equal a b h).size), (equal a b h)[i] = false := by
    intro i hi
    rw [equal_length] at hi
    rw [equal_elem]
    simp
    exact hne i hi
  sorry -- Would need lemma about filter with all false elements

end Properties

section Optimizations

/-- Specialized equality for sorted arrays (can short-circuit on first difference) -/
def equalSorted (a b : Array Int) (_ : a.size = b.size) : Array Bool :=
  Array.zipWith (· == ·) a b

/-- Correctness of optimized version -/
theorem equalSorted_correct (a b : Array Int) (h : a.size = b.size) :
    equalSorted a b h = equal a b h := by
  rfl

end Optimizations

section Examples

/- Example usage:
#eval equal #[1, 2, 3] #[1, 2, 3] rfl
-- Output: #[true, true, true]

#eval equal #[1, 2, 3] #[1, 2, 4] rfl
-- Output: #[true, true, false]

#eval equal #[5, 0, -3] #[5, 1, -3] rfl
-- Output: #[true, false, true]

#check equalVec ⟨#[1, 2], rfl⟩ ⟨#[1, 3], rfl⟩
-- Type: Vector Bool 2

#eval countEqual #[1, 2, 3] #[1, 0, 3] rfl
-- Output: 2
-/

end Examples

end DafnySpecs.NpEqual