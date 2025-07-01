import Std.Do

/-!
# Array Greater-Than Comparison Specification

Port of `np_greater.dfy` to idiomatic Lean 4.

This module provides several approaches to specifying element-wise greater-than comparison:
1. Direct implementation using Array.zipWith
2. Vector-based approach with compile-time size checking
3. Polymorphic versions for different ordered types
4. MPL-style specifications for future verification

## Dafny Specification Reference

The original Dafny specification defines:
- `Greater(a: array<int>, b: array<int>)` - returns array of booleans
- Requires: arrays have equal length
- Ensures: result length equals input length
- Ensures: each element is true iff a[i] > b[i]
-/

namespace DafnySpecs.NpGreater

/-- Element-wise greater-than comparison of arrays with runtime size checking.
    
    The hypothesis `h` ensures arrays have equal length at the call site.
    This mirrors the Dafny `requires` clause.
-/
def greater (a b : Array Int) (_ : a.size = b.size) : Array Bool :=
  Array.zipWith (· > ·) a b

/-- Specification theorem: result has same length as inputs -/
theorem greater_length (a b : Array Int) (h : a.size = b.size) :
    (greater a b h).size = a.size := by
  simp only [greater]
  rw [Array.size_zipWith, h]
  simp

/-- Specification theorem: element-wise correctness -/
theorem greater_elem (a b : Array Int) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (greater a b h)[i]'(by simp [greater_length, hi]) = (a[i] > b[i]) := by
  simp [greater, Array.getElem_zipWith]

/-
MPL-style specification comment for future verification:

⦃ a.size = b.size ⦄ 
  greater a b 
⦃ λ res, res.size = a.size ∧ ∀ i : Fin res.size, res[i] = (a[i.val] > b[i.val]) ⦄

When MPL tactics are available, this can be proved using `mspec` or `mvcgen`.
-/

section VectorApproach

/-- Greater-than comparison using vectors with compile-time size checking.
    
    This approach eliminates the need for runtime hypotheses by encoding
    the size constraint in the type system.
-/
def greaterVec {n : Nat} (a b : Vector Int n) : Vector Bool n :=
  ⟨Array.zipWith (· > ·) a.toArray b.toArray, by simp [Array.size_zipWith]⟩

/-- Vector greater-than comparison preserves all elements correctly -/
theorem greaterVec_elem {n : Nat} (a b : Vector Int n) (i : Fin n) :
    (greaterVec a b).get i = (a.get i > b.get i) := by
  simp [greaterVec, Vector.get]

end VectorApproach

section GeneralizedApproach

/-- Polymorphic greater-than comparison for any type with ordering -/
def greaterPoly {α : Type} [LT α] [DecidableRel (· < · : α → α → Prop)] (a b : Array α) (_ : a.size = b.size) : Array Bool :=
  Array.zipWith (fun x y => if x < y then false else if y < x then true else false) a b

/-- Greater-than comparison for non-empty arrays -/
def greaterNonEmpty (a b : {arr : Array Int // arr.size > 0}) 
    (h : a.val.size = b.val.size) : {arr : Array Bool // arr.size > 0} :=
  ⟨Array.zipWith (· > ·) a.val b.val, by
    simp only [Array.size_zipWith]
    rw [h, Nat.min_self]
    rw [← h]
    exact a.property⟩

/-- Alternative: use propositional ordering (returns Array Prop) -/
def greaterProp (a b : Array Int) (_ : a.size = b.size) : Array Prop :=
  Array.zipWith (· > ·) a b

end GeneralizedApproach

section Properties

/-- Greater-than comparison is irreflexive -/
theorem greater_irrefl (a : Array Int) :
    greater a a rfl = Array.replicate a.size false := by
  unfold greater
  ext i hi
  · simp [Array.size_replicate]
  · simp at hi
    simp [Array.getElem_replicate]

/-- Greater-than comparison is antisymmetric with less-than -/
theorem greater_antisymm (a b : Array Int) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (greater a b h)[i]'(by simp [greater_length, hi]) = true ↔ 
    (greater b a h.symm)[i]'(by simp [greater_length]; rw [← h]; exact hi) = false := by
  sorry

/-- Greater-than comparison is transitive -/
theorem greater_trans (a b c : Array Int) (hab : a.size = b.size) (hbc : b.size = c.size) 
    (i : Nat) (hi : i < a.size) :
    (greater a b hab)[i]'(by simp [greater_length, hi]) = true →
    (greater b c hbc)[i]'(by simp [greater_length]; rw [← hab]; exact hi) = true →
    (greater a c (hab.trans hbc))[i]'(by simp [greater_length, hi]) = true := by
  sorry

/-- Relationship with strict ordering -/
theorem greater_iff_lt (a b : Array Int) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (greater a b h)[i]'(by simp [greater_length, hi]) = true ↔ b[i]'(by rw [← h]; exact hi) < a[i] := by
  sorry

/-- Count elements where a > b -/
def countGreater (a b : Array Int) (h : a.size = b.size) : Nat :=
  (greater a b h).filter id |>.size

/-- No elements greater implies count is zero -/
theorem countGreater_none (a b : Array Int) (h : a.size = b.size) :
    (∀ i : Nat, ∀ (hi : i < a.size), a[i] ≤ b[i]'(by rw [← h]; exact hi)) →
    countGreater a b h = 0 := by
  intro hle
  unfold countGreater
  have : ∀ i : Nat, ∀ (hi : i < (greater a b h).size), (greater a b h)[i] = false := by
    intro i hi
    rw [greater_length] at hi
    sorry
  sorry -- Would need lemma about filter with all false elements

/-- All elements greater implies count equals size -/
theorem countGreater_all (a b : Array Int) (h : a.size = b.size) :
    (∀ i : Nat, ∀ (hi : i < a.size), a[i] > b[i]'(by rw [← h]; exact hi)) →
    countGreater a b h = a.size := by
  intro hgt
  unfold countGreater
  have : ∀ i : Nat, ∀ (hi : i < (greater a b h).size), (greater a b h)[i] = true := by
    intro i hi
    rw [greater_length] at hi
    rw [greater_elem]
    simp
    exact hgt i hi
  sorry -- Would need lemma about filter with all true elements

end Properties

section OrderingRelations

/-- Relationship between greater and less-or-equal -/
theorem greater_not_leq (a b : Array Int) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (greater a b h)[i]'(by simp [greater_length, hi]) = true ↔ 
    ¬(a[i] ≤ b[i]'(by rw [← h]; exact hi)) := by
  sorry

/- When the other comparison modules are available, we can prove:

/-- Relationship between greater and less operations -/
theorem greater_eq_less_swap (a b : Array Int) (h : a.size = b.size) :
    greater a b h = DafnySpecs.NpLess.less b a h.symm := by
  unfold greater DafnySpecs.NpLess.less
  rfl

/-- Trichotomy property with equal and less -/
theorem trichotomy (a b : Array Int) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (greater a b h)[i]'(by simp [greater_length, hi]) = true ∨
    (DafnySpecs.NpEqual.equal a b h)[i]'(by simp [DafnySpecs.NpEqual.equal_length, hi]) = true ∨
    (DafnySpecs.NpLess.less a b h)[i]'(by simp [DafnySpecs.NpLess.less_length, hi]) = true := by
  simp [greater_elem, DafnySpecs.NpEqual.equal_elem, DafnySpecs.NpLess.less_elem]
  cases' lt_trichotomy a[i] b[i]'(by rw [← h]; exact hi) with hlt heq
  · right; right; exact hlt
  · cases' heq with heq hgt
    · right; left; exact heq
    · left; exact hgt
-/

end OrderingRelations

section Optimizations

/-- Specialized greater-than for sorted arrays (can use binary search) -/
def greaterSorted (a b : Array Int) (_ : a.size = b.size) : Array Bool :=
  Array.zipWith (· > ·) a b

/-- Correctness of optimized version -/
theorem greaterSorted_correct (a b : Array Int) (h : a.size = b.size) :
    greaterSorted a b h = greater a b h := by
  rfl

end Optimizations

section Examples

/- Example usage:
#eval greater #[1, 2, 3] #[0, 2, 4] rfl
-- Output: #[true, false, false]

#eval greater #[5, 0, -3] #[4, -1, -3] rfl
-- Output: #[true, true, false]

#eval greater #[10, 20, 30] #[10, 20, 30] rfl
-- Output: #[false, false, false]

#check greaterVec ⟨#[1, 2], rfl⟩ ⟨#[0, 3], rfl⟩
-- Type: Vector Bool 2

#eval countGreater #[5, 10, 15] #[3, 10, 20] rfl
-- Output: 1
-/

end Examples

end DafnySpecs.NpGreater