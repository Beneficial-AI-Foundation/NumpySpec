import Std.Do

/-!
# Array Less-Than Comparison Specification

Port of `np_less.dfy` to idiomatic Lean 4.

This module provides several approaches to specifying element-wise less-than comparison:
1. Direct implementation using Array.zipWith
2. Vector-based approach with compile-time size checking
3. Polymorphic versions for different ordered types
4. MPL-style specifications for future verification

## Dafny Specification Reference

The original Dafny specification defines:
- `Less(a: array<int>, b: array<int>)` - returns array of booleans
- Requires: arrays have equal length
- Ensures: result length equals input length
- Ensures: each element is true iff a[i] < b[i]
-/

namespace DafnySpecs.NpLess

/-- Element-wise less-than comparison of arrays with runtime size checking.
    
    The hypothesis `h` ensures arrays have equal length at the call site.
    This mirrors the Dafny `requires` clause.
-/
def less (a b : Array Int) (_ : a.size = b.size) : Array Bool :=
  Array.zipWith (· < ·) a b

/-- Specification theorem: result has same length as inputs -/
theorem less_length (a b : Array Int) (h : a.size = b.size) :
    (less a b h).size = a.size := by
  simp only [less]
  rw [Array.size_zipWith, h]
  simp

/-- Specification theorem: element-wise correctness -/
theorem less_elem (a b : Array Int) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (less a b h)[i]'(by simp [less_length, hi]) = (a[i] < b[i]) := by
  simp [less, Array.getElem_zipWith]

/-
MPL-style specification comment for future verification:

⦃ a.size = b.size ⦄ 
  less a b 
⦃ λ res, res.size = a.size ∧ ∀ i : Fin res.size, res[i] = (a[i.val] < b[i.val]) ⦄

When MPL tactics are available, this can be proved using `mspec` or `mvcgen`.
-/

section VectorApproach

/-- Less-than comparison using vectors with compile-time size checking.
    
    This approach eliminates the need for runtime hypotheses by encoding
    the size constraint in the type system.
-/
def lessVec {n : Nat} (a b : Vector Int n) : Vector Bool n :=
  ⟨Array.zipWith (· < ·) a.toArray b.toArray, by simp [Array.size_zipWith]⟩

/-- Vector less-than comparison preserves all elements correctly -/
theorem lessVec_elem {n : Nat} (a b : Vector Int n) (i : Fin n) :
    (lessVec a b).get i = (a.get i < b.get i) := by
  simp [lessVec, Vector.get]

end VectorApproach

section GeneralizedApproach

/-- Polymorphic less-than comparison for any type with ordering -/
def lessPoly {α : Type} [LT α] [DecidableRel (· < · : α → α → Prop)] (a b : Array α) (_ : a.size = b.size) : Array Bool :=
  Array.zipWith (fun x y => if x < y then true else false) a b

/-- Less-than comparison for non-empty arrays -/
def lessNonEmpty (a b : {arr : Array Int // arr.size > 0}) 
    (h : a.val.size = b.val.size) : {arr : Array Bool // arr.size > 0} :=
  ⟨Array.zipWith (· < ·) a.val b.val, by
    simp only [Array.size_zipWith]
    rw [h, Nat.min_self]
    rw [← h]
    exact a.property⟩

end GeneralizedApproach

section Properties

/-- Less-than comparison is irreflexive -/
theorem less_irrefl (a : Array Int) :
    less a a rfl = Array.replicate a.size false := by
  unfold less
  ext i hi
  · simp [Array.size_replicate]
  · simp at hi
    simp [Array.getElem_replicate]

/-- Less-than comparison is transitive -/
theorem less_trans (a b c : Array Int) (hab : a.size = b.size) (hbc : b.size = c.size) 
    (i : Nat) (hi : i < a.size) :
    (less a b hab)[i]'(by simp [less_length, hi]) = true →
    (less b c hbc)[i]'(by simp [less_length]; rw [← hab]; exact hi) = true →
    (less a c (hab.trans hbc))[i]'(by simp [less_length, hi]) = true := by
  sorry

end Properties

section Examples

/- Example usage:
#eval less #[1, 2, 3] #[2, 2, 4] rfl
-- Output: #[true, false, true]

#eval less #[5, 0, -3] #[4, 1, -3] rfl
-- Output: #[false, true, false]

#eval less #[10, 20, 30] #[10, 20, 30] rfl
-- Output: #[false, false, false]
-/

end Examples

end DafnySpecs.NpLess