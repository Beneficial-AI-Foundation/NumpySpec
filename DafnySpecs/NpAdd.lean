import Std.Do

/-!
# Array Addition Specification

Port of `np_add.dfy` to idiomatic Lean 4.

This module demonstrates several approaches to specifying array addition:
1. Runtime constraints via hypotheses
2. Compile-time constraints via dependent types
3. MPL-style specifications for future verification
-/

namespace DafnySpecs.NpAdd

/-- Element-wise addition of arrays with runtime size checking.
    
    The hypothesis `h` ensures arrays have equal length at the call site.
    This mirrors the Dafny `requires` clause.
-/
def add (a b : Array Int) (h : a.size = b.size) : Array Int :=
  Array.zipWith (· + ·) a b

/-- Specification theorem: result has same length as inputs -/
theorem add_length (a b : Array Int) (h : a.size = b.size) :
    (add a b h).size = a.size := by
  simp only [add]
  rw [Array.size_zipWith, h]
  exact Nat.min_self a.size

/-- Specification theorem: element-wise correctness -/
theorem add_elem (a b : Array Int) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (add a b h)[i]'(by simp [add_length, hi]) = a[i] + b[i] := by
  simp [add]
  rfl

/-- MPL-style specification comment for future verification:
    
    ⦃ a.size = b.size ⦄ 
      add a b 
    ⦃ λ res, res.size = a.size ∧ ∀ i : Fin res.size, res[i] = a[i.val] + b[i.val] ⦄
    
    When MPL tactics are available, this can be proved using `mspec` or `mvcgen`.
-/

/- Vector approach using compile-time size checking -/

section VectorApproach

/-- Addition using vectors with compile-time size checking.
    
    This approach eliminates the need for runtime hypotheses by encoding
    the size constraint in the type system.
-/
def addVec {n : Nat} (a b : Vector Int n) : Vector Int n :=
  ⟨Array.zipWith (· + ·) a.toArray b.toArray, by simp [Array.size_zipWith]⟩

/-- Vector addition preserves all elements correctly -/
theorem addVec_elem {n : Nat} (a b : Vector Int n) (i : Fin n) :
    (addVec a b).get i = a.get i + b.get i := by
  simp [addVec, Vector.get]

end VectorApproach


section GeneralizedApproach

/-- Polymorphic addition for any type with an Add instance -/
def addPoly {α : Type} [Add α] (a b : Array α) (h : a.size = b.size) : Array α :=
  Array.zipWith (· + ·) a b

/-- Addition for non-empty arrays (refinement type approach) -/
def addNonEmpty (a b : {arr : Array Int // arr.size > 0}) 
    (h : a.val.size = b.val.size) : {arr : Array Int // arr.size > 0} :=
  ⟨Array.zipWith (· + ·) a.val b.val, by
    simp only [Array.size_zipWith]
    rw [h]
    exact Nat.min_pos a.property b.property⟩

end GeneralizedApproach

section Properties

/-- Addition is commutative when the element type is commutative -/
theorem add_comm (a b : Array Int) (h : a.size = b.size) :
    add a b h = add b a h.symm := by
  unfold add
  ext i _
  simp [Array.get_zipWith, Int.add_comm]

/-- Addition is associative (with appropriate size constraints) -/
theorem add_assoc (a b c : Array Int) 
    (hab : a.size = b.size) (hbc : b.size = c.size) :
    add (add a b hab) c (by rw [add_length, hab, hbc]) = 
    add a (add b c hbc) (by rw [hab, hbc]) := by
  unfold add
  ext i _
  simp [Array.get_zipWith, Int.add_assoc]

/-- Zero array is the identity element -/
def zeros (n : Nat) : Array Int := Array.replicate n 0

theorem add_zero (a : Array Int) :
    add a (zeros a.size) (by simp only [zeros, Array.size_replicate]) = a := by
  unfold add zeros
  ext i _
  simp [Array.get_zipWith, Array.get_replicate]

end Properties

section Examples

/- Example usage:
#eval add #[1, 2, 3] #[4, 5, 6] rfl
-- Output: #[5, 7, 9]

#check addVec ⟨#[1, 2, 3], rfl⟩ ⟨#[4, 5, 6], rfl⟩
-- Type: Vector Int 3
-/

end Examples

end DafnySpecs.NpAdd