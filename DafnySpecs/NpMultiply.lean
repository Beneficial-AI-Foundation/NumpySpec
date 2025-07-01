/-!
# Array Multiplication Specification

Port of `np_multiply.dfy` to idiomatic Lean 4.

This module demonstrates several approaches to specifying element-wise array multiplication:
1. Runtime constraints via hypotheses
2. Compile-time constraints via dependent types
3. MPL-style specifications for future verification
-/

namespace DafnySpecs.NpMultiply

/-- Element-wise multiplication of arrays with runtime size checking.
    
    The hypothesis `h` ensures arrays have equal length at the call site.
    This mirrors the Dafny `requires` clause.
-/
def multiply (a b : Array Int) (_ : a.size = b.size) : Array Int :=
  Array.zipWith (· * ·) a b

/-- Specification theorem: result has same length as inputs -/
theorem multiply_length (a b : Array Int) (h : a.size = b.size) :
    (multiply a b h).size = a.size := by
  simp only [multiply, Array.size_zipWith, h, Nat.min_self]

/-- Specification theorem: element-wise correctness -/
theorem multiply_elem (a b : Array Int) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (multiply a b h)[i]'(by simp [multiply_length, hi]) = a[i] * b[i] := by
  sorry

section VectorApproach

/-- Multiplication using vectors with compile-time size checking.
    
    This approach eliminates the need for runtime hypotheses by encoding
    the size constraint in the type system.
-/
def multiplyVec {n : Nat} (a b : Vector Int n) : Vector Int n :=
  ⟨Array.zipWith (· * ·) a.toArray b.toArray, by simp [Array.size_zipWith]⟩

/-- Vector multiplication preserves all elements correctly -/
theorem multiplyVec_elem {n : Nat} (a b : Vector Int n) (i : Fin n) :
    (multiplyVec a b).get i = a.get i * b.get i := by
  simp [multiplyVec, Vector.get]

end VectorApproach

section GeneralizedApproach

/-- Polymorphic multiplication for any type with a Mul instance -/
def multiplyPoly {α : Type} [Mul α] (a b : Array α) (_ : a.size = b.size) : Array α :=
  Array.zipWith (· * ·) a b

/-- Multiplication for non-empty arrays (refinement type approach) -/
def multiplyNonEmpty (a b : {arr : Array Int // arr.size > 0}) 
    (h : a.val.size = b.val.size) : {arr : Array Int // arr.size > 0} :=
  ⟨Array.zipWith (· * ·) a.val b.val, by
    simp only [Array.size_zipWith, h, Nat.min_self]
    exact b.property⟩

end GeneralizedApproach

section Properties

/-- Multiplication is commutative when the element type is commutative -/
theorem multiply_comm (a b : Array Int) (h : a.size = b.size) :
    multiply a b h = multiply b a h.symm := by
  sorry

/-- Multiplication is associative (with appropriate size constraints) -/
theorem multiply_assoc (a b c : Array Int) 
    (hab : a.size = b.size) (hbc : b.size = c.size) :
    multiply (multiply a b hab) c (sorry : (multiply a b hab).size = c.size) = 
    multiply a (multiply b c hbc) (sorry : a.size = (multiply b c hbc).size) := by
  sorry

/-- One array is the identity element -/
def ones (n : Nat) : Array Int := Array.replicate n 1

theorem multiply_one (a : Array Int) :
    multiply a (ones a.size) (by simp only [ones, Array.size_replicate]) = a := by
  sorry

/-- Zero array is the zero element (multiplication by zero) -/
def zeros (n : Nat) : Array Int := Array.replicate n 0

theorem multiply_zero (a : Array Int) :
    multiply a (zeros a.size) (by simp only [zeros, Array.size_replicate]) = zeros a.size := by
  sorry

/-- Multiplication distributes over addition -/
theorem multiply_add_distrib (a b c : Array Int) 
    (hab : a.size = b.size) (hac : a.size = c.size) :
    multiply a (Array.zipWith (· + ·) b c) (sorry : a.size = (Array.zipWith (· + ·) b c).size) =
    Array.zipWith (· + ·) (multiply a b hab) (multiply a c hac) := by
  sorry

end Properties

section Examples

#check multiply #[1, 2, 3] #[4, 5, 6] rfl

end Examples

end DafnySpecs.NpMultiply