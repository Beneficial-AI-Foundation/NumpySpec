/-
# NumPy Bitwise Xor Specification

Port of np_bitwise_xor.dfy to Lean 4
-/

namespace DafnySpecs.BitwiseXor

/-- Element-wise bitwise XOR of two vectors -/
def bitwiseXor {n : Nat} (a b : Vector Nat n) : Vector Nat n := Vector.zipWith (· ^^^ ·) a b

/-- Specification: The result has the same length as inputs -/
theorem bitwiseXor_length {n : Nat} (a b : Vector Nat n) :
  (bitwiseXor a b).size = n := rfl

/-- Specification: Each element is the bitwise XOR of corresponding input elements -/
theorem bitwiseXor_spec {n : Nat} (a b : Vector Nat n) :
  ∀ i : Fin n, (bitwiseXor a b)[i] = a[i] ^^^ b[i] := by
    intro i
    simp [bitwiseXor]

end DafnySpecs.BitwiseXor