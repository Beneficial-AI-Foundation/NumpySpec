/-
  Find the intersection of two integer arrays
  (Ported from Dafny synthesis task 249)
-/

import Std

namespace NumpySpec.DafnyBenchmarks.SynthesisTask249

/-- Check if an element exists in an array -/
def inArray (a : Array Int) (x : Int) : Prop :=
  ∃ i : Fin a.size, a[i] = x

/-- Find the intersection of two integer arrays, returning unique elements -/
def intersection (a : Array Int) (b : Array Int) : List Int := sorry

theorem intersection_spec (a b : Array Int) :
  let result := intersection a b
  -- All elements in the output are in both a and b
  (∀ x ∈ result, inArray a x ∧ inArray b x) ∧
  -- The elements in the output are all different
  (∀ i j : Nat, i < j → j < result.length → result[i]! ≠ result[j]!) := by sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask249