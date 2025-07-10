/-
Copyright (c) 2025 NumpySpec. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/

namespace NumpySpec.DafnyBenchmarks.SynthesisTask2

/-- Check if an element exists in an array -/
def InArray (a : Array Int) (x : Int) : Prop :=
  ∃ i : Nat, i < a.size ∧ a[i]! = x

/-- Find shared elements between two arrays.
    Returns a list of elements that appear in both arrays, with no duplicates. -/
def SharedElements (a : Array Int) (b : Array Int) : List Int :=
  sorry

/-- Specification: All elements in the result are in both arrays -/
theorem SharedElements_all_in_both (a : Array Int) (b : Array Int) :
  ∀ x ∈ SharedElements a b, InArray a x ∧ InArray b x := by
  sorry

/-- Specification: The elements in the result are all different -/
theorem SharedElements_no_duplicates (a : Array Int) (b : Array Int) :
  (SharedElements a b).Nodup := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask2