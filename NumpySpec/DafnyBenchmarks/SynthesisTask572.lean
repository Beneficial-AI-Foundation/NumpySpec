-- Synthesis Task 572: Remove duplicates from array

namespace NumpySpec.DafnyBenchmarks.SynthesisTask572

/-- Remove duplicates from an array, preserving order of first occurrence -/
def removeDuplicates (a : Array Int) : List Int :=
  sorry

/-- Specification: Result contains each element exactly once -/
theorem removeDuplicates_spec (a : Array Int) :
    let result := removeDuplicates a
    (∀ x : Int, x ∈ result ↔ ∃ i : Nat, i < a.size ∧ a[i]! = x) ∧
    (∀ i j : Nat, i < j → j < result.length → result[i]! ≠ result[j]!) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask572