-- Synthesis Task 101: Get the k-th element from an array (1-indexed)

namespace NumpySpec.DafnyBenchmarks.SynthesisTask101

/-- Returns the k-th element from an array (1-indexed) -/
def kthElement (arr : Array Int) (k : Int) : Int :=
  sorry

/-- Specification: Returns the element at position k-1 (0-indexed) -/
theorem kthElement_spec (arr : Array Int) (k : Int)
    (h : 1 ≤ k ∧ k ≤ arr.size) :
  kthElement arr k = arr[(k - 1).toNat]! :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask101