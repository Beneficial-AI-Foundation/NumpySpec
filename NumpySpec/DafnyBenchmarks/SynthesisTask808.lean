-- Synthesis Task 808: Check if element is in list

namespace NumpySpec.DafnyBenchmarks.SynthesisTask808

/-- Check if an integer k is in the list s -/
def containsK (s : List Int) (k : Int) : Bool :=
  sorry

/-- Specification: containsK returns true iff k is in the list -/
theorem containsK_spec (s : List Int) (k : Int) :
    containsK s k = true ↔ k ∈ s :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask808