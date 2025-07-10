-- Synthesis Task 470: Pairwise addition of consecutive elements

namespace NumpySpec.DafnyBenchmarks.SynthesisTask470

/-- Add consecutive pairs of elements in an array -/
def pairwiseAddition (a : Array Int) : Array Int :=
  sorry

/-- Specification: Add consecutive pairs to produce array of half length -/
theorem pairwiseAddition_spec (a : Array Int) 
    (h_even : a.size % 2 = 0) :
    let result := pairwiseAddition a
    result.size = a.size / 2 ∧
    ∀ i : Nat, i < result.size → result[i]! = a[2*i]! + a[2*i + 1]! :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask470