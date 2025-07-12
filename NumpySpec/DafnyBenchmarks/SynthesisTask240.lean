-- Synthesis Task 240: Replace last element with another sequence

namespace NumpySpec.DafnyBenchmarks.SynthesisTask240

/-- Replace the last element of first sequence with all elements of second sequence -/
def replaceLastElement (first second : List Int) : List Int :=
  sorry

/-- Specification: Replace last element of first with entire second sequence -/
theorem replaceLastElement_spec (first second : List Int) 
    (h_nonempty : first.length > 0) :
    let result := replaceLastElement first second
    result.length = first.length - 1 + second.length ∧
    (∀ i : Nat, i < first.length - 1 → result[i]! = first[i]!) ∧
    (∀ i : Nat, first.length - 1 ≤ i ∧ i < result.length → 
      result[i]! = second[i - first.length + 1]!) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask240