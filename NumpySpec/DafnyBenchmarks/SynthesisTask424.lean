-- Synthesis Task 424: Extract rear characters

namespace NumpySpec.DafnyBenchmarks.SynthesisTask424

/-- Extract the last character from each string in a list -/
def extractRearChars (l : List String) : List Char :=
  sorry

/-- Specification: Extract last character from each non-empty string -/
theorem extractRearChars_spec (l : List String)
    (h_nonempty : ∀ s ∈ l, s.length > 0) :
    (extractRearChars l).length = l.length :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask424