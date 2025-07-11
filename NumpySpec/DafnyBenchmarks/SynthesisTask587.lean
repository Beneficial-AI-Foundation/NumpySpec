-- Synthesis Task 587: Convert array to sequence

namespace NumpySpec.DafnyBenchmarks.SynthesisTask587

/-- Convert an array to a list -/
def arrayToSeq (a : Array Int) : List Int :=
  sorry

/-- Specification: Array to list conversion preserves elements -/
theorem arrayToSeq_spec (a : Array Int) :
    let s := arrayToSeq a
    s.length = a.size ∧
    ∀ i : Nat, i < a.size → s[i]! = a[i]! :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask587