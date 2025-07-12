-- Synthesis Task 262: Split array into two parts

namespace NumpySpec.DafnyBenchmarks.SynthesisTask262

/-- Split an array into two parts at index L -/
def splitArray (arr : Array Int) (L : Nat) : List Int × List Int :=
  sorry

/-- Specification: Split array into two parts at index L -/
theorem splitArray_spec (arr : Array Int) (L : Nat)
    (h_range : L ≤ arr.size) :
    let (firstPart, secondPart) := splitArray arr L
    firstPart.length = L ∧
    secondPart.length = arr.size - L ∧
    firstPart ++ secondPart = arr.toList :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask262