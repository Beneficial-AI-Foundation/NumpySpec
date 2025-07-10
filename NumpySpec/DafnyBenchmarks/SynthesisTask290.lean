-- Synthesis Task 290: Find the longest list from a sequence of lists

namespace NumpySpec.DafnyBenchmarks.SynthesisTask290

/-- Returns the longest list from a sequence of lists -/
def maxLengthList (lists : List (List Int)) : List Int :=
  sorry

/-- Specification: The returned list is at least as long as any list in the input,
    and it is one of the lists in the input -/
theorem maxLengthList_spec (lists : List (List Int)) (h : lists.length > 0) :
  let maxList := maxLengthList lists
  (∀ l ∈ lists, l.length ≤ maxList.length) ∧ maxList ∈ lists :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask290