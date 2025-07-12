namespace NumpySpec.DafnyBenchmarks.SynthesisTask792

/-- Count the number of lists in a list of lists -/
def countLists (lists : List (List Int)) : Nat :=
  sorry

/-- Specification: The count equals the length of the outer list -/
theorem countLists_spec (lists : List (List Int)) :
    countLists lists = lists.length := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask792