-- Synthesis Task 95: Find the length of the smallest list in a sequence

namespace NumpySpec.DafnyBenchmarks.SynthesisTask95

/-- Returns the length of the smallest list in a sequence of lists -/
def smallestListLength (s : List (List Int)) : Int :=
  sorry

/-- Specification: The returned value is the minimum length among all lists,
    and there exists at least one list with that length -/
theorem smallestListLength_spec (s : List (List Int)) (h : s.length > 0) :
  let v := smallestListLength s
  (∀ i : Nat, i < s.length → v ≤ s[i]!.length) ∧
  (∃ i : Nat, i < s.length ∧ v = s[i]!.length) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask95