-- Synthesis Task 94: Find the first element of the list with minimum second value

namespace NumpySpec.DafnyBenchmarks.SynthesisTask94

/-- Returns the first element of the list that has the minimum second value -/
def minSecondValueFirst (s : Array (List Int)) : Int :=
  sorry

/-- Specification: Find the list with minimum second element and return its first element -/
theorem minSecondValueFirst_spec (s : Array (List Int)) 
    (h_size : s.size > 0)
    (h_len : ∀ i : Nat, i < s.size → s[i]!.length ≥ 2) :
  let firstOfMinSecond := minSecondValueFirst s
  ∃ i : Nat, i < s.size ∧ 
    firstOfMinSecond = s[i]![0]! ∧
    (∀ j : Nat, j < s.size → s[i]![1]! ≤ s[j]![1]!) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask94