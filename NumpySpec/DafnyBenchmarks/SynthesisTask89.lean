-- Synthesis Task 89: Find closest smaller integer

namespace NumpySpec.DafnyBenchmarks.SynthesisTask89

/-- Find the closest smaller integer (n-1) -/
def closestSmaller (n : Nat) : Nat :=
  sorry

/-- Specification: Result is n-1 -/
theorem closestSmaller_spec (n : Nat) (h : n > 0) :
    closestSmaller n + 1 = n :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask89