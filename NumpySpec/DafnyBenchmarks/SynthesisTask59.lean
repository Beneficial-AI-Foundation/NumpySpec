-- Synthesis Task 59: Calculate nth octagonal number

namespace NumpySpec.DafnyBenchmarks.SynthesisTask59

/-- Calculate the nth octagonal number -/
def nthOctagonalNumber (n : Nat) : Nat :=
  sorry

/-- Specification: The nth octagonal number is n(3n-2) -/
theorem nthOctagonalNumber_spec (n : Nat) :
    nthOctagonalNumber n = n * (3 * n - 2) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask59