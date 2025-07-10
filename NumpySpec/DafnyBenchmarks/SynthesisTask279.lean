-- Synthesis Task 279: Calculate nth decagonal number

namespace NumpySpec.DafnyBenchmarks.SynthesisTask279

/-- Calculate the nth decagonal number -/
def nthDecagonalNumber (n : Nat) : Int :=
  sorry

/-- Specification: The nth decagonal number is 4n²-3n -/
theorem nthDecagonalNumber_spec (n : Nat) :
    nthDecagonalNumber n = 4 * n * n - 3 * n :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask279