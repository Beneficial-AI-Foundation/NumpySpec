-- Synthesis Task 135: Calculate nth hexagonal number

namespace NumpySpec.DafnyBenchmarks.SynthesisTask135

/-- Calculate the nth hexagonal number -/
def nthHexagonalNumber (n : Nat) : Nat :=
  sorry

/-- Specification: The nth hexagonal number is n(2n-1) -/
theorem nthHexagonalNumber_spec (n : Nat) :
    nthHexagonalNumber n = n * (2 * n - 1) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask135