-- Synthesis Task 268: Calculate star number

namespace NumpySpec.DafnyBenchmarks.SynthesisTask268

/-- Calculate the nth star number -/
def starNumber (n : Nat) : Nat :=
  sorry

/-- Specification: The nth star number is 6n(n-1)+1 -/
theorem starNumber_spec (n : Nat) :
    starNumber n = 6 * n * (n - 1) + 1 :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask268