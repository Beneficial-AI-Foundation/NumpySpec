-- Synthesis Task 77: Check if divisible by 11

namespace NumpySpec.DafnyBenchmarks.SynthesisTask77

/-- Check if an integer is divisible by 11 -/
def isDivisibleBy11 (n : Int) : Bool :=
  sorry

/-- Specification: Returns true iff n is divisible by 11 -/
theorem isDivisibleBy11_spec (n : Int) :
    isDivisibleBy11 n = (n % 11 = 0) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask77