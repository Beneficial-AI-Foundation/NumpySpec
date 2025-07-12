-- Synthesis Task 406: Check if integer is odd

namespace NumpySpec.DafnyBenchmarks.SynthesisTask406

/-- Check if an integer is odd -/
def isOdd (n : Int) : Bool :=
  sorry

/-- Specification: Returns true iff n is odd -/
theorem isOdd_spec (n : Int) :
    isOdd n = (n % 2 = 1) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask406