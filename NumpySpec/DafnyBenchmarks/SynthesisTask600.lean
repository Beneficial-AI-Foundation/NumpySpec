-- Synthesis Task 600: Check if number is even

namespace NumpySpec.DafnyBenchmarks.SynthesisTask600

/-- Check if a number is even -/
def isEven (n : Int) : Bool :=
  sorry

/-- Specification: Returns true if n is even -/
theorem isEven_spec (n : Int) :
    isEven n = (n % 2 = 0) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask600