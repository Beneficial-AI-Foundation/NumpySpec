-- Synthesis Task 58: Check if two integers have opposite signs

namespace NumpySpec.DafnyBenchmarks.SynthesisTask58

/-- Check if two integers have opposite signs -/
def hasOppositeSign (a b : Int) : Bool :=
  sorry

/-- Specification: Returns true iff one is positive and the other is negative -/
theorem hasOppositeSign_spec (a b : Int) :
    hasOppositeSign a b = ((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask58