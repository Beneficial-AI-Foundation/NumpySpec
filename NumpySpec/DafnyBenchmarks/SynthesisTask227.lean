-- Synthesis Task 227: Find minimum of three integers

namespace NumpySpec.DafnyBenchmarks.SynthesisTask227

/-- Find the minimum of three integers -/
def minOfThree (a b c : Int) : Int :=
  sorry

/-- Specification: Result is the minimum and is one of the inputs -/
theorem minOfThree_spec (a b c : Int) :
    let min := minOfThree a b c
    min ≤ a ∧ min ≤ b ∧ min ≤ c ∧
    (min = a ∨ min = b ∨ min = c) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask227