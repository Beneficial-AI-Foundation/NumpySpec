-- Synthesis Task 257: Swap two integers

namespace NumpySpec.DafnyBenchmarks.SynthesisTask257

/-- Swap two integers and return as a list -/
def swap (a b : Int) : List Int :=
  sorry

/-- Specification: Swap returns [b, a] -/
theorem swap_spec (a b : Int) :
    let result := swap a b
    result.length = 2 ∧
    result[0]! = b ∧
    result[1]! = a :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask257