-- Synthesis Task 17: Calculate square perimeter

namespace NumpySpec.DafnyBenchmarks.SynthesisTask17

/-- Calculate the perimeter of a square given its side length -/
def squarePerimeter (side : Nat) : Nat :=
  sorry

/-- Specification: Perimeter is 4 times the side length -/
theorem squarePerimeter_spec (side : Nat) (h : side > 0) :
    squarePerimeter side = 4 * side :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask17