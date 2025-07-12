-- Synthesis Task 171: Pentagon perimeter

namespace NumpySpec.DafnyBenchmarks.SynthesisTask171

/-- Calculate the perimeter of a regular pentagon -/
def pentagonPerimeter (side : Int) : Int :=
  sorry

/-- Specification: Pentagon perimeter is 5 times the side length -/
theorem pentagonPerimeter_spec (side : Int)
    (h_positive : side > 0) :
    pentagonPerimeter side = 5 * side :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask171