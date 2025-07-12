-- Synthesis Task 458: Calculate rectangle area

namespace NumpySpec.DafnyBenchmarks.SynthesisTask458

/-- Calculate the area of a rectangle -/
def rectangleArea (length width : Int) : Int :=
  sorry

/-- Specification: Rectangle area is length times width -/
theorem rectangleArea_spec (length width : Int)
    (h_length : length > 0)
    (h_width : width > 0) :
    rectangleArea length width = length * width :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask458