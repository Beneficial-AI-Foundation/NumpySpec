-- Synthesis Task 139: Circle circumference
-- Note: Using Float instead of Real since Mathlib is not available

namespace NumpySpec.DafnyBenchmarks.SynthesisTask139

/-- Pi approximation -/
def pi : Float := 3.14159265358979323846

/-- Calculate the circumference of a circle -/
def circleCircumference (radius : Float) : Float :=
  sorry

/-- Specification: Circle circumference is 2π times radius -/
theorem circleCircumference_spec (radius : Float)
    (h_positive : radius > 0) :
    circleCircumference radius = 2 * pi * radius :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask139