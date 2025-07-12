-- Synthesis Task 574: Calculate cylinder surface area

namespace NumpySpec.DafnyBenchmarks.SynthesisTask574

/-- Calculate the surface area of a cylinder -/
def cylinderSurfaceArea (radius height : Float) : Float :=
  sorry

/-- Specification: Surface area = 2πr(r+h) -/
theorem cylinderSurfaceArea_spec (radius height : Float) 
    (hr : radius > 0) (hh : height > 0) :
    cylinderSurfaceArea radius height = 2 * 3.14159265358979323846 * radius * (radius + height) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask574