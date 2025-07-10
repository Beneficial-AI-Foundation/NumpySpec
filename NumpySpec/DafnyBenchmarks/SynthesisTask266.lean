-- Synthesis Task 266: Lateral surface area of a cube

namespace NumpySpec.DafnyBenchmarks.SynthesisTask266

/-- Calculate the lateral surface area of a cube with given size -/
def lateralSurfaceArea (size : Int) : Int := 
  sorry

/-- Specification for lateralSurfaceArea function -/
theorem lateralSurfaceArea_spec (size : Int) (h_size : size > 0) :
  lateralSurfaceArea size = 4 * size * size := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask266