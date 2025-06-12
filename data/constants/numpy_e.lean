/-!
Simple Lean counterpart for the constant `numpy.e`.
-/

namespace numpy

/-- Euler's constant, base of natural logarithms. -/
noncomputable def e : ℝ :=
  Real.exp 1

end numpy
