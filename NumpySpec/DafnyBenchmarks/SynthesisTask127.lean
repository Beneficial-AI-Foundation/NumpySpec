/-
  Multiply two integers
  (Ported from Dafny synthesis task 127)
-/

import Std

namespace NumpySpec.DafnyBenchmarks.SynthesisTask127

/-- Multiply two integers -/
def multiply (a : Int) (b : Int) : Int := sorry

theorem multiply_spec (a b : Int) :
  multiply a b = a * b := by sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask127