import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace NumpySpec.DafnyBenchmarks.SynthesisTask641

/-- Compute the nth nonagonal number -/
def nthNonagonalNumber (n : Int) : Int :=
  sorry

/-- Specification: The nth nonagonal number is n * (7 * n - 5) / 2 -/
theorem nthNonagonalNumber_spec (n : Int) (h : n ≥ 0) :
  nthNonagonalNumber n = n * (7 * n - 5) / 2 := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask641