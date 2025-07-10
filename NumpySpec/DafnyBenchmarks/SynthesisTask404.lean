/-
Dafny to Lean 4 translation of synthesis task 404
Find minimum of two integers
-/

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace NumpySpec.DafnyBenchmarks.SynthesisTask404

/-- Min: Returns the minimum of two integers -/
def min (a b : Int) : Id Int :=
  sorry

/-- Specification: The result is either a or b, and is less than or equal to both -/
theorem min_spec (a b : Int) :
  ⦃⌜True⌝⦄
  min a b
  ⦃⇓minValue => ⌜
    (minValue = a ∨ minValue = b) ∧ 
    minValue ≤ a ∧ 
    minValue ≤ b
  ⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask404