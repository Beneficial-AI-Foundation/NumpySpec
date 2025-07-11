/-
Dafny to Lean 4 translation of synthesis task 431
Check if two arrays have a common element
-/

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace NumpySpec.DafnyBenchmarks.SynthesisTask431

/-- Check if two arrays have at least one common element -/
def hasCommonElement (a b : Array Int) : Id Bool :=
  sorry

/-- Specification: result is true iff there exist indices where elements are equal -/
theorem hasCommonElement_spec (a b : Array Int) :
  ⦃⌜True⌝⦄
  hasCommonElement a b
  ⦃⇓result => ⌜
    (result = true ↔ ∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ∧
    (result = false ↔ ∀ i j, i < a.size → j < b.size → a[i]! ≠ b[j]!)
  ⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask431