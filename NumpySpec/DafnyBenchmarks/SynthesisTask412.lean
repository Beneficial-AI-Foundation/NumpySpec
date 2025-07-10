/-
Dafny to Lean 4 translation of synthesis task 412
Remove odd numbers from an array of numbers
-/

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace NumpySpec.DafnyBenchmarks.SynthesisTask412

/-- Predicate to check if a number is even -/
def isEven (n : Int) : Bool :=
  n % 2 = 0

/-- Remove odd numbers from an array, returning only even numbers -/
def removeOddNumbers (arr : Array Int) : Id (List Int) :=
  sorry

/-- Specification: All numbers in output are even and exist in input,
    and all even numbers in input are in output -/
theorem removeOddNumbers_spec (arr : Array Int) :
  ⦃⌜True⌝⦄
  removeOddNumbers arr
  ⦃⇓evenList => ⌜
    (∀ i : Nat, i < evenList.length → 
      isEven (evenList[i]!) ∧ evenList[i]! ∈ arr.toList) ∧
    (∀ i : Nat, i < arr.size → isEven arr[i]! → arr[i]! ∈ evenList)
  ⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask412