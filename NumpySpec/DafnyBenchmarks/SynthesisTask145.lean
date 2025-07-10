import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- MaxDifference: Find the maximum difference between any two elements in an array.
    
    Given an array with at least 2 elements, returns the maximum value of a[i] - a[j]
    for any valid indices i and j.
    
    Example: maxDifference([1, 5, 3]) could return 4 (5 - 1)
-/
def maxDifference (a : Array Int) : Id Int :=
  sorry

/-- Specification: maxDifference returns a value that is greater than or equal to 
    any difference between two elements in the array.
    
    Precondition: The array has at least 2 elements
    Postcondition: For all pairs of indices i,j, the difference a[i] - a[j] is at most the result
-/
theorem maxDifference_spec (a : Array Int) :
    ⦃⌜a.size > 1⌝⦄
    maxDifference a
    ⦃⇓diff => ⌜∀ i j : Fin a.size, a[i] - a[j] ≤ diff⌝⦄ := by
  sorry