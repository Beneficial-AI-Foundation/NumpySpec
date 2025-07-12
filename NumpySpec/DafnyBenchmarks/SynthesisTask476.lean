import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Min: Find the minimum element in a non-empty list.
    
    Recursively finds the minimum element by comparing the last element
    with the minimum of the prefix.
-/
def min : List Int → Int
  | [] => 0  -- Should not happen given precondition
  | [a] => a
  | l => 
    let minPrefix := min (l.take (l.length - 1))
    let lastElem := l.getLast!
    if lastElem ≤ minPrefix then lastElem else minPrefix
termination_by l => l.length
decreasing_by sorry

/-- Max: Find the maximum element in a non-empty list.
    
    Recursively finds the maximum element by comparing the last element
    with the maximum of the prefix.
-/
def max : List Int → Int
  | [] => 0  -- Should not happen given precondition
  | [a] => a
  | l => 
    let maxPrefix := max (l.take (l.length - 1))
    let lastElem := l.getLast!
    if lastElem ≥ maxPrefix then lastElem else maxPrefix
termination_by l => l.length
decreasing_by sorry

/-- SumMinMax: Return the sum of the minimum and maximum elements in an array.
    
    Given a non-empty array, returns the sum of its minimum and maximum elements.
    
    Example: sumMinMax([3, 1, 4, 1, 5]) = 1 + 5 = 6
-/
def sumMinMax (a : Array Int) : Id Int :=
  sorry

/-- Specification: sumMinMax returns the sum of the minimum and maximum elements.
    
    Precondition: The array is non-empty
    Postcondition: The result equals max(a.toList) + min(a.toList)
-/
theorem sumMinMax_spec (a : Array Int) :
    ⦃⌜a.size > 0⌝⦄
    sumMinMax a
    ⦃⇓sum => ⌜sum = max a.toList + min a.toList⌝⦄ := by
  sorry