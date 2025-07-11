import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- IsPerfectSquare: Check if a non-negative integer is a perfect square.
    
    Given a non-negative integer n, returns true if n is a perfect square
    (i.e., there exists an integer i such that i * i = n).
    
    Example: isPerfectSquare(16) = true, isPerfectSquare(15) = false
-/
def isPerfectSquare (n : Int) : Id Bool :=
  sorry

/-- Specification: isPerfectSquare returns true if and only if n is a perfect square.
    
    Precondition: n >= 0
    Postcondition: 
    - If result is true, then there exists i with 0 <= i <= n such that i * i = n
    - If result is false, then for all positive a where a*a < n, we have a*a ≠ n
-/
theorem isPerfectSquare_spec (n : Int) :
    ⦃⌜n ≥ 0⌝⦄
    isPerfectSquare n
    ⦃⇓result => ⌜
      (result = true → ∃ i : Int, 0 ≤ i ∧ i ≤ n ∧ i * i = n) ∧
      (result = false → ∀ a : Int, 0 < a * a ∧ a * a < n → a * a ≠ n)
    ⌝⦄ := by
  sorry