import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.strings.ljust: Return an array with the elements left-justified in a string of length width.

    Left-justifies each string in the input array by padding it with the specified
    fill character (default is space) to reach the specified width. If the original
    string is longer than or equal to the width, it remains unchanged.

    Parameters:
    - a: Input array of strings
    - width: Target width for each string
    - fillchar: Character to use for padding (must be exactly one character)
    
    Returns:
    - Array where each string is left-justified to the specified width
-/
def ljust {n : Nat} (a : Vector String n) (width : Nat) (fillchar : String) : Id (Vector String n) :=
  sorry

/-- Specification: ljust returns a vector where each string is left-justified
    to the specified width using the given fill character.

    Precondition: The fillchar must be exactly one character long
    Postcondition: Each result string either remains unchanged (if already >= width)
    or is left-justified with padding to reach the target width
-/
theorem ljust_spec {n : Nat} (a : Vector String n) (width : Nat) (fillchar : String)
    (h_fillchar : fillchar.length = 1) :
    ⦃⌜fillchar.length = 1⌝⦄
    ljust a width fillchar
    ⦃⇓result => ⌜∀ i : Fin n, 
        let orig := a.get i
        let res := result.get i
        -- Case 1: Original string is already >= width, no padding needed
        (orig.length ≥ width → res = orig) ∧
        -- Case 2: Original string is < width, padding is added
        (orig.length < width → 
            res.length = width ∧
            res.startsWith orig ∧
            (∃ padding : String, res = orig ++ padding ∧ padding.length = width - orig.length)) ∧
        -- Sanity check: Result length is always max(orig.length, width)
        res.length = max orig.length width⌝⦄ := by
  sorry
