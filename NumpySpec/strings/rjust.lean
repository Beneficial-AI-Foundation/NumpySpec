import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.strings.rjust",
  "category": "String operations",
  "description": "Return an array with the elements of a right-justified in a string of length width",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.rjust.html",
  "doc": "Return an array with the elements of \`a\` right-justified in a string of length \`width\`.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nwidth : array_like, with any integer dtype\n    The length of the resulting strings, unless \`\`width < str_len(a)\`\`.\nfillchar : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    The character to use for padding. Default is space.\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types",
  "code": "def rjust(a, width, fillchar=' '):\n    \"\"\"\n    Return an array with the elements of \`a\` right-justified in a\n    string of length \`width\`.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    width : array_like, with any integer dtype\n        The length of the resulting strings, unless \`\`width < str_len(a)\`\`.\n    fillchar : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype, optional\n        The character to use for padding. Default is space.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    See Also\n    --------\n    ljust, center\n\n    Examples\n    --------\n    >>> np.strings.rjust(['hello', 'world'], 10, fillchar='*')\n    array(['*****hello', '*****world'], dtype='<U10')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    fillchar = np.asanyarray(fillchar, dtype=a.dtype)\n    width = np.asanyarray(width)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if not _is_string_dtype(fillchar.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if width.dtype.kind not in \"iu\":\n        raise TypeError(f\"expected an integer array-like, got {width.dtype}\")\n    if np.any(str_len(fillchar) != 1):\n        raise TypeError(\"The fill character must be exactly one character long\")\n    return _center_ljust_rjust_ufunc(a, width, fillchar, 2)"
}
-/

open Std.Do

/-- numpy.strings.rjust: Return an array with the elements of a right-justified in a string of length width.

    Right-justifies each string in the input array by padding it with the specified
    fill character (default is space) to reach the specified width. If the original
    string is longer than or equal to the width, it remains unchanged.

    Parameters:
    - a: Input array of strings
    - width: Target width for each string
    - fillchar: Character to use for padding (must be exactly one character)
    
    Returns:
    - Array where each string is right-justified to the specified width
    
    Mathematical Properties:
    1. Length preservation: If original.length >= width, return original unchanged
    2. Right-justification: If original.length < width, pad on the left with fillchar
    3. Padding placement: Original string appears as suffix in the result
    4. Character preservation: Original string appears as contiguous substring
    5. Width compliance: Result length equals max(original.length, width)
-/
def rjust {n : Nat} (a : Vector String n) (width : Nat) (fillchar : String) : Id (Vector String n) :=
  sorry

/-- Specification: rjust returns a vector where each string is right-justified
    to the specified width using the given fill character.

    Precondition: The fillchar must be exactly one character long
    Postcondition: Each result string either remains unchanged (if already >= width)
    or is right-justified with left padding to reach the target width
    
    Mathematical Properties:
    1. Length preservation: If original string length >= target width, return original
    2. Right-justification: If original string length < target width, pad left with fillchar
    3. Padding placement: Padding appears as prefix, original string as suffix
    4. Character preservation: Original string appears as contiguous substring
    5. Width compliance: Result length equals max(original.length, target_width)
    6. Fill character usage: Padding uses the specified fill character exclusively
-/
theorem rjust_spec {n : Nat} (a : Vector String n) (width : Nat) (fillchar : String)
    (h_fillchar : fillchar.length = 1) :
    ⦃⌜fillchar.length = 1⌝⦄
    rjust a width fillchar
    ⦃⇓result => ⌜∀ i : Fin n, 
        let orig := a.get i
        let res := result.get i
        -- Case 1: Original string is already >= width, no padding needed
        (orig.length ≥ width → res = orig) ∧
        -- Case 2: Original string is < width, left padding is added for right-justification
        (orig.length < width → 
            res.length = width ∧
            res.endsWith orig ∧
            (∃ padding : String, res = padding ++ orig ∧ 
                padding.length = width - orig.length ∧
                ∀ c ∈ padding.data, c = fillchar.get ⟨0, by simp [h_fillchar]⟩)) ∧
        -- Sanity check: Result length is always max(orig.length, width)
        res.length = max orig.length width⌝⦄ := by
  sorry
