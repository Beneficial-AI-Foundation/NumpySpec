import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.lstrip",
  "category": "String operations",
  "description": "For each element in a, return a copy with the leading characters removed",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.lstrip.html",
  "doc": "For each element in \`a\`, return a copy with the leading characters removed.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nchars : array_like with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    The characters to be removed. If None, whitespace characters are removed.\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types",
  "code": "def lstrip(a, chars=None):\n    \"\"\"\n    For each element in \`a\`, return a copy with the leading characters\n    removed.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    chars : array_like with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype, optional\n        The \`\`chars\`\` argument is a string specifying the set of\n        characters to be removed. If \`\`None\`\`, the \`\`chars\`\`\n        argument defaults to removing whitespace. The \`\`chars\`\` argument\n        is not a prefix or suffix; rather, all combinations of its\n        values are stripped.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    See Also\n    --------\n    str.lstrip\n\n    Examples\n    --------\n    >>> c = np.array(['aAaAaA', '  aA  ', 'abBABba'])\n    >>> np.strings.lstrip(c, 'a')\n    array(['AaAaA', '  aA  ', 'bBABba'], dtype='<U7')\n    >>> np.strings.lstrip(c, 'A')\n    array(['aAaAaA', '  aA  ', 'abBABba'], dtype='<U7')\n    >>> np.strings.lstrip(c)\n    array(['aAaAaA', 'aA  ', 'abBABba'], dtype='<U7')\n\n    \"\"\"\n    if chars is None:\n        return _lstrip_whitespace_ufunc(a)\n    return _lstrip_chars_ufunc(a, chars)"
}
-/

/-- For each element in a vector, return a copy with the leading characters removed. -/
def lstrip {n : Nat} (a : Vector String n) (chars : Option String) : Id (Vector String n) :=
  sorry

/-- Specification: lstrip removes leading characters from each string in the vector.
    If chars is None, whitespace characters are removed.
    If chars is provided, any combination of those characters is removed from the beginning. -/
theorem lstrip_spec {n : Nat} (a : Vector String n) (chars : Option String) :
    ⦃⌜True⌝⦄
    lstrip a chars
    ⦃⇓result => 
      ∀ i : Fin n, 
        (chars.isNone → (result.get i = (a.get i).trimLeft)) ∧
        (chars.isSome → 
          ∃ k : Nat, k ≤ (a.get i).length ∧ 
          result.get i = (a.get i).drop k ∧
          (∀ j : Nat, j < k → (a.get i).get ⟨j, by sorry⟩ ∈ chars.get!.toList) ∧
          (k < (a.get i).length → (a.get i).get ⟨k, by sorry⟩ ∉ chars.get!.toList))⦄ := by
  sorry
