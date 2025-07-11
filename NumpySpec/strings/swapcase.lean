/-!
{
  "name": "numpy.strings.swapcase",
  "category": "String transformation",
  "description": "Return element-wise a copy of the string with uppercase characters converted to lowercase and vice versa",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.swapcase.html",
  "doc": "Return element-wise a copy of the string with uppercase characters converted to lowercase and vice versa.\n\nFor byte strings, this method is locale-dependent.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Input array\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input type",
  "code": "def swapcase(a):\n    \"\"\"\n    Return element-wise a copy of the string with\n    uppercase characters converted to lowercase and vice versa.\n\n    For byte strings, this method is locale-dependent.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        Input array\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input type\n\n    See Also\n    --------\n    str.swapcase\n\n    Examples\n    --------\n    >>> c=np.array(['a1B c','1b Ca','b Ca1','cA1b'],'S5'); c\n    array([b'a1B c', b'1b Ca', b'b Ca1', b'cA1b'],\n          dtype='|S5')\n    >>> np.strings.swapcase(c)\n    array([b'A1b C', b'1B cA', b'B cA1', b'Ca1B'],\n          dtype='|S5')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _swapcase_ufunc(a)"
}
-/

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Return element-wise a copy of the string with uppercase characters converted to lowercase and vice versa -/
def swapcase {n : Nat} (a : Vector String n) : Id (Vector String n) :=
  sorry

/-- Specification: swapcase transforms each string by swapping the case of all alphabetic characters -/
theorem swapcase_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    swapcase a
    ⦃⇓result => ∀ i : Fin n, 
      (∀ c ∈ (a.get i).toList, c.isLower → (result.get i).toList.get? ((a.get i).toList.indexOf c) = some c.toUpper) ∧
      (∀ c ∈ (a.get i).toList, c.isUpper → (result.get i).toList.get? ((a.get i).toList.indexOf c) = some c.toLower) ∧
      (∀ c ∈ (a.get i).toList, ¬c.isAlpha → (result.get i).toList.get? ((a.get i).toList.indexOf c) = some c) ∧
      (result.get i).length = (a.get i).length⦄ := by
  sorry
