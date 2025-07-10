/-!
{
  "name": "numpy.strings.islower",
  "category": "String information",
  "description": "Returns true for each element if all cased characters in the string are lowercase and there is at least one cased character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.islower.html",
  "doc": "Returns true for each element if all cased characters in the string are lowercase and there is at least one cased character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def islower(a):\n    \"\"\"\n    Returns true for each element if all cased characters in the\n    string are lowercase and there is at least one cased character,\n    false otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.islower\n\n    Examples\n    --------\n    >>> np.strings.islower(\"GHC\")\n    array(False)\n    >>> np.strings.islower(\"ghc\")\n    array(True)\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _islower_ufunc(a)"
}
-/

-- TODO: Implement islower
