/-!
{
  "name": "numpy.strings.isupper",
  "category": "String information",
  "description": "Return true for each element if all cased characters in the string are uppercase and there is at least one character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.isupper.html",
  "doc": "Return true for each element if all cased characters in the string are uppercase and there is at least one character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def isupper(a):\n    \"\"\"\n    Return true for each element if all cased characters in the\n    string are uppercase and there is at least one character, false\n    otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.isupper\n\n    Examples\n    --------\n    >>> np.strings.isupper(\"GHC\")\n    array(True)\n    >>> a = np.array([\"hello\", \"HELLO\", \"Hello\"])\n    >>> np.strings.isupper(a)\n    array([False,  True, False])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _isupper_ufunc(a)"
}
-/

-- TODO: Implement isupper
