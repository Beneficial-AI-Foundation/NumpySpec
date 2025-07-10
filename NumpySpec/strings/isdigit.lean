/-!
{
  "name": "numpy.strings.isdigit",
  "category": "String information",
  "description": "Returns true for each element if all characters in the string are digits, and there is at least one character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.isdigit.html",
  "doc": "Returns true for each element if all characters in the string are digits, and there is at least one character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def isdigit(a):\n    \"\"\"\n    Returns true for each element if all characters in the string are\n    digits, and there is at least one character, false otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.isdigit\n\n    Examples\n    --------\n    >>> a = np.array(['a', 'b', '0'], dtype='S1')\n    >>> np.strings.isdigit(a)\n    array([False, False,  True])\n    >>> a = np.array(['a', 'b', '0'], dtype='U1')\n    >>> np.strings.isdigit(a)\n    array([False, False,  True])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _isdigit_ufunc(a)"
}
-/

-- TODO: Implement isdigit
