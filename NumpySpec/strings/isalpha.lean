/-!
{
  "name": "numpy.strings.isalpha",
  "category": "String information",
  "description": "Returns true for each element if all characters in the string are alphabetic and there is at least one character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.isalpha.html",
  "doc": "Returns true for each element if all characters in the string are alphabetic and there is at least one character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def isalpha(a):\n    \"\"\"\n    Returns true for each element if all characters in the string are\n    alphabetic and there is at least one character, false otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.isalpha\n\n    Examples\n    --------\n    >>> a = np.array(['a', '1', 'a1', ''])\n    >>> np.strings.isalpha(a)\n    array([ True,  False,  False, False])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _isalpha_ufunc(a)"
}
-/

-- TODO: Implement isalpha
