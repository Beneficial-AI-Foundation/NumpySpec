/-!
{
  "name": "numpy.strings.isspace",
  "category": "String information",
  "description": "Returns true for each element if there are only whitespace characters in the string and there is at least one character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.isspace.html",
  "doc": "Returns true for each element if there are only whitespace characters in the string and there is at least one character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def isspace(a):\n    \"\"\"\n    Returns true for each element if there are only whitespace\n    characters in the string and there is at least one character,\n    false otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.isspace\n\n    Examples\n    --------\n    >>> a = np.array([' ', '\\\\t', '\\\\n', 'a'])\n    >>> np.strings.isspace(a)\n    array([ True,  True,  True, False])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _isspace_ufunc(a)"
}
-/

-- TODO: Implement isspace
