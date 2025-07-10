/-!
{
  "name": "numpy.strings.istitle",
  "category": "String information",
  "description": "Returns true for each element if the element is a titlecased string and there is at least one character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.istitle.html",
  "doc": "Returns true for each element if the element is a titlecased string and there is at least one character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def istitle(a):\n    \"\"\"\n    Returns true for each element if the element is a titlecased\n    string and there is at least one character, false otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.istitle\n\n    Examples\n    --------\n    >>> np.strings.istitle(\"Numpy Is Great\")\n    array(True)\n\n    >>> np.strings.istitle(\"Numpy is great\")\n    array(False)\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _istitle_ufunc(a)"
}
-/

-- TODO: Implement istitle
