/-!
{
  "name": "numpy.strings.isnumeric",
  "category": "String information",
  "description": "For each element, return True if there are only numeric characters in the element",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.isnumeric.html",
  "doc": "For each element, return True if there are only numeric characters in the element.\n\nNumeric characters include digit characters, and all characters that have the Unicode numeric value property.\n\nParameters\n----------\na : array_like, with \`str_\` or \`StringDType\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def isnumeric(a):\n    \"\"\"\n    For each element, return True if there are only numeric\n    characters in the element.\n\n    Numeric characters include digit characters, and all characters\n    that have the Unicode numeric value property, e.g. \`\`U+2155,\n    VULGAR FRACTION ONE FIFTH\`\`.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Array of booleans of same shape as \`\`a\`\`.\n\n    See Also\n    --------\n    str.isnumeric\n\n    Examples\n    --------\n    >>> np.strings.isnumeric(['123', '123abc', '9.0', '1/4', '\\u2155'])\n    array([ True, False, False, False,  True])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _isnumeric_ufunc(a)"
}
-/

-- TODO: Implement isnumeric
