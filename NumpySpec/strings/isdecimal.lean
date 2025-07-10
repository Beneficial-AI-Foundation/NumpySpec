/-!
{
  "name": "numpy.strings.isdecimal",
  "category": "String information",
  "description": "For each element, return True if there are only decimal characters in the element",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.isdecimal.html",
  "doc": "For each element, return True if there are only decimal characters in the element.\n\nDecimal characters include digit characters, and all characters that can be used to form decimal-radix numbers.\n\nParameters\n----------\na : array_like, with \`str_\` or \`StringDType\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def isdecimal(a):\n    \"\"\"\n    For each element, return True if there are only decimal\n    characters in the element.\n\n    Decimal characters include digit characters, and all characters\n    that can be used to form decimal-radix numbers,\n    e.g. \`\`U+0660, ARABIC-INDIC DIGIT ZERO\`\`.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Array of booleans identical in shape to \`\`a\`\`.\n\n    See Also\n    --------\n    isdigit\n\n    Examples\n    --------\n    >>> np.strings.isdecimal(['12345', '4.99', '123ABC', ''])\n    array([ True, False, False, False])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _isdecimal_ufunc(a)"
}
-/

-- TODO: Implement isdecimal
