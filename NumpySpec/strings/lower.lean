/-!
{
  "name": "numpy.strings.lower",
  "category": "String transformation",
  "description": "Return an array with the elements converted to lowercase",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.lower.html",
  "doc": "Return an array with the elements of \`a\` converted to lowercase.\n\nFor byte strings, this method is locale-dependent.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Input array\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input type\n\nExamples\n--------\n>>> np.strings.lower(['HELLO', 'WORLD'])\narray(['hello', 'world'], dtype='<U5')",
  "code": "def lower(a):\n    \"\"\"\n    Return an array with the elements converted to lowercase.\n\n    For byte strings, this method is locale-dependent.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        Input array\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input type\n\n    See Also\n    --------\n    str.lower\n\n    Examples\n    --------\n    >>> c = np.array(['A1B C', '1BCA', 'BCA1']); c\n    array(['A1B C', '1BCA', 'BCA1'], dtype='<U5')\n    >>> np.strings.lower(c)\n    array(['a1b c', '1bca', 'bca1'], dtype='<U5')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _lower_ufunc(a)"
}
-/

-- TODO: Implement lower
