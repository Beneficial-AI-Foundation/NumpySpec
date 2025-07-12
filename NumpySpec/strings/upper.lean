/-!
{
  "name": "numpy.strings.upper",
  "category": "String transformation",
  "description": "Return an array with the elements converted to uppercase",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.upper.html",
  "doc": "Return an array with the elements converted to uppercase.\n\nFor byte strings, this method is locale-dependent.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Input array\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input type",
  "code": "def upper(a):\n    \"\"\"\n    Return an array with the elements converted to uppercase.\n\n    For byte strings, this method is locale-dependent.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        Input array\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input type\n\n    See Also\n    --------\n    str.upper\n\n    Examples\n    --------\n    >>> c = np.array(['a1b c', '1bca', 'bca1']); c\n    array(['a1b c', '1bca', 'bca1'], dtype='<U5')\n    >>> np.strings.upper(c)\n    array(['A1B C', '1BCA', 'BCA1'], dtype='<U5')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _upper_ufunc(a)"
}
-/

-- TODO: Implement upper
