/-!
{
  "name": "numpy.strings.split",
  "category": "String operations",
  "description": "For each element in a, return a list of the words in the string, using sep as the delimiter string",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.split.html",
  "doc": "For each element in \`a\`, return a list of the words in the string, using \`sep\` as the delimiter string.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsep : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    If \`sep\` is not specified or None, any whitespace string is a separator.\nmaxsplit : array_like, with any integer dtype, optional\n    If \`maxsplit\` is given, at most \`maxsplit\` splits are done.\n\nReturns\n-------\nout : ndarray\n    Output array of objects",
  "code": "def split(a, sep=None, maxsplit=None):\n    \"\"\"\n    For each element in \`\`a\`\`, return a list of the words in the\n    string, using \`\`sep\`\` as the delimiter string.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    sep : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype, optional\n       If \`\`sep\`\` is not specified or \`\`None\`\`, any whitespace string\n       is a separator.\n\n    maxsplit : array_like, with any integer dtype\n       If \`\`maxsplit\`\` is given, at most \`\`maxsplit\`\` splits are done.\n\n    Returns\n    -------\n    out : ndarray\n        Array of list objects\n\n    See Also\n    --------\n    str.split, rsplit\n\n    Examples\n    --------\n    >>> x = np.array(\"Numpy is nice!\")\n    >>> np.strings.split(x, \" \")\n    array(list(['Numpy', 'is', 'nice!']), dtype=object)\n\n    >>> np.strings.split(x, \" \", 1)\n    array(list(['Numpy', 'is nice!']), dtype=object)\n\n    \"\"\"\n    if not np.isscalar(a):\n        a = np.asanyarray(a)\n    if a.dtype.char == \"T\":\n        return _split(a, sep, maxsplit)\n    return _to_bytes_or_str_array(_split(_to_string_dtype_array(a), sep, maxsplit))"
}
-/

-- TODO: Implement split
