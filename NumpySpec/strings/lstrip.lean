/-!
{
  "name": "numpy.strings.lstrip",
  "category": "String operations",
  "description": "For each element in a, return a copy with the leading characters removed",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.lstrip.html",
  "doc": "For each element in \`a\`, return a copy with the leading characters removed.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nchars : array_like with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    The characters to be removed. If None, whitespace characters are removed.\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types",
  "code": "def lstrip(a, chars=None):\n    \"\"\"\n    For each element in \`a\`, return a copy with the leading characters\n    removed.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    chars : array_like with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype, optional\n        The \`\`chars\`\` argument is a string specifying the set of\n        characters to be removed. If \`\`None\`\`, the \`\`chars\`\`\n        argument defaults to removing whitespace. The \`\`chars\`\` argument\n        is not a prefix or suffix; rather, all combinations of its\n        values are stripped.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    See Also\n    --------\n    str.lstrip\n\n    Examples\n    --------\n    >>> c = np.array(['aAaAaA', '  aA  ', 'abBABba'])\n    >>> np.strings.lstrip(c, 'a')\n    array(['AaAaA', '  aA  ', 'bBABba'], dtype='<U7')\n    >>> np.strings.lstrip(c, 'A')\n    array(['aAaAaA', '  aA  ', 'abBABba'], dtype='<U7')\n    >>> np.strings.lstrip(c)\n    array(['aAaAaA', 'aA  ', 'abBABba'], dtype='<U7')\n\n    \"\"\"\n    if chars is None:\n        return _lstrip_whitespace_ufunc(a)\n    return _lstrip_chars_ufunc(a, chars)"
}
-/

-- TODO: Implement lstrip
