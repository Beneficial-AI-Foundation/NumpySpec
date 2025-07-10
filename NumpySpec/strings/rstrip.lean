/-!
{
  "name": "numpy.strings.rstrip",
  "category": "String operations",
  "description": "For each element in a, return a copy with the trailing characters removed",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.rstrip.html",
  "doc": "For each element in \`a\`, return a copy with the trailing characters removed.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nchars : array_like with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    The characters to be removed. If None, whitespace characters are removed.\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types",
  "code": "def rstrip(a, chars=None):\n    \"\"\"\n    For each element in \`a\`, return a copy with the trailing characters\n    removed.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    chars : array_like with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype, optional\n        The \`\`chars\`\` argument is a string specifying the set of\n        characters to be removed. If \`\`None\`\`, the \`\`chars\`\`\n        argument defaults to removing whitespace. The \`\`chars\`\` argument\n        is not a prefix or suffix; rather, all combinations of its\n        values are stripped.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    See Also\n    --------\n    str.rstrip\n\n    Examples\n    --------\n    >>> c = np.array(['aAaAaA', 'abBABba'], dtype='S7'); c\n    array([b'aAaAaA', b'abBABba'],\n          dtype='|S7')\n    >>> np.strings.rstrip(c, b'a')\n    array([b'aAaAaA', b'abBABb'],\n          dtype='|S7')\n    >>> np.strings.rstrip(c, b'A')\n    array([b'aAaAa', b'abBABba'],\n          dtype='|S7')\n\n    \"\"\"\n    if chars is None:\n        return _rstrip_whitespace_ufunc(a)\n    return _rstrip_chars_ufunc(a, chars)"
}
-/

-- TODO: Implement rstrip
