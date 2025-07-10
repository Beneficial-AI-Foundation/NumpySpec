/-!
{
  "name": "numpy.strings.join",
  "category": "String operations",
  "description": "Return a string which is the concatenation of the strings in the sequence seq",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.join.html",
  "doc": "Return a string which is the concatenation of the strings in the sequence \`seq\`.\n\nParameters\n----------\nsep : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nseq : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types",
  "code": "def join(sep, seq):\n    \"\"\"\n    Return a string which is the concatenation of the strings in the\n    sequence \`\`seq\`\`.\n\n    Parameters\n    ----------\n    sep : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    seq : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    See Also\n    --------\n    str.join\n\n    Examples\n    --------\n    >>> np.strings.join('-', 'osd')\n    array('o-s-d', dtype='<U5')\n\n    >>> np.strings.join(['-', '.'], ['ghc', 'osd'])\n    array(['g-h-c', 'o.s.d'], dtype='<U5')\n\n    \"\"\"\n    return _join(sep, seq)"
}
-/

-- TODO: Implement join
