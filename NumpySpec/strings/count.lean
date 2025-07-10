/-!
{
  "name": "numpy.strings.count",
  "category": "String information",
  "description": "Returns an array with the number of non-overlapping occurrences of substring sub in the range [start, end]",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.count.html",
  "doc": "Returns an array with the number of non-overlapping occurrences of substring \`sub\` in the range [\`start\`, \`end\`].\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsub : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    The substring to search for.\nstart, end : array_like, with any integer dtype, optional\n    The range to look in, interpreted as slice notation.\n\nReturns\n-------\nout : ndarray\n    Output array of ints",
  "code": "def count(a, sub, start=0, end=None):\n    \"\"\"\n    Returns an array with the number of non-overlapping occurrences of\n    substring \`\`sub\`\` in the range [\`\`start\`\`, \`\`end\`\`].\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    sub : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        The substring to search for.\n\n    start, end : array_like, with any integer dtype, optional\n        The range to look in, interpreted as slice notation.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ints\n\n    See Also\n    --------\n    str.count\n\n    Examples\n    --------\n    >>> c = np.array(['aAaAaA', '  aA  ', 'abBABba'])\n    >>> np.strings.count(c, 'A')\n    array([3, 1, 1])\n    >>> np.strings.count(c, 'aA')\n    array([3, 1, 0])\n    >>> np.strings.count(c, 'A', start=1, end=4)\n    array([2, 1, 0])\n    >>> np.strings.count(c, 'A', start=1, end=3)\n    array([1, 0, 0])\n\n    \"\"\"\n    end = end if end is not None else np.iinfo(np.int64).max\n    return _count_ufunc(a, sub, start, end)"
}
-/

-- TODO: Implement count
