/-!
{
  "name": "numpy.strings.index",
  "category": "String information",
  "description": "Like find, but raises ValueError when the substring is not found",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.index.html",
  "doc": "Like \`find\`, but raises \`ValueError\` when the substring is not found.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsub : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nstart, end : array_like, with any integer dtype, optional\n    The range to look in, interpreted as slice notation.\n\nReturns\n-------\nout : ndarray\n    Output array of ints.\n\nRaises\n------\nValueError\n    If substring not found.",
  "code": "def index(a, sub, start=0, end=None):\n    \"\"\"\n    Like :py:meth:\`find\`, but raises :py:exc:\`ValueError\` when the\n    substring is not found.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    sub : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    start, end : array_like, with any integer dtype, optional\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ints.\n\n    See Also\n    --------\n    find, str.index\n\n    Examples\n    --------\n    >>> a = np.array([\"Computer Science\"])\n    >>> np.strings.index(a, \"Science\", start=0, end=None)\n    array([9])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    sub = np.asanyarray(sub, dtype=a.dtype)\n\n    end = end if end is not None else np.iinfo(np.int64).max\n    out = _find_ufunc(a, sub, start, end)\n    if np.any(out == -1):\n        raise ValueError(\"substring not found\")\n    return out"
}
-/

-- TODO: Implement index
