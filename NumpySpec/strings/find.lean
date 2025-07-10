/-!
{
  "name": "numpy.strings.find",
  "category": "String information",
  "description": "For each element, return the lowest index in the string where substring sub is found",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.find.html",
  "doc": "For each element, return the lowest index in the string where substring \`sub\` is found, such that \`sub\` is contained in the range [\`start\`, \`end\`].\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsub : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nstart, end : array_like, with any integer dtype, optional\n    The range to look in, interpreted as slice notation.\n\nReturns\n-------\nout : ndarray\n    Output array of ints. Returns -1 if \`sub\` is not found.",
  "code": "def find(a, sub, start=0, end=None):\n    \"\"\"\n    For each element, return the lowest index in the string where\n    substring \`\`sub\`\` is found, such that \`\`sub\`\` is contained in the\n    range [\`\`start\`\`, \`\`end\`\`].\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    sub : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        The substring to search for.\n\n    start, end : array_like, with any integer dtype, optional\n        The range to look in, interpreted as slice notation.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ints.  Returns -1 if \`\`sub\`\` is not found.\n\n    See Also\n    --------\n    str.find\n\n    Examples\n    --------\n    >>> a = np.array([\"NumPy is a Python library\"])\n    >>> np.strings.find(a, \"Python\", start=0, end=None)\n    array([11])\n\n    \"\"\"\n    end = end if end is not None else np.iinfo(np.int64).max\n    return _find_ufunc(a, sub, start, end)"
}
-/

-- TODO: Implement find
