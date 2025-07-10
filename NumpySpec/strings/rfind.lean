/-!
{
  "name": "numpy.strings.rfind",
  "category": "String information",
  "description": "For each element, return the highest index in the string where substring sub is found, such that sub is contained within [start, end]",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.rfind.html",
  "doc": "For each element, return the highest index in the string where substring \`sub\` is found, such that \`sub\` is contained within [\`start\`, \`end\`].\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsub : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    The substring to search for.\nstart, end : array_like, with any integer dtype, optional\n    The range to look in, interpreted as slice notation.\n\nReturns\n-------\nout : ndarray\n    Output array of ints. Returns -1 if \`sub\` is not found.",
  "code": "def rfind(a, sub, start=0, end=None):\n    \"\"\"\n    For each element, return the highest index in the string where\n    substring \`\`sub\`\` is found, such that \`\`sub\`\` is contained within\n    [\`\`start\`\`, \`\`end\`\`].\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    sub : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        The substring to search for.\n\n    start, end : array_like, with any integer dtype, optional\n        The range to look in, interpreted as slice notation.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ints.  Returns -1 if \`\`sub\`\` is not found.\n\n    See Also\n    --------\n    str.rfind\n\n    Examples\n    --------\n    >>> a = np.array([\"Computer Science\"])\n    >>> np.strings.rfind(a, \"Science\", start=0, end=None)\n    array([9])\n\n    \"\"\"\n    end = end if end is not None else np.iinfo(np.int64).max\n    return _rfind_ufunc(a, sub, start, end)"
}
-/

-- TODO: Implement rfind
