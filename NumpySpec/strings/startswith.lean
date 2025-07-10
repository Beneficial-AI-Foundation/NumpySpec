/-!
{
  "name": "numpy.strings.startswith",
  "category": "String information",
  "description": "Returns a boolean array which is True where the string element in a starts with prefix, otherwise False",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.startswith.html",
  "doc": "Returns a boolean array which is \`True\` where the string element in \`a\` starts with \`prefix\`, otherwise \`False\`.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nprefix : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nstart, end : array_like, with any integer dtype, optional\n    With optional \`start\`, test beginning at that position. With optional \`end\`, stop comparing at that position.\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def startswith(a, prefix, start=0, end=None):\n    \"\"\"\n    Returns a boolean array which is \`True\` where the string element\n    in \`\`a\`\` starts with \`\`prefix\`\`, otherwise \`\`False\`\`.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    prefix : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    start, end : array_like, with any integer dtype, optional\n        With optional \`\`start\`\`, test beginning at that position. With\n        optional \`\`end\`\`, stop comparing at that position.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.startswith\n\n    Examples\n    --------\n    >>> s = np.array(['foo', 'bar'])\n    >>> np.strings.startswith(s, 'fo')\n    array([ True, False])\n    >>> np.strings.startswith(s, 'o', start=1, end=2)\n    array([ True, False])\n\n    \"\"\"\n    end = end if end is not None else np.iinfo(np.int64).max\n    return _startswith_ufunc(a, prefix, start, end)"
}
-/

-- TODO: Implement startswith
