/-!
{
  "name": "numpy.strings.str_len",
  "category": "String information",
  "description": "Returns the length of each element",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.str_len.html",
  "doc": "Returns the length of each element.\n\nFor byte strings, this is the number of bytes. For Unicode strings, this is the number of Unicode code points.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of ints",
  "code": "def str_len(a):\n    \"\"\"\n    Returns the length of each element.\n\n    For byte strings, this is the number of bytes. For Unicode\n    strings, this is the number of Unicode code points.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ints\n\n    See Also\n    --------\n    len\n\n    Examples\n    --------\n    >>> a = np.array(['Grace Hopper Conference', 'Open Source Day'])\n    >>> np.strings.str_len(a)\n    array([23, 15])\n    >>> a = np.array([u'Р', u'о'])\n    >>> np.strings.str_len(a)\n    array([1, 1])\n    >>> a = np.array([['hello', 'world'], ['val', ''], [u'Р', u'о']])\n    >>> np.strings.str_len(a)\n    array([[5, 5],\n           [3, 0],\n           [1, 1]])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _str_len_ufunc(a)"
}
-/

-- TODO: Implement str_len
