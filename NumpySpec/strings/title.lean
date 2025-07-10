/-!
{
  "name": "numpy.strings.title",
  "category": "String transformation",
  "description": "Return element-wise title cased version of string or unicode",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.title.html",
  "doc": "Return element-wise title cased version of string or unicode.\n\nTitle case words start with uppercase characters, all remaining cased characters are lowercase.\n\nFor byte strings, this method is locale-dependent.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Input array\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input type",
  "code": "def title(a):\n    \"\"\"\n    Return element-wise title cased version of string or unicode.\n\n    Title case words start with uppercase characters, all remaining cased\n    characters are lowercase.\n\n    For byte strings, this method is locale-dependent.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        Input array\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input type\n\n    See Also\n    --------\n    str.title\n\n    Examples\n    --------\n    >>> c=np.array(['a1b c','1b ca','b ca1','ca1b'],'S5'); c\n    array([b'a1b c', b'1b ca', b'b ca1', b'ca1b'],\n          dtype='|S5')\n    >>> np.strings.title(c)\n    array([b'A1B C', b'1B Ca', b'B Ca1', b'Ca1B'],\n          dtype='|S5')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _title_ufunc(a)"
}
-/

-- TODO: Implement title
