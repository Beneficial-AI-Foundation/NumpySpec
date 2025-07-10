/-!
{
  "name": "numpy.strings.expandtabs",
  "category": "String transformation",
  "description": "Return a copy of each string element where all tab characters are replaced by spaces",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.expandtabs.html",
  "doc": "Return a copy of each string element where all tab characters are replaced by one or more spaces.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Input array\ntabsize : array_like, with any integer dtype, optional\n    Replace tabs with \`tabsize\` number of spaces. Default is 8.\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input type",
  "code": "def expandtabs(a, tabsize=8):\n    \"\"\"\n    Return a copy of each string element where all tab characters are\n    replaced by one or more spaces.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        Input array\n    tabsize : array_like, with any integer dtype, optional\n        Replace tabs with \`\`tabsize\`\` number of spaces.  If not given defaults\n        to 8 spaces.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input type\n\n    See Also\n    --------\n    str.expandtabs\n\n    Examples\n    --------\n    >>> a = np.array(['\\\\t\\\\tHello\\\\tworld'])\n    >>> np.strings.expandtabs(a)\n    array(['                Hello   world'], dtype='<U28')\n    \n    \"\"\"\n    a = np.asanyarray(a)\n    tabsize = np.asanyarray(tabsize)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if tabsize.dtype.kind not in \"iu\":\n        raise TypeError(f\"expected an integer array-like, got {tabsize.dtype}\")\n    return _expandtabs_ufunc(a, tabsize)"
}
-/

-- TODO: Implement expandtabs
