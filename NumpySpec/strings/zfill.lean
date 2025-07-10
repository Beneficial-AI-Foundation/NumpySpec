/-!
{
  "name": "numpy.strings.zfill",
  "category": "String operations",
  "description": "Return the numeric string left-filled with zeros",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.zfill.html",
  "doc": "Return the numeric string left-filled with zeros.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nwidth : array_like, with any integer dtype\n    Width of string to left-fill elements in \`a\`\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input type",
  "code": "def zfill(a, width):\n    \"\"\"\n    Return the numeric string left-filled with zeros\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    width : array_like, with any integer dtype\n        Width of string to left-fill elements in \`\`a\`\`.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input type\n\n    See Also\n    --------\n    str.zfill\n\n    Examples\n    --------\n    >>> np.strings.zfill('1', 3)\n    array('001', dtype='<U3')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    width = np.asanyarray(width)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if width.dtype.kind not in \"iu\":\n        raise TypeError(f\"expected an integer array-like, got {width.dtype}\")\n    return _zfill_ufunc(a, width)"
}
-/

-- TODO: Implement zfill
