/-!
{
  "name": "numpy.strings.mod",
  "category": "String operations",
  "description": "Return (a % i), that is pre-Python 2.6 string formatting (interpolation), element-wise for a pair of array_likes of string objects",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.mod.html",
  "doc": "Return (a % i), that is pre-Python 2.6 string formatting (interpolation), element-wise for a pair of array_likes of string objects.\n\nFor example, if \`a = '%.2f hours'\` and \`i = 2.5\`, the result is '2.50 hours'.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\ni : array_like\n    A single Python object, or a sequence of objects, used for filling in the format string.\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types",
  "code": "def mod(a, values):\n    \"\"\"\n    Return (a % i), that is pre-Python 2.6 string formatting\n    (interpolation), element-wise for a pair of array_likes of \`\`bytes\`\`\n    or \`\`str\`\`.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    values : array_like\n        These values will be element-wise interpolated into array \`\`a\`\`.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    Examples\n    --------\n    >>> np.strings.mod(['Hello, %s', 'A is %i'], ['World', 10])\n    array(['Hello, World', 'A is 10'], dtype='<U12')\n\n    \"\"\"\n    if not np.isscalar(a):\n        a = np.asanyarray(a)\n    if not np.isscalar(values):\n        values = np.asanyarray(values)\n\n    if a.dtype.char == \"T\":\n        return _mod(a, values)\n    return _to_bytes_or_str_array(_mod(_to_string_dtype_array(a), values))"
}
-/

-- TODO: Implement mod
