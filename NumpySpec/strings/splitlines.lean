/-!
{
  "name": "numpy.strings.splitlines",
  "category": "String operations",
  "description": "For each element in a, return a list of the lines in the element, breaking at line boundaries",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.splitlines.html",
  "doc": "For each element in \`a\`, return a list of the lines in the element, breaking at line boundaries.\n\nLine breaks are not included in the resulting list unless keepends is given and true.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nkeepends : bool, optional\n    Line breaks are not included in the resulting list unless keepends is given and true.\n\nReturns\n-------\nout : ndarray\n    Output array of objects",
  "code": "def splitlines(a, keepends=None):\n    \"\"\"\n    For each element in \`\`a\`\`, return a list of the lines in the\n    element, breaking at line boundaries.\n\n    Line breaks are not included in the resulting list unless\n    \`\`keepends\`\` is given and true.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    keepends : bool, optional\n        Line breaks are not included in the resulting list unless\n        \`\`keepends\`\` is given and true.\n\n    Returns\n    -------\n    out : ndarray\n        Array of list objects\n\n    See Also\n    --------\n    str.splitlines\n\n    Examples\n    --------\n    >>> np.strings.splitlines([\"hello\\nworld\"])\n    array(list(['hello', 'world']), dtype=object)\n\n    >>> np.strings.splitlines([\"hello\\nworld\"], keepends=True)\n    array(list(['hello\\n', 'world']), dtype=object)\n\n    \"\"\"\n    return _splitlines(a, keepends)"
}
-/

-- TODO: Implement splitlines
