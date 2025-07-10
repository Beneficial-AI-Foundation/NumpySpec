/-!
{
  "name": "numpy.extract",
  "category": "Boolean/mask indexing",
  "description": "Return the elements of an array that satisfy some condition",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.extract.html",
  "doc": "Return the elements of an array that satisfy some condition.\n\nThis is equivalent to \`\`np.compress(ravel(condition), ravel(arr))\`\`. If \`condition\` is boolean \`\`np.extract\`\` is equivalent to \`\`arr[condition]\`\`.\n\nNote that \`place\` does the exact opposite of \`extract\`.\n\nParameters\n----------\ncondition : array_like\n    An array whose nonzero or True entries indicate the elements of \`arr\` to extract.\narr : array_like\n    Input array of the same size as \`condition\`.\n\nReturns\n-------\nextract : ndarray\n    Rank 1 array of values from \`arr\` where \`condition\` is True.",
  "code": "@array_function_dispatch(_extract_dispatcher)\ndef extract(condition, arr):\n    \"\"\"\n    Return the elements of an array that satisfy some condition.\n\n    This is equivalent to \`\`np.compress(ravel(condition), ravel(arr))\`\`.  If\n    \`condition\` is boolean \`\`np.extract\`\` is equivalent to \`\`arr[condition]\`\`.\n\n    Note that \`place\` does the exact opposite of \`extract\`.\n\n    Parameters\n    ----------\n    condition : array_like\n        An array whose nonzero or True entries indicate the elements of \`arr\`\n        to extract.\n    arr : array_like\n        Input array of the same size as \`condition\`.\n\n    Returns\n    -------\n    extract : ndarray\n        Rank 1 array of values from \`arr\` where \`condition\` is True.\n    \"\"\"\n    return _nx.take(ravel(arr), nonzero(ravel(condition))[0])"
}
-/

-- TODO: Implement extract
