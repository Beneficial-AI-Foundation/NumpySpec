/-!
{
  "name": "numpy.triu",
  "category": "Diagonal operations",
  "description": "Upper triangle of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.triu.html",
  "doc": "Upper triangle of an array.\n\nReturn a copy of an array with the elements below the \`k\`-th diagonal zeroed. For arrays with \`\`ndim\`\` exceeding 2, \`triu\` will apply to the final two axes.\n\nParameters\n----------\nm : array_like, shape (..., M, N)\n    Input array.\nk : int, optional\n    Diagonal below which to zero elements. \`k = 0\` (the default) is the main diagonal, \`k < 0\` is below it and \`k > 0\` is above.\n\nReturns\n-------\ntriu : ndarray, shape (..., M, N)\n    Upper triangle of \`m\`, of same shape and data-type as \`m\`.",
  "code": "@array_function_dispatch(_trilu_dispatcher)\ndef triu(m, k=0):\n    \"\"\"\n    Upper triangle of an array.\n\n    Return a copy of an array with the elements below the \`k\`-th diagonal\n    zeroed. For arrays with \`\`ndim\`\` exceeding 2, \`triu\` will apply to the\n    final two axes.\n\n    Parameters\n    ----------\n    m : array_like, shape (..., M, N)\n        Input array.\n    k : int, optional\n        Diagonal below which to zero elements.  \`k = 0\` (the default) is the\n        main diagonal, \`k < 0\` is below it and \`k > 0\` is above.\n\n    Returns\n    -------\n    triu : ndarray, shape (..., M, N)\n        Upper triangle of \`m\`, of same shape and data-type as \`m\`.\n    \"\"\"\n    m = asanyarray(m)\n    mask = tri(*m.shape[-2:], k=k-1, dtype=bool)\n\n    return where(mask, zeros(1, m.dtype), m)"
}
-/

-- TODO: Implement triu
