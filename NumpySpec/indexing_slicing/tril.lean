/-!
{
  "name": "numpy.tril",
  "category": "Diagonal operations",
  "description": "Lower triangle of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.tril.html",
  "doc": "Lower triangle of an array.\n\nReturn a copy of an array with elements above the \`k\`-th diagonal zeroed. For arrays with \`\`ndim\`\` exceeding 2, \`tril\` will apply to the final two axes.\n\nParameters\n----------\nm : array_like, shape (..., M, N)\n    Input array.\nk : int, optional\n    Diagonal above which to zero elements. \`k = 0\` (the default) is the main diagonal, \`k < 0\` is below it and \`k > 0\` is above.\n\nReturns\n-------\ntril : ndarray, shape (..., M, N)\n    Lower triangle of \`m\`, of same shape and data-type as \`m\`.",
  "code": "@array_function_dispatch(_trilu_dispatcher)\ndef tril(m, k=0):\n    \"\"\"\n    Lower triangle of an array.\n\n    Return a copy of an array with elements above the \`k\`-th diagonal zeroed.\n    For arrays with \`\`ndim\`\` exceeding 2, \`tril\` will apply to the final two\n    axes.\n\n    Parameters\n    ----------\n    m : array_like, shape (..., M, N)\n        Input array.\n    k : int, optional\n        Diagonal above which to zero elements.  \`k = 0\` (the default) is the\n        main diagonal, \`k < 0\` is below it and \`k > 0\` is above.\n\n    Returns\n    -------\n    tril : ndarray, shape (..., M, N)\n        Lower triangle of \`m\`, of same shape and data-type as \`m\`.\n    \"\"\"\n    m = asanyarray(m)\n    mask = tri(*m.shape[-2:], k=k, dtype=bool)\n\n    return where(mask, m, zeros(1, m.dtype))"
}
-/

-- TODO: Implement tril
