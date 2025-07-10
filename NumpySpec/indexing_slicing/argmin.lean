/-!
{
  "name": "numpy.argmin",
  "category": "Index finding",
  "description": "Returns the indices of the minimum values along an axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.argmin.html",
  "doc": "Returns the indices of the minimum values along an axis.\n\nParameters\n----------\na : array_like\n    Input array.\naxis : int, optional\n    By default, the index is into the flattened array, otherwise along the specified axis.\nout : array, optional\n    If provided, the result will be inserted into this array.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\n\nReturns\n-------\nindex_array : ndarray of ints\n    Array of indices into the array. It has the same shape as \`\`a.shape\`\` with the dimension along \`axis\` removed.\n\nNotes\n-----\nIn case of multiple occurrences of the minimum values, the indices corresponding to the first occurrence are returned.",
  "code": "@array_function_dispatch(_argmin_dispatcher)\ndef argmin(a, axis=None, out=None, *, keepdims=np._NoValue):\n    \"\"\"\n    Returns the indices of the minimum values along an axis.\n\n    Parameters\n    ----------\n    a : array_like\n        Input array.\n    axis : int, optional\n        By default, the index is into the flattened array, otherwise\n        along the specified axis.\n    out : array, optional\n        If provided, the result will be inserted into this array. It should\n        be of the appropriate shape and dtype.\n    keepdims : bool, optional\n        If this is set to True, the axes which are reduced are left\n        in the result as dimensions with size one. With this option,\n        the result will broadcast correctly against the array.\n\n    Returns\n    -------\n    index_array : ndarray of ints\n        Array of indices into the array. It has the same shape as \`\`a.shape\`\`\n        with the dimension along \`axis\` removed.\n\n    Notes\n    -----\n    In case of multiple occurrences of the minimum values, the indices\n    corresponding to the first occurrence are returned.\n    \"\"\"\n    kwds = {'keepdims': keepdims} if keepdims is not np._NoValue else {}\n    return _wrapfunc(a, 'argmin', axis=axis, out=out, **kwds)"
}
-/

-- TODO: Implement argmin
