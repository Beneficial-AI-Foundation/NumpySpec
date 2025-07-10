/-!
{
  "name": "numpy.nonzero",
  "category": "Boolean/mask indexing",
  "description": "Return the indices of the elements that are non-zero",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nonzero.html",
  "doc": "Return the indices of the elements that are non-zero.\n\nReturns a tuple of arrays, one for each dimension of \`a\`, containing the indices of the non-zero elements in that dimension. The values in \`a\` are always tested and returned in row-major, C-style order.\n\nParameters\n----------\na : array_like\n    Input array.\n\nReturns\n-------\ntuple_of_arrays : tuple\n    Indices of elements that are non-zero.",
  "code": "@array_function_dispatch(_nonzero_dispatcher)\ndef nonzero(a):\n    \"\"\"\n    Return the indices of the elements that are non-zero.\n\n    Returns a tuple of arrays, one for each dimension of \`a\`,\n    containing the indices of the non-zero elements in that\n    dimension. The values in \`a\` are always tested and returned in\n    row-major, C-style order.\n\n    Parameters\n    ----------\n    a : array_like\n        Input array.\n\n    Returns\n    -------\n    tuple_of_arrays : tuple\n        Indices of elements that are non-zero.\n    \"\"\"\n    return _wrapfunc(a, 'nonzero')"
}
-/

-- TODO: Implement nonzero
