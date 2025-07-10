/-!
{
  "name": "numpy.compress",
  "category": "Basic indexing",
  "description": "Return selected slices of an array along given axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.compress.html",
  "doc": "Return selected slices of an array along given axis.\n\nWhen working on a 1-D array, compress is equivalent to extract.\n\nParameters\n----------\ncondition : 1-D array of bools\n    Array that selects which entries to return.\na : array_like\n    Array from which to extract a part.\naxis : int, optional\n    Axis along which to take slices.\nout : ndarray, optional\n    Output array.\n\nReturns\n-------\ncompressed_array : ndarray\n    A copy of \`a\` without the slices along axis for which corresponding element in condition is False.",
  "code": "@array_function_dispatch(_compress_dispatcher)\ndef compress(condition, a, axis=None, out=None):\n    \"\"\"\n    Return selected slices of an array along given axis.\n\n    When working on a 1-D array, compress is equivalent to extract.\n\n    Parameters\n    ----------\n    condition : 1-D array of bools\n        Array that selects which entries to return.\n    a : array_like\n        Array from which to extract a part.\n    axis : int, optional\n        Axis along which to take slices.\n    out : ndarray, optional\n        Output array.\n\n    Returns\n    -------\n    compressed_array : ndarray\n        A copy of \`a\` without the slices along axis for which corresponding element in condition is False.\n    \"\"\"\n    return _wrapfunc(a, 'compress', condition, axis=axis, out=out)"
}
-/

-- TODO: Implement compress
