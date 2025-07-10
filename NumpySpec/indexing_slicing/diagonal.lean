/-!
{
  "name": "numpy.diagonal",
  "category": "Diagonal operations",
  "description": "Return specified diagonals",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.diagonal.html",
  "doc": "Return specified diagonals.\n\nIf \`a\` is 2-D, returns the diagonal of \`a\` with the given offset, i.e., the collection of elements of the form \`\`a[i, i+offset]\`\`. If \`a\` has more than two dimensions, then the axes specified by \`axis1\` and \`axis2\` are used to determine the 2-D sub-array whose diagonal is returned. The shape of the resulting array can be determined by removing \`axis1\` and \`axis2\` and appending an index to the right equal to the size of the resulting diagonals.\n\nParameters\n----------\na : array_like\n    Array from which the diagonals are taken.\noffset : int, optional\n    Offset of the diagonal from the main diagonal. Can be positive or negative.\naxis1 : int, optional\n    Axis to be used as the first axis of the 2-D sub-arrays from which the diagonals should be taken.\naxis2 : int, optional\n    Axis to be used as the second axis of the 2-D sub-arrays from which the diagonals should be taken.\n\nReturns\n-------\narray_of_diagonals : ndarray\n    If \`a\` is 2-D, then a 1-D array containing the diagonal and of the same type as \`a\` is returned. If \`a\` has more than two dimensions, then the dimensions specified by \`axis1\` and \`axis2\` are removed, and a new axis inserted at the end corresponding to the diagonal.",
  "code": "@array_function_dispatch(_diagonal_dispatcher)\ndef diagonal(a, offset=0, axis1=0, axis2=1):\n    \"\"\"\n    Return specified diagonals.\n    \n    [Full docstring truncated for brevity]\n    \"\"\"\n    if isinstance(a, np.matrix):\n        # Optimize the common case where axis1, axis2 are 0, 1 and the\n        # array is 2D to avoid the array transpose (since matrix is strict 2D)\n        if axis1 == 0 and axis2 == 1 and a.ndim == 2:\n            return asarray(a)._diagonal_retval(\n                offset=offset, axis1=axis1, axis2=axis2\n            )\n        else:\n            return asanyarray(a).diagonal(\n                offset=offset, axis1=axis1, axis2=axis2\n            )\n    else:\n        return asanyarray(a).diagonal(offset=offset, axis1=axis1, axis2=axis2)"
}
-/

-- TODO: Implement diagonal
