/-!
{
  "name": "numpy.indices",
  "category": "Index generation",
  "description": "Return an array representing the indices of a grid",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.indices.html",
  "doc": "Return an array representing the indices of a grid.\n\nCompute an array where the subarrays contain index values 0, 1, ... varying only along the corresponding axis.\n\nParameters\n----------\ndimensions : sequence of ints\n    The shape of the grid.\ndtype : dtype, optional\n    Data type of the result.\nsparse : boolean, optional\n    Return a sparse representation of the grid instead of a dense representation.\n\nReturns\n-------\ngrid : one ndarray or tuple of ndarrays\n    If sparse is False:\n        Returns one array of grid indices, \`\`grid.shape = (len(dimensions),) + tuple(dimensions)\`\`.\n    If sparse is True:\n        Returns a tuple of arrays, with \`\`grid[i].shape = (1, ..., dimensions[i], ..., 1)\`\` with dimensions[i] in the ith place.",
  "code": "# Implementation in numpy/lib/_index_tricks_impl.py or numpy/_core/numeric.py"
}
-/

-- TODO: Implement indices
