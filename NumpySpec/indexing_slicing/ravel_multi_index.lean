/-!
{
  "name": "numpy.ravel_multi_index",
  "category": "Index generation",
  "description": "Converts a tuple of index arrays into an array of flat indices",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ravel_multi_index.html",
  "doc": "Converts a tuple of index arrays into an array of flat indices, applying boundary modes to the multi-index.\n\nParameters\n----------\nmulti_index : tuple of array_like\n    A tuple of integer arrays, one array for each dimension.\ndims : tuple of ints\n    The shape of array into which the indices from multi_index apply.\nmode : {'raise', 'wrap', 'clip'}, optional\n    Specifies how out-of-bounds indices are handled.\norder : {'C', 'F'}, optional\n    Determines whether the multi-index should be viewed as indexing in row-major (C-style) or column-major (Fortran-style) order.\n\nReturns\n-------\nraveled_indices : ndarray\n    An array of indices into the flattened version of an array of dimensions dims.",
  "code": "# C implementation: from numpy._core.multiarray import ravel_multi_index"
}
-/

-- TODO: Implement ravel_multi_index
