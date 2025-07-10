/-!
{
  "name": "numpy.unravel_index",
  "category": "Index generation",
  "description": "Converts a flat index or array of flat indices into a tuple of coordinate arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.unravel_index.html",
  "doc": "Converts a flat index or array of flat indices into a tuple of coordinate arrays.\n\nParameters\n----------\nindices : array_like\n    An integer array whose elements are indices into the flattened version of an array of dimensions shape.\nshape : tuple of ints\n    The shape of the array to use for unraveling indices.\norder : {'C', 'F'}, optional\n    Determines whether the indices should be viewed as indexing in row-major (C-style) or column-major (Fortran-style) order.\n\nReturns\n-------\nunraveled_coords : tuple of ndarray\n    Each array in the tuple has the same shape as the indices array.",
  "code": "# C implementation: from numpy._core.multiarray import unravel_index"
}
-/

-- TODO: Implement unravel_index
