/-!
{
  "name": "ufunc.reduceat",
  "category": "Reduction Method",
  "description": "Performs a (local) reduce with specified slices over a single axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ufunc.reduceat.html",
  "signature": "ufunc.reduceat(array, indices, axis=0, dtype=None, out=None)",
  "parameters": {
    "array": "Input array",
    "indices": "Indices specifying slice boundaries",
    "axis": "Axis along which to apply reduceat",
    "dtype": "Data type for intermediate computations",
    "out": "Location for the result"
  },
  "notes": [
    "Applies reduction to specified slices of the array",
    "Useful for segmented reductions"
  ]
}
-/

-- TODO: Implement reduceat
