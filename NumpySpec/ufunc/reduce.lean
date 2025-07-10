/-!
{
  "name": "ufunc.reduce",
  "category": "Reduction Method",
  "description": "Reduces array's dimension by applying ufunc along specified axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ufunc.reduce.html",
  "signature": "ufunc.reduce(array, axis=0, dtype=None, out=None, keepdims=False, initial=<no value>, where=True)",
  "parameters": {
    "array": "Array to be reduced",
    "axis": "Axis or axes along which to reduce",
    "dtype": "Data type for intermediate computations",
    "out": "Location for the result",
    "keepdims": "If True, axes which are reduced are left as dimensions with size one",
    "initial": "Starting value for the reduction",
    "where": "Boolean array for selective reduction"
  },
  "example": "np.multiply.reduce([2,3,5])  # Returns 30\nnp.add.reduce([[1,2],[3,4]], axis=0)  # Returns [4, 6]",
  "notes": [
    "For add.reduce, equivalent to sum()",
    "For multiply.reduce, equivalent to prod()",
    "Supports multi-axis reduction"
  ]
}
-/

-- TODO: Implement reduce
