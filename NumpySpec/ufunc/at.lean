/-!
{
  "name": "ufunc.at",
  "category": "In-place Method",
  "description": "Performs operation in-place at specified array indices",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ufunc.at.html",
  "signature": "ufunc.at(a, indices, b=None, /)",
  "parameters": {
    "a": "Array to perform in-place operation on",
    "indices": "Indices where operation is applied",
    "b": "Second operand for binary ufuncs"
  },
  "example": "a = np.array([1, 2, 3, 4])\nnp.add.at(a, [0, 1, 2, 2], 1)\n# a becomes [2, 3, 5, 4]",
  "notes": [
    "Performs unbuffered in-place operation",
    "Useful for updating specific array elements"
  ]
}
-/

-- TODO: Implement at
