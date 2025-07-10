/-!
{
  "name": "ufunc.outer",
  "category": "Outer Product Method",
  "description": "Apply ufunc to all pairs (a, b) with a in A and b in B",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ufunc.outer.html",
  "signature": "ufunc.outer(A, B, /, **kwargs)",
  "parameters": {
    "A": "First input array",
    "B": "Second input array",
    "**kwargs": "Additional keyword arguments passed to the ufunc"
  },
  "example": "np.multiply.outer([1, 2, 3], [4, 5, 6])\n# Returns:\n# array([[ 4,  5,  6],\n#        [ 8, 10, 12],\n#        [12, 15, 18]])",
  "notes": [
    "Result has dimension A.ndim + B.ndim",
    "More general than numpy.outer which only works on 1-D arrays"
  ]
}
-/

-- TODO: Implement outer
