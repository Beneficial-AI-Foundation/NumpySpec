/-!
{
  "name": "numpy.ndindex",
  "category": "Index generation",
  "description": "An N-dimensional iterator object to index arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ndindex.html",
  "doc": "An N-dimensional iterator object to index arrays.\n\nGiven the shape of an array, an \`ndindex\` instance iterates over the N-dimensional index of the array.",
  "code": "@set_module('numpy')\nclass ndindex:\n    \"\"\"\n    An N-dimensional iterator object to index arrays.\n\n    Given the shape of an array, an \`ndindex\` instance iterates over\n    the N-dimensional index of the array.\n    \"\"\"\n\n    def __init__(self, *shape):\n        if len(shape) == 1 and isinstance(shape[0], tuple):\n            shape = shape[0]\n        x = as_strided(_nx.zeros(1), shape=shape,\n                       strides=_nx.zeros_like(shape))\n        self._it = _nx.nditer(x, flags=['multi_index', 'zerosize_ok'],\n                              order='C')\n\n    def __iter__(self):\n        return self\n\n    def __next__(self):\n        next(self._it)\n        return self._it.multi_index"
}
-/

-- TODO: Implement ndindex
