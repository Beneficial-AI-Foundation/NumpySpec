/-!
{
  "name": "numpy.fromstring",
  "category": "String I/O",
  "description": "A new 1-D array initialized from text data in a string",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fromstring.html",
  "doc": "A new 1-D array initialized from text data in a string. Deprecated since version 1.14: Passing sep='', the default, is deprecated since it will trigger the deprecated binary mode of this function. This mode interprets string as binary bytes, rather than ASCII text with decimal numbers.",
  "code": "# C implementation for performance\n# A new 1-D array initialized from text data in a string\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: C implementation in numpy/core/src/multiarray/ctors.c (PyArray_FromString)"
}
-/

-- TODO: Implement fromstring
