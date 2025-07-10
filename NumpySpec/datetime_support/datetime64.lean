/-!
{
  "name": "numpy.datetime64",
  "category": "Datetime types",
  "description": "Create a datetime64 object representing an offset from 1970-01-01T00:00:00",
  "url": "https://numpy.org/doc/stable/reference/arrays.datetime.html#numpy.datetime64",
  "doc": "If created from a 64-bit integer, it represents an offset from \`\`1970-01-01T00:00:00\`\`. If created from string, the string can be in ISO 8601 date or datetime format.\n\nWhen parsing a string to create a datetime object, if the string contains a trailing timezone (A 'Z' or a timezone offset), the timezone will be dropped and a User Warning is given.\n\nDatetime64 objects should be considered to be UTC and therefore have an offset of +0000.\n\n>>> np.datetime64(10, 'Y')\nnp.datetime64('1980')\n>>> np.datetime64('1980', 'Y')\nnp.datetime64('1980')\n>>> np.datetime64(10, 'D')\nnp.datetime64('1970-01-11')\n\nSee :ref:\`arrays.datetime\` for more information.\n\n:Character code: \`\`'M'\`\`",
  "code": "# C implementation for performance\n# Create a datetime64 object representing an offset from 1970-01-01T00:00:00\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: C implementation in numpy/_core/src/multiarray/datetime.c"
}
-/

-- TODO: Implement datetime64
