/-!
{
  "name": "numpy.datetime_data",
  "category": "Datetime metadata",
  "description": "Get information about the step size of a date or time type",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.datetime_data.html",
  "doc": "datetime_data(dtype, /)\n\nGet information about the step size of a date or time type.\n\nThe returned tuple can be passed as the second argument of \`numpy.datetime64\` and \`numpy.timedelta64\`.\n\nParameters\n----------\ndtype : dtype\n    The dtype object, which must be a \`datetime64\` or \`timedelta64\` type.\n\nReturns\n-------\nunit : str\n    The :ref:\`datetime unit <arrays.dtypes.dateunits>\` on which this dtype is based.\ncount : int\n    The number of base units in a step.\n\nExamples\n--------\n>>> import numpy as np\n>>> dt_25s = np.dtype('timedelta64[25s]')\n>>> np.datetime_data(dt_25s)\n('s', 25)\n>>> np.array(10, dt_25s).astype('timedelta64[s]')\narray(250, dtype='timedelta64[s]')\n\nThe result can be used to construct a datetime that uses the same units as a timedelta\n\n>>> np.datetime64('2010', np.datetime_data(dt_25s))\nnp.datetime64('2010-01-01T00:00:00','25s')",
  "code": "# C implementation for performance\n# Get information about the step size of a date or time type\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: C implementation in numpy/_core/src/multiarray/datetime.c"
}
-/

-- TODO: Implement datetime_data
