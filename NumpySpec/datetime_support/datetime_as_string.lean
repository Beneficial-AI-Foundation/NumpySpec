/-!
{
  "name": "numpy.datetime_as_string",
  "category": "Datetime conversion",
  "description": "Convert an array of datetimes into an array of strings",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.datetime_as_string.html",
  "doc": "datetime_as_string(arr, unit=None, timezone='naive', casting='same_kind')\n\nConvert an array of datetimes into an array of strings.\n\nParameters\n----------\narr : array_like of datetime64\n    The array of UTC timestamps to format.\nunit : str\n    One of None, 'auto', or a :ref:\`datetime unit <arrays.dtypes.dateunits>\`.\ntimezone : {'naive', 'UTC', 'local'} or tzinfo\n    Timezone information to use when displaying the datetime. If 'UTC', end with a Z to indicate UTC time. If 'local', convert to the local timezone first, and suffix with a +-#### timezone offset. If a tzinfo object, then do as with 'local', but use the specified timezone.\ncasting : {'no', 'equiv', 'safe', 'same_kind', 'unsafe'}\n    Casting to allow when changing between datetime units.\n\nReturns\n-------\nstr_arr : ndarray\n    An array of strings the same shape as \`arr\`.\n\nExamples\n--------\n>>> import numpy as np\n>>> import pytz\n>>> d = np.arange('2002-10-27T04:30', 4*60, 60, dtype='M8[m]')\n>>> d\narray(['2002-10-27T04:30', '2002-10-27T05:30', '2002-10-27T06:30',\n       '2002-10-27T07:30'], dtype='datetime64[m]')\n\nSetting the timezone to UTC shows the same information, but with a Z suffix\n\n>>> np.datetime_as_string(d, timezone='UTC')\narray(['2002-10-27T04:30Z', '2002-10-27T05:30Z', '2002-10-27T06:30Z',\n       '2002-10-27T07:30Z'], dtype='<U35')",
  "code": "# C implementation for performance\n# Convert an array of datetimes into an array of strings\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: C implementation in numpy/_core/src/multiarray/datetime_strings.c"
}
-/

-- TODO: Implement datetime_as_string
