/-!
{
  "name": "numpy.is_busday",
  "category": "Business day operations",
  "description": "Calculates which of the given dates are valid days, and which are not",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.is_busday.html",
  "doc": "is_busday(dates, weekmask='1111100', holidays=None, busdaycal=None, out=None)\n\nCalculates which of the given dates are valid days, and which are not.\n\nParameters\n----------\ndates : array_like of datetime64[D]\n    The array of dates to process.\nweekmask : str or array_like of bool, optional\n    A seven-element array indicating which of Monday through Sunday are valid days. May be specified as a length-seven list or array, like [1,1,1,1,1,0,0]; a length-seven string, like '1111100'; or a string like \"Mon Tue Wed Thu Fri\", made up of 3-character abbreviations for weekdays, optionally separated by white space. Valid abbreviations are: Mon Tue Wed Thu Fri Sat Sun\nholidays : array_like of datetime64[D], optional\n    An array of dates to consider as invalid dates. They may be specified in any order, and NaT (not-a-time) dates are ignored. This list is saved in a normalized form that is suited for fast calculations of valid days.\nbusdaycal : busdaycalendar, optional\n    A \`busdaycalendar\` object which specifies the valid days. If this parameter is provided, neither weekmask nor holidays may be provided.\nout : array of bool, optional\n    If provided, this array is filled with the result.\n\nReturns\n-------\nout : array of bool\n    An array with the same shape as \`\`dates\`\`, containing True for each valid day, and False for each invalid day.",
  "code": "# C implementation for performance\n# Calculates which of the given dates are valid days, and which are not\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: C implementation in numpy/_core/src/multiarray/datetime_busday.c"
}
-/

-- TODO: Implement is_busday
