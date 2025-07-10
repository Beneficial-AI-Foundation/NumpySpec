/-!
{
  "name": "numpy.nanmax",
  "category": "Order statistics",
  "description": "Return the maximum of an array or maximum along an axis, ignoring any NaNs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nanmax.html",
  "doc": "numpy.nanmax(a, axis=None, out=None, keepdims=<no value>, initial=<no value>, where=<no value>)\n\nReturn the maximum of an array or maximum along an axis, ignoring any NaNs.\nWhen all-NaN slices are encountered a RuntimeWarning is raised and NaN is returned for that slice.\n\nParameters\n----------\na : array_like\n    Array containing numbers whose maximum is desired. If a is not an array, a conversion is attempted.\naxis : {int, tuple of int, None}, optional\n    Axis or axes along which the maximum is computed. The default is to compute the maximum of the flattened array.\nout : ndarray, optional\n    Alternate output array in which to place the result. The default is None; if provided, it must have the same shape as the expected output.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\ninitial : scalar, optional\n    The minimum value of an output element. Must be present to allow computation on empty slice.\nwhere : array_like of bool, optional\n    Elements to compare for the maximum.\n\nReturns\n-------\nnanmax : ndarray\n    An array with the same shape as a, with the specified axis removed. If a is a 0-d array, or if axis is None, an ndarray scalar is returned.",
  "code": "# Implementation in numpy/lib/_nanfunctions_impl.py\n@array_function_dispatch(_nanmax_dispatcher)\ndef nanmax(a, axis=None, out=None, keepdims=np._NoValue, initial=np._NoValue,\n           where=np._NoValue):\n    \"\"\"\n    Return the maximum of an array or maximum along an axis, ignoring any NaNs.\n    \"\"\"\n    kwargs = {}\n    if initial is not np._NoValue:\n        kwargs['initial'] = initial\n    if where is not np._NoValue:\n        kwargs['where'] = where\n    if type(a) is not mu.ndarray:\n        try:\n            nanmax = a.nanmax\n        except AttributeError:\n            pass\n        else:\n            return nanmax(axis=axis, out=out, keepdims=keepdims, **kwargs)\n    return _nanextremum(np.max, a, axis, out, keepdims, initial, where)"
}
-/

-- TODO: Implement nanmax
