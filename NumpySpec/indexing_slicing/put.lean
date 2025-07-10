/-!
{
  "name": "numpy.put",
  "category": "Basic indexing",
  "description": "Replaces specified elements of an array with given values",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.put.html",
  "doc": "Replaces specified elements of an array with given values.\n\nThe indexing works on the flattened target array.\n\nParameters\n----------\na : ndarray\n    Target array.\nind : array_like\n    Target indices, interpreted as integers.\nv : array_like\n    Values to place in \`a\` at target indices.\nmode : {'raise', 'wrap', 'clip'}, optional\n    Specifies how out-of-bounds indices will behave.\n\nReturns\n-------\nNone",
  "code": "@array_function_dispatch(_put_dispatcher)\ndef put(a, ind, v, mode='raise'):\n    \"\"\"\n    Replaces specified elements of an array with given values.\n\n    The indexing works on the flattened target array.\n\n    Parameters\n    ----------\n    a : ndarray\n        Target array.\n    ind : array_like\n        Target indices, interpreted as integers.\n    v : array_like\n        Values to place in \`a\` at target indices.\n    mode : {'raise', 'wrap', 'clip'}, optional\n        Specifies how out-of-bounds indices will behave.\n\n    Returns\n    -------\n    None\n    \"\"\"\n    try:\n        put = a.put\n    except AttributeError as e:\n        raise TypeError(f\"argument 1 must be numpy.ndarray, not {type(a)}\") from e\n\n    return put(ind, v, mode=mode)"
}
-/

-- TODO: Implement put
