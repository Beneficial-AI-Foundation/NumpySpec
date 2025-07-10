/-!
{
  "name": "numpy.diagflat",
  "category": "Diagonal operations",
  "description": "Create a two-dimensional array with the flattened input as a diagonal",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.diagflat.html",
  "doc": "Create a two-dimensional array with the flattened input as a diagonal.\n\nParameters\n----------\nv : array_like\n    Input data, which is flattened and set as the \`k\`-th diagonal of the output.\nk : int, optional\n    Diagonal to set; 0, the default, corresponds to the \"main\" diagonal.\n\nReturns\n-------\nout : ndarray\n    The 2-D output array.",
  "code": "@array_function_dispatch(_diag_dispatcher)\ndef diagflat(v, k=0):\n    \"\"\"\n    Create a two-dimensional array with the flattened input as a diagonal.\n\n    Parameters\n    ----------\n    v : array_like\n        Input data, which is flattened and set as the \`k\`-th\n        diagonal of the output.\n    k : int, optional\n        Diagonal to set; 0, the default, corresponds to the \"main\" diagonal.\n\n    Returns\n    -------\n    out : ndarray\n        The 2-D output array.\n    \"\"\"\n    try:\n        wrap = v.__array_wrap__\n    except AttributeError:\n        wrap = None\n    v = asarray(v).ravel()\n    s = len(v)\n    n = s + abs(k)\n    res = zeros((n, n), v.dtype)\n    if (k >= 0):\n        i = arange(0, n - k, dtype=intp)\n        fi = i + k + i * n\n    else:\n        i = arange(0, n + k, dtype=intp)\n        fi = i + (i - k) * n\n    res.flat[fi] = v\n    if wrap:\n        return wrap(res)\n    return res"
}
-/

-- TODO: Implement diagflat
