/-!
{
  "name": "numpy.ix_",
  "category": "Advanced indexing",
  "description": "Construct an open mesh from multiple sequences",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ix_.html",
  "doc": "Construct an open mesh from multiple sequences.\n\nThis function takes N 1-D sequences and returns N outputs with N dimensions each, such that the shape is 1 in all but one dimension and the dimension with the non-unit shape value cycles through all N dimensions.\n\nParameters\n----------\nargs : 1-D sequences\n    Each sequence should be of integer or boolean type.\n    Boolean sequences will be interpreted as boolean masks.\n\nReturns\n-------\nout : tuple of ndarrays\n    N arrays with N dimensions each, with N the number of input\n    sequences. Together these arrays form an open mesh.",
  "code": "def ix_(*args):\n    \"\"\"\n    Construct an open mesh from multiple sequences.\n\n    This function takes N 1-D sequences and returns N outputs with N\n    dimensions each, such that the shape is 1 in all but one dimension\n    and the dimension with the non-unit shape value cycles through all\n    N dimensions.\n\n    Parameters\n    ----------\n    args : 1-D sequences\n        Each sequence should be of integer or boolean type.\n        Boolean sequences will be interpreted as boolean masks.\n\n    Returns\n    -------\n    out : tuple of ndarrays\n        N arrays with N dimensions each, with N the number of input\n        sequences. Together these arrays form an open mesh.\n    \"\"\"\n    out = []\n    nd = len(args)\n    for k, new in enumerate(args):\n        if not isinstance(new, _nx.ndarray):\n            new = np.asarray(new)\n            if new.size == 0:\n                new = new.astype(_nx.intp)\n        if new.ndim != 1:\n            raise ValueError(\"Cross index must be 1 dimensional\")\n        if issubdtype(new.dtype, _nx.bool):\n            new, = new.nonzero()\n        new = new.reshape((1,) * k + (new.size,) + (1,) * (nd - k - 1))\n        out.append(new)\n    return tuple(out)"
}
-/

-- TODO: Implement ix_
