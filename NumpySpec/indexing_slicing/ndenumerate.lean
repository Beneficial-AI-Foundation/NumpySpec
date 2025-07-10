/-!
{
  "name": "numpy.ndenumerate",
  "category": "Iterating over arrays",
  "description": "Multidimensional index iterator",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ndenumerate.html",
  "doc": "Multidimensional index iterator.\n\nReturn an iterator yielding pairs of array coordinates and values.\n\nParameters\n----------\narr : ndarray\n    Input array.",
  "code": "@set_module('numpy')\nclass ndenumerate:\n    \"\"\"\n    Multidimensional index iterator.\n\n    Return an iterator yielding pairs of array coordinates and values.\n\n    Parameters\n    ----------\n    arr : ndarray\n      Input array.\n    \"\"\"\n\n    def __init__(self, arr):\n        self.iter = np.asarray(arr).flat\n\n    def __next__(self):\n        return self.iter.coords, next(self.iter)\n\n    def __iter__(self):\n        return self"
}
-/

-- TODO: Implement ndenumerate
