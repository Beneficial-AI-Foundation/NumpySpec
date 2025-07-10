/-!
{
  "name": "NDArray",
  "category": "Core Type Aliases",
  "description": "Generic type alias for numpy.ndarray that is generic with respect to its dtype",
  "url": "https://numpy.org/doc/stable/reference/typing.html#numpy.typing.NDArray",
  "doc": "A generic type alias for numpy.ndarray[Any, dtype[+ScalarT]].\n\nCan be used during runtime for typing arrays with a given dtype and unspecified shape.\n\nExamples:\n>>> import numpy as np\n>>> import numpy.typing as npt\n\n>>> print(npt.NDArray)\nnumpy.ndarray[typing.Any, numpy.dtype[+_ScalarType_co]]\n\n>>> print(npt.NDArray[np.float64])\nnumpy.ndarray[typing.Any, numpy.dtype[numpy.float64]]\n\n>>> NDArrayInt = npt.NDArray[np.int_]\n>>> a: NDArrayInt = np.arange(10)",
  "code": "# From numpy._typing._array_like.py\nfrom ._shape import _AnyShape\n\n_ScalarT = TypeVar(\"_ScalarT\", bound=np.generic)\n\nNDArray: TypeAlias = np.ndarray[_AnyShape, dtype[_ScalarT]]"
}
-/

-- TODO: Implement NDArray
