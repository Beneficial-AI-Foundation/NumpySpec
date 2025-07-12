/-!
{
  "name": "ArrayLike",
  "category": "Core Type Aliases",
  "description": "Union type representing objects that can be converted to arrays",
  "url": "https://numpy.org/doc/stable/reference/typing.html#numpy.typing.ArrayLike",
  "doc": "A union type representing objects that can be coerced into an ndarray.\n\nAmong others this includes the likes of:\n- Scalars\n- (Nested) sequences\n- Objects implementing the __array__ protocol\n\nThe ArrayLike type tries to avoid creating object arrays by excluding certain types that would otherwise be valid. For example, ArrayLike does not include arbitrary sequences of strings to prevent string sequences from being interpreted as object arrays.",
  "code": "# From numpy._typing._array_like.py\n_ArrayLike = Union[\n    _SupportsArray[dtype[_ScalarT]],\n    _NestedSequence[_SupportsArray[dtype[_ScalarT]]],\n    # Accept also bare dtypes\n    # Sequence[Sequence] ... e.g. [[1, 2], [3, 4]]\n    _FiniteNestedSequence[_NumberLike | _BoolLike],\n    # Mypy can't handle extended precision datatypes\n    # _FiniteNestedSequence[str | bytes | _ExtendedPrecision],\n    _FiniteNestedSequence[str | bytes],\n]\n\n# The actual ArrayLike type\nArrayLike = _ArrayLike[Any]"
}
-/

-- TODO: Implement ArrayLike
