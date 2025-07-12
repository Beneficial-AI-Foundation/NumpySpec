/-!
{
  "name": "DTypeLike",
  "category": "Core Type Aliases",
  "description": "Union type representing objects that can be converted to dtypes",
  "url": "https://numpy.org/doc/stable/reference/typing.html#numpy.typing.DTypeLike",
  "doc": "A union type representing objects that can be coerced into a dtype.\n\nAmong others this includes the likes of:\n- Type objects (e.g. np.int32)\n- Character codes (e.g. 'i4')\n- Objects with a .dtype attribute\n- Tuples for structured types\n- None (which gives the default dtype)\n\nThe DTypeLike type tries to avoid creation of dtype objects using dictionary of fields like np.dtype({'field1': ..., 'field2': ..., ...}) and direct usage of dictionaries as a dtype is disallowed.",
  "code": "# From numpy._typing._dtype_like.py\nDTypeLike: TypeAlias = Union[\n    dtype[Any],\n    # default data type (float64)\n    None,\n    # array-scalar types and generic types\n    type[Any],\n    # character codes, type strings or comma-separated fields, e.g., 'float64'\n    str,\n    # (flexible_dtype, itemsize)\n    tuple[_DTypeLikeNested, int],\n    # (fixed_dtype, shape)\n    tuple[_DTypeLikeNested, _ShapeLike],\n    # (base_dtype, new_dtype)\n    tuple[_DTypeLikeNested, _DTypeLikeNested],\n    # a list of fields\n    list[tuple[str, _DTypeLikeNested]],\n    # (field_name, field_dtype, field_shape)\n    _DTypeDict,\n    # e.g., [('x', '<i4'), ('y', '<i4')]\n    tuple[_DTypeLikeNested, ...],\n]"
}
-/

-- TODO: Implement DTypeLike
