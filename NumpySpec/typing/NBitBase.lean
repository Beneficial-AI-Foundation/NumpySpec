/-!
{
  "name": "NBitBase",
  "category": "Precision Types",
  "description": "A type representing numpy.number precision during static type checking",
  "url": "https://numpy.org/doc/stable/reference/typing.html#numpy.typing.NBitBase",
  "doc": "A type representing numpy.number precision during static type checking.\n\nUsed exclusively for static type checking, NBitBase represents the base of a hierarchical set of subclasses. Each subsequent subclass represents a lower level of precision, e.g. 64Bit > 32Bit > 16Bit.\n\n.. deprecated:: 2.3\n    NBitBase is deprecated and will be removed from numpy.typing in the future. Use @typing.overload or a TypeVar with a scalar-type as upper bound, instead.",
  "code": "# From numpy._typing._nbit_base.py\n@final  # Disallow the creation of arbitrary \`NBitBase\` subclasses\n@set_module(\"numpy.typing\")\nclass NBitBase:\n    \"\"\"\n    A type representing \`numpy.number\` precision during static type checking.\n\n    Used exclusively for static type checking, \`NBitBase\` represents the base\n    of a hierarchical set of subclasses. Each subsequent subclass represents\n    a lower level of precision, e.g. \`64Bit > 32Bit > 16Bit\`.\n\n    .. deprecated:: 2.3\n    Use \`@typing.overload\` or a \`TypeVar\` with a scalar-type as upper bound.\n    \"\"\"\n    def __init_subclass__(cls) -> None:\n        allowed_names = {\n            \"NBitBase\", \"_128Bit\", \"_96Bit\", \"_64Bit\", \"_32Bit\", \"_16Bit\", \"_8Bit\"\n        }\n        if cls.__name__ not in allowed_names:\n            raise TypeError('cannot inherit from final class \"NBitBase\"')\n        super().__init_subclass__()"
}
-/

-- TODO: Implement NBitBase
