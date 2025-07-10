/-!
{
  "name": "numpy.binary_repr",
  "category": "Data exchange",
  "description": "Return the binary representation of the input number as a string",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.binary_repr.html",
  "doc": "Return the binary representation of the input number as a string",
  "code": "@set_module('numpy')\ndef binary_repr(num, width=None):\n    \"\"\"\n    Return the binary representation of the input number as a string.\n\n    For negative numbers, if width is not given, a minus sign is added to the\n    front. If width is given, the two's complement of the number is\n    returned, with respect to that width.\n\n    In a two's-complement system negative numbers are represented by the two's\n    complement of the absolute value. This is the most common method of\n    representing signed integers on computers [1]_. A N-bit two's-complement\n    system can represent every integer in the range\n    :math:\`-2^{N-1}\` to :math:\`+2^{N-1}-1\`.\n\n    Parameters\n    ----------\n    num : int\n        Only an integer decimal number can be used.\n    width : int, optional\n        The length of the returned string if \`num\` is positive, or the length\n        of the two's complement if \`num\` is negative, provided that \`width\` is\n        at least a sufficient number of bits for \`num\` to be represented in\n        the designated form. If the \`width\` value is insufficient, an error is\n        raised.\n\n    Returns\n    -------\n    bin : str\n        Binary representation of \`num\` or two's complement of \`num\`.\n\n    See Also\n    --------\n    base_repr: Return a string representation of a number in the given base\n               system.\n    bin: Python's built-in binary representation generator of an integer.\n\n    Notes\n    -----\n    \`binary_repr\` is equivalent to using \`base_repr\` with base 2, but about 25x\n    faster.\n\n    References\n    ----------\n    .. [1] Wikipedia, \"Two's complement\",\n        https://en.wikipedia.org/wiki/Two's_complement"
}
-/

-- TODO: Implement binary_repr
