/-!
{
  "name": "numpy.base_repr",
  "category": "Data exchange",
  "description": "Return a string representation of a number in the given base system",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.base_repr.html",
  "doc": "Return a string representation of a number in the given base system.\n\n    Parameters\n    ----------\n    number : int\n        The value to convert. Positive and negative values are handled.\n    base : int, optional\n        Convert \`number\` to the \`base\` number system. The valid range is 2-36,\n        the default value is 2.\n    padding : int, optional\n        Number of zeros padded on the left. Default is 0 (no padding).\n\n    Returns\n    -------\n    out : str\n        String representation of \`num...",
  "code": "@set_module('numpy')\ndef base_repr(number, base=2, padding=0):\n    \"\"\"\n    Return a string representation of a number in the given base system.\n\n    Parameters\n    ----------\n    number : int\n        The value to convert. Positive and negative values are handled.\n    base : int, optional\n        Convert \`number\` to the \`base\` number system. The valid range is 2-36,\n        the default value is 2.\n    padding : int, optional\n        Number of zeros padded on the left. Default is 0 (no padding).\n\n    Returns\n    -------\n    out : str\n        String representation of \`number\` in \`base\` system.\n\n    See Also\n    --------\n    binary_repr : Faster version of \`base_repr\` for base 2.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> np.base_repr(5)\n    '101'\n    >>> np.base_repr(6, 5)\n    '11'\n    >>> np.base_repr(7, base=5, padding=3)\n    '00012'\n\n    >>> np.base_repr(10, base=16)\n    'A'\n    >>> np.base_repr(32, base=16)\n    '20'\n\n    \"\"\"\n    digits = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'\n    if base > len(digits):\n        raise ValueError(\"Bases greater than 36 not handled in base_repr.\")\n    elif base < 2:\n        raise ValueError(\"Bases less than 2 not handled in base_repr.\")\n\n    num = abs(int(number))\n    res = []\n    while num:\n        res.append(digits[num % base])\n        num //= base\n    if padding:\n        res.append('0' * padding)\n    if number < 0:\n        res.append('-')\n    return ''.join(reversed(res or '0'))"
}
-/

-- TODO: Implement base_repr
