/-!
{
  "name": "numpy.strings.decode",
  "category": "String encoding",
  "description": "Decode byte strings using the codec",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.decode.html",
  "doc": "Calls \`\`bytes.decode\`\` element-wise.\n\nParameters\n----------\na : array_like, with \`bytes_\` dtype\n    Input byte array\nencoding : str, optional\n    The name of an encoding. Default is 'utf-8'\nerrors : str, optional\n    Specifies how to handle encoding errors.\n    Default is 'strict'\n\nReturns\n-------\nout : ndarray\n    Output array of \`str_\` dtype",
  "code": "def decode(a, encoding='utf-8', errors='strict'):\n    \"\"\"\n    Calls :meth:\`bytes.decode\` element-wise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`bytes_\`\` dtype\n\n    encoding : str, optional\n        The name of an encoding\n\n    errors : str, optional\n        Specifies how to handle encoding errors\n\n    Returns\n    -------\n    out : ndarray\n\n    See Also\n    --------\n    :py:meth:\`bytes.decode\`\n\n    Notes\n    -----\n    The set of available codecs comes from the Python standard library,\n    and may be extended at runtime.  For more information, see the\n    :mod:\`codecs\` module.\n\n    Examples\n    --------\n    >>> np.strings.decode(b'\\\\xc3\\\\xa9')\n    array('é', dtype='<U1')\n\n    \"\"\"\n    return _to_bytes_or_str_array(\n        _vec_string_with_args(a, np.str_, 'decode', (encoding, errors)),\n        np.str_)"
}
-/

-- TODO: Implement decode
