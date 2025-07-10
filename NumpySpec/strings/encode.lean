/-!
{
  "name": "numpy.strings.encode",
  "category": "String encoding",
  "description": "Encode strings using the codec",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.encode.html",
  "doc": "Calls \`\`str.encode\`\` element-wise.\n\nParameters\n----------\na : array_like, with \`str_\` or \`StringDType\` dtype\n    Input string array\nencoding : str, optional\n    The name of an encoding. Default is 'utf-8'\nerrors : str, optional\n    Specifies how to handle encoding errors.\n    Default is 'strict'\n\nReturns\n-------\nout : ndarray\n    Output array of \`bytes_\` dtype",
  "code": "def encode(a, encoding='utf-8', errors='strict'):\n    \"\"\"\n    Calls :meth:\`str.encode\` element-wise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    encoding : str, optional\n        The name of an encoding\n\n    errors : str, optional\n        Specifies how to handle encoding errors\n\n    Returns\n    -------\n    out : ndarray\n\n    See Also\n    --------\n    :py:meth:\`str.encode\`\n\n    Notes\n    -----\n    The set of available codecs comes from the Python standard library,\n    and may be extended at runtime.  For more information, see the\n    :mod:\`codecs\` module.\n\n    \"\"\"\n    return _to_bytes_or_str_array(\n        _vec_string_with_args(a, np.bytes_, 'encode', (encoding, errors)),\n        np.bytes_)"
}
-/

-- TODO: Implement encode
