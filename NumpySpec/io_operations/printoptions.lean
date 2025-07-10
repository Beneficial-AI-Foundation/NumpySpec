/-!
{
  "name": "numpy.printoptions",
  "category": "String formatting",
  "description": "Context manager for setting print options",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.printoptions.html",
  "doc": "Context manager for setting print options.\n\n    Set print options for the scope of the \`with\` block, and restore the old\n    options at the end. See \`set_printoptions\` for the full description of\n    available options.\n\n    Examples\n    --------\n    >>> import numpy as np\n\n    >>> from numpy.testing import assert_equal\n    >>> with np.printoptions(precision=2):\n    ...     np.array([2.0]) / 3\n    array([0.67])\n\n    The \`as\`-clause of the \`with\`-statement gives the current print options:\n\n    >>>...",
  "code": "@set_module('numpy')\n@contextlib.contextmanager\ndef printoptions(*args, **kwargs):\n    \"\"\"Context manager for setting print options.\n\n    Set print options for the scope of the \`with\` block, and restore the old\n    options at the end. See \`set_printoptions\` for the full description of\n    available options.\n\n    Examples\n    --------\n    >>> import numpy as np\n\n    >>> from numpy.testing import assert_equal\n    >>> with np.printoptions(precision=2):\n    ...     np.array([2.0]) / 3\n    array([0.67])\n\n    The \`as\`-clause of the \`with\`-statement gives the current print options:\n\n    >>> with np.printoptions(precision=2) as opts:\n    ...      assert_equal(opts, np.get_printoptions())\n\n    See Also\n    --------\n    set_printoptions, get_printoptions\n\n    \"\"\"\n    token = _set_printoptions(*args, **kwargs)\n\n    try:\n        yield get_printoptions()\n    finally:\n        format_options.reset(token)"
}
-/

-- TODO: Implement printoptions
