/-!
{
  "name": "numpy.get_printoptions",
  "category": "String formatting",
  "description": "Return the current print options",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.get_printoptions.html",
  "doc": "Return the current print options.\n\n    Returns\n    -------\n    print_opts : dict\n        Dictionary of current print options with keys\n\n        - precision : int\n        - threshold : int\n        - edgeitems : int\n        - linewidth : int\n        - suppress : bool\n        - nanstr : str\n        - infstr : str\n        - sign : str\n        - formatter : dict of callables\n        - floatmode : str\n        - legacy : str or False\n\n        For a full description of these options, see \`set_printoptio...",
  "code": "@set_module('numpy')\ndef get_printoptions():\n    \"\"\"\n    Return the current print options.\n\n    Returns\n    -------\n    print_opts : dict\n        Dictionary of current print options with keys\n\n        - precision : int\n        - threshold : int\n        - edgeitems : int\n        - linewidth : int\n        - suppress : bool\n        - nanstr : str\n        - infstr : str\n        - sign : str\n        - formatter : dict of callables\n        - floatmode : str\n        - legacy : str or False\n\n        For a full description of these options, see \`set_printoptions\`.\n\n    See Also\n    --------\n    set_printoptions, printoptions\n\n    Examples\n    --------\n    >>> import numpy as np\n\n    >>> np.get_printoptions()\n    {'edgeitems': 3, 'threshold': 1000, ..., 'override_repr': None}\n\n    >>> np.get_printoptions()['linewidth']\n    75\n    >>> np.set_printoptions(linewidth=100)\n    >>> np.get_printoptions()['linewidth']\n    100\n\n    \"\"\"\n    opts = format_options.get().copy()\n    opts['legacy'] = {\n        113: '1.13', 121: '1.21', 125: '1.25', 201: '2.1',\n        202: '2.2', sys.maxsize: False,\n    }[opts['legacy']]\n    return opts"
}
-/

-- TODO: Implement get_printoptions
