/-!
{
  "name": "numpy.testing.rundocs",
  "category": "Test Running",
  "description": "Run doctests found in the given file",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.rundocs.html",
  "doc": "Run doctests found in the given file.\n\nBy default \`rundocs\` raises an AssertionError on failure.",
  "code": "def rundocs(filename=None, raise_on_error=True):\n    \"\"\"\n    Run doctests found in the given file.\n\n    By default \`rundocs\` raises an AssertionError on failure.\n\n    Parameters\n    ----------\n    filename : str\n        The path to the file for which the doctests are run.\n    raise_on_error : bool\n        Whether to raise an AssertionError when a doctest fails. Default is\n        True.\n\n    Notes\n    -----\n    The doctests can be run by the user/developer by adding the \`\`doctests\`\`\n    argument to the \`\`test()\`\` call. For example, to run all tests (including\n    doctests) for \`numpy.lib\`::\n\n        >>> np.lib.test(doctests=True)  # doctest: +SKIP\n    \"\"\"\n    from numpy._core import arange\n    import doctest\n\n    if filename is None:\n        f = sys._getframe(1)\n        filename = f.f_globals['__file__']\n    name = os.path.splitext(os.path.basename(filename))[0]\n    m = sys.modules.get(name)\n\n    if m is None:\n        raise ImportError(name)\n\n    tests = doctest.DocTestFinder().find(m)\n    runner = doctest.DocTestRunner(verbose=True)\n\n    msg = \"Some doctests failed:\\n\"\n    had_failure = False\n\n    for test in tests:\n        failures, tries = runner.run(test)\n\n        if failures > 0:\n            had_failure = True\n            msg += \"\\n\".join(\n                [test.name, \"-\"*70, runner.failures[0][0].getvalue()])\n\n    if had_failure and raise_on_error:\n        raise AssertionError(msg)"
}
-/

-- TODO: Implement rundocs
