/-!
{
  "name": "numpy.argwhere",
  "category": "Boolean/mask indexing",
  "description": "Find the indices of array elements that are non-zero, grouped by element",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.argwhere.html",
  "doc": "Find the indices of array elements that are non-zero, grouped by element.\n\nParameters\n----------\na : array_like\n    Input data.\n\nReturns\n-------\nindex_array : (N, a.ndim) ndarray\n    Indices of elements that are non-zero. Indices are grouped by element.\n    This array will have shape \`\`(N, a.ndim)\`\` where \`\`N\`\` is the number of\n    non-zero items.\n\nNotes\n-----\n\`\`np.argwhere(a)\`\` is almost the same as \`\`np.transpose(np.nonzero(a))\`\`, but produces the correct result for a 0D array.\n\nThe output of \`\`argwhere\`\` is not suitable for indexing arrays. For this purpose use \`\`nonzero(a)\`\` instead.",
  "code": "@array_function_dispatch(_argwhere_dispatcher)\ndef argwhere(a):\n    \"\"\"\n    Find the indices of array elements that are non-zero, grouped by element.\n\n    Parameters\n    ----------\n    a : array_like\n        Input data.\n\n    Returns\n    -------\n    index_array : (N, a.ndim) ndarray\n        Indices of elements that are non-zero. Indices are grouped by element.\n        This array will have shape \`\`(N, a.ndim)\`\` where \`\`N\`\` is the number of\n        non-zero items.\n\n    See Also\n    --------\n    where, nonzero\n\n    Notes\n    -----\n    \`\`np.argwhere(a)\`\` is almost the same as \`\`np.transpose(np.nonzero(a))\`\`,\n    but produces the correct result for a 0D array.\n\n    The output of \`\`argwhere\`\` is not suitable for indexing arrays.\n    For this purpose use \`\`nonzero(a)\`\` instead.\n    \"\"\"\n    # nonzero does not behave well on 0d, so promote to 1d\n    if np.ndim(a) == 0:\n        a = shape_base.atleast_1d(a)\n        # then remove the added dimension\n        return argwhere(a)[:, :0]\n    return transpose(nonzero(a))"
}
-/

-- TODO: Implement argwhere
