/-!
{
  "name": "numpy.place",
  "category": "Boolean/mask indexing",
  "description": "Change elements of an array based on conditional and input values",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.place.html",
  "doc": "Change elements of an array based on conditional and input values.\n\nSimilar to \`\`np.copyto(arr, vals, where=mask)\`\`, the difference is that \`place\` uses the first N elements of \`vals\`, where N is the number of True values in \`mask\`, while \`copyto\` uses the elements where \`mask\` is True.\n\nNote that \`extract\` does the exact opposite of \`place\`.\n\nParameters\n----------\narr : ndarray\n    Array to put data into.\nmask : array_like\n    Boolean mask array. Must have the same size as \`a\`.\nvals : 1-D sequence\n    Values to put into \`a\`. Only the first N elements are used, where N is the number of True values in \`mask\`. If \`vals\` is smaller than N, it will be repeated, and if elements of \`a\` are to be masked, this sequence must be non-empty.",
  "code": "# C implementation: from numpy._core.multiarray import _place as place"
}
-/

-- TODO: Implement place
