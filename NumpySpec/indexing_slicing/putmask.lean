/-!
{
  "name": "numpy.putmask",
  "category": "Boolean/mask indexing",
  "description": "Changes elements of an array based on conditional and input values",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.putmask.html",
  "doc": "Changes elements of an array based on conditional and input values.\n\nSets \`\`a.flat[n] = values[n]\`\` for each n where \`\`mask.flat[n]==True\`\`.\n\nIf \`values\` is not the same size as \`a\` and \`mask\` then it will repeat. This gives behavior different from \`\`a[mask] = values\`\`.\n\nParameters\n----------\na : array_like\n    Target array.\nmask : array_like\n    Boolean mask array. It has to be the same shape as \`a\`.\nvalues : array_like\n    Values to put into \`a\` where \`mask\` is True. If \`values\` is smaller than \`a\` it will be repeated.",
  "code": "# C implementation: from numpy._core import putmask"
}
-/

-- TODO: Implement putmask
