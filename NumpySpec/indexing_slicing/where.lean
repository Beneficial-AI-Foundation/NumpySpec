/-!
{
  "name": "numpy.where",
  "category": "Boolean/mask indexing",
  "description": "Return elements chosen from x or y depending on condition",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.where.html",
  "doc": "Return elements chosen from \`x\` or \`y\` depending on \`condition\`.\n\nParameters\n----------\ncondition : array_like, bool\n    Where True, yield \`x\`, otherwise yield \`y\`.\nx, y : array_like\n    Values from which to choose. \`x\`, \`y\` and \`condition\` need to be broadcastable to some shape.\n\nReturns\n-------\nout : ndarray\n    If both \`x\` and \`y\` are given, the output array contains elements of \`x\` where \`condition\` is True, and those from \`y\` elsewhere.\n\nNote\n----\nIf only \`condition\` is given, return \`\`condition.nonzero()\`\`.",
  "code": "# C implementation: from numpy._core.multiarray import where"
}
-/

-- TODO: Implement where
