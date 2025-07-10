/-!
{
  "name": "numpy.s_",
  "category": "Advanced indexing",
  "description": "A nicer way to build up index tuples for arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.s_.html",
  "doc": "A nicer way to build up index tuples for arrays.\n\nUse one of the two predefined instances \`index_exp\` or \`s_\` rather than directly using IndexExpression.\n\nFor any index combination, including slicing and axis insertion, \`\`a[indices]\`\` is the same as \`\`a[np.index_exp[indices]]\`\` for any array \`a\`. However, \`\`np.index_exp[indices]\`\` can be used anywhere in Python code and returns a tuple of slice objects that can be used in the construction of complex index expressions.",
  "code": "# numpy.s_ is an instance of IndexExpression"
}
-/

-- TODO: Implement s_
