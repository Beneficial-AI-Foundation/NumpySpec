/-!
{
  "name": "numpy.flatiter",
  "category": "Iterating over arrays",
  "description": "Flat iterator object to iterate over arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.flatiter.html",
  "doc": "Flat iterator object to iterate over arrays.\n\nA \`flatiter\` iterator is returned by \`\`x.flat\`\` for any array \`x\`. It allows iterating over the array as if it were a 1-D array, either in a for-loop or by calling its \`next\` method.\n\nIteration is done in row-major, C-style order (the last index varying the fastest). The iterator can also be indexed using basic slicing or advanced indexing.\n\nNotes\n-----\nA \`flatiter\` iterator can not be constructed directly from Python code by calling the \`flatiter\` constructor.",
  "code": "# C implementation - flatiter is implemented in C"
}
-/

-- TODO: Implement flatiter
