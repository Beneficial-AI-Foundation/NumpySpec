/-!
{
  "name": "numpy.r_",
  "category": "Advanced indexing",
  "description": "Translates slice objects to concatenation along the first axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.r_.html",
  "doc": "Translates slice objects to concatenation along the first axis.\n\nThis is a simple way to build up arrays quickly. There are two use cases.\n\n1. If the index expression contains comma separated arrays, then stack them along their first axis.\n2. If the index expression contains slice notation or scalars then create a 1-D array with a range indicated by the slice notation.\n\nIf slice notation is used, the syntax \`\`start:stop:step\`\` is equivalent to \`\`np.arange(start, stop, step)\`\` inside of the brackets. However, if \`\`step\`\` is an imaginary number (i.e. 100j) then its integer portion is interpreted as a number-of-points desired and the start and stop are inclusive. In other words \`\`start:stop:stepj\`\` is interpreted as \`\`np.linspace(start, stop, step, endpoint=1)\`\` inside of the brackets. After expansion of slice notation, all comma separated sequences are concatenated together.",
  "code": "# numpy.r_ is an instance of RClass which implements special indexing behavior"
}
-/

-- TODO: Implement r_
