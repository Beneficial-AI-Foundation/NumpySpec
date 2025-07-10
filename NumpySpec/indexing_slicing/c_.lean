/-!
{
  "name": "numpy.c_",
  "category": "Advanced indexing",
  "description": "Translates slice objects to concatenation along the second axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.c_.html",
  "doc": "Translates slice objects to concatenation along the second axis.\n\nThis is short-hand for \`\`np.r_['-1,2,0', index expression]\`\`, which is useful because of its common occurrence. In particular, arrays will be stacked along their last axis after being upgraded to at least 2-D with 1's post-pended to the shape (column vectors made out of 1-D arrays).",
  "code": "# numpy.c_ is an instance of CClass which implements special indexing behavior"
}
-/

-- TODO: Implement c_
