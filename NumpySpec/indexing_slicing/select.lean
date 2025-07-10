/-!
{
  "name": "numpy.select",
  "category": "Basic indexing",
  "description": "Return an array drawn from elements in choicelist, depending on conditions",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.select.html",
  "doc": "Return an array drawn from elements in choicelist, depending on conditions.\n\nParameters\n----------\ncondlist : list of bool ndarrays\n    The list of conditions which determine from which array in \`choicelist\`\n    the output elements are taken. When multiple conditions are satisfied,\n    the first one encountered in \`condlist\` is used.\nchoicelist : list of ndarrays\n    The list of arrays from which the output elements are taken. It has\n    to be of the same length as \`condlist\`.\ndefault : scalar, optional\n    The element inserted in \`output\` when all conditions evaluate to False.\n\nReturns\n-------\noutput : ndarray\n    The output at position m is the m-th element of the array in\n    \`choicelist\` where the m-th element of the corresponding array in\n    \`condlist\` is True.",
  "code": "@array_function_dispatch(_select_dispatcher)\ndef select(condlist, choicelist, default=0):\n    \"\"\"\n    Return an array drawn from elements in choicelist, depending on conditions.\n\n    Parameters\n    ----------\n    condlist : list of bool ndarrays\n        The list of conditions which determine from which array in \`choicelist\`\n        the output elements are taken. When multiple conditions are satisfied,\n        the first one encountered in \`condlist\` is used.\n    choicelist : list of ndarrays\n        The list of arrays from which the output elements are taken. It has\n        to be of the same length as \`condlist\`.\n    default : scalar, optional\n        The element inserted in \`output\` when all conditions evaluate to False.\n\n    Returns\n    -------\n    output : ndarray\n        The output at position m is the m-th element of the array in\n        \`choicelist\` where the m-th element of the corresponding array in\n        \`condlist\` is True.\n    \"\"\"\n    # [Implementation details in the actual function]"
}
-/

-- TODO: Implement select
