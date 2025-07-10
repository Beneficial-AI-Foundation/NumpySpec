/-!
{
  "name": "numpy.mgrid",
  "category": "Advanced indexing",
  "description": "Dense multi-dimensional \"meshgrid\"",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.mgrid.html",
  "doc": "Dense multi-dimensional \"meshgrid\".\n\nAn instance of \`numpy.lib.index_tricks.nd_grid\` which returns a dense (or fleshed out) mesh-grid when indexed, so that each returned argument has the same shape. The dimensions and number of the output arrays are equal to the number of indexing dimensions. If the step length is not a complex number, then the stop is not inclusive.\n\nHowever, if the step length is a complex number (e.g. 5j), then the integer part of its magnitude is interpreted as specifying the number of points to create between the start and stop values, where the stop value is inclusive.",
  "code": "# numpy.mgrid is an instance of nd_grid with sparse=False"
}
-/

-- TODO: Implement mgrid
