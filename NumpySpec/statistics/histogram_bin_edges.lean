/-!
{
  "name": "numpy.histogram_bin_edges",
  "category": "Histograms",
  "description": "Function to calculate only the edges of the bins used by the histogram function",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.histogram_bin_edges.html",
  "doc": "numpy.histogram_bin_edges(a, bins=10, range=None, weights=None)\n\nFunction to calculate only the edges of the bins used by the histogram function.\n\nParameters\n----------\na : array_like\n    Input data. The histogram is computed over the flattened array.\nbins : int or sequence of scalars or str, optional\n    If bins is an int, it defines the number of equal-width bins in the given range (10, by default). If bins is a sequence, it defines the bin edges, including the rightmost edge, allowing for non-uniform bin widths.\n    If bins is a string from the list below, histogram_bin_edges will use the method chosen to calculate the optimal bin width and consequently the number of bins.\nrange : (float, float), optional\n    The lower and upper range of the bins. If not provided, range is simply (a.min(), a.max()). Values outside the range are ignored.\nweights : array_like, optional\n    An array of weights, of the same shape as a. Each value in a only contributes its associated weight towards the bin count (instead of 1).\n\nReturns\n-------\nbin_edges : array of dtype float\n    The edges to pass into histogram",
  "code": "# Implementation in numpy/lib/_histograms_impl.py\n@array_function_dispatch(_histogram_bin_edges_dispatcher)\ndef histogram_bin_edges(a, bins=10, range=None, weights=None):\n    \"\"\"\n    Function to calculate only the edges of the bins used by the histogram\n    function.\n    \"\"\"\n    a, weights = _ravel_and_check_weights(a, weights)\n    bin_edges, _ = _get_bin_edges(a, bins, range, weights)\n    return bin_edges"
}
-/

-- TODO: Implement histogram_bin_edges
