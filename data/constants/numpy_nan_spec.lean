/-!
# Spec for `numpy.nan`

A trivial specification stating that the Lean constant equals `Float.nan`.
-/

import ./numpy_nan

open numpy

namespace numpySpec

/-- `numpy.nan` is defined as `Float.nan`. -/
lemma numpy_nan_eq : numpy.nan = Float.nan := rfl

end numpySpec
