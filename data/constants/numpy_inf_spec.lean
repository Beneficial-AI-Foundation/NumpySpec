/-!
# Spec for `numpy.inf`

A trivial specification stating that the Lean constant equals `Float.infinity`.
-/

import ./numpy_inf

open numpy

namespace numpySpec

/-- `numpy.inf` is defined as `Float.infinity`. -/
lemma numpy_inf_eq : numpy.inf = Float.infinity := rfl

end numpySpec
