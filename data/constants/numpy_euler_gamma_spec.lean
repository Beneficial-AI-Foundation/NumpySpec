/-!
# Spec for `numpy.euler_gamma`

A trivial specification stating that the Lean constant equals `Real.eulerGamma`.
-/

import ./numpy_euler_gamma

open numpy

namespace numpySpec

/-- `numpy.eulerGamma` is defined as `Real.eulerGamma`. -/
noncomputable lemma numpy_euler_gamma_eq : numpy.eulerGamma = Real.eulerGamma := rfl

end numpySpec
