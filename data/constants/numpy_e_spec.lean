/-!
# Spec for `numpy.e`

A trivial specification stating that the Lean constant equals `Real.exp 1`.
-/

import ./numpy_e

open numpy

namespace numpySpec

/-- `numpy.e` is defined as `Real.exp 1`. -/
noncomputable lemma numpy_e_eq : numpy.e = Real.exp 1 := rfl

end numpySpec
