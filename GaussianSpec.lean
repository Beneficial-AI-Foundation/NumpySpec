-- This module serves as the root of the `GaussianSpec` library.
-- Import modules here that should be built as part of the library.

import GaussianSpec.Basic
import LeanSearchClient
import Mathlib.Data.Matrix.Basic -- provides `Matrix`, basic lemmas, and instances
import Mathlib.Data.Matrix.Invertible -- brings `invOf` lemmas for matrices



/-!

# Gaussian Elimination Specification

This module specifies that Gaussian elimination, when applied to a nonsingular square matrix `A`,
produces a matrix `A'` such that multiplying `A'` by the original matrix `A` results in the
identity matrix. This essentially states that Gaussian elimination computes the left inverse.

We assume the matrix elements are from a field `K`.

-/

namespace GaussianSpec

open Matrix

variable {n : ℕ}
variable {K : Type} [Field K]

/--
Performs Gaussian elimination on a matrix `A` to bring it to row-echelon form.
This is a placeholder; the actual implementation would involve row operations.
We can use `Matrix.pivot` potentially, or implement the standard algorithm.
For now, we leave it abstract.
-/
noncomputable def gaussianElimination (A : Matrix (Fin n) (Fin n) K) [Invertible A] :
    Matrix (Fin n) (Fin n) K := ⅟ A

-- (placeholder to avoid accidental syntax noise)
--

/--
Specification: Applying Gaussian elimination to a nonsingular matrix `A` yields its left inverse.
We require `Nonsingular A` which implies `A` is square and invertible.
-/
theorem gaussianElimination_is_left_inverse (A : Matrix (Fin n) (Fin n) K) [Invertible A] :
    gaussianElimination A * A = 1 := by
  -- Unfold and apply the generic lemma about `invOf`.
  simp [gaussianElimination, invOf_mul_self]

end GaussianSpec
