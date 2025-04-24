-- Implement basic spec skeleton

/-
# Gaussian elimination specification

This file provides the *type-level* skeleton for our Gaussian elimination
specification.  We defer all proofs (`sorry`) for downstream development.

We work over an arbitrary commutative ring `R` and square matrices of fixed
size `n`.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

-- |A placeholder definition for the matrix produced by Gaussian elimination.
def gaussianElimination (A : Matrix n n R) : Matrix n n R :=
  -- TODO: implement the algorithm; for now, return `A⁻¹` when available or 0.
  if h : IsUnit (det A) then
    Classical.choose (IsUnit.exists_right_inv h)
  else 0

lemma gaussianElimination_is_left_inverse (A : Matrix n n R) (hA : IsUnit (det A)) :
    gaussianElimination A ⬝ₘ A = (1 : Matrix n n R) := by
  -- TODO: formalize the usual proof that GE yields a left inverse.
  -- We `sorry` for now.
  sorry

/-!
### Notes

* We rely on `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` for the existence of an inverse when `det A` is a unit.
* Once the implementation of `gaussianElimination` is complete, the above lemma should follow from its correctness.
-/
