import Std.Tactic.BVDecide
/-
# NumPy Invert Specification

Port of np_invert.dfy to Lean 4
-/

namespace DafnySpecs.Invert

/-- Element-wise bitwise NOT (invert) of a vector with specified bit width -/
def invert {n : Nat} (a : Vector Int n) : Vector Int n := a.map (~~~ ·)

/-- Specification: The result has the same length as input -/
theorem invert_length {n : Nat} (a : Vector Int n) :
  (invert a).size = n := rfl

/-- Specification: Invert is an involution. -/
theorem invert_spec {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n, (invert (invert a))[i] = a[i] := by
    intro i
    simp [invert]
    -- Bitwise NOT is an involution: ~~~(~~~x) = x
    sorry

end DafnySpecs.Invert
