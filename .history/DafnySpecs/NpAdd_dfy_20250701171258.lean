import Std.Do
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/--
  *Specification only* (no implementation) for element‑wise addition on *fixed‑length* vectors.
  Because `Vector` carries its length `n` in the type, the pre‑condition that the two inputs share
  the same length is enforced by the type checker and no longer appears as a logical requirement.
-/
theorem Add_dfy {n : Nat} (a b : Vector Int n) : Vector Int n :=
  Vector.zipWith (· + ·) a b

/-- Hoare‑style contract for `Add_dfy`. -/
@[spec]
axiom Add_spec {n : Nat} (a b : Vector Int n) :
  ⦃ spred(True) ⦄
    pure (f := Id) (Add_dfy a b)
    ⦃ ⇓ res => ∀ i : Fin n, res.get i = a.get i + b.get i ⦄
