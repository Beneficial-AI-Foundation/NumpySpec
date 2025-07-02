/-
# NumPy GCD Specification

Port of np_gcd.dfy to Lean 4
-/

namespace DafnySpecs.Gcd

/-- Helper function for computing GCD of two integers -/
def gcdInt (a b : Int) : Int := Int.ofNat (Int.gcd a b)

/-- Element-wise greatest common divisor of two vectors -/
def gcd {n : Nat} (a b : Vector Int n) : Vector Int n :=
  Vector.zipWith gcdInt a b

/-- Specification: Output length equals input length -/
theorem gcd_length {n : Nat} (a b : Vector Int n) :
  (gcd a b).size = n := rfl

/-- Specification: Non-negative inputs requirement -/
theorem gcd_nonneg_requirement {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, 0 ≤ (gcd a b)[i] := by
  intro i
  simp [gcd, gcdInt]
  grind

/-- Specification: Element-wise GCD computation -/
theorem gcd_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (gcd a b)[i] = gcdInt (a[i]) (b[i]) := by
  intro i
  simp [gcd]

end DafnySpecs.Gcd
