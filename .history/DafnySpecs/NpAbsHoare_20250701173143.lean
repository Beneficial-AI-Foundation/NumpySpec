import Std.Do
import Std.Tactic.Do
import Std.Do.Triple

/-!
# Absolute Value Specification using Hoare Logic

Port of `np_abs.dfy` to Lean 4's new Hoare logic syntax.
-/

namespace DafnySpecs.NpAbsHoare

/-- Helper function for absolute value of integers -/
def absInt (x : Int) : Int := if x < 0 then -x else x

/-- Array absolute value specification using Hoare logic syntax
    
    Precondition: None (works for any array)
    Postcondition: 
    - res.size = a.size
    - ∀ i, res[i] = |a[i]|  
    - ∀ i, res[i] ≥ 0
-/
def abs (a : Array Int) : Id (Array Int) := do
  -- No precondition needed
  let res ← sorry  -- No implementation, only specification
  ensures fun res => 
    res.size = a.size ∧ 
    (∀ i : Fin res.size, res[i] = absInt a[i.val]) ∧
    (∀ i : Fin res.size, res[i] ≥ 0)
  return res

/-- Alternative specification using the triple notation -/
def absTriple : Triple 
  (fun (a : Array Int) => True)  -- No precondition
  (fun (a : Array Int) => sorry : Id (Array Int))
  (fun (a : Array Int) res => 
    res.size = a.size ∧ 
    (∀ i : Fin res.size, res[i] = absInt a[i.val]) ∧
    (∀ i : Fin res.size, res[i] ≥ 0)) :=
  sorry

/-- Polymorphic version for any type with absolute value -/
def absPoly {α : Type} [Abs α] [LE α] [OfNat α 0] (a : Array α) : Id (Array α) := do
  let res ← sorry
  ensures fun res => 
    res.size = a.size ∧ 
    (∀ i : Fin res.size, res[i] = abs a[i.val]) ∧
    (∀ i : Fin res.size, res[i] ≥ 0)
  return res

/-- In-place absolute value (mutating the array) -/
def absInPlace (a : Array Int) : Id Unit := do
  sorry  -- Mutate a in place
  ensures fun _ => 
    a.size = old(a.size) ∧  -- Size unchanged
    (∀ i : Fin a.size, a[i] = absInt (old(a[i]))) ∧
    (∀ i : Fin a.size, a[i] ≥ 0)
  return ()

/-- Vector absolute value with compile-time size -/
def absVec {n : Nat} (a : Vector Int n) : Id (Vector Int n) := do
  let res ← sorry
  ensures fun res => 
    (∀ i : Fin n, res.get i = absInt (a.get i)) ∧
    (∀ i : Fin n, res.get i ≥ 0)
  return res

/-- Absolute value for non-empty arrays -/
def absNonEmpty (a : {arr : Array Int // arr.size > 0}) : Id {arr : Array Int // arr.size > 0} := do
  let res ← sorry
  ensures fun res => 
    res.val.size = a.val.size ∧ 
    res.val.size > 0 ∧
    (∀ i : Fin res.val.size, res.val[i] = absInt a.val[i.val]) ∧
    (∀ i : Fin res.val.size, res.val[i] ≥ 0)
  return res

/-- Specification with bounds information -/
def absWithBounds (a : Array Int) : Id (Array Int × Int × Int) := do
  let res ← sorry
  let minVal ← sorry  
  let maxVal ← sorry
  ensures fun (res, minVal, maxVal) => 
    res.size = a.size ∧ 
    (∀ i : Fin res.size, res[i] = absInt a[i.val]) ∧
    (∀ i : Fin res.size, res[i] ≥ 0) ∧
    (∀ i : Fin res.size, minVal ≤ res[i] ∧ res[i] ≤ maxVal) ∧
    (∃ i : Fin res.size, res[i] = minVal) ∧
    (∃ i : Fin res.size, res[i] = maxVal)
  return (res, minVal, maxVal)

end DafnySpecs.NpAbsHoare