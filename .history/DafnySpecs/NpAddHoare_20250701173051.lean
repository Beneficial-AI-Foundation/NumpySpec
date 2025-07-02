import Std.Do
import Std.Tactic.Do
import Std.Do.Triple

/-!
# Array Addition Specification using Hoare Logic

Port of `np_add.dfy` to Lean 4's new Hoare logic syntax.
This uses the pre/post condition syntax merged in:
https://github.com/leanprover/lean4/commit/f87d05ad4e55ce5126a67b990583d5e96a8b4e20
-/

namespace DafnySpecs.NpAddHoare

/-- Array addition specification using Hoare logic syntax
    
    Precondition (requires): a.size = b.size  
    Postcondition (ensures): res.size = a.size ∧ ∀ i : Fin res.size, res[i] = a[i.val] + b[i.val]
-/
def add (a b : Array Int) : Id (Array Int) := do
  requires (a.size = b.size)
  let res ← sorry  -- No implementation, only specification
  ensures fun res => res.size = a.size ∧ ∀ i : Fin res.size, res[i] = a[i.val] + b[i.val]
  return res

/-- Alternative specification using the triple notation -/
def addTriple : Triple 
  (fun (a b : Array Int) => a.size = b.size)
  (fun (a b : Array Int) => sorry : Id (Array Int))
  (fun (a b : Array Int) res => res.size = a.size ∧ ∀ i : Fin res.size, res[i] = a[i.val] + b[i.val]) :=
  sorry

/-- Specification with additional properties -/
def addWithProperties (a b : Array Int) : Id (Array Int) := do
  requires (a.size = b.size)
  let res ← sorry
  ensures fun res => 
    res.size = a.size ∧ 
    (∀ i : Fin res.size, res[i] = a[i.val] + b[i.val]) ∧
    (∀ i : Nat, i < res.size → res[i]? = some (a[i]?.getD 0 + b[i]?.getD 0))
  return res

/-- Polymorphic version for any additive type -/
def addPoly {α : Type} [Add α] (a b : Array α) : Id (Array α) := do
  requires (a.size = b.size)
  let res ← sorry
  ensures fun res => res.size = a.size ∧ ∀ i : Fin res.size, res[i] = a[i.val] + b[i.val]
  return res

/-- Non-empty array addition specification -/
def addNonEmpty (a b : {arr : Array Int // arr.size > 0}) : Id {arr : Array Int // arr.size > 0} := do
  requires (a.val.size = b.val.size)
  let res ← sorry
  ensures fun res => 
    res.val.size = a.val.size ∧ 
    res.val.size > 0 ∧
    (∀ i : Fin res.val.size, res.val[i] = a.val[i.val] + b.val[i.val])
  return res

/-- Vector addition with compile-time size checking -/
def addVec {n : Nat} (a b : Vector Int n) : Id (Vector Int n) := do
  -- No precondition needed - size equality guaranteed by types
  let res ← sorry
  ensures fun res => ∀ i : Fin n, res.get i = a.get i + b.get i
  return res

/-- Specification for in-place addition (mutating first array) -/
def addInPlace (a : Array Int) (b : Array Int) : Id Unit := do
  requires (a.size = b.size)
  sorry  -- Mutate a in place
  ensures fun _ => 
    a.size = b.size ∧  -- Size unchanged
    (∀ i : Fin a.size, a[i] = old(a[i]) + b[i.val])  -- Each element updated
  return ()

/-- Partial addition for arrays of different sizes -/
def addPartial (a b : Array Int) : Id (Array Int) := do
  -- No size requirement
  let minSize := min a.size b.size
  let res ← sorry
  ensures fun res => 
    res.size = minSize ∧
    (∀ i : Fin res.size, res[i] = a[i.val] + b[i.val])
  return res

end DafnySpecs.NpAddHoare