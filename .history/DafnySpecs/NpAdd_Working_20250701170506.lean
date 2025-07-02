import Std.Do
import Std.Do.Triple
import Std.Tactic.Do


/- Working example: Translating Dafny's np_add.dfy to Lean 4 with Hoare-style syntax -/

namespace NumpySpec.DafnyHoare

open Std.Do

/- Original Dafny:
method Add(a: array<int>, b: array<int>) returns (res: array<int>)
  requires a.Length == b.Length
  ensures res.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] + b[i]
-/

-- First, let's define a simple stateful add function
def addArraysStateM (a b : Array Int) : StateM Unit (Option (Array Int)) := do
  if a.size ≠ b.size then
    return none
  else
    let mut res := #[]
    for i in [:a.size] do
      res := res.push (a[i]! + b[i]!)
    return some res

-- Now let's express this with a Hoare triple
theorem addArrays_hoare (a b : Array Int) :
  ⦃ spred(True) ⦄
    addArraysStateM a b
  ⦃ fun res => spred(
      match res with
      | some arr => a.size = b.size → (arr.size = a.size ∧ ∀ i : Fin arr.size, arr[i] = a[i.val]'(by simp [arr.size_eq]; exact i.isLt) + b[i.val]'(by rw [arr.size_eq]; simp; exact i.isLt))
      | none => a.size ≠ b.size
    ) ⦄ := by
  mspec
  intro _
  -- Case split on whether sizes are equal
  by_cases h : a.size = b.size
  · -- Equal sizes case
    simp [addArraysStateM, h, StateM.run']
    intro heq
    constructor
    · -- Prove size equality
      sorry -- Would prove that the resulting array has size a.size
    · -- Prove element-wise equality
      intro i
      sorry -- Would prove arr[i] = a[i] + b[i]
  · -- Unequal sizes case
    simp [addArraysStateM, h, StateM.run']
    exact h

-- Example with precondition
theorem addArrays_with_precond (a b : Array Int) :
  ⦃ spred(a.size = b.size) ⦄
    addArraysStateM a b
  ⦃ fun res => spred(∃ arr, res = some arr ∧ arr.size = a.size ∧ ∀ i : Fin arr.size, arr[i] = a[i] + b[i]) ⦄ := by
  mspec
  intro h
  simp [addArraysStateM, h, StateM.run']
  use Array.zipWith a b (· + ·)
  sorry -- Would complete the proof

/- Let's also show a simpler example with pure functions -/

def addPure (x y : Int) : StateM Unit Int :=
  return (x + y)

theorem addPure_hoare (x y : Int) :
  ⦃ spred(True) ⦄
    addPure x y
  ⦃ fun res => spred(res = x + y) ⦄ := by
  mspec
  intro _
  simp [addPure, StateM.run']

/- Key features demonstrated:
1. ⦃P⦄ x ⦃Q⦄ syntax for Hoare triples
2. `spred` converts propositions to assertions
3. `mspec` tactic introduces Hoare reasoning
4. Pattern matching in postconditions
5. Direct mapping from Dafny's requires/ensures

Comparison with Dafny:
- Dafny: requires a.Length == b.Length
- Lean:  ⦃ spred(a.size = b.size) ⦄

- Dafny: ensures res.Length == a.Length
- Lean:  ⦃ fun res => spred(res.size = a.size) ⦄
-/

end NumpySpec.DafnyHoare
