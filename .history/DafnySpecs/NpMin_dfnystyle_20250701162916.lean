import Batteries

/-!
# Array Minimum with Dafny-style Verification

This demonstrates how Dafny-style specifications could work in Lean 4
once PR #8995's features are available. For now, we simulate the approach
using existing Lean 4 features.

Note: The actual Triple type and mspec/mvcgen tactics from PR #8995 are not
yet available, so we define our own versions for demonstration.
-/

namespace DafnySpecs.NpMinDafnyStyle

-- Aliases to avoid conflicts
local notation "minInt" => @min Int _

/-! ## Simulating Hoare Triple Type

Since PR #8995's `Std.Do.Triple` isn't available yet, we simulate it.
-/

/-- A simple Hoare triple type for demonstration.
    Represents `{P} c {Q}` where P is precondition, c is computation, Q is postcondition. -/
structure Triple (P : Prop) (α : Type) (Q : α → Prop) where
  /-- The computation that transforms precondition to result -/
  computation : P → α
  /-- Proof that computation satisfies the postcondition -/
  specification : ∀ (hp : P), Q (computation hp)

/-! ## Array Minimum with Specifications -/

/-- Specification: minimum of non-empty array.

    Dafny equivalent:
    ```dafny
    method ArrayMin(a: array<int>) returns (min: int)
      requires a.Length > 0
      ensures exists i :: 0 <= i < a.Length && min == a[i]
      ensures forall i :: 0 <= i < a.Length ==> min <= a[i]
    ```
-/
def minSpec (a : Array Int) : Triple (a.size > 0) Int
  (fun res => (∃ i : Fin a.size, res = a[i]) ∧ (∀ i : Fin a.size, res ≤ a[i])) where
  computation h := a.foldl (init := a[0]'h) minInt
  specification h := by
    constructor
    · -- Exists proof: the fold starts with a[0] which is in the array
      refine ⟨⟨0, h⟩, ?_⟩
      sorry
    · -- Universal proof: fold computes minimum
      intro i
      sorry

/-- The actual minimum function -/
def min (a : Array Int) (h : a.size > 0) : Int :=
  a.foldl (init := a[0]'h) minInt

/-- Verification theorem showing min satisfies its specification -/
theorem min_satisfies_spec (a : Array Int) (h : a.size > 0) :
    let result := min a h
    (∃ i : Fin a.size, result = a[i]) ∧ (∀ i : Fin a.size, result ≤ a[i]) :=
  (minSpec a).specification h

/-! ## Minimum with Index -/

/-- Specification for minimum with index.

    Dafny equivalent:
    ```dafny
    method ArrayMinWithIndex(a: array<int>) returns (min: int, idx: nat)
      requires a.Length > 0
      ensures idx < a.Length && min == a[idx]
      ensures forall i :: 0 <= i < a.Length ==> min <= a[i]
    ```
-/
def minWithIndexSpec (a : Array Int) :
  Triple (a.size > 0) (Int × Fin a.size)
    (fun res => res.1 = a[res.2] ∧ ∀ i : Fin a.size, res.1 ≤ a[i]) where
  computation h :=
    let rec loop (i : Nat) (currMin : Int) (idx : Fin a.size) : Int × Fin a.size :=
      if hi : i < a.size then
        let val := a[i]'hi
        if val < currMin then
          loop (i + 1) val ⟨i, hi⟩
        else
          loop (i + 1) currMin idx
      else
        (currMin, idx)
    loop 1 (a[0]'h) ⟨0, h⟩
  specification h := by
    refine ⟨⟨0, h⟩, ?_⟩
    sorry -- Would prove loop maintains invariant

/-- Implementation of minWithIndex -/
def minWithIndex (a : Array Int) (h : a.size > 0) : Int × Fin a.size :=
  let rec loop (i : Nat) (currMin : Int) (idx : Fin a.size) : Int × Fin a.size :=
    if hi : i < a.size then
      let val := a[i]'hi
      if val < currMin then
        loop (i + 1) val ⟨i, hi⟩
      else
        loop (i + 1) currMin idx
    else
      (currMin, idx)
  loop 1 (a[0]'h) ⟨0, h⟩

/-! ## Loop Invariants

Demonstrating how loop invariants would work with the Dafny-style approach.
-/

/-- Loop invariant for the minimum computation.

    In Dafny:
    ```dafny
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant exists k :: 0 <= k < i && currMin == a[k]
      invariant forall k :: 0 <= k < i ==> currMin <= a[k]
    ```
-/
structure LoopInvariant (a : Array Int) (i : Nat) (currMin : Int) : Prop where
  /-- Bounds check: i is within array bounds -/
  bounds : i ≤ a.size
  /-- There exists a witness index for the current minimum -/
  exists_witness : i > 0 → ∃ k : Fin a.size, k.val < i ∧ currMin = a[k]
  /-- Current minimum is less than or equal to all seen elements -/
  universal_property : ∀ k : Fin a.size, k.val < i → currMin ≤ a[k]

/-- Proof that loop maintains invariant -/
theorem loop_maintains_invariant (a : Array Int) (i : Nat) (currMin : Int)
    (h : i < a.size) (inv : LoopInvariant a i currMin) :
    let val := a[i]'h
    let newMin := if val < currMin then val else currMin
    LoopInvariant a (i + 1) newMin := by
  sorry -- Would prove invariant preservation

/-! ## Option-based API -/

/-- Specification for optional minimum.

    Weaker precondition - works for all arrays.
-/
def minOptionSpec (a : Array Int) :
  Triple True (Option Int)
    (fun res => match res with
      | none => a.size = 0
      | some m => a.size > 0 ∧ (∃ i : Fin a.size, m = a[i]) ∧ (∀ i : Fin a.size, m ≤ a[i])) where
  computation _ :=
    if h : a.size > 0 then
      some (a.foldl (init := a[0]'h) minInt)
    else
      none
  specification _ := by
    by_cases h : a.size > 0 <;> simp [h]
    · constructor
      · refine ⟨⟨0, h⟩, ?_⟩
        sorry
      · intro i
        sorry
    · -- When size is not > 0, it must be 0, so array is empty
      have : a.size = 0 := by omega
      exact Array.eq_empty_of_size_eq_zero this

/-- Safe minimum that returns None for empty arrays -/
def minOption (a : Array Int) : Option Int :=
  if h : a.size > 0 then
    some (min a h)
  else
    none

/-! ## Polymorphic Version -/

/-- Polymorphic minimum specification -/
def minPolySpec {α : Type} [Min α] [LE α] [DecidableRel (· ≤ · : α → α → Prop)]
    (a : Array α) :
  Triple (a.size > 0) α
    (fun res => ∃ i : Fin a.size, res = a[i]) where
  computation h := a.foldl (init := a[0]'h) Min.min
  specification h := by
    refine ⟨⟨0, h⟩, ?_⟩
    sorry

/-- Polymorphic minimum -/
def minPoly {α : Type} [Min α] (a : Array α) (h : a.size > 0) : α :=
  a.foldl (init := a[0]'h) Min.min

/-! ## Verification Condition Generation

This section demonstrates how verification conditions would be generated
from specifications (what mvcgen would do automatically).
-/

/-- Generated verification condition for min function -/
def minVC (a : Array Int) (h : a.size > 0) : Prop :=
  let result := min a h
  (∃ i : Fin a.size, result = a[i]) ∧ (∀ i : Fin a.size, result ≤ a[i])

/-- Proof that VC holds (would be automated with grind/simp) -/
theorem minVC_holds (a : Array Int) (h : a.size > 0) : minVC a h := by
  unfold minVC
  exact min_satisfies_spec a h

/-! ## Examples -/

section Examples

/-- Example: minimum of concrete array -/
example : min #[3, 1, 4, 1, 5, 9] (by simp) = 1 := by
  unfold min
  simp [Array.foldl]
  -- The computation traces through: foldl min 3 [1,4,1,5,9] = 1
  rfl

/-- Example: minimum with index -/
example : (minWithIndex #[3, 1, 4, 1, 5, 9] (by simp)).1 = 1 := by
  -- Would trace through loop execution
  sorry

/-- Example: option API -/
example : minOption #[] = none := by
  unfold minOption
  simp

example : minOption #[42] = some 42 := by
  unfold minOption
  simp [min]

/-- Example showing how specification is used -/
example (a : Array Int) (h : a.size = 3) :
  ∃ i : Fin a.size, min a (by simp [h]) = a[i] := by
  have h' : a.size > 0 := by simp [h]
  have spec := min_satisfies_spec a h'
  exact spec.1

end Examples

/-! ## Dafny-Style Assertions

In Dafny, you can write assertions mid-computation. We simulate this:
-/

/-- Minimum with assertions (Dafny style) -/
def minWithAssertions (a : Array Int) (h : a.size > 0) : Int :=
  let result := a.foldl (init := a[0]'h) minInt
  -- In Dafny: assert exists i :: result == a[i];
  have h1 : ∃ i : Fin a.size, result = a[i] := by
    sorry
  -- In Dafny: assert forall i :: result <= a[i];
  have h2 : ∀ i : Fin a.size, result ≤ a[i] := by
    sorry
  result

end DafnySpecs.NpMinDafnyStyle

/-! ## Summary

This file demonstrates how Dafny-style verification would work in Lean 4:

1. **Triple Type**: Bundles computation with its specification
2. **Specifications as Values**: First-class specifications that can be composed
3. **Loop Invariants**: Explicit invariant structures
4. **Verification Conditions**: Generated from specifications
5. **Separation of Spec and Implementation**: Clear distinction between what and how

When PR #8995's features are available:
- Replace our `Triple` with `Std.Do.Triple`
- Use `@[spec]` attribute on specifications
- Use `mspec` tactic to apply specifications
- Use `mvcgen` to generate verification conditions
- Use `grind` or SMT tactics to discharge VCs automatically

The key insight is that Dafny-style verification focuses on:
- Automatic VC generation from pre/post conditions
- SMT-based automation for proof discharge
- Loop invariants as first-class concepts
- Separation of specification from implementation
-/
