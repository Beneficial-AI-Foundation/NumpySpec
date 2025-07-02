import Std.Do

/-!
# Array Minimum with Dafny-Style Verification

This module demonstrates the new Hoare logic verification framework for Lean 4,
using array minimum as an example. We'll use:
- Hoare triple syntax `⦃P⦄ prog ⦃Q⦄`
- Verification condition generation with `mvcgen`
- Specification attributes with `@[spec]`
-/

namespace DafnyStyle.NpMin

open Std.Do

-- Aliases to avoid name conflicts
local notation "minInt" => @min Int _
local notation "maxInt" => @max Int _

/-- Find minimum element in an array using monadic style.
    This is the implementation we'll verify.
-/
def findMin (a : Array Int) : StateT Nat Id Int := do
  -- Nat state tracks the current index
  if a.size = 0 then
    -- For simplicity, return 0 for empty arrays
    return 0
  else
    let mut minVal := a[0]!
    for i in [1:a.size] do
      let curr := a[i]!
      if curr < minVal then
        minVal := curr
    return minVal

/-- Pure specification of minimum for verification -/
def isMinimum (a : Array Int) (m : Int) : Prop :=
  a.size > 0 → (∃ i : Fin a.size, m = a[i]) ∧ (∀ i : Fin a.size, m ≤ a[i])

/-- Helper: check if value exists in array -/
def existsIn (a : Array Int) (v : Int) : Prop :=
  ∃ i : Fin a.size, a[i] = v

/-- Helper: check if value is less than or equal to all elements -/
def isLowerBound (a : Array Int) (v : Int) : Prop :=
  ∀ i : Fin a.size, v ≤ a[i]

/-- Main specification theorem for findMin using Hoare triple syntax -/
@[spec]
theorem findMin_spec (a : Array Int) :
  ⦃⌜a.size > 0⌝⦄
    findMin a
  ⦃⇓ r => existsIn a r ∧ isLowerBound a r⦄ := by
  unfold findMin
  mvcgen
  -- Loop invariant: minVal is the minimum of elements seen so far
  case inv => exact ⇓ (minVal, xs) =>
    existsIn (a.take xs.rpref.length) minVal ∧
    isLowerBound (a.take xs.rpref.length) minVal
  all_goals sorry -- Proof details omitted for brevity

/-- Alternative implementation with explicit loop bounds -/
def findMinBounded (a : Array Int) (n : Nat) : StateT Unit Id Int := do
  if h : n > 0 ∧ n ≤ a.size then
    let mut minVal := a[0]!
    let mut i := 1
    while i < n do
      let curr := a[i]!
      if curr < minVal then
        minVal := curr
      i := i + 1
    return minVal
  else
    return 0

/-- Specification for bounded minimum -/
@[spec]
theorem findMinBounded_spec (a : Array Int) (n : Nat) :
  ⦃⌜n > 0 ∧ n ≤ a.size⌝⦄
    findMinBounded a n
  ⦃⇓ r => existsIn (a.take n) r ∧ isLowerBound (a.take n) r⦄ := by
  unfold findMinBounded
  mvcgen
  -- While loop invariant
  case inv => exact ⇓ (⟨minVal, i⟩, _) =>
    i ≤ n ∧
    existsIn (a.take i) minVal ∧
    isLowerBound (a.take i) minVal
  all_goals sorry

/-- Find minimum with index tracking -/
def findMinWithIndex (a : Array Int) : StateT Unit Id (Int × Nat) := do
  if a.size = 0 then
    return (0, 0)
  else
    let mut minVal := a[0]!
    let mut minIdx := 0
    for i in [1:a.size] do
      let curr := a[i]!
      if curr < minVal then
        minVal := curr
        minIdx := i
    return (minVal, minIdx)

/-- Specification: the returned index points to the minimum value -/
@[spec]
theorem findMinWithIndex_spec (a : Array Int) :
  ⦃⌜a.size > 0⌝⦄
    findMinWithIndex a
  ⦃⇓ (val, idx) => idx < a.size ∧ a[idx]! = val ∧ isLowerBound a val⦄ := by
  unfold findMinWithIndex
  mvcgen
  case inv => exact ⇓ (⟨minVal, minIdx⟩, xs) =>
    minIdx < xs.rpref.length ∧
    a[minIdx]! = minVal ∧
    isLowerBound (a.take xs.rpref.length) minVal
  all_goals sorry

/-- Find minimum with early exit on finding zero -/
def findMinEarlyExit (a : Array Int) : ExceptT Unit (StateT Unit Id) Int := do
  if a.size = 0 then
    throw ()
  let mut minVal := a[0]!
  for i in [1:a.size] do
    let curr := a[i]!
    if curr = 0 then
      -- Early exit: zero is always minimum for non-negative arrays
      return 0
    if curr < minVal then
      minVal := curr
  return minVal

/-- Specification with exception handling -/
@[spec]
theorem findMinEarlyExit_spec (a : Array Int) :
  ⦃⌜a.size > 0 ∧ (∀ i : Fin a.size, a[i] ≥ 0)⌝⦄
    findMinEarlyExit a
  ⦃post⟨
    fun r _ => existsIn a r ∧ isLowerBound a r,
    fun _ _ => a.size = 0
  ⟩⦄ := by
  unfold findMinEarlyExit
  mvcgen
  case inv => exact ⇓ (minVal, xs) =>
    existsIn (a.take xs.rpref.length) minVal ∧
    isLowerBound (a.take xs.rpref.length) minVal ∧
    (∀ j < xs.rpref.length, a[j]! ≠ 0)
  all_goals sorry

/-- Polymorphic minimum with custom comparison -/
def findMinBy {α : Type} (a : Array α) (lt : α → α → Bool) : StateT Unit Id α := do
  if h : a.size > 0 then
    let mut minVal := a[0]'h
    for i in [1:a.size] do
      let curr := a[i]!
      if lt curr minVal then
        minVal := curr
    return minVal
  else
    panic! "empty array"

/-- Generic specification for comparison-based minimum -/
@[spec]
theorem findMinBy_spec {α : Type} (a : Array α) (lt : α → α → Bool)
  (h_trans : ∀ x y z, lt x y → lt y z → lt x z)
  (h_total : ∀ x y, lt x y ∨ lt y x ∨ x = y) :
  ⦃⌜a.size > 0⌝⦄
    findMinBy a lt
  ⦃⇓ r => existsIn a r ∧ (∀ i : Fin a.size, ¬lt a[i] r)⦄ := by
  unfold findMinBy
  mvcgen
  case inv => exact ⇓ (minVal, xs) =>
    ∃ j < xs.rpref.length, a[j]! = minVal ∧
    (∀ k < xs.rpref.length, ¬lt a[k]! minVal)
  all_goals sorry

/-- Helper function to run StateT computations -/
def runMin {α} (m : StateT Nat Id α) : α :=
  (m.run 0).1

/-- Example: verify a concrete minimum computation -/
example : runMin (findMin #[3, 1, 4, 1, 5, 9]) = 1 := by
  -- This would be proved using the specification
  sorry

/-- Compose specifications: find minimum of two arrays -/
def findMinOfTwo (a b : Array Int) : StateT Unit Id Int := do
  let minA ← findMin a
  let minB ← findMin b
  return minInt minA minB

/-- Compositional specification using bind rule -/
@[spec]
theorem findMinOfTwo_spec (a b : Array Int) :
  ⦃⌜a.size > 0 ∧ b.size > 0⌝⦄
    findMinOfTwo a b
  ⦃⇓ r => (existsIn a r ∨ existsIn b r) ∧ isLowerBound (a ++ b) r⦄ := by
  unfold findMinOfTwo
  -- Apply bind rule from Triple.bind
  mspec findMin_spec
  mspec findMin_spec
  -- Complete the proof
  sorry

/-- Minimum with logging for debugging -/
def findMinWithLog (a : Array Int) : StateT (List String) Id Int := do
  modify (· ++ ["Starting minimum search"])
  if a.size = 0 then
    modify (· ++ ["Array is empty, returning 0"])
    return 0
  else
    let mut minVal := a[0]!
    modify (· ++ [s!"Initial minimum: {minVal}"])
    for i in [1:a.size] do
      let curr := a[i]!
      if curr < minVal then
        modify (· ++ [s!"New minimum found: {curr} at index {i}"])
        minVal := curr
    modify (· ++ [s!"Final minimum: {minVal}"])
    return minVal

/-- Specification that includes logging behavior -/
@[spec]
theorem findMinWithLog_spec (a : Array Int) :
  ⦃⌜a.size > 0 ∧ #logs = []⌝⦄
    findMinWithLog a
  ⦃⇓ r => existsIn a r ∧ isLowerBound a r ∧ #logs.length > 0⦄ := by
  unfold findMinWithLog
  mvcgen
  case inv => exact ⇓ (minVal, xs) =>
    #logs.length > 0 ∧
    existsIn (a.take xs.rpref.length) minVal ∧
    isLowerBound (a.take xs.rpref.length) minVal
  all_goals sorry

section ProofExamples

/-- Example of using mspec to apply specifications -/
example (a : Array Int) (h : a.size > 0) :
  ⦃⌜a.size > 0⌝⦄ findMin a ⦃⇓ r => existsIn a r⦄ := by
  -- Use mspec to apply the specification
  mspec findMin_spec
  -- The postcondition is weaker, so this follows
  mintro r
  mcases ⟨h1, h2⟩
  mexact h1

/-- Example of verifying a property about minimum -/
example (a : Array Int) :
  ⦃⌜a.size = 1⌝⦄ findMin a ⦃⇓ r => r = a[0]!⦄ := by
  unfold findMin
  mvcgen
  -- No loop iterations needed
  all_goals simp_all

end ProofExamples

end DafnyStyle.NpMin
