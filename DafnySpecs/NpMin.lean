import Std.Do

/-!
# Array Minimum Specification

Port of `np_min.dfy` to idiomatic Lean 4.

This module demonstrates several approaches to finding the minimum element in an array:
1. Runtime constraints via hypotheses (non-empty requirement)
2. Compile-time constraints via dependent types
3. Refinement types for non-empty arrays
4. MPL-style specifications for future verification

The Dafny specification requires:
- Precondition: array length > 0
- Postcondition 1: result equals some element in the array
- Postcondition 2: result is less than or equal to all elements
-/

namespace DafnySpecs.NpMin

-- Aliases to avoid name conflicts with our functions
local notation "minInt" => @min Int _
local notation "maxInt" => @max Int _

/-- Find minimum element in a non-empty array.
    
    The hypothesis `h` ensures the array is non-empty at the call site.
    This mirrors the Dafny `requires a.Length > 0` clause.
-/
def min (a : Array Int) (h : a.size > 0) : Int :=
  a.foldl (init := a[0]'h) minInt

/-- Specification theorem: the minimum is an element of the array -/
theorem min_exists (a : Array Int) (h : a.size > 0) :
    ∃ i : Fin a.size, min a h = a[i] := by
  sorry -- Proof would use properties of foldl and min

/-- Specification theorem: the minimum is less than or equal to all elements -/
theorem min_universal (a : Array Int) (h : a.size > 0) :
    ∀ i : Fin a.size, min a h ≤ a[i] := by
  sorry -- Proof would use induction on foldl

/-- Combined specification capturing both Dafny postconditions -/
theorem min_spec (a : Array Int) (h : a.size > 0) :
    (∃ i : Fin a.size, min a h = a[i]) ∧ 
    (∀ i : Fin a.size, min a h ≤ a[i]) := by
  constructor
  · exact min_exists a h
  · exact min_universal a h

/-
  MPL-style specification comment for future verification:
  
  ⦃ a.size > 0 ⦄ 
    min a 
  ⦃ λ res, (∃ i : Fin a.size, res = a[i]) ∧ (∀ i : Fin a.size, res ≤ a[i]) ⦄
  
  When MPL tactics are available, this can be proved using `mspec` or `mvcgen`.
-/

/- Alternative implementations with different trade-offs -/

section AlternativeImplementations

/-- Minimum using explicit recursion for clarity -/
def minRec (a : Array Int) (h : a.size > 0) : Int :=
  go 1 (a[0]'h)
where
  go (i : Nat) (currMin : Int) : Int :=
    if hi : i < a.size then
      go (i + 1) (minInt currMin (a[i]'hi))
    else
      currMin

/-- Minimum that returns both the value and its index -/
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

/-- Theorem: minWithIndex returns a valid minimum and witness index -/
theorem minWithIndex_correct (a : Array Int) (h : a.size > 0) :
    let (m, idx) := minWithIndex a h
    m = a[idx] ∧ ∀ i : Fin a.size, m ≤ a[i] := by
  sorry

end AlternativeImplementations

/- Vector approach using compile-time size checking -/

section VectorApproach

/-- Type alias for fixed-size arrays (simplified Vector) -/
def Vector (α : Type) (n : Nat) := {a : Array α // a.size = n}

namespace Vector

/-- Get element from a Vector at a valid index -/
def get {α : Type} {n : Nat} (v : Vector α n) (i : Fin n) : α :=
  have : i.val < v.val.size := by simp [v.property, i.isLt]
  v.val[i.val]'this

/-- Convert Vector to underlying Array -/
def toArray {α : Type} {n : Nat} (v : Vector α n) : Array α :=
  v.val

end Vector

/-- Minimum for vectors with compile-time non-empty guarantee -/
def minVec {n : Nat} (a : Vector Int (n + 1)) : Int :=
  a.toArray.foldl (init := a.get ⟨0, Nat.zero_lt_succ n⟩) minInt

/-- Vector minimum satisfies the existence property -/
theorem minVec_exists {n : Nat} (a : Vector Int (n + 1)) :
    ∃ i : Fin (n + 1), minVec a = a.get i := by
  sorry

/-- Vector minimum satisfies the universal property -/
theorem minVec_universal {n : Nat} (a : Vector Int (n + 1)) :
    ∀ i : Fin (n + 1), minVec a ≤ a.get i := by
  sorry

end VectorApproach

/- Refinement type approach -/

section RefinementTypes

/-- Non-empty array as a refinement type -/
abbrev NonEmptyArray (α : Type) := {arr : Array α // arr.size > 0}

/-- Minimum for non-empty arrays using refinement types -/
def minNonEmpty (a : NonEmptyArray Int) : Int :=
  a.val.foldl (init := a.val[0]'a.property) minInt

/-- Get an element from a non-empty array -/
def NonEmptyArray.get (a : NonEmptyArray α) (i : Fin a.val.size) : α :=
  a.val[i]

/-- Refinement type version preserves specifications -/
theorem minNonEmpty_spec (a : NonEmptyArray Int) :
    (∃ i : Fin a.val.size, minNonEmpty a = a.get i) ∧ 
    (∀ i : Fin a.val.size, minNonEmpty a ≤ a.get i) := by
  sorry

end RefinementTypes

/- Polymorphic versions -/

section Polymorphic

/-- Polymorphic minimum for any type with Min and LT instances -/
def minPoly {α : Type} [Min α] [LT α] (a : Array α) (h : a.size > 0) : α :=
  a.foldl (init := a[0]'h) Min.min

/-- Minimum with custom comparison function -/
def minBy {α : Type} (a : Array α) (h : a.size > 0) (cmp : α → α → Bool) : α :=
  a.foldl (init := a[0]'h) fun x y => if cmp y x then y else x

/-- Minimum by key extraction -/
def minByKey {α β : Type} [LT β] [DecidableRel (· < · : β → β → Prop)] (a : Array α) (h : a.size > 0) (key : α → β) : α :=
  a.foldl (init := a[0]'h) fun x y => if key y < key x then y else x

end Polymorphic

/- Properties and theorems -/

section Properties

/-- Minimum is idempotent -/
theorem min_singleton (x : Int) :
    min #[x] (by simp) = x := by
  unfold min
  simp

/-- Minimum of two elements -/
theorem min_pair (x y : Int) :
    min #[x, y] (by simp) = minInt x y := by
  unfold min
  simp

/-- Minimum is preserved under array concatenation -/
theorem min_append (a b : Array Int) (ha : a.size > 0) (hb : b.size > 0) :
    min (a ++ b) (by simp only [Array.size_append]; omega) = minInt (min a ha) (min b hb) := by
  sorry

/-- Minimum respects monotone transformations -/
theorem min_map_mono {f : Int → Int} (hf : ∀ x y, x ≤ y → f x ≤ f y) (a : Array Int) (h : a.size > 0) :
    f (min a h) = min (a.map f) (by simp [h]) := by
  sorry

/-- Helper: array maximum for theorem statement -/
private def arrayMax (a : Array Int) (h : a.size > 0) : Int :=
  a.foldl (init := a[0]'h) maxInt

/-- Relation between min and max -/
theorem min_neg_eq_neg_arrayMax (a : Array Int) (h : a.size > 0) :
    min a h = -(arrayMax (a.map (·.neg)) (by simp [Array.size_map, h])) := by
  sorry

end Properties

/- Option-based API for more idiomatic Lean -/

section OptionAPI

/-- Safe minimum that returns None for empty arrays -/
def minOption (a : Array Int) : Option Int :=
  if h : a.size > 0 then
    some (min a h)
  else
    none

/-- Option version specification -/
theorem minOption_spec (a : Array Int) :
    match minOption a with
    | none => a.size = 0
    | some m => a.size > 0 ∧ (∃ i : Fin a.size, m = a[i]) ∧ (∀ i : Fin a.size, m ≤ a[i]) := by
  sorry

/-- Minimum with default value for empty arrays -/
def minWithDefault (a : Array Int) (default : Int) : Int :=
  minOption a |>.getD default

end OptionAPI

/- Comparison with maximum -/

section MinMaxRelations

/-- Both min and max exist for non-empty arrays -/
theorem min_max_exists (a : Array Int) (h : a.size > 0) :
    let minVal := min a h
    let maxVal := a.foldl (init := a[0]'h) maxInt
    minVal ≤ maxVal := by
  sorry

/-- Argmin: index of minimum element -/
def argmin (a : Array Int) (h : a.size > 0) : Fin a.size :=
  (minWithIndex a h).2

/-- Argmin is correct -/
theorem argmin_correct (a : Array Int) (h : a.size > 0) :
    a[argmin a h] = min a h := by
  sorry

end MinMaxRelations

/- Helper functions for working with reductions -/

section Reductions

/-- Fold with index tracking for min/max operations -/
def foldlWithIndex {α β : Type} (a : Array α) (init : β) (f : Nat → β → α → β) : β :=
  let rec loop (i : Nat) (acc : β) : β :=
    if h : i < a.size then
      loop (i + 1) (f i acc (a[i]'h))
    else
      acc
  loop 0 init

/-- Alternative minWithIndex using foldlWithIndex -/
def minWithIndex' (a : Array Int) (h : a.size > 0) : Int × Fin a.size :=
  foldlWithIndex a ((a[0]'h), ⟨0, h⟩) fun i (currMin, idx) val =>
    if h : i < a.size then
      if val < currMin then (val, ⟨i, h⟩) else (currMin, idx)
    else
      (currMin, idx)

end Reductions

section Examples

/- Example usage:
#eval min #[3, 1, 4, 1, 5, 9] (by simp)
-- Output: 1

#eval minWithIndex #[3, 1, 4, 1, 5, 9] (by simp)
-- Output: (1, 1)

#eval minOption #[]
-- Output: none

#eval minOption #[42]
-- Output: some 42

#eval minWithDefault #[] 999
-- Output: 999

#check minVec ⟨#[1, 2, 3], rfl⟩
-- Type: Int
-/

end Examples

end DafnySpecs.NpMin