import Std.Do

/-!
# Array Maximum Specification

Port of `np_max.dfy` to idiomatic Lean 4.

This module demonstrates several approaches to finding the maximum element in an array:
1. Runtime constraints via hypotheses (non-empty requirement)
2. Compile-time constraints via dependent types
3. Refinement types for non-empty arrays
4. MPL-style specifications for future verification

The Dafny specification requires:
- Precondition: array length > 0
- Postcondition 1: result equals some element in the array
- Postcondition 2: result is greater than or equal to all elements
-/

namespace DafnySpecs.NpMax

/-- Find maximum element in a non-empty array.
    
    The hypothesis `h` ensures the array is non-empty at the call site.
    This mirrors the Dafny `requires a.Length > 0` clause.
-/
def max (a : Array Int) (h : a.size > 0) : Int :=
  a.foldl (init := a[0]'(h)) max

/-- Specification theorem: the maximum is an element of the array -/
theorem max_exists (a : Array Int) (h : a.size > 0) :
    ∃ i : Fin a.size, max a h = a[i] := by
  sorry -- Proof would use properties of foldl and max

/-- Specification theorem: the maximum is greater than or equal to all elements -/
theorem max_universal (a : Array Int) (h : a.size > 0) :
    ∀ i : Fin a.size, a[i] ≤ max a h := by
  sorry -- Proof would use induction on foldl

/-- Combined specification capturing both Dafny postconditions -/
theorem max_spec (a : Array Int) (h : a.size > 0) :
    (∃ i : Fin a.size, max a h = a[i]) ∧ 
    (∀ i : Fin a.size, a[i] ≤ max a h) := by
  constructor
  · exact max_exists a h
  · exact max_universal a h

/-- MPL-style specification comment for future verification:
    
    ⦃ a.size > 0 ⦄ 
      max a 
    ⦃ λ res, (∃ i : Fin a.size, res = a[i]) ∧ (∀ i : Fin a.size, a[i] ≤ res) ⦄
    
    When MPL tactics are available, this can be proved using `mspec` or `mvcgen`.
-/

/- Alternative implementations with different trade-offs -/

section AlternativeImplementations

/-- Maximum using explicit recursion for clarity -/
def maxRec (a : Array Int) (h : a.size > 0) : Int :=
  go 1 a[0]'(h)
where
  go (i : Nat) (currMax : Int) : Int :=
    if hi : i < a.size then
      go (i + 1) (max currMax a[i])
    else
      currMax

/-- Maximum that returns both the value and its index -/
def maxWithIndex (a : Array Int) (h : a.size > 0) : Int × Fin a.size :=
  a.foldlIdx (init := (a[0]'(h), ⟨0, h⟩)) fun i (currMax, idx) val =>
    if val > currMax then (val, i) else (currMax, idx)

/-- Theorem: maxWithIndex returns a valid maximum and witness index -/
theorem maxWithIndex_correct (a : Array Int) (h : a.size > 0) :
    let (m, idx) := maxWithIndex a h
    m = a[idx] ∧ ∀ i : Fin a.size, a[i] ≤ m := by
  sorry

end AlternativeImplementations

/- Vector approach using compile-time size checking -/

section VectorApproach

/-- Maximum for vectors with compile-time non-empty guarantee -/
def maxVec {n : Nat} (a : Vector Int (n + 1)) : Int :=
  a.toArray.foldl (init := a.get ⟨0, Nat.zero_lt_succ n⟩) max

/-- Vector maximum satisfies the existence property -/
theorem maxVec_exists {n : Nat} (a : Vector Int (n + 1)) :
    ∃ i : Fin (n + 1), maxVec a = a.get i := by
  sorry

/-- Vector maximum satisfies the universal property -/
theorem maxVec_universal {n : Nat} (a : Vector Int (n + 1)) :
    ∀ i : Fin (n + 1), a.get i ≤ maxVec a := by
  sorry

end VectorApproach

/- Refinement type approach -/

section RefinementTypes

/-- Non-empty array as a refinement type -/
abbrev NonEmptyArray (α : Type) := {arr : Array α // arr.size > 0}

/-- Maximum for non-empty arrays using refinement types -/
def maxNonEmpty (a : NonEmptyArray Int) : Int :=
  a.val.foldl (init := a.val[0]'(a.property)) max

/-- Get an element from a non-empty array -/
def NonEmptyArray.get (a : NonEmptyArray α) (i : Fin a.val.size) : α :=
  a.val[i]

/-- Refinement type version preserves specifications -/
theorem maxNonEmpty_spec (a : NonEmptyArray Int) :
    (∃ i : Fin a.val.size, maxNonEmpty a = a.get i) ∧ 
    (∀ i : Fin a.val.size, a.get i ≤ maxNonEmpty a) := by
  sorry

end RefinementTypes

/- Polymorphic versions -/

section Polymorphic

/-- Polymorphic maximum for any linearly ordered type -/
def maxPoly {α : Type} [LinearOrder α] (a : Array α) (h : a.size > 0) : α :=
  a.foldl (init := a[0]'(h)) max

/-- Maximum with custom comparison function -/
def maxBy {α : Type} (a : Array α) (h : a.size > 0) (cmp : α → α → Bool) : α :=
  a.foldl (init := a[0]'(h)) fun x y => if cmp y x then y else x

/-- Maximum by key extraction -/
def maxByKey {α β : Type} [LinearOrder β] (a : Array α) (h : a.size > 0) (key : α → β) : α :=
  a.foldl (init := a[0]'(h)) fun x y => if key y > key x then y else x

end Polymorphic

/- Properties and theorems -/

section Properties

/-- Maximum is idempotent -/
theorem max_singleton (x : Int) :
    max #[x] (by simp) = x := by
  unfold max
  simp

/-- Maximum of two elements -/
theorem max_pair (x y : Int) :
    max #[x, y] (by simp) = Int.max x y := by
  unfold max
  simp [Int.max]

/-- Maximum is preserved under array concatenation -/
theorem max_append (a b : Array Int) (ha : a.size > 0) (hb : b.size > 0) :
    max (a ++ b) (by simp [ha, hb]) = Int.max (max a ha) (max b hb) := by
  sorry

/-- Maximum respects monotone transformations -/
theorem max_map_mono {f : Int → Int} (hf : Monotone f) (a : Array Int) (h : a.size > 0) :
    f (max a h) = max (a.map f) (by simp [h]) := by
  sorry

end Properties

/- Option-based API for more idiomatic Lean -/

section OptionAPI

/-- Safe maximum that returns None for empty arrays -/
def maxOption (a : Array Int) : Option Int :=
  if h : a.size > 0 then
    some (max a h)
  else
    none

/-- Option version specification -/
theorem maxOption_spec (a : Array Int) :
    match maxOption a with
    | none => a.size = 0
    | some m => a.size > 0 ∧ (∃ i : Fin a.size, m = a[i]) ∧ (∀ i : Fin a.size, a[i] ≤ m) := by
  sorry

/-- Maximum with default value for empty arrays -/
def maxWithDefault (a : Array Int) (default : Int) : Int :=
  maxOption a |>.getD default

end OptionAPI

section Examples

/- Example usage:
#eval max #[3, 1, 4, 1, 5, 9] (by simp)
-- Output: 9

#eval maxWithIndex #[3, 1, 4, 1, 5, 9] (by simp)
-- Output: (9, 5)

#eval maxOption #[]
-- Output: none

#eval maxOption #[42]
-- Output: some 42

#check maxVec ⟨#[1, 2, 3], rfl⟩
-- Type: Int
-/

end Examples

end DafnySpecs.NpMax