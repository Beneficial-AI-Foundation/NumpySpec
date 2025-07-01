import Std.Do

/-!
# Array Range Generation Specification

Port of `np_arange.dfy` to idiomatic Lean 4.

This module provides several approaches to generating arrays with evenly spaced values:
1. Runtime constraints via hypotheses
2. Compile-time constraints via dependent types
3. Safe APIs with Option types
4. MPL-style specifications for future verification

## Dafny Specification Reference

The original Dafny specification defines:
- `arange(start: real, stop: real, step: real)` - returns array of evenly spaced values
- Requires: `step ≠ 0`
- Requires: if `step < 0` then `start > stop` else `start < stop`
- Ensures: `ret.Length == ((stop - start)/step).Floor`
- Ensures: `ret.Length > 0`
- Ensures: `ret[0] == start`
- Ensures: `∀ i, 1 ≤ i < ret.Length ⟹ ret[i] - ret[i-1] == step`

This Lean implementation provides equivalent functionality with:
- `arange` - core implementation with runtime checks
- `arangeVec` - compile-time size calculation
- `arangeOption` - safe API returning Option
-/

namespace DafnySpecs.NpArange

/-- Calculate the number of elements in the range -/
def rangeSize (start stop step : Int) : Nat :=
  if step = 0 then 0
  else if step > 0 ∧ start < stop then
    ((stop - start + step - 1) / step).toNat
  else if step < 0 ∧ start > stop then
    ((start - stop - step - 1) / (-step)).toNat
  else
    0

/-- Generate array with evenly spaced values.
    
    The hypotheses mirror Dafny's requires clauses:
    - `hstep`: step must be non-zero
    - `hdir`: direction must be consistent (positive step with start < stop, etc.)
-/
def arange (start stop step : Int) 
    (hstep : step ≠ 0)
    (hdir : if step > 0 then start < stop else start > stop) : Array Int :=
  let n := rangeSize start stop step
  Array.ofFn fun i : Fin n => start + step * i

/-- Specification theorem: first element equals start -/
theorem arange_first (start stop step : Int) (hstep : step ≠ 0)
    (hdir : if step > 0 then start < stop else start > stop) 
    (hsize : rangeSize start stop step > 0) :
    (arange start stop step hstep hdir)[0]'(by simp [arange]; exact hsize) = start := by
  simp [arange]

/-- Specification theorem: consecutive elements differ by step -/
theorem arange_step (start stop step : Int) (hstep : step ≠ 0)
    (hdir : if step > 0 then start < stop else start > stop)
    (i : Nat) (hi : i + 1 < (arange start stop step hstep hdir).size) :
    (arange start stop step hstep hdir)[i + 1] - (arange start stop step hstep hdir)[i] = step := by
  simp [arange]
  -- The elements are start + step * index
  show (start + step * (↑i + 1)) - (start + step * ↑i) = step
  rw [Int.mul_add, Int.mul_one]
  simp [Int.add_sub_cancel]

/-- Specification theorem: all elements are within bounds -/
theorem arange_bounds (start stop step : Int) (hstep : step ≠ 0)
    (hdir : if step > 0 then start < stop else start > stop)
    (i : Fin (arange start stop step hstep hdir).size) :
    if step > 0 then
      start ≤ (arange start stop step hstep hdir)[i] ∧ (arange start stop step hstep hdir)[i] < stop
    else
      stop < (arange start stop step hstep hdir)[i] ∧ (arange start stop step hstep hdir)[i] ≤ start := by
  sorry

/- MPL-style specification comment for future verification:
    
    ⦃ step ≠ 0 ∧ (step > 0 → start < stop) ∧ (step < 0 → start > stop) ⦄ 
      arange start stop step
    ⦃ λ res, res.size = rangeSize start stop step ∧
             res.size > 0 ∧
             res[0] = start ∧
             ∀ i : Fin (res.size - 1), res[i.val + 1] - res[i] = step ⦄
    
    When MPL tactics are available, this can be proved using `mspec` or `mvcgen`.
-/

section AlternativeImplementations

/-- Tail-recursive implementation for efficiency -/
def arangeTR (start stop step : Int) 
    (hstep : step ≠ 0)
    (hdir : if step > 0 then start < stop else start > stop) : Array Int :=
  let n := rangeSize start stop step
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if h : i < n then
      loop (i + 1) (acc.push (start + step * i))
    else
      acc
  termination_by n - i
  loop 0 #[]

/-- Theorem: tail-recursive version equals functional version -/
theorem arangeTR_eq_arange (start stop step : Int) (hstep : step ≠ 0)
    (hdir : if step > 0 then start < stop else start > stop) :
    arangeTR start stop step hstep hdir = arange start stop step hstep hdir := by
  sorry

/-- Generate range with default step of 1 -/
def arangeSimple (start stop : Int) (h : start < stop) : Array Int :=
  arange start stop 1 (by simp) (by simp [h])

/-- Generate range from 0 to n (exclusive) -/
def range (n : Nat) : Array Nat :=
  Array.ofFn fun i : Fin n => i.val

end AlternativeImplementations

section VectorApproach

/-- Calculate size at compile time when possible -/
def arangeVecSize (start stop step : Int) (hstep : step ≠ 0)
    (hdir : if step > 0 then start < stop else start > stop) : Nat :=
  rangeSize start stop step

/-- Arange with compile-time size (when parameters are known) -/
def arangeVec (start stop step : Int) (hstep : step ≠ 0)
    (hdir : if step > 0 then start < stop else start > stop) :
    Vector Int (arangeVecSize start stop step hstep hdir) :=
  ⟨arange start stop step hstep hdir, by simp [arange, arangeVecSize]⟩

end VectorApproach

section SafeAPI

/-- Safe arange that returns None for invalid parameters -/
def arangeOption (start stop step : Int) : Option (Array Int) :=
  if hstep : step = 0 then
    none
  else if hdir : (step > 0 ∧ start < stop) ∨ (step < 0 ∧ start > stop) then
    if hpos : step > 0 then
      have hd : start < stop := by
        cases hdir with
        | inl h => exact h.2
        | inr h => have : step < 0 := h.1; omega
      have : (if step > 0 then start < stop else start > stop) := by simp [hpos, hd]
      some (arange start stop step hstep this)
    else
      have hneg : step < 0 := by omega
      have hd : start > stop := by
        cases hdir with
        | inl h => have : step > 0 := h.1; omega
        | inr h => exact h.2
      have : (if step > 0 then start < stop else start > stop) := by 
        split
        · have : step > 0 := by assumption
          omega
        · exact hd
      some (arange start stop step hstep this)
  else
    none

/-- Specification for Option version -/
theorem arangeOption_spec (start stop step : Int) :
    match arangeOption start stop step with
    | none => step = 0 ∨ (step > 0 ∧ start ≥ stop) ∨ (step < 0 ∧ start ≤ stop)
    | some arr => step ≠ 0 ∧ 
                  (if step > 0 then start < stop else start > stop) ∧
                  arr.size > 0 ∧
                  (∀ h : 0 < arr.size, arr[0]'h = start) ∧
                  (∀ i : Nat, ∀ hi : i + 1 < arr.size, arr[i + 1]'hi - arr[i]'(Nat.lt_of_succ_lt hi) = step) := by
  sorry

/-- Arange with default values for common use cases -/
def arangeDefault (stop : Int) : Array Int :=
  arangeOption 0 stop 1 |>.getD #[]

end SafeAPI

section Polymorphic

/-- Polymorphic arange for any numeric type -/
def arangePoly {α : Type} [Add α] [Mul α] [OfNat α 0] [OfNat α 1] [LT α]
    (start stop : α) (step : α) (n : Nat) : Array α :=
  Array.ofFn fun i : Fin n => 
    let rec addStep (x : α) : Nat → α
      | 0 => x
      | k + 1 => addStep (x + step) k
    addStep start i.val

end Polymorphic

section Properties

/-- Empty range when start equals stop -/
theorem arange_empty (start step : Int) (hstep : step ≠ 0) :
    ¬(if step > 0 then start < start else start > start) := by
  split <;> simp

/-- Range size is positive when conditions are met -/
theorem rangeSize_pos (start stop step : Int) (hstep : step ≠ 0)
    (hdir : if step > 0 then start < stop else start > stop) :
    rangeSize start stop step > 0 := by
  sorry

/-- Arange produces strictly increasing sequence for positive step -/
theorem arange_increasing (start stop step : Int) (hstep : step > 0) (hdir : start < stop) :
    let h_nonzero : step ≠ 0 := by omega
    let h_cond : (if step > 0 then start < stop else start > stop) := by simp [hstep, hdir]
    let arr := arange start stop step h_nonzero h_cond
    ∀ i j : Fin arr.size, i < j → arr[i] < arr[j] := by
  sorry

/-- Arange produces strictly decreasing sequence for negative step -/
theorem arange_decreasing (start stop step : Int) (hstep : step < 0) (hdir : start > stop) :
    let h_nonzero : step ≠ 0 := by omega
    let h_cond : (if step > 0 then start < stop else start > stop) := by 
      split
      · have : step > 0 := by assumption
        omega
      · exact hdir
    let arr := arange start stop step h_nonzero h_cond
    ∀ i j : Fin arr.size, i < j → arr[i] > arr[j] := by
  sorry

/-- Last element is within step distance of stop -/
theorem arange_last_bound (start stop step : Int) (hstep : step ≠ 0)
    (hdir : if step > 0 then start < stop else start > stop) :
    let arr := arange start stop step hstep hdir
    let h_pos : 0 < arr.size := by
      simp [arange]
      sorry
    let last := arr[arr.size - 1]'(Nat.sub_lt h_pos (by simp))
    if step > 0 then
      last < stop ∧ last + step ≥ stop
    else
      last > stop ∧ last + step ≤ stop := by
  sorry

end Properties

section FloatSupport

/-- Arange for floating point numbers (using Float as approximation of real) -/
def arangeFloat (start stop step : Float) : Array Float :=
  if hstep : step == 0.0 then #[]
  else if (step > 0 ∧ start < stop) ∨ (step < 0 ∧ start > stop) then
    let n := ((stop - start) / step).floor.toUInt64.toNat
    Array.ofFn fun i : Fin n => start + step * i.val.toFloat
  else #[]

end FloatSupport

section Examples

/- Example usage:
#eval arange 0 5 1 (by simp) (by simp)
-- Output: #[0, 1, 2, 3, 4]

#eval arange 1 10 2 (by simp) (by simp)
-- Output: #[1, 3, 5, 7, 9]

#eval arange 10 0 (-2) (by simp) (by simp)
-- Output: #[10, 8, 6, 4, 2]

#eval arangeOption 5 5 1
-- Output: none

#eval arangeDefault 5
-- Output: #[0, 1, 2, 3, 4]

#eval range 5
-- Output: #[0, 1, 2, 3, 4]
-/

end Examples

end DafnySpecs.NpArange