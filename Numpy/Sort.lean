/-
# NumPy Sorting Functions

This module provides mathematical specifications for NumPy's sorting functionality.
Based on https://numpy.org/devdocs/reference/routines.sort.html

## Key Concepts
1. **Permutation**: The sorted array contains the same elements as the input array
2. **Ordering**: Elements are arranged in non-decreasing order
3. **Stability**: Equal elements maintain their relative positions
-/

namespace Numpy.Sort

/-- Predicate indicating if an array is ordered (non-decreasing) -/
def isOrdered {α : Type} [Ord α] [LE α] [Inhabited α] (a : Array α) : Prop :=
  ∀ i j, i < j → j < a.size → a[i]! ≤ a[j]!

/-- Predicate indicating if one array is a permutation of another -/
def isPerm {α : Type} [BEq α] (a b : Array α) : Prop :=
  a.size = b.size ∧ ∀ x, (a.foldl (fun count y => if y == x then count + 1 else count) 0) = (b.foldl (fun count y => if y == x then count + 1 else count) 0)

/-- Element-wise sort of an array -/
def sort {α : Type} [Ord α] (a : Array α) : Array α :=
  sorry

/-- Specification: Sorting is idempotent -/
theorem sort_idempotent {α : Type} [Ord α] (a : Array α) :
  sort (sort a) = sort a := sorry

/-- Specification: Sorting produces an ordered array -/
theorem sort_ordered {α : Type} [Ord α] [LE α] [Inhabited α] (a : Array α) :
  isOrdered (sort a) := sorry

/-- Specification: Sorting preserves elements (permutation) -/
theorem sort_perm {α : Type} [Ord α] [BEq α] (a : Array α) :
  isPerm (sort a) a := sorry

/-- Returns indices that would sort an array -/
def argsort {α : Type} [Ord α] (a : Array α) : Array Nat :=
  sorry

/-- Specification: argsort returns indices within bounds -/
theorem argsort_valid_indices {α : Type} [Ord α] (a : Array α) :
  (argsort a).size = a.size ∧ ∀ i, i < a.size → (argsort a)[i]! < a.size := sorry

/-- Specification: argsort produces indices that would sort the array -/
theorem argsort_sorts {α : Type} [Ord α] [LE α] [Inhabited α] (a : Array α) :
  ∀ i j, i < j → j < a.size → a[(argsort a)[i]!]! ≤ a[(argsort a)[j]!]! := sorry

/-- Performs lexicographical sort on multiple keys -/
def lexsort {α : Type} [Ord α] (keys : Array (Array α)) : Array Nat :=
  sorry

/-- Specification: lexsort returns valid indices -/
theorem lexsort_valid_indices {α : Type} [Ord α] (keys : Array (Array α)) :
  keys.size > 0 → (lexsort keys).size = keys[0]!.size ∧
  ∀ i, i < keys[0]!.size → (lexsort keys)[i]! < keys[0]!.size := sorry

/-- Finds insertion points in a sorted array -/
def searchsorted {α : Type} [Ord α] (a : Array α) (v : α) (side : String := "left") : Nat :=
  sorry

/-- Specification: searchsorted returns a valid insertion point -/
theorem searchsorted_valid_index {α : Type} [Ord α] (a : Array α) (v : α) :
  searchsorted a v ≤ a.size := sorry

/-- Specification: left searchsorted finds first position where v could be inserted -/
theorem searchsorted_left_correct {α : Type} [Ord α] [LE α] [LT α] [Inhabited α] (a : Array α) (v : α) :
  isOrdered a → ∀ i, i < searchsorted a v "left" → i < a.size → a[i]! < v := sorry

/-- Rearranges elements so the kth element is in its final sorted position -/
def partition {α : Type} [Ord α] (a : Array α) (kth : Nat) : Array α :=
  sorry

/-- Specification: partition preserves array size -/
theorem partition_size {α : Type} [Ord α] (a : Array α) (kth : Nat) :
  kth < a.size → (partition a kth).size = a.size := sorry

/-- Specification: partition places kth element in its sorted position -/
theorem partition_kth_position {α : Type} [Ord α] [LE α] [Inhabited α] (a : Array α) (kth : Nat) :
  kth < a.size →
  (∀ i, i < kth → i < a.size → (partition a kth)[i]! ≤ (partition a kth)[kth]!) ∧
  (∀ i, kth < i → i < a.size → (partition a kth)[kth]! ≤ (partition a kth)[i]!) := sorry

/-- Specification: partition result is a permutation of input -/
theorem partition_perm {α : Type} [Ord α] [BEq α] (a : Array α) (kth : Nat) :
  kth < a.size → isPerm (partition a kth) a := sorry

end Numpy.Sort
