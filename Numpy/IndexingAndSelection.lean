/-
# NumPy Indexing and Selection Functions

This module provides mathematical specifications for NumPy's indexing and selection functionality.
Based on https://numpy.org/doc/stable/reference/arrays.indexing.html

## Key Concepts
1. **Basic Indexing**: Basic slicing and integer arrays indexing
2. **Advanced Indexing**: Boolean arrays indexing and fancy indexing
3. **Selection**: Functions for selecting elements based on conditions
4. **Masking**: Operations using boolean masks
-/

namespace Numpy.IndexingAndSelection

/-- Helper function to check if an index is valid for an array -/
def isValidIndex {α : Type} (a : Array α) (idx : Nat) : Bool :=
  sorry

/-- Helper function to check if a slice is valid -/
def isValidSlice (start : Option Nat) (stop : Option Nat) (step : Option Int) (size : Nat) : Bool :=
  sorry

/-- Get single element from array at given index -/
def getItem {α : Type} [Inhabited α] (a : Array α) (idx : Nat) : α :=
  sorry

/-- Basic array slicing: a[start:stop:step] -/
def slice {α : Type} (a : Array α) (start : Option Nat := none) (stop : Option Nat := none) (step : Option Int := none) : Array α :=
  sorry

/-- Get subset of an array using a boolean mask -/
def booleanMask {α : Type} [Inhabited α] (a : Array α) (mask : Array Bool) : Array α :=
  sorry

/-- Get multiple elements of an array using an array of indices -/
def fancyIndexing {α : Type} [Inhabited α] (a : Array α) (indices : Array Nat) : Array α :=
  sorry

/-- Get diagonals from a 2D array -/
def diagonal {α : Type} (a : Array (Array α)) (offset : Int := 0) : Array α :=
  sorry

/-- Take elements from an array along an axis -/
def take {α : Type} [Inhabited α] (a : Array α) (indices : Array Nat) (axis : Option Nat := none) : Array α :=
  sorry

/-- Insert values along the given axis before the given indices -/
def insert {α : Type} [Inhabited α] (arr : Array α) (obj : Array α) (indices : Array Nat) (axis : Option Nat := none) : Array α :=
  sorry

/-- Return selected slices of an array along given axis -/
def select {α : Type} [Inhabited α] (arr : Array α) (indices : Array Nat) (axis : Option Nat := none) : Array α :=
  sorry

/-- Return a masked array where a condition is False -/
def masked_array {α : Type} [Inhabited α] (arr : Array α) (mask : Array Bool) : Array (Option α) :=
  sorry

/-- Fill in masked values with a given value -/
def fill_masked {α : Type} [Inhabited α] (arr : Array (Option α)) (fillValue : α) : Array α :=
  sorry

/-- Put values into an array at the specified indices -/
def put {α : Type} [Inhabited α] (arr : Array α) (indices : Array Nat) (values : Array α) : Array α :=
  sorry

/-- Set array values using boolean mask -/
def putmask {α : Type} [Inhabited α] (arr : Array α) (mask : Array Bool) (values : Array α) : Array α :=
  sorry

/-- Return indices that would sort an array -/
def argsort {α : Type} [Ord α] (arr : Array α) (axis : Option Nat := none) : Array Nat :=
  sorry

/-- Theorem: slicing with all elements returns the original array -/
theorem slice_identity {α : Type} [BEq α] (a : Array α) :
  slice a none none none = a := sorry

/-- Theorem: getItem is consistent with array access -/
theorem getItem_consistent {α : Type} [Inhabited α] [BEq α] (a : Array α) (idx : Nat) :
  isValidIndex a idx → getItem a idx = a[idx]! := sorry

/-- Theorem: take selects elements at specified indices -/
theorem take_selects_elements {α : Type} [Inhabited α] [BEq α] (a : Array α) (indices : Array Nat) :
  indices.all (isValidIndex a) → 
  ∀ i, i < indices.size → (take a indices none)[i]! = a[indices[i]!]! := sorry

/-- Theorem: boolean mask selects elements where mask is true -/
theorem boolean_mask_selects {α : Type} [BEq α] [Inhabited α] (a : Array α) (mask : Array Bool) :
  a.size = mask.size →
  let result := booleanMask a mask;
  let trueIndices := mask.zipIdx.filter (fun p => p.1) |>.map (fun p => p.2);
  result.size = trueIndices.size ∧
  ∀ i, i < result.size → result[i]! = a[trueIndices[i]!]! := sorry

/-- Theorem: argsort produces indices that would sort the array -/
theorem argsort_produces_sort_indices {α : Type} [Ord α] [BEq α] [Inhabited α] [LE α] (arr : Array α) :
  let indices := argsort arr none;
  indices.size = arr.size ∧
  ∀ i j, i < indices.size → j < indices.size → i < j → 
    arr[indices[i]!]! ≤ arr[indices[j]!]! := sorry

/-- Theorem: diagonal extracts the actual diagonal elements -/
theorem diagonal_correct {α : Type} [BEq α] [Inhabited α] (a : Array (Array α)) (offset : Int := 0) :
  let result := diagonal a offset;
  ∀ i, i < result.size → 
    (offset ≥ 0 → result[i]! = a[i]![i + offset.toNat]!) ∧
    (offset < 0 → result[i]! = a[i + (-offset).toNat]![i]!) := sorry

end Numpy.IndexingAndSelection
