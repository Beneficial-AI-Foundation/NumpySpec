/-
# NumPy One-Dimensional Array Functions

This module provides mathematical specifications for NumPy's one-dimensional array functions.
Based on https://numpy.org/doc/stable/reference/routines.array-manipulation.html

## Key Concepts
1. **Shape manipulation**: Functions that change the shape of arrays
2. **Transpose-like operations**: Functions that transpose or permute array dimensions
3. **Changing array dimensions**: Functions that add/remove dimensions
4. **Joining arrays**: Functions that combine multiple arrays
5. **Splitting arrays**: Functions that split arrays into multiple subarrays
-/

namespace Numpy.OneDimensional

/-- Reshape an array to a given shape -/
def reshape {α : Type} (a : Array α) (shape : Array Nat) : Array α :=
  sorry

/-- Specification: reshape preserves the total number of elements -/
theorem reshape_preserves_size {α : Type} (a : Array α) (shape : Array Nat) :
  a.size = shape.foldl (fun acc x => acc * x) 1 → (reshape a shape).size = a.size := sorry

/-- Transpose an array by swapping dimensions -/
def transpose {α : Type} (a : Array (Array α)) : Array (Array α) :=
  sorry

/-- Specification: transpose preserves all elements -/
theorem transpose_preserves_elements {α : Type} [BEq α] [Inhabited α] (a : Array (Array α)) :
  a.size > 0 → 
  ∀ i j, i < a.size → j < a[0]!.size → 
  (transpose a)[j]![i]! = a[i]![j]! := sorry

/-- Flatten a multi-dimensional array into a 1D array -/
def flatten {α : Type} (a : Array (Array α)) : Array α :=
  sorry

/-- Specification: flatten preserves the total number of elements -/
theorem flatten_preserves_size {α : Type} (a : Array (Array α)) :
  (flatten a).size = a.foldl (fun acc x => acc + x.size) 0 := sorry

/-- Concatenate arrays along a specified axis -/
def concatenate {α : Type} (arrays : Array (Array α)) (axis : Nat := 0) : Array α :=
  sorry

/-- Specification: concatenate preserves the total number of elements -/
theorem concatenate_preserves_size {α : Type} (arrays : Array (Array α)) (axis : Nat := 0) :
  (concatenate arrays axis).size = arrays.foldl (fun acc x => acc + x.size) 0 := sorry

/-- Stack arrays along a new axis -/
def stack {α : Type} (arrays : Array (Array α)) (axis : Nat := 0) : Array (Array α) :=
  sorry

/-- Specification: stack preserves the dimensions of input arrays -/
theorem stack_preserves_dims {α : Type} (arrays : Array (Array α)) (axis : Nat := 0) :
  arrays.size > 0 → 
  (stack arrays axis).size = arrays.size := sorry

/-- Split an array into multiple sub-arrays -/
def split {α : Type} (a : Array α) (sections : Array Nat) (axis : Nat := 0) : Array (Array α) :=
  sorry

/-- Specification: split preserves all elements -/
theorem split_preserves_elements {α : Type} (a : Array α) (sections : Array Nat) (axis : Nat := 0) :
  (split a sections axis).foldl (fun acc x => acc + x.size) 0 = a.size := sorry

/-- Roll array elements along a given axis -/
def roll {α : Type} (a : Array α) (shift : Int) (axis : Nat := 0) : Array α :=
  sorry

/-- Specification: roll preserves array size -/
theorem roll_preserves_size {α : Type} (a : Array α) (shift : Int) (axis : Nat := 0) :
  (roll a shift axis).size = a.size := sorry

/-- Repeat elements of an array (named repeatArray to avoid name conflict) -/
def repeatArray {α : Type} (a : Array α) (repeats : Nat) : Array α :=
  sorry

/-- Specification: repeatArray multiplies array size by repeats -/
theorem repeatArray_size {α : Type} (a : Array α) (repeats : Nat) :
  repeats > 0 → (repeatArray a repeats).size = a.size * repeats := sorry

end Numpy.OneDimensional
