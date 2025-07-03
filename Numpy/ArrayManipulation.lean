/-
# NumPy Array Manipulation Functions

This module provides mathematical specifications for NumPy's array manipulation functionality.
Based on https://numpy.org/doc/stable/reference/routines.array-manipulation.html

## Key Concepts
1. **Basic Operations**: Reshape, transpose, and other basic array transformations
2. **Joining and Splitting**: Functions to combine and separate arrays
3. **Dimensions**: Adding, removing, and rearranging dimensions
4. **Rearranging**: Functions that change the arrangement of elements
-/

namespace Numpy.ArrayManipulation

/-- Helper function to check if a shape is valid for an array -/
def isValidShape {α : Type} (a : Array α) (shape : Array Nat) : Bool :=
  sorry

/-- Change the shape of an array without changing its data -/
def reshape {α : Type} (a : Array α) (newShape : Array Nat) : Array α :=
  sorry

/-- Theorem: Reshape preserves the total number of elements -/
theorem reshape_preserves_elements {α : Type} (a : Array α) (newShape : Array Nat) :
  isValidShape a newShape → a.size = newShape.foldl (· * ·) 1 := sorry

/-- Transpose an array (swap axes) -/
def transpose {α : Type} (a : Array (Array α)) : Array (Array α) :=
  sorry

/-- Theorem: Transpose is its own inverse (transposing twice returns the original) -/
theorem transpose_self_inverse {α : Type} [BEq α] (a : Array (Array α)) :
  transpose (transpose a) = a := sorry

/-- Flatten a multi-dimensional array into a 1D array -/
def flatten {α : Type} (a : Array α) : Array α :=
  sorry

/-- Ravel an array into a 1D array (similar to flatten but may return a view) -/
def ravel {α : Type} (a : Array α) : Array α :=
  sorry

/-- Stack arrays along a new axis -/
def stack {α : Type} [Inhabited α] (arrays : Array (Array α)) (axis : Nat := 0) : Array (Array α) :=
  sorry

/-- Concatenate arrays along an existing axis -/
def concatenate {α : Type} [Inhabited α] (arrays : Array (Array α)) (axis : Nat := 0) : Array (Array α) :=
  sorry

/-- Split an array into multiple sub-arrays -/
def split {α : Type} [Inhabited α] (a : Array (Array α)) (indices_or_sections : Array Nat) (axis : Nat := 0) : Array (Array (Array α)) :=
  sorry

/-- Expand the shape of an array by inserting a new axis at the specified position -/
def expandDims {α : Type} (a : Array α) (axis : Nat) : Array α :=
  sorry

/-- Squeeze out dimensions of length 1 -/
def squeeze {α : Type} (a : Array α) (axis : Option Nat := none) : Array α :=
  sorry

/-- Flip array in the left/right direction -/
def fliplr {α : Type} (m : Array (Array α)) : Array (Array α) :=
  sorry

/-- Flip array in the up/down direction -/
def flipud {α : Type} (m : Array (Array α)) : Array (Array α) :=
  sorry

/-- Roll array elements along a given axis -/
def roll {α : Type} (a : Array α) (shift : Int) (axis : Option Nat := none) : Array α :=
  sorry

/-- Roll the specified axis backwards until it lies in the given position -/
def rollaxis {α : Type} (a : Array α) (axis : Nat) (start : Nat := 0) : Array α :=
  sorry

/-- Rotate an array by 90 degrees counter-clockwise -/
def rot90 {α : Type} (m : Array (Array α)) (k : Nat := 1) : Array (Array α) :=
  sorry

/-- Theorem: Four 90-degree rotations yield the original array -/
theorem rot90_four_rotations {α : Type} [BEq α] (m : Array (Array α)) :
  rot90 (rot90 (rot90 (rot90 m))) = m := sorry

/-- Move axes of an array to new positions -/
def moveaxis {α : Type} (a : Array α) (source : Array Nat) (destination : Array Nat) : Array α :=
  sorry

/-- Convert a 1D array into a 2D column vector -/
def column_stack {α : Type} [Inhabited α] (tup : Array (Array α)) : Array (Array α) :=
  sorry

/-- Convert a 1D array into a 2D row vector -/
def row_stack {α : Type} [Inhabited α] (tup : Array (Array α)) : Array (Array α) :=
  sorry

/-- Repeat elements of an array -/
def repeatArray {α : Type} (a : Array α) (repeats : Nat) (axis : Option Nat := none) : Array α :=
  sorry

/-- Tile an array by repeating it the specified number of times -/
def tile {α : Type} (a : Array α) (reps : Array Nat) : Array α :=
  sorry

end Numpy.ArrayManipulation
