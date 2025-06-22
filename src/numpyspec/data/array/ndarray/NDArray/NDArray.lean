import Lean

namespace NDArray

/-- Shape represents compile-time array dimensions as a list of natural numbers -/
inductive Shape : Type where
  | nil : Shape
  | cons : Nat → Shape → Shape
  deriving Repr, DecidableEq

namespace Shape

/-- Compute the total number of elements in a shape -/
def size : Shape → Nat
  | nil => 1
  | cons n s => n * s.size

/-- Get the number of dimensions (rank) of a shape -/
def rank : Shape → Nat
  | nil => 0
  | cons _ s => 1 + s.rank

/-- Convert shape to a list for display purposes -/
def toList : Shape → List Nat
  | nil => []
  | cons n s => n :: s.toList

/-- Create a shape from a list -/
def fromList : List Nat → Shape
  | [] => nil
  | n :: ns => cons n (fromList ns)

/-- Check if two shapes are compatible for element-wise operations -/
def compatible (s1 s2 : Shape) : Bool :=
  s1 = s2

/-- Get the i-th dimension (0-indexed) -/
def get? : Shape → Nat → Option Nat
  | nil, _ => none
  | cons n _, 0 => some n
  | cons _ s, i+1 => s.get? i

end Shape

/-- Index type that matches the shape dimensions -/
inductive Index : Shape → Type where
  | nil : Index Shape.nil
  | cons : {n : Nat} → {s : Shape} → Nat → Index s → Index (Shape.cons n s)

namespace Index

/-- Convert an index to a linear position -/
def toLinear : {s : Shape} → Index s → Nat
  | _, Index.nil => 0
  | Shape.cons _ s, Index.cons i idx => i * s.size + toLinear idx

/-- Create an index from a list (with bounds checking) -/
def fromList? : (s : Shape) → List Nat → Option (Index s)
  | Shape.nil, [] => some Index.nil
  | Shape.cons n s, i :: is => do
    if i < n then
      let idx ← fromList? s is
      some (Index.cons i idx)
    else
      none
  | _, _ => none

end Index

/-- Main NDArray structure with compile-time shape -/
structure NDArray (α : Type) (shape : Shape) where
  data : Array α
  size_proof : data.size = shape.size

namespace NDArray

/-- Create an array filled with zeros -/
def zeros [Inhabited α] [OfNat α 0] (shape : Shape) : NDArray α shape :=
  { data := Array.replicate shape.size (0 : α)
    size_proof := by simp [Array.size_replicate] }

/-- Create an array filled with ones -/
def ones [Inhabited α] [OfNat α 1] (shape : Shape) : NDArray α shape :=
  { data := Array.replicate shape.size (1 : α)
    size_proof := by simp [Array.size_replicate] }

/-- Create an array with sequential values -/
def arange (shape : Shape) : NDArray Nat shape :=
  let rec fill (i : Nat) (acc : Array Nat) (fuel : Nat) : Array Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 => 
      if i < shape.size then
        fill (i + 1) (acc.push i) fuel'
      else
        acc
  { data := fill 0 #[] shape.size
    size_proof := sorry } -- Will implement proof properly

/-- Get element at index -/
def get [Inhabited α] {shape : Shape} (arr : NDArray α shape) (idx : Index shape) : α :=
  let pos := Index.toLinear idx
  if h : pos < arr.data.size then
    arr.data[pos]
  else
    panic! "Index out of bounds"

/-- Set element at index -/
def set {shape : Shape} (arr : NDArray α shape) (idx : Index shape) (val : α) : NDArray α shape :=
  let pos := Index.toLinear idx
  if h : pos < arr.data.size then
    { data := arr.data.set pos val, size_proof := by simp [arr.size_proof] }
  else
    arr

/-- Map a function over all elements -/
def map {shape : Shape} (f : α → β) (arr : NDArray α shape) : NDArray β shape :=
  { data := arr.data.map f
    size_proof := by simp [arr.size_proof] }

/-- Map a binary function over two arrays with the same shape -/
def map2 [Inhabited α] [Inhabited β] {shape : Shape} (f : α → β → γ) (arr1 : NDArray α shape) (arr2 : NDArray β shape) : NDArray γ shape :=
  let rec zipWith' (i : Nat) (acc : Array γ) : Array γ :=
    if h : i < shape.size then
      let v1 := if h1 : i < arr1.data.size then arr1.data[i] else panic! "index out of bounds"
      let v2 := if h2 : i < arr2.data.size then arr2.data[i] else panic! "index out of bounds"
      zipWith' (i + 1) (acc.push (f v1 v2))
    else
      acc
  { data := zipWith' 0 #[]
    size_proof := sorry }

/-- Fold over all elements -/
def fold {shape : Shape} (f : β → α → β) (init : β) (arr : NDArray α shape) : β :=
  arr.data.foldl f init

/-- Sum all elements -/
def sum [Add α] [OfNat α 0] {shape : Shape} (arr : NDArray α shape) : α :=
  arr.fold (· + ·) 0

/-- Reshape an array to a new shape with the same total size -/
def reshape {s1 s2 : Shape} (arr : NDArray α s1) (h : s1.size = s2.size) : NDArray α s2 :=
  { data := arr.data
    size_proof := by rw [arr.size_proof, h] }

/-- Convert array to list for testing/display -/
def toList {shape : Shape} (arr : NDArray α shape) : List α :=
  arr.data.toList

/-- Create from a list with a given shape -/
def fromList {shape : Shape} (xs : List α) (h : xs.length = shape.size) : NDArray α shape :=
  { data := xs.toArray, size_proof := by simp [h] }

/-- Try to create from a list with a given shape -/
def fromList? {shape : Shape} (xs : List α) : Option (NDArray α shape) :=
  if h : xs.length = shape.size then
    some (fromList xs h)
  else
    none

end NDArray

end NDArray