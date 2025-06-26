import Lean

namespace NDArray

/-- Compute the total number of elements from a shape vector -/
def shapeSize {n : Nat} (shape : Vector Nat n) : Nat :=
  shape.toArray.foldl (· * ·) 1

/-- Compute row-major strides for a shape -/
def computeStrides {n : Nat} (shape : Vector Nat n) : Array Nat := Id.run do
  let shapeArr := shape.toArray
  let mut strides := Array.mkEmpty n
  let mut stride := 1
  -- Build strides from right to left
  for i in [:n] do
    let idx := n - 1 - i
    strides := strides.push stride
    if idx < shapeArr.size then
      stride := stride * shapeArr[idx]!
  return strides

/-- Index type that matches the shape dimensions using Vector -/
structure Index {n : Nat} (shape : Vector Nat n) where
  coords : Vector Nat n
  valid : ∀ i : Fin n, coords.get i < shape.get i

namespace Index

/-- Convert an index to a linear position using row-major order -/
def toLinear {n : Nat} {shape : Vector Nat n} (idx : Index shape) : Nat := Id.run do
  let strides := computeStrides shape
  let mut pos := 0
  for i in [:n] do
    if i < idx.coords.toArray.size && i < strides.size then
      pos := pos + idx.coords.toArray[i]! * strides[i]!
  return pos

/-- Create an index from an array with bounds checking -/
def fromArray? {n : Nat} (shape : Vector Nat n) (arr : Array Nat) : Option (Index shape) :=
  if h : arr.size = n then
    let coords := Vector.ofFn fun i =>
      if h2 : i.val < arr.size then arr[i.val] else 0
    if valid : ∀ i : Fin n, coords.get i < shape.get i then
      some ⟨coords, valid⟩
    else
      none
  else
    none

end Index

/-- Main NDArray structure with compile-time shape using Vector -/
structure NDArray (α : Type) (n : Nat) (shape : Vector Nat n) where
  data : Array α
  size_proof : data.size = shapeSize shape

namespace NDArray

/-- Create an array filled with zeros -/
def zeros [Inhabited α] [OfNat α 0] {n : Nat} (shape : Vector Nat n) : NDArray α n shape :=
  { data := Array.replicate (shapeSize shape) (0 : α)
    size_proof := by simp [Array.size_replicate] }

/-- Create an array filled with ones -/
def ones [Inhabited α] [OfNat α 1] {n : Nat} (shape : Vector Nat n) : NDArray α n shape :=
  { data := Array.replicate (shapeSize shape) (1 : α)
    size_proof := by simp [Array.size_replicate] }

/-- Create an array with sequential values -/
def arange {n : Nat} (shape : Vector Nat n) : NDArray Nat n shape :=
  { data := Array.range (shapeSize shape)
    size_proof := Array.size_range }

/-- Create an array with sequential values using Array.ofFn -/
def arangeV {n : Nat} (shape : Vector Nat n) : NDArray Nat n shape :=
  { data := Array.ofFn (n := shapeSize shape) fun i => i.val
    size_proof := by simp }

/-- Get element at index -/
def get [Inhabited α] {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) (idx : Index shape) : α :=
  let pos := idx.toLinear
  if h : pos < arr.data.size then
    arr.data[pos]
  else
    panic! "Index out of bounds"

/-- Get element at index, returning Option -/
def get? {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) (idx : Index shape) : Option α :=
  let pos := idx.toLinear
  if h : pos < arr.data.size then
    some arr.data[pos]
  else
    none

/-- Set element at index -/
def set {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) (idx : Index shape) (val : α) : NDArray α n shape :=
  let pos := idx.toLinear
  if h : pos < arr.data.size then
    { data := arr.data.set pos val, size_proof := by simp [arr.size_proof] }
  else
    arr

/-- Set element at index, returning Option -/
def set? {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) (idx : Index shape) (val : α) : Option (NDArray α n shape) :=
  let pos := idx.toLinear
  if h : pos < arr.data.size then
    some { data := arr.data.set pos val, size_proof := by simp [arr.size_proof] }
  else
    none

/-- Map a function over all elements -/
def map {n : Nat} {shape : Vector Nat n} (f : α → β) (arr : NDArray α n shape) : NDArray β n shape :=
  { data := arr.data.map f
    size_proof := by simp [arr.size_proof] }

/-- Map a binary function over two arrays with the same shape -/
def map2 [Inhabited α] [Inhabited β] {n : Nat} {shape : Vector Nat n}
    (f : α → β → γ) (arr1 : NDArray α n shape) (arr2 : NDArray β n shape) : NDArray γ n shape :=
  { data := arr1.data.zipWith f arr2.data
    size_proof := by 
      simp [Array.size_zipWith, arr1.size_proof, arr2.size_proof, Nat.min_self] }

/-- Fold over all elements -/
def fold {n : Nat} {shape : Vector Nat n} (f : β → α → β) (init : β) (arr : NDArray α n shape) : β :=
  arr.data.foldl f init

/-- Sum all elements -/
def sum [Add α] [OfNat α 0] {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) : α :=
  arr.fold (· + ·) 0

/-- Product of all elements -/
def prod [Mul α] [OfNat α 1] {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) : α :=
  arr.fold (· * ·) 1

/-- Reshape an array to a new shape with the same total size -/
def reshape {n m : Nat} {shape1 : Vector Nat n} {shape2 : Vector Nat m}
    (arr : NDArray α n shape1) (h : shapeSize shape1 = shapeSize shape2) : NDArray α m shape2 :=
  { data := arr.data
    size_proof := by rw [arr.size_proof, h] }

/-- Convert array to list for testing/display -/
def toList {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) : List α :=
  arr.data.toList

/-- Convert array to nested array structure for display -/
def toArray {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) : Array α :=
  arr.data

/-- Create from an array with a given shape -/
def fromArray {n : Nat} {shape : Vector Nat n} (data : Array α) (h : data.size = shapeSize shape) : NDArray α n shape :=
  { data := data, size_proof := h }

/-- Create from a list with a given shape -/
def fromList {n : Nat} {shape : Vector Nat n} (xs : List α) (h : xs.length = shapeSize shape) : NDArray α n shape :=
  fromArray xs.toArray (by simp [h])

/-- Try to create from a list with a given shape -/
def fromList? {n : Nat} {shape : Vector Nat n} (xs : List α) : Option (NDArray α n shape) :=
  if h : xs.length = shapeSize shape then
    some (fromList xs h)
  else
    none

/-- Try to create from an array with a given shape -/
def fromArray? {n : Nat} {shape : Vector Nat n} (data : Array α) : Option (NDArray α n shape) :=
  if h : data.size = shapeSize shape then
    some (fromArray data h)
  else
    none

/-- Element-wise addition -/
instance [Add α] [Inhabited α] : Add (NDArray α n shape) where
  add a b := map2 (· + ·) a b

/-- Element-wise multiplication -/
instance [Mul α] [Inhabited α] : Mul (NDArray α n shape) where
  mul a b := map2 (· * ·) a b

/-- GetElem instance for NDArray to enable bracket notation -/
instance [Inhabited α] : GetElem (NDArray α n shape) (Index shape) α (fun _ _ => True) where
  getElem arr idx _ := arr.get idx

/-- Helper to create a shape vector from a list -/
def shapeFromList (dims : List Nat) : Vector Nat dims.length :=
  Vector.ofFn fun i => dims[i.val]!

/-- Get the size (number of dimensions) of the NDArray -/
def rank {n : Nat} {shape : Vector Nat n} (_ : NDArray α n shape) : Nat := n

/-- Get the shape as a Vector -/
def shape {n : Nat} {shape : Vector Nat n} (_ : NDArray α n shape) : Vector Nat n := shape

/-- Get the total number of elements -/
def size {n : Nat} {shape : Vector Nat n} (_ : NDArray α n shape) : Nat := shapeSize shape

end NDArray

end NDArray
