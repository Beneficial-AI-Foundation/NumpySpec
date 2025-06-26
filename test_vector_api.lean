import Lean

-- Examples of creating range/arange functions for Vector type

namespace VectorRange

/-- Create a vector of sequential natural numbers from 0 to n-1 -/
def range (n : Nat) : Vector Nat n :=
  Vector.ofFn (fun i => i.val)

/-- Create a vector of sequential natural numbers starting from `start` -/
def arange (n : Nat) (start : Nat := 0) : Vector Nat n :=
  Vector.ofFn (fun i => start + i.val)

/-- Create a vector of sequential integers with a given start and step -/
def arangeStep (n : Nat) (start : Int) (step : Int) : Vector Int n :=
  Vector.ofFn (fun i => start + step * i.val)

/-- Create a vector of floats from start to stop with n elements -/
def linspace (n : Nat) (start stop : Float) : Vector Float n :=
  if h : n = 0 then
    h ▸ Vector.ofFn (fun i => absurd i.isLt (Nat.not_lt_zero _))
  else if h2 : n = 1 then
    h2 ▸ Vector.ofFn (fun _ => start)
  else
    let step := (stop - start) / (n - 1).toFloat
    Vector.ofFn (fun i => start + step * i.val.toFloat)

-- Helper to convert to list for testing
def vectorToList {α : Type} {n : Nat} (v : Vector α n) : List α :=
  v.toArray.toList

-- Examples
#eval vectorToList (range 5)  -- [0, 1, 2, 3, 4]
#eval vectorToList (arange 5 10)  -- [10, 11, 12, 13, 14]
#eval vectorToList (arangeStep 5 20 (-3))  -- [20, 17, 14, 11, 8]
#eval vectorToList (linspace 5 0.0 10.0)  -- [0.0, 2.5, 5.0, 7.5, 10.0]

-- Theorems about range functions
theorem range_get (n : Nat) (i : Fin n) : (range n)[i] = i.val := by
  simp [range]

theorem arange_get (n : Nat) (start : Nat) (i : Fin n) : 
    (arange n start)[i] = start + i.val := by
  simp [arange]

theorem arangeStep_get (n : Nat) (start step : Int) (i : Fin n) : 
    (arangeStep n start step)[i] = start + step * i.val := by
  simp [arangeStep]

-- Example: Create a 5x5 identity-like pattern using range
def identityPattern : Vector (Vector Nat 5) 5 :=
  Vector.ofFn fun i => Vector.ofFn fun j => if i = j then 1 else 0

#eval identityPattern.toArray.map vectorToList

-- Create coordinates for 2D grid
def meshgrid (m n : Nat) : Vector (Vector (Nat × Nat) n) m :=
  Vector.ofFn fun i => Vector.ofFn fun j => (i.val, j.val)

#eval (meshgrid 3 4).toArray.map fun row => row.toArray.toList

end VectorRange

-- Alternative using a custom structure similar to List.Vector
structure ListVector (α : Type) (n : Nat) where
  data : List α
  size_proof : data.length = n

namespace ListVector

def ofFn {α : Type} {n : Nat} (f : Fin n → α) : ListVector α n :=
  { data := List.ofFn f, size_proof := List.length_ofFn }

def range (n : Nat) : ListVector Nat n :=
  ofFn (fun i => i.val)

def arange (n : Nat) (start : Nat := 0) : ListVector Nat n :=
  ofFn (fun i => start + i.val)

def arangeStep (n : Nat) (start : Int) (step : Int) : ListVector Int n :=
  ofFn (fun i => start + step * i.val)

-- Examples
#eval (range 5).data  -- [0, 1, 2, 3, 4]
#eval (arange 5 10).data  -- [10, 11, 12, 13, 14]
#eval (arangeStep 5 20 (-3)).data  -- [20, 17, 14, 11, 8]

end ListVector

-- Summary: Common patterns for creating range/arange functions in Lean 4
/-
For Vector type (Lean's built-in fixed-size array wrapper):
- Use `Vector.ofFn` with a function that generates values based on index
- Access elements with bracket notation `v[i]`
- Convert to list with `v.toArray.toList` for display

For custom ListVector type:
- Use `List.ofFn` to create the underlying list
- Prove the length property with `List.length_ofFn`

Common patterns:
1. range(n) = [0, 1, ..., n-1]
   Vector.ofFn (fun i => i.val)

2. arange(n, start) = [start, start+1, ..., start+n-1]
   Vector.ofFn (fun i => start + i.val)

3. arangeStep(n, start, step) = [start, start+step, ..., start+(n-1)*step]
   Vector.ofFn (fun i => start + step * i.val)

4. linspace(n, start, stop) = n evenly spaced values from start to stop
   Vector.ofFn (fun i => start + (stop - start) * i.val / (n-1))
-/