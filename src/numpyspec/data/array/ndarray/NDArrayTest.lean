import NDArray.NDArray

open NDArray

-- Helper to create indices more easily
def idx1 (i : Nat) : Index (Shape.cons n Shape.nil) := Index.cons i Index.nil
def idx2 (i j : Nat) : Index (Shape.cons m (Shape.cons n Shape.nil)) := Index.cons i (Index.cons j Index.nil)
def idx3 (i j k : Nat) : Index (Shape.cons l (Shape.cons m (Shape.cons n Shape.nil))) :=
  Index.cons i (Index.cons j (Index.cons k Index.nil))
def idx4 (i j k l : Nat) : Index (Shape.cons a (Shape.cons b (Shape.cons c (Shape.cons d Shape.nil)))) :=
  Index.cons i (Index.cons j (Index.cons k (Index.cons l Index.nil)))

/-- Test suite for NDArray implementation -/
def testSuite : IO Unit := do
  IO.println "=== NDArray Test Suite ==="
  IO.println ""

  -- Test Shape operations
  IO.println "-- Shape Tests --"
  let shape1d := Shape.cons 5 Shape.nil
  let shape2d := Shape.cons 3 (Shape.cons 4 Shape.nil)
  let shape3d := Shape.cons 2 (Shape.cons 3 (Shape.cons 4 Shape.nil))
  let shape4d := Shape.cons 10 (Shape.cons 28 (Shape.cons 28 (Shape.cons 3 Shape.nil)))
  let shape5d := Shape.cons 2 (Shape.cons 3 (Shape.cons 4 (Shape.cons 5 (Shape.cons 6 Shape.nil))))

  IO.println s!"1D shape [5]: size = {shape1d.size}, rank = {shape1d.rank}"
  IO.println s!"2D shape [3,4]: size = {shape2d.size}, rank = {shape2d.rank}"
  IO.println s!"3D shape [2,3,4]: size = {shape3d.size}, rank = {shape3d.rank}"
  IO.println s!"4D shape [10,28,28,3]: size = {shape4d.size}, rank = {shape4d.rank}"
  IO.println s!"5D shape [2,3,4,5,6]: size = {shape5d.size}, rank = {shape5d.rank}"
  IO.println ""

  -- Test 1D arrays
  IO.println "-- 1D Array Tests --"
  let arr1d : NDArray Nat shape1d := NDArray.arange shape1d
  IO.println s!"1D array created with arange: {arr1d.toList}"

  let zeros1d : NDArray Nat shape1d := NDArray.zeros shape1d
  IO.println s!"1D zeros: {zeros1d.toList}"

  let ones1d : NDArray Nat shape1d := NDArray.ones shape1d
  IO.println s!"1D ones: {ones1d.toList}"

  -- Test element access
  if let some idx := Index.fromList? shape1d [2] then
    IO.println s!"arr1d[2] = {arr1d.get idx}"

  IO.println ""

  -- Test 2D arrays (matrices)
  IO.println "-- 2D Array Tests (Matrices) --"
  let mat : NDArray Nat shape2d := NDArray.arange shape2d
  IO.println s!"2D matrix [3,4]: {mat.toList}"

  -- Access element at (1,2)
  if let some idx := Index.fromList? shape2d [1, 2] then
    IO.println s!"mat[1,2] = {mat.get idx}"

  -- Test operations
  let mat2 := mat.map (· * 2)
  IO.println s!"Matrix * 2: {mat2.toList}"

  let matSum := mat.sum
  IO.println s!"Sum of all elements: {matSum}"
  IO.println ""

  -- Test 3D arrays
  IO.println "-- 3D Array Tests --"
  let arr3d : NDArray Nat shape3d := NDArray.arange shape3d
  IO.println s!"3D array [2,3,4] size: {arr3d.data.size}"
  IO.println s!"First 10 elements: {arr3d.toList.take 10}"

  -- Access element at (0,1,2)
  if let some idx := Index.fromList? shape3d [0, 1, 2] then
    IO.println s!"arr3d[0,1,2] = {arr3d.get idx}"

  -- Test slice-like operation (getting all elements at position [1,*,*])
  IO.println "Elements at arr3d[1,*,*]:"
  for i in [0:3] do
    for j in [0:4] do
      if let some idx := Index.fromList? shape3d [1, i, j] then
        IO.print s!"{arr3d.get idx} "
    IO.println ""
  IO.println ""

  -- Test 4D arrays (common in ML - batch × height × width × channels)
  IO.println "-- 4D Array Tests (ML-style: batch × height × width × channels) --"
  let batch_size := 10
  let height := 28
  let width := 28
  let channels := 3
  -- Note: Creating smaller array for demo
  let shape4d_small := Shape.cons 2 (Shape.cons 4 (Shape.cons 4 (Shape.cons 3 Shape.nil)))
  let images : NDArray Nat shape4d_small := NDArray.zeros shape4d_small
  IO.println s!"4D image batch [2,4,4,3] created with size: {images.data.size}"

  -- Simulate accessing first image, first pixel, all channels
  IO.println "First pixel channels of first image:"
  for c in [0:3] do
    if let some idx := Index.fromList? shape4d_small [0, 0, 0, c] then
      IO.print s!"{images.get idx} "
  IO.println ""
  IO.println ""

  -- Test 5D arrays
  IO.println "-- 5D Array Tests --"
  let shape5d_small := Shape.cons 2 (Shape.cons 2 (Shape.cons 2 (Shape.cons 2 (Shape.cons 2 Shape.nil))))
  let arr5d : NDArray Nat shape5d_small := NDArray.ones shape5d_small
  IO.println s!"5D array [2,2,2,2,2] created with size: {arr5d.data.size}"
  IO.println s!"All elements (should be all 1s): {arr5d.toList}"
  IO.println ""

  -- Test reshaping
  IO.println "-- Reshape Tests --"
  let shape_before := Shape.cons 6 (Shape.cons 4 Shape.nil)
  let shape_after := Shape.cons 8 (Shape.cons 3 Shape.nil)
  let arr_reshape : NDArray Nat shape_before := NDArray.arange shape_before
  IO.println s!"Original shape [6,4]: {arr_reshape.toList}"

  -- Note: Can only reshape if sizes match (6*4 = 24 = 8*3)
  if h : shape_before.size = shape_after.size then
    let reshaped := arr_reshape.reshape h
    IO.println s!"Reshaped to [8,3]: {reshaped.toList}"
  else
    IO.println "Cannot reshape: sizes don't match"
  IO.println ""

  -- Test edge cases
  IO.println "-- Edge Cases --"

  -- Scalar (0D array)
  let scalar := NDArray.ones Shape.nil
  IO.println s!"Scalar (0D array): {scalar.toList}"

  -- Single element arrays
  let single1d := Shape.cons 1 Shape.nil
  match NDArray.fromList? (shape := single1d) [42] with
  | some arr_single => IO.println s!"Single element 1D array: {arr_single.toList}"
  | none => IO.println "Failed to create single element array"

  -- Empty dimension (one dimension is 0)
  let empty_shape := Shape.cons 0 (Shape.cons 5 Shape.nil)
  let empty_arr : NDArray Nat empty_shape := NDArray.zeros empty_shape
  IO.println s!"Array with empty dimension [0,5]: size = {empty_arr.data.size}"

  IO.println ""
  IO.println "=== All tests completed successfully! ==="

-- Run the test suite
#eval! testSuite

-- Main entry point for executable
def main : IO Unit := testSuite
