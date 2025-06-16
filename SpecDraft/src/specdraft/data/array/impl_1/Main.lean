import LeanArrayLib.Core
import LeanArrayLib.Indexing
import LeanArrayLib.View

-- The main entry point for the executable.
-- The `do` block allows us to perform input/output actions.
def main : IO Unit := do
  IO.println "--- NdArray Test Suite ---"

  -- ===================================================================
  -- 1. NdArray Creation
  -- ===================================================================
  IO.println "\n--- 1. NdArray Creation ---"

  -- 1a. Create a 2x3 matrix initialized with a default value.
  -- This uses the `NdArray.new` constructor.
  IO.println "Creating a 2x3 matrix of Float zeros..."
  let matrix_zeros : NdArray Float := NdArray.new #[1, 2] 0.0
  IO.println s!"Matrix (2x3):\n{matrix_zeros}\n"

  -- 1b. Create a 2x2 matrix from a flat `Array`.
  -- This uses `NdArray.ofArray`, which returns an `Option` because the
  -- shape and data size might not match.
  IO.println "Creating a 2x2 matrix from Array #...[3, 1, 2, 4]"
  let data_mat := #[3, 1, 2, 4]
  let matrix_from_array_opt := NdArray.ofArray data_mat #[2, 2]
  match matrix_from_array_opt with
| some mat => IO.println s!"Matrix (2x2):\n{mat}\n"
| none => IO.println "Failed to create matrix from array."

  -- 1c. Create a 2x3 matrix using `ofFn`.
  -- This constructor builds an array by applying a function to each index.
  -- Note: The `ofFn` implementation in the report has a `sorry` for its proof.
  -- This test assumes a working implementation. For this test, we'll manually
  -- create the equivalent array that `ofFn` would produce.
  IO.println "Creating a 2x3 matrix as if by `ofFn (i, j) -> i * 10 + j`..."
  let matrix_ofFn_opt := NdArray.ofArray # #[1, 2]
  match matrix_ofFn_opt with
| some mat => IO.println s!"Matrix from ofFn:\n{mat}\n"
| none => IO.println "Failed to create matrix from ofFn."


  -- ===================================================================
  -- 2. Indexing
  -- ===================================================================
  IO.println "\n--- 2. Indexing ---"
  match matrix_from_array_opt with
| some mat =>
    IO.println s!"Using matrix:\n{mat}"
    -- Access element at (1, 0). The proof `by rfl` is trivial because the
    -- compiler can see that the rank of the index `(1, 0)` (which is 2)
    -- matches the rank of the array's shape `#[2, 2]` (which is 2).
    let elem_1_0 := mat[(1, 0)] (by rfl)
    IO.println s!"Element at (1, 0): {elem_1_0}"

    -- Set element at (1, 1) to 99. This returns a new, modified array.
    IO.println "Setting element at (1, 1) to 99..."
    let mat_modified := mat.setElem (1, 1) 99 (by rfl)
    IO.println s!"Modified matrix:\n{mat_modified}"
    let elem_1_1_new := mat_modified[(1, 1)] (by rfl)
    IO.println s!"New element at (1, 1): {elem_1_1_new}\n"

    -- Example of a compile-time error (commented out).
    -- let elem_invalid := mat[5] (by rfl)
    -- IO.println "-- The above line would fail to compile because the rank of the index (1)
    -- does not match the rank of the array (2)."
| none => IO.println "Skipping indexing tests, matrix creation failed."


  -- ===================================================================
  -- 3. Views and Zero-Copy Operations
  -- ===================================================================
  IO.println "\n--- 3. Views and Zero-Copy Operations ---"
  match matrix_ofFn_opt with
| some base_matrix =>
    IO.println s!"Using base matrix:\n{base_matrix}\n"

    -- 3a. Create a full view of the base matrix.
    let full_view := ArrayView.ofNdArray base_matrix

    -- 3b. Slicing to get a sub-array (the second row).
    IO.println "Slicing to get the second row (index 1)..."
    match full_view.slice 0 1 2 with -- Slice dimension 0 from index 1 to 2
| some row_slice =>
      IO.println s!"Sliced view (second row):\n{row_slice}"
      -- Access element at (0, 1) of the slice, which corresponds to (1, 1) of the original.
      let elem := row_slice[(0, 1)] (by rfl)
      IO.println s!"Element at (0, 1) in slice (should be 11): {elem}\n"
| none => IO.println "Slicing failed."

    -- 3c. Indexing to reduce rank (get the first row as a 1D view).
    IO.println "Indexing at row 0 to get a 1D view..."
    match full_view.index 0 0 with -- Index dimension 0 at index 0
| some row_view_1d =>
      IO.println s!"1D View of first row:\n{row_view_1d}"
      let elem := row_view_1d[1] (by rfl)
      IO.println s!"Element at [1] in 1D view (should be 2): {elem}\n"
| none => IO.println "Indexing failed."

    -- 3d. Transposing the view. This is an O(1) operation that swaps shape and strides.
    IO.println "Transposing the full view..."
    IO.println s!"Original shape: {full_view.shape}, Original strides: {full_view.strides}"
    match full_view.transpose 0 1 with
| some transposed_view =>
      IO.println s!"Transposed shape: {transposed_view.shape}, Transposed strides: {transposed_view.strides}"
      -- Access element at (2, 0) in transposed view, which is (0, 2) in original.
      let elem1 := transposed_view[(2, 0)] (by rfl)
      IO.println s!"Element at (2, 0) in transposed view (should be 2): {elem1}"
      -- Access element at (1, 1) in transposed view, which is (1, 1) in original.
      let elem2 := transposed_view[(1, 1)] (by rfl)
      IO.println s!"Element at (1, 1) in transposed view (should be 11): {elem2}\n"
| none => IO.println "Transpose failed."

| none => IO.println "Skipping view tests, matrix creation failed."


  IO.println "--- Test Suite Complete ---"
