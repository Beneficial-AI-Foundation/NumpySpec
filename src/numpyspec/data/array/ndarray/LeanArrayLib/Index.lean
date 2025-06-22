namespace LeanArrayLib

/-- `IndexType` is a type class that defines how to map multi-dimensional indices to linear positions.

    For an index type `I` and array size `n`, this class provides a function to convert
    any index of type `I` to a position in the linear storage as a `Fin n`.

    This abstraction allows arrays to support various indexing schemes while maintaining
    type safety and bounds checking at compile time.
-/
class IndexType (I : Type) (n : Nat) where
  /-- Convert a multi-dimensional index to a linear position in [0, n) -/
  toLinear : I → Fin n

/-- Instance for simple 1D indexing with `Fin n`.

    This is the identity mapping since `Fin n` already represents a linear index.
-/
instance {n} : IndexType (Fin n) n where
  toLinear := id

/-- Instance for 2D row-major indexing using pairs `(Fin m × Fin n)`.

    Maps a 2D coordinate (i, j) to a linear index using row-major order:
    `linear_index = i * n + j`

    The proof ensures that the resulting index is within bounds (< m*n).
-/
instance {m n} : IndexType (Fin m × Fin n) (m*n) where
  toLinear := fun (i,j) =>
    have h : i.val * n + j.val < m * n := by
      have hi : i.val < m := i.isLt
      have hj : j.val < n := j.isLt
      have h1 : i.val * n + j.val < i.val * n + n := Nat.add_lt_add_left hj _
      have h2 : i.val * n + n ≤ m * n := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
      exact Nat.lt_of_lt_of_le h1 h2
    ⟨i.val * n + j.val, h⟩

end LeanArrayLib
