/-
# Standard Array Arithmetic Operations

This module defines element-wise arithmetic operations on arrays with specifications.
All operations preserve array sizes and apply operations element-by-element.
-/

/-- Element-wise addition of two arrays.
Returns an array where each element is the sum of corresponding elements.
The arrays must have the same size. -/
def Array.add [Add α] (xs ys : Array α) : Array α :=
  if h : xs.size = ys.size then
    xs.zipWith (· + ·) ys
  else
    panic! s!"Array.add: size mismatch {xs.size} ≠ {ys.size}"

/-- Specification: Element-wise addition preserves size -/
theorem Array.add_size [Add α] (xs ys : Array α) (h : xs.size = ys.size) :
    (xs.add ys).size = xs.size := by
  unfold add
  simp [h, Array.size_zipWith]

/-- Specification: Element-wise addition is correct -/
theorem Array.add_get [Add α] (xs ys : Array α) (h : xs.size = ys.size) (i : Fin xs.size) :
    (xs.add ys)[i.val]'(by rw [add_size xs ys h]; exact i.isLt) = xs[i] + ys[i.val]'(h ▸ i.isLt) := by
  sorry

/-- Element-wise subtraction of two arrays.
Returns an array where each element is the difference of corresponding elements.
The arrays must have the same size. -/
def Array.sub [Sub α] (xs ys : Array α) : Array α :=
  if h : xs.size = ys.size then
    xs.zipWith (· - ·) ys
  else
    panic! s!"Array.sub: size mismatch {xs.size} ≠ {ys.size}"

/-- Specification: Element-wise subtraction preserves size -/
theorem Array.sub_size [Sub α] (xs ys : Array α) (h : xs.size = ys.size) :
    (xs.sub ys).size = xs.size := by
  unfold sub
  simp [h, Array.size_zipWith]

/-- Specification: Element-wise subtraction is correct -/
theorem Array.sub_get [Sub α] (xs ys : Array α) (h : xs.size = ys.size) (i : Fin xs.size) :
    (xs.sub ys)[i.val]'(by rw [sub_size xs ys h]; exact i.isLt) = xs[i] - ys[i.val]'(h ▸ i.isLt) := by
  sorry

/-- Element-wise multiplication of two arrays.
Returns an array where each element is the product of corresponding elements.
The arrays must have the same size. -/
def Array.mul [Mul α] (xs ys : Array α) : Array α :=
  if h : xs.size = ys.size then
    xs.zipWith (· * ·) ys
  else
    panic! s!"Array.mul: size mismatch {xs.size} ≠ {ys.size}"

/-- Specification: Element-wise multiplication preserves size -/
theorem Array.mul_size [Mul α] (xs ys : Array α) (h : xs.size = ys.size) :
    (xs.mul ys).size = xs.size := by
  unfold mul
  simp [h, Array.size_zipWith]

/-- Specification: Element-wise multiplication is correct -/
theorem Array.mul_get [Mul α] (xs ys : Array α) (h : xs.size = ys.size) (i : Fin xs.size) :
    (xs.mul ys)[i.val]'(by rw [mul_size xs ys h]; exact i.isLt) = xs[i] * ys[i.val]'(h ▸ i.isLt) := by
  sorry

/-- Element-wise division and modulo of two arrays.
Returns a pair of arrays where the first contains quotients and the second contains remainders.
The arrays must have the same size. -/
def Array.divMod [Div α] [Mod α] (xs ys : Array α) : Array α × Array α :=
  if h : xs.size = ys.size then
    (xs.zipWith (· / ·) ys, xs.zipWith (· % ·) ys)
  else
    panic! s!"Array.divMod: size mismatch {xs.size} ≠ {ys.size}"

/-- Specification: Element-wise divMod preserves size for quotient -/
theorem Array.divMod_fst_size [Div α] [Mod α] (xs ys : Array α) (h : xs.size = ys.size) :
    (xs.divMod ys).fst.size = xs.size := by
  unfold divMod
  simp [h, Array.size_zipWith]

/-- Specification: Element-wise divMod preserves size for remainder -/
theorem Array.divMod_snd_size [Div α] [Mod α] (xs ys : Array α) (h : xs.size = ys.size) :
    (xs.divMod ys).snd.size = xs.size := by
  unfold divMod
  simp [h, Array.size_zipWith]

/-- Specification: Element-wise division is correct -/
theorem Array.divMod_fst_get [Div α] [Mod α] (xs ys : Array α) (h : xs.size = ys.size) (i : Fin xs.size) :
    (xs.divMod ys).fst[i.val]'(by rw [divMod_fst_size xs ys h]; exact i.isLt) = xs[i] / ys[i.val]'(h ▸ i.isLt) := by
  sorry

/-- Specification: Element-wise modulo is correct -/
theorem Array.divMod_snd_get [Div α] [Mod α] (xs ys : Array α) (h : xs.size = ys.size) (i : Fin xs.size) :
    (xs.divMod ys).snd[i.val]'(by rw [divMod_snd_size xs ys h]; exact i.isLt) = xs[i] % ys[i.val]'(h ▸ i.isLt) := by
  sorry

/-- Creates an array of zeros with the specified size.
Each element is the zero value of the type. -/
def Array.zeros [Zero α] (n : Nat) : Array α :=
  Array.replicate n 0

/-- Specification: zeros has the correct size -/
theorem Array.zeros_size [Zero α] (n : Nat) :
    (Array.zeros n : Array α).size = n := by
  unfold zeros
  simp [Array.size_replicate]

/-- Specification: zeros contains only zero values -/
theorem Array.zeros_get [Zero α] (n : Nat) (i : Fin n) :
    (Array.zeros n : Array α)[i.val]'(by rw [zeros_size]; exact i.isLt) = 0 := by
  unfold zeros
  simp [Array.getElem_replicate]

-- Additional convenience functions

/-- Scalar multiplication: multiply each element by a scalar -/
def Array.scalarMul [Mul α] (c : α) (xs : Array α) : Array α :=
  xs.map (c * ·)

/-- Specification: Scalar multiplication preserves size -/
theorem Array.scalarMul_size [Mul α] (c : α) (xs : Array α) :
    (xs.scalarMul c).size = xs.size := by
  unfold scalarMul
  simp [Array.size_map]

/-- Specification: Scalar multiplication is correct -/
theorem Array.scalarMul_get [Mul α] (c : α) (xs : Array α) (i : Fin xs.size) :
    (xs.scalarMul c)[i.val]'(by rw [scalarMul_size]; exact i.isLt) = c * xs[i] := by
  unfold scalarMul
  simp [Array.getElem_map]

/-- Element-wise negation for arrays -/
def Array.neg [Neg α] (xs : Array α) : Array α :=
  xs.map (- ·)

/-- Specification: Negation preserves size -/
theorem Array.neg_size [Neg α] (xs : Array α) :
    xs.neg.size = xs.size := by
  unfold neg
  simp [Array.size_map]

/-- Specification: Negation is correct -/
theorem Array.neg_get [Neg α] (xs : Array α) (i : Fin xs.size) :
    xs.neg[i.val]'(by rw [neg_size]; exact i.isLt) = -xs[i] := by
  unfold neg
  simp [Array.getElem_map]
