-- Synthesis Task 591: Swap first and last elements of an array

namespace NumpySpec.DafnyBenchmarks.SynthesisTask591

/-- Swap the first and last elements of an array -/
def swapFirstAndLast (a : Array Int) : Array Int :=
  sorry

/-- Specification: swapFirstAndLast swaps first and last elements, keeps others unchanged -/
theorem swapFirstAndLast_spec (a : Array Int) (h : a.size > 0) :
  let a' := swapFirstAndLast a
  a'.size = a.size ∧
  a'[0]! = a[a.size - 1]! ∧
  a'[a.size - 1]! = a[0]! ∧
  (∀ k : Nat, 1 ≤ k ∧ k < a.size - 1 → a'[k]! = a[k]!) := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask591