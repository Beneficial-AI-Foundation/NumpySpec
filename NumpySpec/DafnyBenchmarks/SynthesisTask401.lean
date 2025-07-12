-- Synthesis Task 401: IndexWiseAddition - Element-wise addition of two 2D arrays

namespace NumpySpec.DafnyBenchmarks.SynthesisTask401

/-- IndexWiseAddition: Element-wise addition of two 2D arrays -/
def indexWiseAddition (a b : Array (Array Int)) : Array (Array Int) :=
  sorry

/-- Specification: Element-wise addition of matrices with same dimensions -/
theorem indexWiseAddition_spec (a b : Array (Array Int))
    (h_a_nonempty : a.size > 0)
    (h_b_nonempty : b.size > 0)
    (h_same_size : a.size = b.size)
    (h_same_inner_sizes : ∀ i : Nat, i < a.size → a[i]!.size = b[i]!.size) :
    let result := indexWiseAddition a b
    result.size = a.size ∧
    (∀ i : Nat, i < result.size → result[i]!.size = a[i]!.size) ∧
    (∀ i : Nat, i < result.size → ∀ j : Nat, j < result[i]!.size →
      result[i]![j]! = a[i]![j]! + b[i]![j]!) := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask401