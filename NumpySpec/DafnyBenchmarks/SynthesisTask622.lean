-- Synthesis Task 622: Find median of two sorted arrays

namespace NumpySpec.DafnyBenchmarks.SynthesisTask622

/-- Find the median of two sorted arrays -/
def findMedian (a b : Array Int) : Int :=
  sorry

/-- Specification: Find median of two sorted arrays of equal length -/
theorem findMedian_spec (a b : Array Int)
    (h_len_eq : a.size = b.size)
    (h_nonempty : a.size > 0)
    (h_sorted_a : ∀ i : Fin (a.size - 1), a[i.val] ≤ a[i.val + 1])
    (h_sorted_b : ∀ i : Fin (b.size - 1), b[i.val] ≤ b[i.val + 1]) :
    findMedian a b =
      if h : a.size % 2 = 0 then
        have h1 : a.size / 2 - 1 < a.size := by
          sorry
        (a[a.size / 2 - 1] + b[0]) / 2
      else
        have h2 : a.size / 2 < a.size := by
          sorry
        a[a.size / 2] :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask622