-- Synthesis Task 170: Sum in range

namespace NumpySpec.DafnyBenchmarks.SynthesisTask170

/-- Sum elements in array from start to end (exclusive) -/
def sumTo (a : Array Int) (start endPos : Nat) : Int :=
  if h : start ≤ endPos ∧ endPos ≤ a.size then
    if start = endPos then 0 
    else 
      have h_bound : endPos - 1 < a.size := by
        sorry
      sumTo a start (endPos - 1) + a[endPos - 1]
  else 0
  termination_by endPos - start

/-- Calculate sum of elements in range [start, end) -/
def sumInRange (a : Array Int) (start endPos : Nat) : Int :=
  sorry

/-- Specification: Sum in range equals recursive definition -/
theorem sumInRange_spec (a : Array Int) (start endPos : Nat)
    (h_range : start ≤ endPos ∧ endPos ≤ a.size) :
    sumInRange a start endPos = sumTo a start endPos :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask170