-- Synthesis Task 762: Check if month has 30 days

namespace NumpySpec.DafnyBenchmarks.SynthesisTask762

/-- Check if a month has 30 days -/
def isMonthWith30Days (month : Int) : Bool :=
  sorry

/-- Specification: Returns true if month has 30 days (April, June, September, November) -/
theorem isMonthWith30Days_spec (month : Int)
    (h_range : 1 ≤ month ∧ month ≤ 12) :
    isMonthWith30Days month = (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask762