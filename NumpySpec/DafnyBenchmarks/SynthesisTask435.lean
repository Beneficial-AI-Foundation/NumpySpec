-- Synthesis Task 435: Get last digit of integer

namespace NumpySpec.DafnyBenchmarks.SynthesisTask435

/-- Get the last digit of a non-negative integer -/
def lastDigit (n : Nat) : Nat :=
  sorry

/-- Specification: Last digit is n % 10 and is between 0 and 9 -/
theorem lastDigit_spec (n : Nat) :
    let d := lastDigit n
    0 ≤ d ∧ d < 10 ∧ n % 10 = d :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask435