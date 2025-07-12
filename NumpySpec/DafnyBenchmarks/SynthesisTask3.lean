-- Synthesis Task 3: Check if number is non-prime

namespace NumpySpec.DafnyBenchmarks.SynthesisTask3

/-- Check if a number is non-prime (composite) -/
def isNonPrime (n : Nat) : Bool :=
  sorry

/-- Specification: Returns true iff n has a divisor between 2 and n-1 -/
theorem isNonPrime_spec (n : Nat) (h : n ≥ 2) :
    isNonPrime n = ∃ k : Nat, 2 ≤ k ∧ k < n ∧ n % k = 0 :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask3