-- Synthesis Task 623: Power of list elements

namespace NumpySpec.DafnyBenchmarks.SynthesisTask623

/-- Power function for non-negative exponents -/
def power (base : Int) (exponent : Nat) : Int :=
  match exponent with
  | 0 => 1
  | n + 1 => base * power base n

/-- Raise each element of a list to the given power -/
def powerOfListElements (l : List Int) (n : Nat) : List Int :=
  sorry

/-- Specification: Raise each element of list to power n -/
theorem powerOfListElements_spec (l : List Int) (n : Nat) :
    let result := powerOfListElements l n
    result.length = l.length ∧
    ∀ i : Nat, i < result.length → result[i]! = power l[i]! n :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask623