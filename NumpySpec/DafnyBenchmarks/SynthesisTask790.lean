-- Synthesis Task 790: Check if even-indexed elements are even

namespace NumpySpec.DafnyBenchmarks.SynthesisTask790

/-- Check if a number is even -/
def isEven (n : Int) : Bool :=
  n % 2 = 0

/-- Check if all even-indexed elements are even -/
def isEvenAtIndexEven (lst : List Int) : Bool :=
  sorry

/-- Specification: Returns true if all even-indexed elements are even -/
theorem isEvenAtIndexEven_spec (lst : List Int) :
    isEvenAtIndexEven lst = true ↔
    ∀ i : Fin lst.length, isEven i.val → isEven lst[i] :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask790