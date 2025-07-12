-- Synthesis Task 775: Check if odd-indexed elements are odd

namespace NumpySpec.DafnyBenchmarks.SynthesisTask775

/-- Check if a number is odd -/
def isOdd (n : Int) : Bool :=
  n % 2 = 1

/-- Check if all odd-indexed elements are odd -/
def isOddAtIndexOdd (a : Array Int) : Bool :=
  sorry

/-- Specification: Returns true if all odd-indexed elements are odd -/
theorem isOddAtIndexOdd_spec (a : Array Int) :
    isOddAtIndexOdd a = true ↔
    ∀ i : Fin a.size, isOdd i.val → isOdd a[i] :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask775