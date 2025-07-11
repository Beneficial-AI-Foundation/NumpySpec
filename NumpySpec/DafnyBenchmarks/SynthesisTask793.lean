-- Synthesis Task 793: Find last position of element in sorted array

namespace NumpySpec.DafnyBenchmarks.SynthesisTask793

/-- Find the last position of an element in a sorted array -/
def lastPosition (arr : Array Int) (elem : Int) : Int :=
  sorry

/-- Specification: lastPosition returns the last index of elem in sorted array, or -1 if not found -/
theorem lastPosition_spec (arr : Array Int) (elem : Int)
    (h_nonempty : arr.size > 0)
    (h_sorted : ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!) :
    let pos := lastPosition arr elem
    (pos = -1 ∨ (0 ≤ pos ∧ pos < arr.size ∧ arr[pos.toNat]! = elem ∧ 
     (pos.toNat = arr.size - 1 ∨ arr[(pos.toNat + 1)]! > elem))) :=
  sorry

/-- The array is not modified -/
theorem lastPosition_preserves_array (arr : Array Int) (elem : Int) :
    lastPosition arr elem = lastPosition arr elem :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask793