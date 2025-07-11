/-
Synthesis Task 610: RemoveElement

Method removes element at index k from array and returns a new array with length - 1.
-/

namespace NumpySpec.DafnyBenchmarks.SynthesisTask610

/-- Removes element at index k from array s and returns new array with length - 1 -/
def removeElement (s : Array Int) (k : Nat) : Array Int :=
  sorry

theorem removeElement_spec (s : Array Int) (k : Nat) 
    (h_range : 0 ≤ k ∧ k < s.size) :
    let v := removeElement s k
    v.size = s.size - 1 ∧
    (∀ i : Nat, 0 ≤ i ∧ i < k → v[i]! = s[i]!) ∧
    (∀ i : Nat, k ≤ i ∧ i < v.size → v[i]! = s[i + 1]!) := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask610