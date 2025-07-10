-- Synthesis Task 106: Append array to sequence

namespace NumpySpec.DafnyBenchmarks.SynthesisTask106

/-- Append array elements to a sequence -/
def appendArrayToSeq (s : List Int) (a : Array Int) : List Int :=
  sorry

/-- Specification: Append preserves original sequence and adds array elements -/
theorem appendArrayToSeq_spec (s : List Int) (a : Array Int) :
    let r := appendArrayToSeq s a
    r.length = s.length + a.size ∧
    (∀ i : Fin s.length, r[i]! = s[i]!) ∧
    (∀ i : Fin a.size, r[s.length + i]! = a[i]) :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask106