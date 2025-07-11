/-
Synthesis Task 460: GetFirstElements

Method returns a list containing the first element from each sublist.
-/

namespace NumpySpec.DafnyBenchmarks.SynthesisTask460

/-- Returns a list containing the first element from each non-empty sublist -/
def getFirstElements (lst : List (List Int)) : List Int :=
  sorry

theorem getFirstElements_spec (lst : List (List Int)) 
    (h_nonempty : ∀ i : Fin lst.length, (lst[i]!).length > 0) :
    let result := getFirstElements lst
    result.length = lst.length ∧
    ∀ i : Fin result.length, result[i]! = (lst[i.val]!)[0]! := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask460