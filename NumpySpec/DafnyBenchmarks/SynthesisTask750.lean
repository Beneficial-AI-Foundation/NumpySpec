namespace NumpySpec.DafnyBenchmarks.SynthesisTask750

/-- Method AddTupleToList that appends a tuple to a list of tuples -/
def addTupleToList (l : List (Int × Int)) (t : Int × Int) : List (Int × Int) :=
  sorry

/-- Specification theorem for addTupleToList -/
theorem addTupleToList_spec (l : List (Int × Int)) (t : Int × Int) :
  let r := addTupleToList l t
  r.length = l.length + 1 ∧
  r[r.length - 1]! = t ∧
  ∀ i : Nat, i < l.length → r[i]! = l[i]! := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask750