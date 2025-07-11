-- Synthesis Task 565: Split string into characters

namespace NumpySpec.DafnyBenchmarks.SynthesisTask565

/-- Split a string into a list of characters -/
def splitStringIntoChars (s : String) : List Char :=
  sorry

/-- Specification: Split string preserves all characters in order -/
theorem splitStringIntoChars_spec (s : String) :
    splitStringIntoChars s = s.toList :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask565