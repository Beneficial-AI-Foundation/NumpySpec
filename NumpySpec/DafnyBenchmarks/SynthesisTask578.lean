-- Synthesis Task 578: Interleave three sequences

namespace NumpySpec.DafnyBenchmarks.SynthesisTask578

/-- Interleave three sequences of equal length -/
def interleave (s1 s2 s3 : List Int) : List Int :=
  sorry

/-- Specification: Interleave elements from three sequences -/
theorem interleave_spec (s1 s2 s3 : List Int) 
    (h_len : s1.length = s2.length ∧ s2.length = s3.length) :
    let r := interleave s1 s2 s3
    r.length = 3 * s1.length ∧
    ∀ i : Nat, i < s1.length → 
      r[3*i]! = s1[i]! ∧ 
      r[3*i + 1]! = s2[i]! ∧ 
      r[3*i + 2]! = s3[i]! :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask578