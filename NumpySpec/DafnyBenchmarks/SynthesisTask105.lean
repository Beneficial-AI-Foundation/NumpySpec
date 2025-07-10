/-
  Count the number of true values in a boolean array
  (Ported from Dafny synthesis task 105)
-/

import Std

namespace NumpySpec.DafnyBenchmarks.SynthesisTask105

/-- Helper function: Count true values up to index n -/
def countTo (a : Array Bool) (n : Nat) : Nat :=
  if h : n = 0 then 
    0 
  else if h' : n ≤ a.size then
    have : n - 1 < n := Nat.sub_lt (Nat.zero_lt_of_ne_zero h) (Nat.zero_lt_one)
    countTo a (n - 1) + (if h'' : n - 1 < a.size then (if a[n - 1] then 1 else 0) else 0)
  else
    0
termination_by n

/-- Count the number of true values in a boolean array -/
def countTrue (a : Array Bool) : Nat := sorry

theorem countTrue_spec (a : Array Bool) :
  countTrue a = countTo a a.size := by sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask105