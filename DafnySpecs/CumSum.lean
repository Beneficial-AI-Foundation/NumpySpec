/-
# Cumulative Sum Specification

Port of np_cum_sum.dfy to Lean 4
-/

namespace DafnySpecs.CumSum

/-- Helper function to compute cumulative sum at index i -/
def cumSumAt {n : Nat} (a : Vector Int n) : Fin n → Int
  | ⟨0, _⟩ => a[0]
  | ⟨i+1, h⟩ => cumSumAt a ⟨i, Nat.lt_trans (Nat.lt_succ_self i) h⟩ + a[i+1]

/-- Cumulative sum operation on a vector of integers -/
def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (cumSumAt a)

/-- The cumulative sum preserves the first element -/
theorem cumSum_first {n : Nat} (hn : 0 < n) (a : Vector Int n) :
    (cumSum a)[0]'(by omega) = a[0]'(by omega) := by
  simp [cumSum, cumSumAt]

/-- Each element is the sum of the previous cumulative sum and the current element -/
theorem cumSum_recursive {n : Nat} (a : Vector Int n) (i : Fin n) (hi : 0 < i.val) :
    (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  cases i with | mk val hval =>
    cases val with
    | zero => contradiction
    | succ j =>
      simp [cumSum, cumSumAt]

end DafnySpecs.CumSum