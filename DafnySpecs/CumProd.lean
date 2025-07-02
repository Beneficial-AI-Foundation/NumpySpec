/-
# Cumulative Product Specification

Port of np_cum_prod.dfy to Lean 4
-/

namespace DafnySpecs.CumProd

/-- Helper function to compute cumulative product at index i -/
def cumProdAt {n : Nat} (a : Vector Int n) : Fin n → Int
  | ⟨0, _⟩ => a[0]
  | ⟨i+1, h⟩ => cumProdAt a ⟨i, Nat.lt_trans (Nat.lt_succ_self i) h⟩ * a[i+1]

/-- Cumulative product operation on a vector of integers -/
def cumProd {n : Nat} (a : Vector Int n) : Vector Int n :=
  Vector.ofFn (cumProdAt a)

/-- The cumulative product preserves the first element -/
theorem cumProd_first {n : Nat} (hn : 0 < n) (a : Vector Int n) :
    (cumProd a)[0]'(by omega) = a[0]'(by omega) := by
  simp [cumProd, cumProdAt]

/-- Each element is the product of the previous cumulative product and the current element -/
theorem cumProd_recursive {n : Nat} (a : Vector Int n) (i : Fin n) (hi : 0 < i.val) :
    (cumProd a)[i] = (cumProd a)[i.val - 1]'(by omega) * a[i] := by
  cases i with | mk val hval =>
    cases val with
    | zero => contradiction
    | succ j =>
      simp [cumProd, cumProdAt]

end DafnySpecs.CumProd
