/-
# NumPy Statistics Functions

This module provides mathematical specifications for NumPy's statistical functionality.
Based on https://numpy.org/doc/stable/reference/routines.statistics.html

## Key Concepts
1. **Order Statistics**: Minimum, maximum, quantiles, and percentiles
2. **Averages**: Mean, median, weighted average, etc.
3. **Correlations**: Correlation coefficients, covariance matrices
4. **Histograms**: Statistical binning operations
-/

namespace Numpy.Statistics

/-- Compute the arithmetic mean along the specified axis -/
def mean {α : Type} [Add α] [Div α] [OfNat α 0] (a : Array α) (axis : Option Nat := none) : Array α :=
  sorry

/-- Mean of all elements in the array -/
theorem mean_all {α : Type} [Add α] [Div α] [OfNat α 0] [OfNat α 1] [Inhabited α] (a : Array α) :
  a.size > 0 → mean a none = #[a.foldl (fun x y => x + y) 0] := sorry

/-- Compute the weighted average along the specified axis -/
def average {α : Type} [Add α] [Mul α] [Div α] [OfNat α 0] (a : Array α) (weights : Option (Array α) := none) (axis : Option Nat := none) : Array α :=
  sorry

/-- Average with uniform weights is the same as mean -/
theorem average_uniform_weights {α : Type} [Add α] [Mul α] [Div α] [BEq α] [OfNat α 0] [OfNat α 1] (a : Array α) (axis : Option Nat) :
  average a none axis = mean a axis := sorry

/-- Compute the median along the specified axis -/
def median {α : Type} [Add α] [Div α] [Ord α] [OfNat α 0] [OfNat α 1] [OfNat α 2] (a : Array α) (axis : Option Nat := none) : Array α :=
  sorry

/-- Median of sorted array is middle element (or average of two middle elements) -/
theorem median_of_sorted {α : Type} [Add α] [Div α] [Ord α] [LE α] [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [Inhabited α] (a : Array α) (h_sorted : ∀ i j, i < j → j < a.size → a[i]! ≤ a[j]!) :
  a.size > 0 → 
    median a none = (if a.size % 2 = 0 
                     then #[(a[a.size / 2 - 1]! + a[a.size / 2]!) / 2]
                     else #[a[a.size / 2]!]) := sorry

/-- Compute the standard deviation along the specified axis -/
def std {α : Type} [Add α] [Sub α] [Mul α] [Div α] [OfNat α 0] [OfNat α 1] (a : Array α) (axis : Option Nat := none) (ddof : Nat := 0) : Array α :=
  sorry

/-- Compute the variance along the specified axis -/
def var {α : Type} [Add α] [Sub α] [Mul α] [Div α] [OfNat α 0] [OfNat α 1] (a : Array α) (axis : Option Nat := none) (ddof : Nat := 0) : Array α :=
  sorry

/-- Relationship between variance and standard deviation -/
theorem std_sqrt_var {α : Type} [Add α] [Sub α] [Mul α] [Div α] [BEq α] [OfNat α 0] [OfNat α 1] [Inhabited α] (a : Array α) (axis : Option Nat) (ddof : Nat) :
  ∀ i, i < (std a axis ddof).size → i < (var a axis ddof).size → 
    (std a axis ddof)[i]! * (std a axis ddof)[i]! = (var a axis ddof)[i]! := sorry

/-- Find the minimum value along the specified axis -/
def min {α : Type} [Ord α] (a : Array α) (axis : Option Nat := none) : Array α :=
  sorry

/-- Find the maximum value along the specified axis -/
def max {α : Type} [Ord α] (a : Array α) (axis : Option Nat := none) : Array α :=
  sorry

/-- Compute the q-th quantile along the specified axis -/
def quantile {α : Type} [Add α] [Mul α] [Div α] [Ord α] [OfNat α 0] [OfNat α 1] (a : Array α) (q : Array Float) (axis : Option Nat := none) : Array α :=
  sorry

/-- Compute the q-th percentile along the specified axis -/
def percentile {α : Type} [Add α] [Mul α] [Div α] [Ord α] [OfNat α 0] [OfNat α 1] [OfNat α 100] (a : Array α) (q : Array Float) (axis : Option Nat := none) : Array α :=
  sorry

/-- Percentile is just quantile scaled by 100 -/
theorem percentile_eq_quantile {α : Type} [Add α] [Mul α] [Div α] [Ord α] [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 100] (a : Array α) (q : Array Float) (axis : Option Nat) :
  percentile a q axis = quantile a (q.map (· / 100)) axis := sorry

/-- Compute the covariance matrix -/
def cov {α : Type} [Add α] [Sub α] [Mul α] [Div α] [OfNat α 0] [OfNat α 1] (m : Array (Array α)) (rowvar : Bool := true) : Array (Array α) :=
  sorry

/-- Compute correlation coefficient -/
def corrcoef {α : Type} [Add α] [Sub α] [Mul α] [Div α] [OfNat α 0] [OfNat α 1] (x : Array (Array α)) (rowvar : Bool := true) : Array (Array α) :=
  sorry

/-- Compute a histogram with uniform binning -/
def histogram {α : Type} [Add α] [Sub α] [Mul α] [Div α] [Ord α] [OfNat α 0] [OfNat α 1] (a : Array α) (bins : Nat) : (Array Nat) × (Array α) :=
  sorry

end Numpy.Statistics
