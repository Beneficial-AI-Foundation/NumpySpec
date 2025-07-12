namespace NumpySpec.DafnyBenchmarks.SynthesisTask804

/-- Check if a number is even -/
def isEven (n : Int) : Bool :=
  n % 2 = 0

/-- Check if the product of all elements in an array is even -/
def isProductEven (a : Array Int) : Bool :=
  sorry

/-- Specification: The product is even if and only if at least one element is even -/
theorem isProductEven_spec (a : Array Int) :
    isProductEven a = true ↔ ∃ i : Fin a.size, isEven a[i] = true := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask804