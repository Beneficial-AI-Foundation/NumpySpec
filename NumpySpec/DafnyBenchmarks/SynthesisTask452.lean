-- Synthesis Task 452: Calculate loss

namespace NumpySpec.DafnyBenchmarks.SynthesisTask452

/-- Calculate loss given cost price and selling price -/
def calculateLoss (costPrice sellingPrice : Int) : Int :=
  sorry

/-- Specification: Loss is cost minus selling price when positive, else 0 -/
theorem calculateLoss_spec (costPrice sellingPrice : Int)
    (h_nonneg : costPrice ≥ 0 ∧ sellingPrice ≥ 0) :
    calculateLoss costPrice sellingPrice =
      if costPrice > sellingPrice then costPrice - sellingPrice else 0 :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTask452