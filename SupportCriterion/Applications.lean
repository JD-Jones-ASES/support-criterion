module

public import SupportCriterion.Main
public import SupportCriterion.SubGaussian
public import SupportCriterion.LawEndpoint

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace SupportCriterion

/-- The support criterion in Mathlib's sub-Gaussian interface, with the actual variance. -/
theorem band_hasSubgaussianMGF (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b/a ≤ sharpRatio) :
    ProbabilityTheory.HasSubgaussianMGF id (varianceNN μ) μ :=
  hasSubgaussianMGF_of_endpoint_bound endpoint_gaussian_gap ha hμ hs hr

/-- The same statement on any probability space by taking the law of the random variable. -/
theorem randomVariable_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a b : ℝ) (ha : 0 < a) (hX : AEMeasurable X μ)
    (hband : ∀ᵐ ω ∂μ, a ≤ |X ω| ∧ |X ω| ≤ b)
    (hs : Symmetric (μ.map X)) (hr : b/a ≤ sharpRatio) :
    ProbabilityTheory.HasSubgaussianMGF X (varianceNN (μ.map X)) μ :=
  hasSubgaussianMGF_randomVariable_of_endpoint_bound endpoint_gaussian_gap ha hX hband hs hr

/-- Independent finite sums inherit the sum of the individual variance proxies. -/
theorem independent_sum_hasSubgaussianMGF
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hband : ∀ i ∈ s, ∀ᵐ ω ∂μ, a i ≤ |X i ω| ∧ |X i ω| ≤ b i)
    (hs : ∀ i ∈ s, Symmetric (μ.map (X i)))
    (hr : ∀ i ∈ s, b i/a i ≤ sharpRatio) :
    ProbabilityTheory.HasSubgaussianMGF (fun ω => ∑ i ∈ s, X i ω)
      (∑ i ∈ s, varianceNN (μ.map (X i))) μ :=
  independent_sum_of_endpoint_bound endpoint_gaussian_gap h_indep ha hX hband hs hr

/-- Symmetry makes the second-moment parameter the usual centered variance. -/
theorem actual_variance_parameter (μ : Measure ℝ) (hs : Symmetric μ) :
    (varianceNN μ : ℝ) = ProbabilityTheory.variance id μ :=
  variance_eq_probabilityVariance hs

/-- The proxy of an arbitrary random variable is its actual second moment. -/
theorem randomVariable_variance_parameter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : AEMeasurable X μ) :
    (varianceNN (μ.map X) : ℝ) = ∫ ω, X ω ^ 2 ∂μ :=
  varianceNN_map_coe hX

/-- A one-sided concentration consequence of the variance proxy. -/
theorem band_upper_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b/a ≤ sharpRatio) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {x | ε ≤ x} ≤ Real.exp (-ε ^ 2 / (2 * variance μ)) := by
  exact (band_hasSubgaussianMGF μ a b ha hμ hs hr).measure_ge_le hε

end SupportCriterion
