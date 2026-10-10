module

public import SupportCriterion.Scaling
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Moments.Variance

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace SupportCriterion

lemma variance_nonneg (μ : Measure ℝ) : 0 ≤ variance μ :=
  integral_nonneg (fun _ => sq_nonneg _)

noncomputable def varianceNN (μ : Measure ℝ) : ℝ≥0 := ⟨variance μ, variance_nonneg μ⟩

@[simp] lemma varianceNN_coe (μ : Measure ℝ) : (varianceNN μ : ℝ) = variance μ := rfl

lemma symmetric_integral_eq_zero {μ : Measure ℝ} (hs : Symmetric μ) : (∫ x : ℝ, x ∂μ) = 0 := by
  have hn := integral_neg_eq hs (f := fun x => x) continuous_id
  rw [integral_neg] at hn
  linarith

lemma variance_eq_probabilityVariance {μ : Measure ℝ} (hs : Symmetric μ) :
    variance μ = ProbabilityTheory.variance id μ := by
  have h : (∫ x, id x ∂μ) = 0 := symmetric_integral_eq_zero hs
  simpa [variance, moment] using
    (ProbabilityTheory.variance_of_integral_eq_zero (X := id) (by fun_prop) h).symm

lemma hasSubgaussianMGF_of_band_mgf_bound {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}
    (hμ : BandSupport μ a b)
    (hbound : ∀ t : ℝ, mgf μ t ≤ Real.exp (variance μ * t ^ 2 / 2)) :
    ProbabilityTheory.HasSubgaussianMGF id (varianceNN μ) μ where
  integrable_exp_mul t := integrable_of_bandSupport hμ (by fun_prop)
  mgf_le t := hbound t

lemma hasSubgaussianMGF_of_endpoint_bound
    (hendpoint : ∀ (v t : ℝ), lowerSq ≤ v → v ≤ upperSq →
      (v - 1) ^ 2 * t ^ 4 / 16000 + t ^ 8 / 64000 ≤
        Real.exp (v * t ^ 2 / 2) - endpointMGF v t)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}
    (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b / a ≤ sharpRatio) :
    ProbabilityTheory.HasSubgaussianMGF id (varianceNN μ) μ := by
  apply hasSubgaussianMGF_of_band_mgf_bound hμ
  intro t
  by_cases ht : t = 0
  · simp [ht, mgf_zero]
  · exact (band_strict_of_gap ha hμ hr t ht (band_gap_of_endpoint_bound hendpoint ha hμ hs hr t)).le

lemma hasSubgaussianMGF_randomVariable_of_endpoint_bound
    (hendpoint : ∀ (v t : ℝ), lowerSq ≤ v → v ≤ upperSq →
      (v - 1) ^ 2 * t ^ 4 / 16000 + t ^ 8 / 64000 ≤
        Real.exp (v * t ^ 2 / 2) - endpointMGF v t)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ} (ha : 0 < a) (hX : AEMeasurable X μ)
    (hband : ∀ᵐ ω ∂μ, a ≤ |X ω| ∧ |X ω| ≤ b)
    (hs : Symmetric (μ.map X)) (hr : b / a ≤ sharpRatio) :
    ProbabilityTheory.HasSubgaussianMGF X (varianceNN (μ.map X)) μ := by
  apply (ProbabilityTheory.HasSubgaussianMGF.id_map_iff hX).1
  apply hasSubgaussianMGF_of_endpoint_bound hendpoint ha ?_ hs hr
  exact (ae_map_iff hX (by measurability)).2 hband

lemma varianceNN_map_coe {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) :
    (varianceNN (μ.map X) : ℝ) = ∫ ω, X ω ^ 2 ∂μ := by
  unfold varianceNN variance moment
  exact integral_map hX (by fun_prop)

lemma independent_sum_of_endpoint_bound
    (hendpoint : ∀ (v t : ℝ), lowerSq ≤ v → v ≤ upperSq →
      (v - 1) ^ 2 * t ^ 4 / 16000 + t ^ 8 / 64000 ≤
        Real.exp (v * t ^ 2 / 2) - endpointMGF v t)
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (h_indep : ProbabilityTheory.iIndepFun X μ)
    {s : Finset ι} {a b : ι → ℝ}
    (ha : ∀ i ∈ s, 0 < a i) (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hband : ∀ i ∈ s, ∀ᵐ ω ∂μ, a i ≤ |X i ω| ∧ |X i ω| ≤ b i)
    (hs : ∀ i ∈ s, Symmetric (μ.map (X i)))
    (hr : ∀ i ∈ s, b i / a i ≤ sharpRatio) :
    ProbabilityTheory.HasSubgaussianMGF (fun ω => ∑ i ∈ s, X i ω)
      (∑ i ∈ s, varianceNN (μ.map (X i))) μ := by
  apply ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun h_indep
  intro i hi
  exact hasSubgaussianMGF_randomVariable_of_endpoint_bound hendpoint (ha i hi) (hX i hi)
    (hband i hi) (hs i hi) (hr i hi)

end SupportCriterion
