module

public import SupportCriterion.EndpointSeries
public import SupportCriterion.LawGap
public import SupportCriterion.Scaling
public import SupportCriterion.ProxyOptimality
public import SupportCriterion.Sharpness
public import SupportCriterion.Rigidity
public import SupportCriterion.TransportFinal

@[expose] public section

/-! Principal support, quantitative separation, sharpness and rigidity theorems. -/
open MeasureTheory

namespace SupportCriterion

/-- The quantitative normalized estimate for every symmetric probability law. -/
theorem normalized_quantitative_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) (t : ℝ) :
    fourthDeficit μ*t^4/48000+t^8/64000 ≤
      Real.exp (variance μ*t^2/2)-mgf μ t :=
  normalized_gap_of_endpoint_bound endpoint_gaussian_gap hμ hs t

/-- The original-scale quantitative estimate, retaining the actual fourth deficit. -/
theorem scaled_quantitative_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b/a ≤ sharpRatio) (t : ℝ) :
    fourthDeficit μ*t^4/48000+a^8/(64000*lowerSq^4)*t^8 ≤
      Real.exp (variance μ*t^2/2)-mgf μ t := by
  apply band_gap_of_normalized_gap ha
  intro s
  exact normalized_quantitative_gap _ (scaleLaw_normalizedSupport ha hμ hr)
    (scaleLaw_symmetric hs _) s

/-- The sharp support criterion, including every real MGF parameter. -/
theorem universal_support_criterion (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b/a ≤ sharpRatio) (t : ℝ) :
    mgf μ t ≤ Real.exp (variance μ*t^2/2) := by
  have hg := scaled_quantitative_gap μ a b ha hμ hs hr t
  have hd := band_fourthDeficit_nonneg ha hμ hr
  have h1 : 0 ≤ fourthDeficit μ*t^4/48000 := by positivity
  have h2 : 0 ≤ a^8/(64000*lowerSq^4)*t^8 := by positivity
  linarith

/-- The Gaussian MGF bound is strict at every nonzero parameter. -/
theorem universal_strict (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b/a ≤ sharpRatio) (t : ℝ) (ht : t ≠ 0) :
    mgf μ t < Real.exp (variance μ*t^2/2) := by
  have hg := scaled_quantitative_gap μ a b ha hμ hs hr t
  have hd := band_fourthDeficit_nonneg ha hμ hr
  have h1 : 0 ≤ fourthDeficit μ*t^4/48000 := by positivity
  have h2 : 0 < a^8/(64000*lowerSq^4)*t^8 := by
    have hA := lowerSq_pos
    positivity
  linarith

/-- No smaller quadratic proxy can bound the MGF of the same law. -/
theorem variance_proxy_optimality (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b τ : ℝ) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hbound : ∀ t : ℝ, mgf μ t ≤ Real.exp (τ*t^2/2)) : variance μ ≤ τ :=
  proxyOptimality hμ hs hbound

/-- Explicit failure at every ratio strictly above the threshold. -/
theorem sharp_universal_ratio (R : ℝ) (hR : sharpRatio < R) :
    IsProbabilityMeasure (counterexampleLaw R) ∧ Symmetric (counterexampleLaw R) ∧
    BandSupport (counterexampleLaw R) 1 R ∧
    ∃ ε > 0, ∀ t : ℝ, 0 < |t| → |t| < ε →
      Real.exp (variance (counterexampleLaw R)*t^2/2) < mgf (counterexampleLaw R) t :=
  sharpness hR

/-- The exact fourth-deficit decomposition into displacement and interior mass. -/
theorem fourth_deficit_decomposition (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    fourthDeficit μ = 3*(variance μ-1)^2+interiority μ := fourthDeficit_identity hμ

/-- Fourth-order Gaussian contact identifies the signed probability measure. -/
theorem critical_law_rigidity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) :
    fourthDeficit μ = 0 ↔ μ = criticalLaw :=
  fourthDeficit_eq_zero_iff_criticalLaw μ hμ hs

/-- The real Wasserstein distance is taken over a nonempty class with finite costs. -/
theorem squared_transport_finiteness (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    (Couplings (squaredLaw μ) (squaredLaw criticalLaw)).Nonempty ∧
    (∀ π ∈ Couplings (squaredLaw μ) (squaredLaw criticalLaw), transportCost π ≠ ⊤) ∧
    wassersteinOneExtended (squaredLaw μ) (squaredLaw criticalLaw) ≠ ⊤ :=
  squaredLaw_transport_finite μ hμ

/-- Constructive transport estimate throughout the normalized bands. -/
theorem squared_transport_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
      |variance μ-1|+interiority μ/Real.sqrt 6 := squaredLaw_transport_bound μ hμ

/-- Sharp local modulus for the ordinary first Wasserstein distance of squared laws. -/
theorem sharp_local_transport (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hδ : fourthDeficit μ ≤ 1/2) :
    wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
      Real.sqrt (fourthDeficit μ/3) := sharp_local_stability μ hμ hδ

/-- Attainment at every deficit in the complete stated interval. -/
theorem local_transport_attainment (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) :
    let μ := endpointLaw (1+Real.sqrt (δ/3))
    IsProbabilityMeasure μ ∧ Symmetric μ ∧ NormalizedSupport μ ∧ fourthDeficit μ = δ ∧
      wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) = Real.sqrt (δ/3) :=
  sharp_local_stability_attained hδ hδ'

end SupportCriterion
