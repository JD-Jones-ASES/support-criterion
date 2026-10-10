module

public import SupportCriterion.Chord

@[expose] public section

open MeasureTheory

namespace SupportCriterion

lemma normalized_gap_of_endpoint_bound
    (hendpoint : ∀ (v t : ℝ), lowerSq ≤ v → v ≤ upperSq →
      (v - 1) ^ 2 * t ^ 4 / 16000 + t ^ 8 / 64000 ≤
        Real.exp (v * t ^ 2 / 2) - endpointMGF v t)
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) (t : ℝ) :
    fourthDeficit μ * t ^ 4 / 48000 + t ^ 8 / 64000 ≤
      Real.exp (variance μ * t ^ 2 / 2) - mgf μ t := by
  have hv := variance_mem hμ
  have h1 := hendpoint (variance μ) t hv.1 hv.2
  have h2 := endpoint_mgf_gap hμ hs t
  have hd := interiority_nonneg hμ
  rw [fourthDeficit_identity hμ]
  nlinarith [mul_nonneg hd (show 0 ≤ t ^ 4 by positivity)]

lemma normalized_strict_of_gap {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (t : ℝ) (ht : t ≠ 0)
    (hgap : fourthDeficit μ * t ^ 4 / 48000 + t ^ 8 / 64000 ≤
      Real.exp (variance μ * t ^ 2 / 2) - mgf μ t) :
    mgf μ t < Real.exp (variance μ * t ^ 2 / 2) := by
  have hd := fourthDeficit_nonneg hμ
  have hp : 0 < t ^ 8 := by
    simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero ht) 4
  nlinarith [mul_nonneg hd (show 0 ≤ t ^ 4 by positivity)]

end SupportCriterion
