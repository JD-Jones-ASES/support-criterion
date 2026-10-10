module

public import SupportCriterion.SharpGap
public import SupportCriterion.Scaling

@[expose] public section

open MeasureTheory

namespace SupportCriterion

/-- The sharp pure eighth-order estimate in the original support scale. -/
theorem scaled_sharp_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b/a ≤ sharpRatio) (t : ℝ) :
    a^8/(25200*lowerSq^4)*t^8 ≤
      Real.exp (variance μ*t^2/2)-mgf μ t := by
  let c := Real.sqrt lowerSq / a
  have hc : c ≠ 0 := ne_of_gt (div_pos (Real.sqrt_pos.2 lowerSq_pos) ha)
  have hn : NormalizedSupport (scaleLaw μ c) := scaleLaw_normalizedSupport ha hμ hr
  have h := normalized_sharp_gap (scaleLaw μ c) hn (scaleLaw_symmetric hs c) (t/c)
  have hd : 0 ≤ interiority (scaleLaw μ c)*(t/c)^4/24 := by
    have := interiority_nonneg hn
    positivity
  have hg : (t/c)^8/25200 ≤
      Real.exp (variance (scaleLaw μ c)*(t/c)^2/2)-mgf (scaleLaw μ c) (t/c) := by
    linarith
  rw [variance_scaleLaw, mgf_scaleLaw] at hg
  have he : c^2*variance μ*(t/c)^2/2 = variance μ*t^2/2 := by field_simp
  have height : (t/c)^8/25200 = a^8/(25200*lowerSq^4)*t^8 := by
    dsimp [c]
    rw [div_pow, div_pow, show (8:ℕ) = 2*4 by norm_num,
      pow_mul (Real.sqrt lowerSq), Real.sq_sqrt lowerSq_nonneg]
    field_simp
  rw [he, height, mul_div_cancel₀ _ hc] at hg
  exact hg

end SupportCriterion
