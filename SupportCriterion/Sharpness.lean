module

public import SupportCriterion.EndpointLaw
public import SupportCriterion.TaylorAux

@[expose] public section

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace SupportCriterion

lemma one_lt_sharpRatio : 1 < sharpRatio := by
  have h3 : 1 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  unfold sharpRatio
  linarith [Real.sqrt_nonneg (2 : ℝ)]

lemma sharpRatio_sq : sharpRatio ^ 2 = 5 + 2 * Real.sqrt 6 := by
  have hp : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num)]
    norm_num
  unfold sharpRatio
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The explicit counterexample law for an amplitude ratio `R`. -/
noncomputable def counterexampleLaw (R : ℝ) : Measure ℝ :=
  ENNReal.ofReal (R ^ 2 / (R ^ 2 + 1)) • symmetricTwoPoint 1 +
    ENNReal.ofReal (1 / (R ^ 2 + 1)) • symmetricTwoPoint R

lemma counterexampleLaw_isProbabilityMeasure (R : ℝ) :
    IsProbabilityMeasure (counterexampleLaw R) := by
  have hd : 0 < R ^ 2 + 1 := by positivity
  have hp : 0 ≤ R ^ 2 / (R ^ 2 + 1) := by positivity
  have hq : 0 ≤ 1 / (R ^ 2 + 1) := by positivity
  constructor
  simp only [counterexampleLaw, Measure.add_apply, MeasurableSet.univ,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp hq]
  have he : R ^ 2 / (R ^ 2 + 1) + 1 / (R ^ 2 + 1) = 1 := by field_simp
  rw [he]
  norm_num

lemma counterexampleLaw_symmetric (R : ℝ) : Symmetric (counterexampleLaw R) := by
  unfold Symmetric counterexampleLaw
  rw [Measure.map_add _ _ (by fun_prop)]
  simp only [Measure.map_smul _ measurable_neg.aemeasurable]
  rw [show Measure.map (fun x : ℝ => -x) (symmetricTwoPoint 1) = symmetricTwoPoint 1
    from symmetricTwoPoint_symmetric _,
    show Measure.map (fun x : ℝ => -x) (symmetricTwoPoint R) = symmetricTwoPoint R
    from symmetricTwoPoint_symmetric _]

lemma counterexampleLaw_bandSupport {R : ℝ} (hR : 1 ≤ R) :
    BandSupport (counterexampleLaw R) 1 R := by
  unfold BandSupport counterexampleLaw symmetricTwoPoint
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;> simp [hR]
  · apply Measure.ae_smul_measure
    rw [ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;> simp [abs_of_nonneg (by linarith : 0 ≤ R), hR]

lemma integral_counterexampleLaw (f : ℝ → ℝ) (R : ℝ) :
    (∫ x, f x ∂counterexampleLaw R) =
      (R ^ 2 / (R ^ 2 + 1)) * ((f 1 + f (-1)) / 2) +
      (1 / (R ^ 2 + 1)) * ((f R + f (-R)) / 2) := by
  have hp : 0 ≤ R ^ 2 / (R ^ 2 + 1) := by positivity
  have hq : 0 ≤ 1 / (R ^ 2 + 1) := by positivity
  unfold counterexampleLaw
  rw [integral_add_measure
    ((integrable_symmetricTwoPoint f _).smul_measure (by simp))
    ((integrable_symmetricTwoPoint f _).smul_measure (by simp))]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal hq, smul_eq_mul, integral_symmetricTwoPoint]

lemma counterexampleLaw_variance (R : ℝ) :
    variance (counterexampleLaw R) = 2 * R ^ 2 / (R ^ 2 + 1) := by
  rw [variance, moment, integral_counterexampleLaw]
  ring

lemma counterexampleLaw_fourthMoment (R : ℝ) :
    moment (counterexampleLaw R) 4 = R ^ 2 := by
  rw [moment, integral_counterexampleLaw]
  have hd : R ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma counterexampleLaw_mgf (R t : ℝ) :
    mgf (counterexampleLaw R) t =
      (R ^ 2 / (R ^ 2 + 1)) * Real.cosh t +
      (1 / (R ^ 2 + 1)) * Real.cosh (R * t) := by
  rw [mgf, integral_counterexampleLaw]
  simp only [Real.cosh_eq]
  congr 1 <;> ring_nf

lemma counterexampleLaw_cumulant (R : ℝ) :
    moment (counterexampleLaw R) 4 - 3 * variance (counterexampleLaw R) ^ 2 =
      R ^ 2 * ((R ^ 2) ^ 2 - 10 * R ^ 2 + 1) / (R ^ 2 + 1) ^ 2 := by
  rw [counterexampleLaw_variance, counterexampleLaw_fourthMoment]
  have hd : R ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma counterexampleLaw_mgf_expansion (R : ℝ) :
    (fun t : ℝ => mgf (counterexampleLaw R) t -
      Real.exp (variance (counterexampleLaw R) * t ^ 2 / 2) -
      ((moment (counterexampleLaw R) 4 - 3 * variance (counterexampleLaw R) ^ 2) / 24)
        * t ^ 4) =o[𝓝 0] (fun t : ℝ => t ^ 4) := by
  have h := ((cosh_mul_taylor_four 1).const_mul_left (R ^ 2 / (R ^ 2 + 1))).add
    ((cosh_mul_taylor_four R).const_mul_left (1 / (R ^ 2 + 1)))
  have he := exp_mul_sq_taylor_four (variance (counterexampleLaw R) / 2)
  apply (h.sub he).congr_left
  intro t
  rw [counterexampleLaw_mgf, counterexampleLaw_variance, counterexampleLaw_fourthMoment]
  have hd : R ^ 2 + 1 ≠ 0 := by positivity
  simp only [one_mul, one_pow]
  field_simp
  ring

lemma counterexampleLaw_cumulant_pos {R : ℝ} (hR : sharpRatio < R) :
    0 < moment (counterexampleLaw R) 4 - 3 * variance (counterexampleLaw R) ^ 2 := by
  have hr : 0 < sharpRatio := lt_trans (by norm_num) one_lt_sharpRatio
  have hR0 : 0 < R := hr.trans hR
  have hq : 5 + 2 * Real.sqrt 6 < R ^ 2 := by
    rw [← sharpRatio_sq]
    nlinarith
  have hp : 0 < (R ^ 2) ^ 2 - 10 * R ^ 2 + 1 := by
    have hf := mul_pos (sub_pos.mpr hq)
      (show 0 < R ^ 2 + (5 + 2 * Real.sqrt 6) - 10 by linarith [sqrt_six_pos])
    nlinarith [sqrt_six_sq]
  rw [counterexampleLaw_cumulant]
  exact div_pos (mul_pos (sq_pos_of_pos hR0) hp) (by positivity)

/-- Every ratio above the threshold has an explicit law that violates the
variance-matched Gaussian MGF bound throughout a punctured neighborhood of zero. -/
theorem sharpness {R : ℝ} (hR : sharpRatio < R) :
    IsProbabilityMeasure (counterexampleLaw R) ∧
    Symmetric (counterexampleLaw R) ∧
    BandSupport (counterexampleLaw R) 1 R ∧
    ∃ ε > 0, ∀ t : ℝ, 0 < |t| → |t| < ε →
      Real.exp (variance (counterexampleLaw R) * t ^ 2 / 2) <
        mgf (counterexampleLaw R) t := by
  refine ⟨counterexampleLaw_isProbabilityMeasure R, counterexampleLaw_symmetric R,
    counterexampleLaw_bandSupport (one_lt_sharpRatio.trans hR).le, ?_⟩
  obtain ⟨ε, hε, he⟩ := eventually_pos_of_pos_fourth_coefficient
    (div_pos (counterexampleLaw_cumulant_pos hR) (by norm_num))
    (counterexampleLaw_mgf_expansion R)
  exact ⟨ε, hε, fun t ht hte => sub_pos.mp (he t ht hte)⟩

end SupportCriterion
