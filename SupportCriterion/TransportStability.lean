module

public import SupportCriterion.TransportChoice
public import SupportCriterion.LawBasics

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SupportCriterion

lemma integrable_of_intervalSupport {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ y ∂μ, lowerSq ≤ y ∧ y ≤ upperSq) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc lowerSq upperSq)).image hf).isBounded.exists_norm_le
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [hμ] with x hx
  exact hC _ (Set.mem_image_of_mem f hx)

lemma integral_endpointFraction (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun y : ℝ => y) μ) :
    (∫ y, endpointFraction y ∂μ) = ((∫ y, y ∂μ) - lowerSq) / (upperSq - lowerSq) := by
  unfold endpointFraction
  rw [integral_div, integral_sub hμ (integrable_const lowerSq)]
  simp

lemma integral_endpointChoice (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, lowerSq ≤ y ∧ y ≤ upperSq) {p : ℝ}
    (hp : 0 ≤ p ∧ p ≤ 1) (hmean : (∫ y, endpointFraction y ∂μ) = p) :
    (∫ y, endpointChoice p y ∂μ) = referenceWeight := by
  have hri : Integrable endpointFraction μ := integrable_of_intervalSupport hμ (by unfold endpointFraction; fun_prop)
  unfold endpointChoice
  split_ifs with h
  · rw [integral_div, integral_const_mul, hmean]
    have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le referenceWeight_pos h)
    field_simp
  · have hp1 : 1 - p ≠ 0 := by linarith [referenceWeight_lt_one]
    have hfi : Integrable (fun y => (1 - endpointFraction y) * (referenceWeight - p) / (1 - p)) μ :=
      (((integrable_const 1).sub hri).mul_const _).div_const _
    rw [integral_add hri hfi, integral_div, integral_mul_const,
      integral_sub (integrable_const 1) hri, hmean]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    field_simp
    ring

lemma integral_choice_displacement (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, lowerSq ≤ y ∧ y ≤ upperSq) {p : ℝ}
    (hp : 0 ≤ p ∧ p ≤ 1) (hmean : (∫ y, endpointFraction y ∂μ) = p) :
    (∫ y, |endpointChoice p y - endpointFraction y| ∂μ) = |p - referenceWeight| := by
  have hri : Integrable endpointFraction μ := integrable_of_intervalSupport hμ (by unfold endpointFraction; fun_prop)
  have hqi : Integrable (endpointChoice p) μ :=
    integrable_of_intervalSupport hμ (endpointChoice_continuous p)
  have hqiMean := integral_endpointChoice μ hμ hp hmean
  rcases le_total referenceWeight p with hp' | hp'
  · calc
      _ = ∫ y, endpointFraction y - endpointChoice p y ∂μ := by
        apply integral_congr_ae
        filter_upwards [hμ] with y hy
        rw [abs_of_nonpos (sub_nonpos.mpr (endpointChoice_le_fraction hp' hy))]
        ring
      _ = p - referenceWeight := by rw [integral_sub hri hqi, hmean, hqiMean]
      _ = |p - referenceWeight| := (abs_of_nonneg (sub_nonneg.mpr hp')).symm
  · have ha : ∀ᵐ y ∂μ, endpointFraction y ≤ endpointChoice p y := by
      filter_upwards [hμ] with y hy
      rcases hp'.eq_or_lt with h | h
      · rw [h, endpointChoice, if_pos le_rfl]
        have hp0 := ne_of_gt referenceWeight_pos
        field_simp
        exact le_rfl
      · exact fraction_le_endpointChoice h hy
    calc
      _ = ∫ y, endpointChoice p y - endpointFraction y ∂μ := by
        apply integral_congr_ae
        filter_upwards [ha] with y hy
        exact abs_of_nonneg (sub_nonneg.mpr hy)
      _ = referenceWeight - p := by rw [integral_sub hqi hri, hmean, hqiMean]
      _ = |p - referenceWeight| := by rw [abs_of_nonpos (sub_nonpos.mpr hp')]; ring

lemma endpointChoice_transport_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, lowerSq ≤ y ∧ y ≤ upperSq) :
    wassersteinOne μ (twoEndpointLaw referenceWeight) ≤
      |(∫ y, y ∂μ) - 1| +
      2 * (∫ y, (y - lowerSq) * (upperSq - y) ∂μ) / (upperSq - lowerSq) := by
  let p := ((∫ y, y ∂μ) - lowerSq) / (upperSq - lowerSq)
  have hri : Integrable endpointFraction μ := integrable_of_intervalSupport hμ (by unfold endpointFraction; fun_prop)
  have hyi : Integrable (fun y : ℝ => y) μ := integrable_of_intervalSupport hμ continuous_id
  have hmean : (∫ y, endpointFraction y ∂μ) = p := integral_endpointFraction μ hyi
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    constructor
    · rw [← hmean]
      exact integral_nonneg_of_ae (hμ.mono fun y hy => (endpointFraction_mem hy).1)
    · have hh := integral_mono_ae hri (integrable_const 1) (hμ.mono fun y hy => (endpointFraction_mem hy).2)
      simpa only [hmean, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] using hh
  have hq0 : ∀ᵐ y ∂μ, 0 ≤ endpointChoice p y := hμ.mono fun y hy => (endpointChoice_mem hp hy).1
  have hq1 : ∀ᵐ y ∂μ, endpointChoice p y ≤ 1 := hμ.mono fun y hy => (endpointChoice_mem hp hy).2
  have hqi : Integrable (endpointChoice p) μ := integrable_of_intervalSupport hμ (endpointChoice_continuous p)
  have hqm : Measurable (endpointChoice p) := (endpointChoice_continuous p).measurable
  have hπ : endpointCoupling μ (endpointChoice p) ∈ Couplings μ (twoEndpointLaw referenceWeight) := by
    have h := endpointCoupling_mem μ (endpointChoice p) hqm hq0 hq1 hqi
    rwa [integral_endpointChoice μ hμ hp hmean] at h
  let c := fun y => (1 - endpointChoice p y) * |y - lowerSq| + endpointChoice p y * |y - upperSq|
  have hqc : Continuous (endpointChoice p) := endpointChoice_continuous p
  have hci : Integrable c μ := integrable_of_intervalSupport hμ (by dsimp [c]; fun_prop)
  have hcnonneg : ∀ᵐ y ∂μ, 0 ≤ c y := by
    filter_upwards [hq0, hq1] with y hy0 hy1
    dsimp [c]
    positivity
  have hc : transportCost (endpointCoupling μ (endpointChoice p)) = ENNReal.ofReal (∫ y, c y ∂μ) := by
    rw [endpointCoupling_cost μ _ hqm hq0 hq1]
    exact (ofReal_integral_eq_lintegral_ofReal hci hcnonneg).symm
  have hW : wassersteinOne μ (twoEndpointLaw referenceWeight) ≤ ∫ y, c y ∂μ := by
    have h := wassersteinOneExtended_le_cost hπ
    rw [hc] at h
    exact (ENNReal.toReal_mono (by simp) h).trans_eq (ENNReal.toReal_ofReal (integral_nonneg_of_ae hcnonneg))
  have hii : Integrable (fun y => (y - lowerSq) * (upperSq - y)) μ :=
    integrable_of_intervalSupport hμ (by fun_prop)
  have hdi : Integrable (fun y => |endpointChoice p y - endpointFraction y|) μ := (hqi.sub hri).abs
  have hbound := integral_mono_ae hci
    ((hii.const_mul 2).div_const (upperSq - lowerSq) |>.add (hdi.const_mul (upperSq - lowerSq)))
    (hμ.mono fun y hy => endpoint_transport_cost_pointwise (q := endpointChoice p y) hy)
  simp only [Pi.add_apply] at hbound
  rw [integral_add ((hii.const_mul 2).div_const _) (hdi.const_mul _), integral_div,
    integral_const_mul, integral_const_mul, integral_choice_displacement μ hμ hp hmean] at hbound
  have hdist : (upperSq - lowerSq) * |p - referenceWeight| = |(∫ y, y ∂μ) - 1| := by
    rw [← abs_of_pos upperSq_sub_lowerSq_pos, ← abs_mul]
    congr 1
    dsimp [p, referenceWeight]
    field_simp [ne_of_gt upperSq_sub_lowerSq_pos]
    <;> ring
  rw [hdist] at hbound
  linarith

end SupportCriterion
