module

public import SupportCriterion.TransportFinal

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SupportCriterion

lemma lowerSq_quadratic : lowerSq ^ 2 - 6 * lowerSq + 3 = 0 := by
  nlinarith only [lowerSq_add_upperSq, lowerSq_mul_upperSq]

lemma upperSq_quadratic : upperSq ^ 2 - 6 * upperSq + 3 = 0 := by
  nlinarith only [lowerSq_add_upperSq, lowerSq_mul_upperSq]

lemma referenceWeight_eq_lowerSq_div_six : referenceWeight = lowerSq / 6 := by
  unfold referenceWeight
  apply (div_eq_iff (ne_of_gt upperSq_sub_lowerSq_pos)).mpr
  nlinarith only [lowerSq_quadratic, lowerSq_mul_upperSq]

lemma one_sub_referenceWeight_eq_upperSq_div_six :
    1 - referenceWeight = upperSq / 6 := by
  rw [referenceWeight_eq_lowerSq_div_six]
  linarith [lowerSq_add_upperSq]

lemma integral_squared_fluctuation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    (∫ x, (x ^ 2 - variance μ) ^ 2 ∂μ) = moment μ 4 - (variance μ) ^ 2 := by
  have he : (fun x : ℝ => (x ^ 2 - variance μ) ^ 2) =
      fun x => x ^ 4 - (2 * variance μ) * x ^ 2 + (variance μ) ^ 2 := by
    funext x; ring
  have his : Integrable (fun x : ℝ => x ^ 4 - (2 * variance μ) * x ^ 2) μ :=
    (integrable_pow hμ 4).sub ((integrable_pow hμ 2).const_mul (2 * variance μ))
  have him : Integrable (fun x : ℝ => (2 * variance μ) * x ^ 2) μ :=
    (integrable_pow hμ 2).const_mul (2 * variance μ)
  rw [he, integral_add his (integrable_const ((variance μ) ^ 2)),
    integral_sub (integrable_pow hμ 4) him, integral_const_mul]
  simp [moment, variance]
  ring

lemma variance_sq_le_fourth_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) : (variance μ) ^ 2 ≤ moment μ 4 := by
  have h := integral_nonneg (μ := μ) (fun x : ℝ => sq_nonneg (x ^ 2 - variance μ))
  rw [integral_squared_fluctuation μ hμ] at h
  linarith

lemma wassersteinOne_le_endpointChoice_cost (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, lowerSq ≤ y ∧ y ≤ upperSq) :
    let p := ((∫ y, y ∂μ) - lowerSq) / (upperSq - lowerSq)
    wassersteinOne μ (twoEndpointLaw referenceWeight) ≤
      ∫ y, (1 - endpointChoice p y) * |y - lowerSq| +
        endpointChoice p y * |y - upperSq| ∂μ := by
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
  change wassersteinOne μ (twoEndpointLaw referenceWeight) ≤ ∫ y, c y ∂μ
  have h := wassersteinOneExtended_le_cost hπ
  rw [hc] at h
  exact (ENNReal.toReal_mono (by simp) h).trans_eq (ENNReal.toReal_ofReal (integral_nonneg_of_ae hcnonneg))


lemma endpointChoice_cost_of_one_le_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, lowerSq ≤ y ∧ y ≤ upperSq)
    (hv : 1 ≤ ∫ y, y ∂μ) :
    let v := ∫ y, y ∂μ
    let p := (v - lowerSq) / (upperSq - lowerSq)
    (∫ y, (1 - endpointChoice p y) * |y - lowerSq| +
      endpointChoice p y * |y - upperSq| ∂μ) =
      (v - 1) + lowerSq * (∫ y, (y - lowerSq) * (upperSq - y) ∂μ) /
        (3 * (v - lowerSq)) := by
  let v := ∫ y, y ∂μ
  let p := (v - lowerSq) / (upperSq - lowerSq)
  have hm : v - lowerSq ≠ 0 := by dsimp [v]; linarith [lowerSq_lt_one]
  have hp : referenceWeight ≤ p := by
    dsimp [referenceWeight, p]
    exact (div_le_div_iff_of_pos_right upperSq_sub_lowerSq_pos).mpr (by dsimp [v]; linarith)
  have hq (y : ℝ) : endpointChoice p y = referenceWeight / (v - lowerSq) * (y - lowerSq) := by
    rw [endpointChoice, if_pos hp]
    dsimp [endpointFraction, p]
    field_simp [hm, ne_of_gt upperSq_sub_lowerSq_pos]
  have hi : Integrable (fun y : ℝ => y - lowerSq) μ :=
    integrable_of_intervalSupport hμ (by fun_prop)
  have hd : Integrable (fun y : ℝ => (y - lowerSq) * (upperSq - y)) μ :=
    integrable_of_intervalSupport hμ (by fun_prop)
  have hyi : Integrable (fun y : ℝ => y) μ := integrable_of_intervalSupport hμ continuous_id
  have he : (∫ y, y - lowerSq ∂μ) = v - lowerSq := by
    rw [integral_sub hyi (integrable_const lowerSq)]
    simp [v]
  change (∫ y, (1 - endpointChoice p y) * |y - lowerSq| +
    endpointChoice p y * |y - upperSq| ∂μ) = _
  calc
    _ = ∫ y, (1 - (upperSq - lowerSq) * referenceWeight / (v - lowerSq)) *
        (y - lowerSq) + (2 * referenceWeight / (v - lowerSq)) *
        ((y - lowerSq) * (upperSq - y)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hμ] with y hy
      rw [hq, abs_of_nonneg (sub_nonneg.mpr hy.1), abs_of_nonpos (sub_nonpos.mpr hy.2)]
      ring
    _ = (v - 1) + lowerSq * (∫ y, (y - lowerSq) * (upperSq - y) ∂μ) /
        (3 * (v - lowerSq)) := by
      have hconst : (upperSq - lowerSq) * referenceWeight = 1 - lowerSq := by
        unfold referenceWeight
        field_simp [ne_of_gt upperSq_sub_lowerSq_pos]
      rw [integral_add (hi.const_mul _) (hd.const_mul _), integral_const_mul,
        integral_const_mul, he, hconst, referenceWeight_eq_lowerSq_div_six]
      field_simp [hm]
      ring

lemma endpointChoice_cost_of_mean_lt_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, lowerSq ≤ y ∧ y ≤ upperSq)
    (hv : (∫ y, y ∂μ) < 1) :
    let v := ∫ y, y ∂μ
    let p := (v - lowerSq) / (upperSq - lowerSq)
    (∫ y, (1 - endpointChoice p y) * |y - lowerSq| +
      endpointChoice p y * |y - upperSq| ∂μ) =
      (1 - v) + upperSq * (∫ y, (y - lowerSq) * (upperSq - y) ∂μ) /
        (3 * (upperSq - v)) := by
  let v := ∫ y, y ∂μ
  let p := (v - lowerSq) / (upperSq - lowerSq)
  have hm : upperSq - v ≠ 0 := by dsimp [v]; linarith [one_lt_upperSq]
  have hp : ¬referenceWeight ≤ p := by
    apply not_le.mpr
    dsimp [referenceWeight, p]
    exact (div_lt_div_iff_of_pos_right upperSq_sub_lowerSq_pos).mpr (by dsimp [v]; linarith)
  have hq (y : ℝ) : endpointChoice p y =
      1 - (1 - referenceWeight) / (upperSq - v) * (upperSq - y) := by
    rw [endpointChoice, if_neg hp]
    dsimp [endpointFraction, p]
    have he : 1 - (v - lowerSq) / (upperSq - lowerSq) =
        (upperSq - v) / (upperSq - lowerSq) := by
      field_simp [ne_of_gt upperSq_sub_lowerSq_pos]
      ring
    rw [he]
    field_simp [hm, ne_of_gt upperSq_sub_lowerSq_pos]
    ring
  have hi : Integrable (fun y : ℝ => upperSq - y) μ :=
    integrable_of_intervalSupport hμ (by fun_prop)
  have hd : Integrable (fun y : ℝ => (y - lowerSq) * (upperSq - y)) μ :=
    integrable_of_intervalSupport hμ (by fun_prop)
  have hyi : Integrable (fun y : ℝ => y) μ := integrable_of_intervalSupport hμ continuous_id
  have he : (∫ y, upperSq - y ∂μ) = upperSq - v := by
    rw [integral_sub (integrable_const upperSq) hyi]
    simp [v]
  change (∫ y, (1 - endpointChoice p y) * |y - lowerSq| +
    endpointChoice p y * |y - upperSq| ∂μ) = _
  calc
    _ = ∫ y, (1 - (upperSq - lowerSq) * (1 - referenceWeight) / (upperSq - v)) *
        (upperSq - y) + (2 * (1 - referenceWeight) / (upperSq - v)) *
        ((y - lowerSq) * (upperSq - y)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hμ] with y hy
      rw [hq, abs_of_nonneg (sub_nonneg.mpr hy.1), abs_of_nonpos (sub_nonpos.mpr hy.2)]
      ring
    _ = (1 - v) + upperSq * (∫ y, (y - lowerSq) * (upperSq - y) ∂μ) /
        (3 * (upperSq - v)) := by
      have hconst : (upperSq - lowerSq) * (1 - referenceWeight) = upperSq - 1 := by
        unfold referenceWeight
        field_simp [ne_of_gt upperSq_sub_lowerSq_pos]
        ring
      rw [integral_add (hi.const_mul _) (hd.const_mul _), integral_const_mul,
        integral_const_mul, he, hconst, one_sub_referenceWeight_eq_upperSq_div_six]
      field_simp [hm]
      ring

/-- Exact remainder identity for the affine endpoint coupling. -/
lemma root_transport_deficit_factorization (r v m : ℝ)
    (hr : r ^ 2 - 6 * r + 3 = 0) (hvr : v - r ≠ 0) :
    (3 * v ^ 2 - m) - 3 * ((v - 1) + r * (6 * v - 3 - m) / (3 * (v - r))) ^ 2 =
      r ^ 2 * (6 * v - 3 - m) * (m - v ^ 2) / (3 * (v - r) ^ 2) := by
  have hh : v ^ 2 * (6 * v - 3 - m) * (r ^ 2 - 6 * r + 3) = 0 := by rw [hr]; ring
  field_simp [hvr]
  nlinarith only [hh]

lemma root_transport_cost_sq_le (r v m : ℝ)
    (hr : r ^ 2 - 6 * r + 3 = 0) (hvr : v - r ≠ 0)
    (hd : 0 ≤ 6 * v - 3 - m) (hm : v ^ 2 ≤ m) :
    3 * ((v - 1) + r * (6 * v - 3 - m) / (3 * (v - r))) ^ 2 ≤ 3 * v ^ 2 - m := by
  have h := root_transport_deficit_factorization r v m hr hvr
  have hn : 0 ≤ r ^ 2 * (6 * v - 3 - m) * (m - v ^ 2) / (3 * (v - r) ^ 2) := by
    exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg r) hd) (sub_nonneg.mpr hm))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  linarith

/-- Sharp first Wasserstein stability for the squared law at every deficit. -/
lemma sharp_global_stability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
      Real.sqrt (fourthDeficit μ / 3) := by
  have hW := wassersteinOne_le_endpointChoice_cost (squaredLaw μ) (squaredLaw_intervalSupport hμ)
  dsimp only at hW
  rw [← squaredLaw_reference] at hW
  have hd : 0 ≤ 6 * variance μ - 3 - moment μ 4 := by
    rw [← interiority_identity hμ]
    exact interiority_nonneg hμ
  have hm := variance_sq_le_fourth_moment μ hμ
  have hs := Real.sq_sqrt (show 0 ≤ fourthDeficit μ / 3 by have := fourthDeficit_nonneg hμ; positivity)
  have hs0 := Real.sqrt_nonneg (fourthDeficit μ / 3)
  have hi : (∫ y, (y - lowerSq) * (upperSq - y) ∂squaredLaw μ) = interiority μ :=
    integral_squaredLaw μ _ (by fun_prop)
  rcases le_or_gt 1 (variance μ) with hv | hv
  · have he := endpointChoice_cost_of_one_le_mean (squaredLaw μ) (squaredLaw_intervalSupport hμ)
      (by rwa [squaredLaw_mean])
    dsimp only at he
    rw [squaredLaw_mean, hi] at he
    rw [squaredLaw_mean] at hW
    rw [he] at hW
    change wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
      variance μ - 1 + lowerSq * interiority μ / (3 * (variance μ - lowerSq)) at hW
    have hc := root_transport_cost_sq_le lowerSq (variance μ) (moment μ 4)
      lowerSq_quadratic (by linarith [lowerSq_lt_one]) hd hm
    rw [← interiority_identity hμ] at hc
    change 3 * (variance μ - 1 + lowerSq * interiority μ / (3 * (variance μ - lowerSq))) ^ 2 ≤
      fourthDeficit μ at hc
    apply hW.trans
    nlinarith only [hc, hs, hs0]
  · have he := endpointChoice_cost_of_mean_lt_one (squaredLaw μ) (squaredLaw_intervalSupport hμ)
      (by rwa [squaredLaw_mean])
    dsimp only at he
    rw [squaredLaw_mean, hi] at he
    rw [squaredLaw_mean] at hW
    rw [he] at hW
    change wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
      1 - variance μ + upperSq * interiority μ / (3 * (upperSq - variance μ)) at hW
    have hc := root_transport_cost_sq_le upperSq (variance μ) (moment μ 4)
      upperSq_quadratic (by linarith [one_lt_upperSq]) hd hm
    rw [← interiority_identity hμ] at hc
    have heq : (variance μ - 1 + upperSq * interiority μ / (3 * (variance μ - upperSq))) =
        -(1 - variance μ + upperSq * interiority μ / (3 * (upperSq - variance μ))) := by
      have hne : upperSq - variance μ ≠ 0 := by linarith [one_lt_upperSq]
      have hne' : variance μ - upperSq ≠ 0 := by linarith [one_lt_upperSq]
      field_simp [hne, hne']
      ring
    rw [heq, neg_sq] at hc
    change 3 * (1 - variance μ + upperSq * interiority μ / (3 * (upperSq - variance μ))) ^ 2 ≤
      fourthDeficit μ at hc
    apply hW.trans
    nlinarith only [hc, hs, hs0]

/-- Complete feasible range of the fourth deficit under normalized support. -/
lemma fourthDeficit_global_range (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    0 ≤ fourthDeficit μ ∧ fourthDeficit μ ≤ 2 * upperSq ^ 2 := by
  refine ⟨fourthDeficit_nonneg hμ, ?_⟩
  have hm := variance_sq_le_fourth_moment μ hμ
  have hv := variance_mem hμ
  have hv0 : 0 ≤ variance μ := le_trans lowerSq_nonneg hv.1
  dsimp [fourthDeficit]
  nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) (add_nonneg upperSq_nonneg hv0)]

lemma global_attaining_variance_mem {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 2 * upperSq ^ 2) :
    lowerSq ≤ 1 + Real.sqrt (δ / 3) ∧ 1 + Real.sqrt (δ / 3) ≤ upperSq := by
  have hs := Real.sq_sqrt (show 0 ≤ δ / 3 by positivity)
  have hs0 := Real.sqrt_nonneg (δ / 3)
  constructor
  · linarith [lowerSq_lt_one]
  · nlinarith [upperSq_quadratic, one_lt_upperSq]

/-- The endpoint family attains the modulus at every feasible deficit. -/
lemma sharp_global_stability_attained {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 2 * upperSq ^ 2) :
    let μ := endpointLaw (1 + Real.sqrt (δ / 3))
    IsProbabilityMeasure μ ∧ Symmetric μ ∧ NormalizedSupport μ ∧
      fourthDeficit μ = δ ∧
      wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) = Real.sqrt (δ / 3) := by
  dsimp only
  let μ := endpointLaw (1 + Real.sqrt (δ / 3))
  have hv := global_attaining_variance_mem hδ hδ'
  have hprob : IsProbabilityMeasure μ := endpointLaw_isProbabilityMeasure _ hv
  letI : IsProbabilityMeasure μ := hprob
  have hsup : NormalizedSupport μ := endpointLaw_normalizedSupport _
  have hdef : fourthDeficit μ = δ := by
    rw [endpointLaw_fourthDeficit _ hv]
    have hs := Real.sq_sqrt (show 0 ≤ δ / 3 by positivity)
    nlinarith
  refine ⟨hprob, endpointLaw_symmetric _, hsup, hdef, ?_⟩
  apply le_antisymm
  · have h := sharp_global_stability μ hsup
    rwa [hdef] at h
  · have hi := integrable_of_intervalSupport (squaredLaw_intervalSupport hsup) continuous_id
    have hi0 := integrable_of_intervalSupport
      (squaredLaw_intervalSupport criticalLaw_normalizedSupport) continuous_id
    have h := mean_distance_le_wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) hi hi0
    rw [squaredLaw_mean, squaredLaw_mean, criticalLaw_variance,
      endpointLaw_variance _ hv, add_sub_cancel_left, abs_of_nonneg (Real.sqrt_nonneg _)] at h
    exact h

end SupportCriterion
