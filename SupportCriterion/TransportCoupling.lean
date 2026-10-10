module

public import SupportCriterion.Transport
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SupportCriterion

noncomputable def twoEndpointLaw (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac lowerSq +
  ENNReal.ofReal p • Measure.dirac upperSq

lemma map_square_smul (c : ℝ≥0∞) (μ : Measure ℝ) :
    Measure.map (fun x : ℝ => x ^ 2) (c • μ) = c • Measure.map (fun x : ℝ => x ^ 2) μ :=
  Measure.map_smul c (by fun_prop)

lemma squaredLaw_symmetricTwoPoint (x : ℝ) :
    squaredLaw (symmetricTwoPoint x) = Measure.dirac (x ^ 2) := by
  unfold squaredLaw symmetricTwoPoint
  rw [Measure.map_add _ _ (by fun_prop)]
  simp only [map_square_smul, Measure.map_dirac, neg_sq,
    ← add_smul, ENNReal.add_halves, one_smul]

lemma squaredLaw_endpointLaw (v : ℝ) :
    squaredLaw (endpointLaw v) = twoEndpointLaw ((v - lowerSq) / (upperSq - lowerSq)) := by
  unfold squaredLaw endpointLaw
  rw [Measure.map_add _ _ (by fun_prop)]
  simp only [map_square_smul]
  change _ • squaredLaw (symmetricTwoPoint _) + _ • squaredLaw (symmetricTwoPoint _) = _
  rw [squaredLaw_symmetricTwoPoint, squaredLaw_symmetricTwoPoint,
    Real.sq_sqrt lowerSq_nonneg, Real.sq_sqrt upperSq_nonneg]
  rfl

/-- Two weighted pushforwards give an explicit endpoint-valued coupling. -/
noncomputable def endpointCoupling (μ : Measure ℝ) (q : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (fun y => (y, lowerSq)) (μ.withDensity fun y => ENNReal.ofReal (1 - q y)) +
  Measure.map (fun y => (y, upperSq)) (μ.withDensity fun y => ENNReal.ofReal (q y))

lemma endpointCoupling_left (μ : Measure ℝ) (q : ℝ → ℝ) (hq : Measurable q)
    (hq0 : ∀ᵐ y ∂μ, 0 ≤ q y) (hq1 : ∀ᵐ y ∂μ, q y ≤ 1) :
    Measure.map Prod.fst (endpointCoupling μ q) = μ := by
  unfold endpointCoupling
  rw [Measure.map_add _ _ measurable_fst,
    Measure.map_map measurable_fst (by fun_prop),
    Measure.map_map measurable_fst (by fun_prop)]
  simp only [Function.comp_def, Measure.map_id', Measure.map_id]
  rw [← withDensity_add_left (by fun_prop)]
  calc
    μ.withDensity (fun y => ENNReal.ofReal (1 - q y) + ENNReal.ofReal (q y)) =
        μ.withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [hq0, hq1] with y hy0 hy1
      rw [← ENNReal.ofReal_add (by linarith) hy0]
      simp
    _ = μ := withDensity_one

lemma endpointCoupling_right (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ → ℝ)
    (hq : Measurable q) (hq0 : ∀ᵐ y ∂μ, 0 ≤ q y) (hq1 : ∀ᵐ y ∂μ, q y ≤ 1)
    (hqi : Integrable q μ) :
    Measure.map Prod.snd (endpointCoupling μ q) = twoEndpointLaw (∫ y, q y ∂μ) := by
  have hqi' : Integrable (fun y => 1 - q y) μ := (integrable_const 1).sub hqi
  unfold endpointCoupling twoEndpointLaw
  rw [Measure.map_add _ _ measurable_snd,
    Measure.map_map measurable_snd (by fun_prop),
    Measure.map_map measurable_snd (by fun_prop)]
  simp only [Function.comp_def, Measure.map_const, withDensity_apply,
    MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hqi' (by filter_upwards [hq1] with y hy; exact sub_nonneg.mpr hy),
    ← ofReal_integral_eq_lintegral_ofReal hqi hq0,
    integral_sub (integrable_const 1) hqi]
  simp

lemma endpointCoupling_isProbabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (q : ℝ → ℝ) (hq : Measurable q) (hq0 : ∀ᵐ y ∂μ, 0 ≤ q y)
    (hq1 : ∀ᵐ y ∂μ, q y ≤ 1) : IsProbabilityMeasure (endpointCoupling μ q) := by
  constructor
  have h := congrArg (fun ν : Measure ℝ => ν Set.univ) (endpointCoupling_left μ q hq hq0 hq1)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using h

lemma endpointCoupling_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ → ℝ)
    (hq : Measurable q) (hq0 : ∀ᵐ y ∂μ, 0 ≤ q y) (hq1 : ∀ᵐ y ∂μ, q y ≤ 1)
    (hqi : Integrable q μ) :
    endpointCoupling μ q ∈ Couplings μ (twoEndpointLaw (∫ y, q y ∂μ)) :=
  ⟨endpointCoupling_isProbabilityMeasure μ q hq hq0 hq1,
    endpointCoupling_left μ q hq hq0 hq1,
    endpointCoupling_right μ q hq hq0 hq1 hqi⟩

lemma endpointCoupling_cost (μ : Measure ℝ) (q : ℝ → ℝ) (hq : Measurable q)
    (hq0 : ∀ᵐ y ∂μ, 0 ≤ q y) (hq1 : ∀ᵐ y ∂μ, q y ≤ 1) :
    transportCost (endpointCoupling μ q) =
      ∫⁻ y, ENNReal.ofReal ((1 - q y) * |y - lowerSq| + q y * |y - upperSq|) ∂μ := by
  unfold transportCost endpointCoupling
  rw [lintegral_add_measure,
    lintegral_map (by fun_prop) (by fun_prop),
    lintegral_map (by fun_prop) (by fun_prop),
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    ← lintegral_add_left (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hq0, hq1] with y hy0 hy1
  simp only [edist_dist, Real.dist_eq, Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (sub_nonneg.mpr hy1), ← ENNReal.ofReal_mul hy0,
    ← ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr hy1) (abs_nonneg _))
      (mul_nonneg hy0 (abs_nonneg _))]

end SupportCriterion
