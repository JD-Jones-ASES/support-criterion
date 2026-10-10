module

public import SupportCriterion.Constants

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SupportCriterion

lemma integrable_symmetricTwoPoint (f : ℝ → ℝ) (x : ℝ) :
    Integrable f (symmetricTwoPoint x) := by
  unfold symmetricTwoPoint
  exact ((integrable_dirac (by simp)).smul_measure (by norm_num)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by norm_num))

lemma integral_symmetricTwoPoint (f : ℝ → ℝ) (x : ℝ) :
    (∫ y, f y ∂symmetricTwoPoint x) = (f x + f (-x)) / 2 := by
  unfold symmetricTwoPoint
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure (by norm_num))
    ((integrable_dirac (by simp)).smul_measure (by norm_num))]
  simp [integral_smul_measure]
  ring

instance symmetricTwoPoint_isProbabilityMeasure (x : ℝ) :
    IsProbabilityMeasure (symmetricTwoPoint x) := by
  constructor
  simp [symmetricTwoPoint, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

lemma symmetricTwoPoint_symmetric (x : ℝ) : Symmetric (symmetricTwoPoint x) := by
  unfold Symmetric symmetricTwoPoint
  rw [Measure.map_add _ _ (by fun_prop)]
  simp only [Measure.map_smul _ measurable_neg.aemeasurable, Measure.map_dirac, neg_neg]
  exact add_comm _ _

lemma endpointLaw_symmetric (v : ℝ) : Symmetric (endpointLaw v) := by
  unfold Symmetric endpointLaw
  rw [Measure.map_add _ _ (by fun_prop)]
  simp only [Measure.map_smul _ measurable_neg.aemeasurable]
  rw [show Measure.map (fun x : ℝ => -x) (symmetricTwoPoint (Real.sqrt lowerSq)) =
      symmetricTwoPoint (Real.sqrt lowerSq) from symmetricTwoPoint_symmetric _,
    show Measure.map (fun x : ℝ => -x) (symmetricTwoPoint (Real.sqrt upperSq)) =
      symmetricTwoPoint (Real.sqrt upperSq) from symmetricTwoPoint_symmetric _]

lemma integrable_endpointLaw (f : ℝ → ℝ) (v : ℝ) :
    Integrable f (endpointLaw v) := by
  exact ((integrable_symmetricTwoPoint f _).smul_measure (by simp)).add_measure
    ((integrable_symmetricTwoPoint f _).smul_measure (by simp))

lemma integral_endpointLaw (f : ℝ → ℝ) (v : ℝ)
    (hv : lowerSq ≤ v ∧ v ≤ upperSq) :
    (∫ x, f x ∂endpointLaw v) =
      (1 - (v - lowerSq) / (upperSq - lowerSq)) *
        ((f (Real.sqrt lowerSq) + f (-Real.sqrt lowerSq)) / 2) +
      ((v - lowerSq) / (upperSq - lowerSq)) *
        ((f (Real.sqrt upperSq) + f (-Real.sqrt upperSq)) / 2) := by
  have hL : 0 < upperSq - lowerSq := sub_pos.mpr lowerSq_lt_upperSq
  have hp : 0 ≤ (v - lowerSq) / (upperSq - lowerSq) := div_nonneg (sub_nonneg.mpr hv.1) hL.le
  have hp1 : (v - lowerSq) / (upperSq - lowerSq) ≤ 1 := (div_le_one hL).mpr (by linarith [hv.2])
  unfold endpointLaw
  rw [integral_add_measure
    ((integrable_symmetricTwoPoint f _).smul_measure (by simp))
    ((integrable_symmetricTwoPoint f _).smul_measure (by simp))]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp1), smul_eq_mul, integral_symmetricTwoPoint]

lemma endpointLaw_isProbabilityMeasure (v : ℝ) (hv : lowerSq ≤ v ∧ v ≤ upperSq) :
    IsProbabilityMeasure (endpointLaw v) := by
  have hL : 0 < upperSq - lowerSq := sub_pos.mpr lowerSq_lt_upperSq
  have hp : 0 ≤ (v - lowerSq) / (upperSq - lowerSq) := div_nonneg (sub_nonneg.mpr hv.1) hL.le
  have hp1 : (v - lowerSq) / (upperSq - lowerSq) ≤ 1 := (div_le_one hL).mpr (by linarith [hv.2])
  constructor
  simp only [endpointLaw, Measure.add_apply, MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp1) hp]
  simp

lemma endpointLaw_normalizedSupport (v : ℝ) : NormalizedSupport (endpointLaw v) := by
  have hA : (Real.sqrt lowerSq) ^ 2 = lowerSq := Real.sq_sqrt lowerSq_pos.le
  have hB : (Real.sqrt upperSq) ^ 2 = upperSq := Real.sq_sqrt upperSq_pos.le
  unfold NormalizedSupport endpointLaw symmetricTwoPoint
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;>
      simp [hA, lowerSq_lt_upperSq.le]
  · apply Measure.ae_smul_measure
    rw [ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;>
      simp [hB, lowerSq_lt_upperSq.le]

lemma endpointLaw_variance (v : ℝ) (hv : lowerSq ≤ v ∧ v ≤ upperSq) :
    variance (endpointLaw v) = v := by
  unfold variance moment
  rw [integral_endpointLaw _ _ hv]
  simp only [neg_sq, Real.sq_sqrt lowerSq_pos.le, Real.sq_sqrt upperSq_pos.le]
  field_simp [ne_of_gt (sub_pos.mpr lowerSq_lt_upperSq)]
  <;> ring

lemma endpointLaw_interiority (v : ℝ) (hv : lowerSq ≤ v ∧ v ≤ upperSq) :
    interiority (endpointLaw v) = 0 := by
  unfold interiority
  rw [integral_endpointLaw _ _ hv]
  simp [Real.sq_sqrt lowerSq_nonneg, Real.sq_sqrt upperSq_nonneg]

lemma endpointLaw_fourth_moment (v : ℝ) (hv : lowerSq ≤ v ∧ v ≤ upperSq) :
    moment (endpointLaw v) 4 = 6 * v - 3 := by
  have hA : lowerSq ^ 2 = 6 * lowerSq - 3 := by
    nlinarith [lowerSq_add_upperSq, lowerSq_mul_upperSq]
  have hB : upperSq ^ 2 = 6 * upperSq - 3 := by
    nlinarith [lowerSq_add_upperSq, lowerSq_mul_upperSq]
  unfold moment
  rw [integral_endpointLaw _ _ hv]
  simp only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_sq,
    Real.sq_sqrt lowerSq_nonneg, Real.sq_sqrt upperSq_nonneg, hA, hB]
  field_simp [ne_of_gt (sub_pos.mpr lowerSq_lt_upperSq)]
  <;> ring

lemma endpointLaw_fourthDeficit (v : ℝ) (hv : lowerSq ≤ v ∧ v ≤ upperSq) :
    fourthDeficit (endpointLaw v) = 3 * (v - 1) ^ 2 := by
  unfold fourthDeficit
  rw [endpointLaw_variance v hv, endpointLaw_fourth_moment v hv]
  ring

instance criticalLaw_isProbabilityMeasure : IsProbabilityMeasure criticalLaw :=
  endpointLaw_isProbabilityMeasure 1 ⟨lowerSq_lt_one.le, one_lt_upperSq.le⟩

lemma criticalLaw_symmetric : Symmetric criticalLaw := endpointLaw_symmetric 1
lemma criticalLaw_normalizedSupport : NormalizedSupport criticalLaw :=
  endpointLaw_normalizedSupport 1
lemma criticalLaw_variance : variance criticalLaw = 1 :=
  endpointLaw_variance 1 ⟨lowerSq_lt_one.le, one_lt_upperSq.le⟩
lemma criticalLaw_fourthDeficit : fourthDeficit criticalLaw = 0 := by
  unfold criticalLaw
  rw [endpointLaw_fourthDeficit 1 ⟨lowerSq_lt_one.le, one_lt_upperSq.le⟩]
  norm_num

end SupportCriterion
