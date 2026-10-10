module

public import SupportCriterion.TransportCoupling

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SupportCriterion

noncomputable def endpointFraction (y : ℝ) : ℝ :=
  (y - lowerSq) / (upperSq - lowerSq)

noncomputable def endpointChoice (p y : ℝ) : ℝ :=
  if referenceWeight ≤ p then referenceWeight * endpointFraction y / p
  else endpointFraction y + (1 - endpointFraction y) * (referenceWeight - p) / (1 - p)

lemma endpointFraction_mem {y : ℝ} (hy : lowerSq ≤ y ∧ y ≤ upperSq) :
    0 ≤ endpointFraction y ∧ endpointFraction y ≤ 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hy.1) upperSq_sub_lowerSq_pos.le
  · exact (div_le_one upperSq_sub_lowerSq_pos).mpr (by linarith [hy.2])

lemma endpointChoice_mem {p y : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hy : lowerSq ≤ y ∧ y ≤ upperSq) :
    0 ≤ endpointChoice p y ∧ endpointChoice p y ≤ 1 := by
  obtain ⟨hr0, hr1⟩ := endpointFraction_mem hy
  unfold endpointChoice
  split_ifs with h
  · have hp0 : 0 < p := lt_of_lt_of_le referenceWeight_pos h
    constructor
    · exact div_nonneg (mul_nonneg referenceWeight_pos.le hr0) hp0.le
    · apply (div_le_one hp0).mpr
      nlinarith [referenceWeight_pos.le]
  · have hp1 : 0 < 1 - p := by linarith [referenceWeight_lt_one]
    have hdiff : 0 ≤ referenceWeight - p := by linarith
    constructor
    · positivity
    · have h : (1 - endpointFraction y) * (referenceWeight - p) / (1 - p) ≤
        1 - endpointFraction y := by
        apply (div_le_iff₀ hp1).mpr
        nlinarith [referenceWeight_lt_one]
      linarith

lemma endpointChoice_le_fraction {p y : ℝ} (hp : referenceWeight ≤ p)
    (hy : lowerSq ≤ y ∧ y ≤ upperSq) : endpointChoice p y ≤ endpointFraction y := by
  have hp0 : 0 < p := lt_of_lt_of_le referenceWeight_pos hp
  have hr0 := (endpointFraction_mem hy).1
  rw [endpointChoice, if_pos hp]
  apply (div_le_iff₀ hp0).mpr
  nlinarith

lemma fraction_le_endpointChoice {p y : ℝ} (hp : p < referenceWeight)
    (hy : lowerSq ≤ y ∧ y ≤ upperSq) : endpointFraction y ≤ endpointChoice p y := by
  rw [endpointChoice, if_neg (not_le.mpr hp)]
  have hr1 := (endpointFraction_mem hy).2
  have hp1 : 0 < 1 - p := by linarith [referenceWeight_lt_one]
  have : 0 ≤ (1 - endpointFraction y) * (referenceWeight - p) / (1 - p) := by positivity
  linarith

lemma endpointChoice_continuous (p : ℝ) : Continuous (endpointChoice p) := by
  unfold endpointChoice
  split_ifs <;> unfold endpointFraction <;> fun_prop

lemma endpoint_transport_cost_pointwise {y q : ℝ} (hy : lowerSq ≤ y ∧ y ≤ upperSq) :
    (1 - q) * |y - lowerSq| + q * |y - upperSq| ≤
      2 * ((y - lowerSq) * (upperSq - y)) / (upperSq - lowerSq) +
      (upperSq - lowerSq) * |q - endpointFraction y| := by
  have hbase : (1 - endpointFraction y) * (y - lowerSq) +
      endpointFraction y * (upperSq - y) =
      2 * ((y - lowerSq) * (upperSq - y)) / (upperSq - lowerSq) := by
    unfold endpointFraction
    field_simp [ne_of_gt upperSq_sub_lowerSq_pos]
    <;> ring
  rw [abs_of_nonneg (sub_nonneg.mpr hy.1), abs_of_nonpos (sub_nonpos.mpr hy.2), ← hbase]
  rcases le_total q (endpointFraction y) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hy.1)]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hy.2)]

end SupportCriterion
