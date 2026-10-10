module

public import SupportCriterion.Definitions

@[expose] public section

namespace SupportCriterion

lemma sqrt_six_sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
lemma sqrt_six_pos : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
lemma two_lt_sqrt_six : 2 < Real.sqrt 6 := by
  have := sqrt_six_sq
  have := sqrt_six_pos
  nlinarith
lemma sqrt_six_lt_three : Real.sqrt 6 < 3 := by
  have := sqrt_six_sq
  have := sqrt_six_pos
  nlinarith
lemma lowerSq_pos : 0 < lowerSq := by
  dsimp [lowerSq]
  linarith [sqrt_six_lt_three]
lemma lowerSq_nonneg : 0 ≤ lowerSq := le_of_lt lowerSq_pos
lemma lowerSq_lt_one : lowerSq < 1 := by
  dsimp [lowerSq]
  linarith [two_lt_sqrt_six]
lemma one_lt_upperSq : 1 < upperSq := by
  dsimp [upperSq]
  linarith [sqrt_six_pos]
lemma upperSq_pos : 0 < upperSq := lt_trans (by norm_num) one_lt_upperSq
lemma upperSq_nonneg : 0 ≤ upperSq := le_of_lt upperSq_pos
lemma lowerSq_lt_upperSq : lowerSq < upperSq := lt_trans lowerSq_lt_one one_lt_upperSq
lemma lowerSq_add_upperSq : lowerSq + upperSq = 6 := by unfold lowerSq upperSq; ring
lemma lowerSq_mul_upperSq : lowerSq * upperSq = 3 := by
  unfold lowerSq upperSq
  nlinarith [sqrt_six_sq]
lemma upperSq_sub_lowerSq : upperSq - lowerSq = 2 * Real.sqrt 6 := by
  unfold lowerSq upperSq; ring
lemma upperSq_sub_lowerSq_pos : 0 < upperSq - lowerSq := sub_pos.2 lowerSq_lt_upperSq
lemma referenceWeight_pos : 0 < referenceWeight :=
  div_pos (sub_pos.2 lowerSq_lt_one) upperSq_sub_lowerSq_pos
lemma referenceWeight_lt_one : referenceWeight < 1 := by
  unfold referenceWeight
  apply (div_lt_one upperSq_sub_lowerSq_pos).2
  linarith [one_lt_upperSq]

lemma lowerSq_ge_eleven_twentieth : (11 : ℝ) / 20 ≤ lowerSq := by
  unfold lowerSq
  nlinarith [sqrt_six_sq, sqrt_six_pos]
lemma upperSq_lt_eleven_mul_lowerSq : upperSq < 11 * lowerSq := by
  unfold lowerSq upperSq
  nlinarith [sqrt_six_sq, sqrt_six_pos]

end SupportCriterion
