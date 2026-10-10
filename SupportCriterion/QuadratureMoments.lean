module

public import SupportCriterion.EndpointLaw
public import SupportCriterion.EndpointMoments

@[expose] public section

/-! Explicit moments of the critical four-point probability measure. These
identify its degree-seven Gaussian moment contact without invoking a general
quadrature theorem. -/

open MeasureTheory

namespace SupportCriterion

lemma endpointLaw_even_moment (v : ℝ) (hv : lowerSq ≤ v ∧ v ≤ upperSq) (n : ℕ) :
    moment (endpointLaw v) (2 * n) = endpointMoment v n := by
  unfold moment
  rw [integral_endpointLaw _ _ hv]
  simp only [pow_mul, neg_sq, Real.sq_sqrt lowerSq_nonneg, Real.sq_sqrt upperSq_nonneg]
  unfold endpointMoment
  ring

lemma endpointLaw_odd_moment (v : ℝ) (hv : lowerSq ≤ v ∧ v ≤ upperSq) (n : ℕ) :
    moment (endpointLaw v) (2 * n + 1) = 0 := by
  unfold moment
  rw [integral_endpointLaw _ _ hv]
  simp only [pow_add, pow_one, pow_mul, neg_sq]
  ring

lemma criticalLaw_moment_zero : moment criticalLaw 0 = 1 := by
  change moment (endpointLaw 1) (2 * 0) = 1
  rw [endpointLaw_even_moment 1 ⟨lowerSq_lt_one.le, one_lt_upperSq.le⟩,
    endpointMoment_zero]

lemma criticalLaw_moment_odd (n : ℕ) : moment criticalLaw (2 * n + 1) = 0 :=
  endpointLaw_odd_moment 1 ⟨lowerSq_lt_one.le, one_lt_upperSq.le⟩ n

lemma criticalLaw_moment_two : moment criticalLaw 2 = 1 := criticalLaw_variance

lemma criticalLaw_moment_four : moment criticalLaw 4 = 3 := by
  rw [criticalLaw, endpointLaw_fourth_moment 1 ⟨lowerSq_lt_one.le, one_lt_upperSq.le⟩]
  norm_num

lemma criticalLaw_moment_six : moment criticalLaw 6 = 15 := by
  change moment (endpointLaw 1) (2 * 3) = 15
  rw [endpointLaw_even_moment 1 ⟨lowerSq_lt_one.le, one_lt_upperSq.le⟩,
    endpointMoment_three]
  norm_num

lemma criticalLaw_moment_eight : moment criticalLaw 8 = 81 := by
  change moment (endpointLaw 1) (2 * 4) = 81
  rw [endpointLaw_even_moment 1 ⟨lowerSq_lt_one.le, one_lt_upperSq.le⟩,
    endpointMoment_four]
  norm_num

/-- Complete moment table through degree eight. -/
theorem criticalLaw_moments :
    moment criticalLaw 0 = 1 ∧ moment criticalLaw 1 = 0 ∧
    moment criticalLaw 2 = 1 ∧ moment criticalLaw 3 = 0 ∧
    moment criticalLaw 4 = 3 ∧ moment criticalLaw 5 = 0 ∧
    moment criticalLaw 6 = 15 ∧ moment criticalLaw 7 = 0 ∧
    moment criticalLaw 8 = 81 :=
  ⟨criticalLaw_moment_zero, criticalLaw_moment_odd 0, criticalLaw_moment_two,
    criticalLaw_moment_odd 1, criticalLaw_moment_four, criticalLaw_moment_odd 2,
    criticalLaw_moment_six, criticalLaw_moment_odd 3, criticalLaw_moment_eight⟩

end SupportCriterion
