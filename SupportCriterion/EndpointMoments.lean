module

public import SupportCriterion.Constants

@[expose] public section

/-! Endpoint moments and the complete Gaussian-dominated tail from order ten. -/
namespace SupportCriterion

noncomputable def endpointMoment (v : ℝ) (n : ℕ) : ℝ :=
  (1-(v-lowerSq)/(upperSq-lowerSq))*lowerSq^n +
  ((v-lowerSq)/(upperSq-lowerSq))*upperSq^n

noncomputable def gaussianMoment (n : ℕ) : ℝ :=
  ((2*n).factorial : ℝ) / (2^n * n.factorial)

lemma endpointMoment_zero (v : ℝ) : endpointMoment v 0 = 1 := by
  unfold endpointMoment; ring
lemma endpointMoment_one (v : ℝ) : endpointMoment v 1 = v := by
  unfold endpointMoment
  have hn := ne_of_gt upperSq_sub_lowerSq_pos
  field_simp
  <;> ring
lemma endpointMoment_rec (v : ℝ) (n : ℕ) :
    endpointMoment v (n+2) = 6*endpointMoment v (n+1)-3*endpointMoment v n := by
  have ha : lowerSq^2-6*lowerSq+3=0 := by
    nlinarith [lowerSq_add_upperSq,lowerSq_mul_upperSq]
  have hb : upperSq^2-6*upperSq+3=0 := by
    nlinarith [lowerSq_add_upperSq,lowerSq_mul_upperSq]
  have hA : lowerSq^(n+2)=6*lowerSq^(n+1)-3*lowerSq^n := by
    rw [pow_add, pow_succ]
    linear_combination lowerSq^n * ha
  have hB : upperSq^(n+2)=6*upperSq^(n+1)-3*upperSq^n := by
    rw [pow_add, pow_succ]
    linear_combination upperSq^n * hb
  unfold endpointMoment
  rw [hA,hB]
  ring

lemma endpointMoment_two (v : ℝ) : endpointMoment v 2 = 6*v-3 := by
  simpa [endpointMoment_one,endpointMoment_zero] using endpointMoment_rec v 0
lemma endpointMoment_three (v : ℝ) : endpointMoment v 3 = 33*v-18 := by
  rw [show 3=1+2 from rfl,endpointMoment_rec,endpointMoment_two,endpointMoment_one]; ring
lemma endpointMoment_four (v : ℝ) : endpointMoment v 4 = 180*v-99 := by
  rw [show 4=2+2 from rfl,endpointMoment_rec,endpointMoment_three,endpointMoment_two]; ring
lemma endpointMoment_five (v : ℝ) : endpointMoment v 5 = 981*v-540 := by
  rw [show 5=3+2 from rfl,endpointMoment_rec,endpointMoment_four,endpointMoment_three]; ring

lemma gaussianMoment_pos (n : ℕ) : 0 < gaussianMoment n := by
  unfold gaussianMoment; positivity
lemma gaussianMoment_succ (n : ℕ) : gaussianMoment (n+1) = (2*n+1)*gaussianMoment n := by
  unfold gaussianMoment
  rw [show 2*(n+1)= (2*n+1)+1 by omega, Nat.factorial_succ,
    Nat.factorial_succ, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  <;> ring

lemma endpointMoment_nonneg (v : ℝ) (hv0 : lowerSq ≤ v) (hv1 : v ≤ upperSq) (n : ℕ) :
    0 ≤ endpointMoment v n := by
  have hp : 0 ≤ (v-lowerSq)/(upperSq-lowerSq) :=
    div_nonneg (sub_nonneg.mpr hv0) upperSq_sub_lowerSq_pos.le
  have hq : (v-lowerSq)/(upperSq-lowerSq) ≤ 1 :=
    (div_le_one upperSq_sub_lowerSq_pos).2 (by linarith)
  unfold endpointMoment
  exact add_nonneg (mul_nonneg (by linarith) (pow_nonneg lowerSq_nonneg _))
    (mul_nonneg hp (pow_nonneg upperSq_nonneg _))

lemma endpointMoment_succ_le (v : ℝ) (hv0 : lowerSq ≤ v) (hv1 : v ≤ upperSq) (n : ℕ) :
    endpointMoment v (n+1) ≤ upperSq*endpointMoment v n := by
  have hp : 0 ≤ (v-lowerSq)/(upperSq-lowerSq) :=
    div_nonneg (sub_nonneg.mpr hv0) upperSq_sub_lowerSq_pos.le
  have hq : 0 ≤ 1-(v-lowerSq)/(upperSq-lowerSq) := by
    have := (div_le_one upperSq_sub_lowerSq_pos).2 (show v-lowerSq ≤ upperSq-lowerSq by linarith)
    linarith
  unfold endpointMoment
  simp only [pow_succ]
  nlinarith [mul_nonneg (mul_nonneg hq (pow_nonneg lowerSq_nonneg n))
    (sub_nonneg.mpr lowerSq_lt_upperSq.le)]

lemma fifth_deficit_pos (v : ℝ) (hv : 0 ≤ v) : 0 < v^5-109*v/105+4/7 := by
  have ht (c : ℝ) (hc : 0 ≤ c) : 5*c^4*v-4*c^5 ≤ v^5 := by
    have hid : v^5 - (5*c^4*v-4*c^5) =
      (v-c)^2*(v^3+2*c*v^2+3*c^2*v+4*c^3) := by ring
    have h : 0 ≤ (v-c)^2*(v^3+2*c*v^2+3*c^2*v+4*c^3) := by positivity
    linarith
  by_cases h : v ≤ 4/5
  · have := ht (2/3) (by norm_num)
    nlinarith
  · have := ht (3/4) (by norm_num)
    nlinarith

lemma endpointMoment_five_lt (v : ℝ) (hv : 0 ≤ v) :
    endpointMoment v 5 < gaussianMoment 5*v^5 := by
  rw [endpointMoment_five]
  norm_num [gaussianMoment, Nat.factorial]
  nlinarith [fifth_deficit_pos v hv]

lemma endpointMoment_tail (v : ℝ) (hv0 : lowerSq ≤ v) (hv1 : v ≤ upperSq)
    (n : ℕ) (hn : 5 ≤ n) : endpointMoment v n ≤ gaussianMoment n*v^n := by
  have hv : 0 ≤ v := lowerSq_nonneg.trans hv0
  have ratio : upperSq < 11*lowerSq := by
    unfold lowerSq upperSq
    have := sqrt_six_sq
    have := sqrt_six_pos
    nlinarith
  induction n, hn using Nat.le_induction with
  | base => exact (endpointMoment_five_lt v hv).le
  | succ n hn ih =>
    have hnR : (5:ℝ) ≤ n := by exact_mod_cast hn
    have hb : upperSq ≤ (2*n+1)*v := by nlinarith
    calc
      endpointMoment v (n+1) ≤ upperSq*endpointMoment v n :=
        endpointMoment_succ_le v hv0 hv1 n
      _ ≤ upperSq*(gaussianMoment n*v^n) := mul_le_mul_of_nonneg_left ih upperSq_nonneg
      _ ≤ ((2*n+1)*v)*(gaussianMoment n*v^n) :=
        mul_le_mul_of_nonneg_right hb (mul_nonneg (gaussianMoment_pos n).le (pow_nonneg hv n))
      _ = gaussianMoment (n+1)*v^(n+1) := by rw [gaussianMoment_succ,pow_succ]; ring

end SupportCriterion
