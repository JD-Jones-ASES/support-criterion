module

public import SupportCriterion.EndpointMoments
public import SupportCriterion.Certificate

@[expose] public section

/-! Entire series comparison for every real MGF parameter. -/
namespace SupportCriterion

noncomputable def endpointGapTerm (v t : ℝ) (n : ℕ) : ℝ :=
  (v*(t^2/2))^n / n.factorial - endpointMoment v n * t^(2*n) / (2*n).factorial

lemma endpointMGF_hasSum (v t : ℝ) :
    HasSum (fun n => endpointMoment v n*t^(2*n)/(2*n).factorial) (endpointMGF v t) := by
  unfold endpointMGF
  have h := ((Real.hasSum_cosh (t*Real.sqrt lowerSq)).mul_left
      (1-(v-lowerSq)/(upperSq-lowerSq))).add
    ((Real.hasSum_cosh (t*Real.sqrt upperSq)).mul_left ((v-lowerSq)/(upperSq-lowerSq)))
  convert h using 1
  ext n
  have ha : (t*Real.sqrt lowerSq)^(2*n) = t^(2*n)*lowerSq^n := by
    simp only [mul_pow, pow_mul, Real.sq_sqrt lowerSq_nonneg]
  have hb : (t*Real.sqrt upperSq)^(2*n) = t^(2*n)*upperSq^n := by
    simp only [mul_pow, pow_mul, Real.sq_sqrt upperSq_nonneg]
  rw [ha,hb]
  unfold endpointMoment
  ring

lemma endpointGap_hasSum (v t : ℝ) :
    HasSum (endpointGapTerm v t) (Real.exp (v*t^2/2)-endpointMGF v t) := by
  have h : HasSum (fun n : ℕ => (v*(t^2/2))^n/n.factorial) (Real.exp (v*(t^2/2))) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (v*(t^2/2))
  unfold endpointGapTerm
  simpa only [mul_div_assoc] using h.sub (endpointMGF_hasSum v t)

lemma endpointGapTerm_nonneg (v t : ℝ) (hv0 : lowerSq ≤ v) (hv1 : v ≤ upperSq)
    (n : ℕ) (hn : 5 ≤ n) : 0 ≤ endpointGapTerm v t n := by
  have h := endpointMoment_tail v hv0 hv1 n hn
  have hf : (0:ℝ) < n.factorial := by positivity
  have hff : (0:ℝ) < (2*n).factorial := by positivity
  have ht : 0 ≤ t^(2*n) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg t) n
  have hi : endpointGapTerm v t n =
      (gaussianMoment n*v^n-endpointMoment v n)*t^(2*n)/(2*n).factorial := by
    unfold endpointGapTerm gaussianMoment
    rw [mul_pow,div_pow,← pow_mul]
    field_simp
    <;> ring
  rw [hi]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr h) ht) hff.le

lemma endpointGap_partial (v t : ℝ) (hv0 : lowerSq ≤ v) (hv1 : v ≤ upperSq) :
    (t^2/2)^2*gapPolynomial v (t^2/2) ≤ Real.exp (v*t^2/2)-endpointMGF v t := by
  have ht (n : ℕ) (hn : n ∉ Finset.range 6) : 0 ≤ endpointGapTerm v t n := by
    have hh : 6 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    exact endpointGapTerm_nonneg v t hv0 hv1 n (by omega)
  have h := sum_le_hasSum (Finset.range 6) ht (endpointGap_hasSum v t)
  have hi : ∑ n ∈ Finset.range 6, endpointGapTerm v t n = (t^2/2)^2*gapPolynomial v (t^2/2) := by
    simp [Finset.sum_range_succ,endpointGapTerm,endpointMoment_zero,endpointMoment_one,
      endpointMoment_two,endpointMoment_three,endpointMoment_four,endpointMoment_five,
      gapPolynomial,Nat.factorial]
    <;> ring
  rwa [hi] at h

lemma gapPolynomial_high (v z : ℝ) (hv : 1 ≤ v) (hz : 0 ≤ z) :
    ((v-1)^2+z^2)/4000 ≤ gapPolynomial v z := by
  have hf3 : 0 ≤ v^3-11*v/5+6/5 := by
    have hid : v^3-11*v/5+6/5 = (v-1)*(v^2+v-6/5) := by ring
    rw [hid]
    apply mul_nonneg (by linarith)
    nlinarith [sq_nonneg (v-1)]
  have hf4 : 8/35 ≤ v^4-12*v/7+33/35 := by
    have hid : v^4-12*v/7+33/35-8/35 = (v-1)*(v^3+v^2+v-5/7) := by ring
    have hpos : 0 ≤ (v-1)*(v^3+v^2+v-5/7) := by
      apply mul_nonneg (by linarith)
      have hv0 : 0 ≤ v := by linarith
      nlinarith [pow_nonneg hv0 3,sq_nonneg v]
    linarith
  have hf5 := (fifth_deficit_pos v (by linarith : 0 ≤ v)).le
  unfold gapPolynomial
  nlinarith [mul_nonneg hf3 hz, mul_nonneg (sub_nonneg.mpr hf4) (sq_nonneg z),
    mul_nonneg hf5 (pow_nonneg hz 3),sq_nonneg (v-1),sq_nonneg z]

lemma endpoint_gaussian_gap (v t : ℝ) (hv0 : lowerSq ≤ v) (hv1 : v ≤ upperSq) :
    (v-1)^2*t^4/16000+t^8/64000 ≤ Real.exp (v*t^2/2)-endpointMGF v t := by
  have hz : 0 ≤ t^2/2 := by positivity
  have hp : ((v-1)^2+(t^2/2)^2)/4000 ≤ gapPolynomial v (t^2/2) := by
    rcases le_total v 1 with hv|hv
    · exact gapPolynomial_lower v (t^2/2) (lowerSq_ge_eleven_twentieth.trans hv0) hv hz
    · exact gapPolynomial_high v (t^2/2) hv hz
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg (t^2/2))
  have hs := endpointGap_partial v t hv0 hv1
  calc
    _ = (t^2/2)^2*(((v-1)^2+(t^2/2)^2)/4000) := by ring
    _ ≤ _ := hm.trans hs

end SupportCriterion
