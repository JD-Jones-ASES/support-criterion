module

public import SupportCriterion.EndpointSeries
public import SupportCriterion.SharpGapCertificate
public import SupportCriterion.Chord

@[expose] public section

open MeasureTheory

namespace SupportCriterion

lemma endpointGap_sum_seven (v t : ℝ) :
    ∑ n ∈ Finset.range 7, endpointGapTerm v t n =
      (t^2/2)^2*sharpGapPolynomial v (t^2/2) := by
  simp [Finset.sum_range_succ,endpointGapTerm,endpointMoment_zero,endpointMoment_one,
    endpointMoment_two,endpointMoment_three,endpointMoment_four,endpointMoment_five,
    endpointMoment_six,sharpGapPolynomial,gapPolynomial,Nat.factorial]
  <;> ring

lemma endpointGap_partial_sharp (v t : ℝ) (hv0 : lowerSq ≤ v) (hv1 : v ≤ upperSq) :
    (t^2/2)^2*sharpGapPolynomial v (t^2/2) ≤
      Real.exp (v*t^2/2)-endpointMGF v t := by
  have ht (n : ℕ) (hn : n ∉ Finset.range 7) : 0 ≤ endpointGapTerm v t n := by
    have hh : 7 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    exact endpointGapTerm_nonneg v t hv0 hv1 n (by omega)
  have h := sum_le_hasSum (Finset.range 7) ht (endpointGap_hasSum v t)
  rwa [endpointGap_sum_seven] at h

lemma endpointMoment_tail_lt (v : ℝ) (hv0 : lowerSq ≤ v) (hv1 : v ≤ upperSq)
    (n : ℕ) (hn : 5 ≤ n) : endpointMoment v n < gaussianMoment n*v^n := by
  have hv : 0 ≤ v := lowerSq_nonneg.trans hv0
  have ratio : upperSq < 11*lowerSq := by
    unfold lowerSq upperSq
    have := sqrt_six_sq
    have := sqrt_six_pos
    nlinarith
  induction n, hn using Nat.le_induction with
  | base => exact endpointMoment_five_lt v hv
  | succ n hn ih =>
    have hnR : (5:ℝ) ≤ n := by exact_mod_cast hn
    have hb : upperSq ≤ (2*n+1)*v := by nlinarith
    calc
      endpointMoment v (n+1) ≤ upperSq*endpointMoment v n :=
        endpointMoment_succ_le v hv0 hv1 n
      _ < upperSq*(gaussianMoment n*v^n) := mul_lt_mul_of_pos_left ih upperSq_pos
      _ ≤ ((2*n+1)*v)*(gaussianMoment n*v^n) :=
        mul_le_mul_of_nonneg_right hb (mul_nonneg (gaussianMoment_pos n).le (pow_nonneg hv n))
      _ = gaussianMoment (n+1)*v^(n+1) := by rw [gaussianMoment_succ,pow_succ]; ring

lemma endpointGapTerm_pos (v t : ℝ) (hv0 : lowerSq ≤ v) (hv1 : v ≤ upperSq)
    (ht : t ≠ 0) (n : ℕ) (hn : 5 ≤ n) : 0 < endpointGapTerm v t n := by
  have h := endpointMoment_tail_lt v hv0 hv1 n hn
  have hf : (0:ℝ) < n.factorial := by positivity
  have hff : (0:ℝ) < (2*n).factorial := by positivity
  have ht' : 0 < t^(2*n) := by rw [pow_mul]; exact pow_pos (sq_pos_of_ne_zero ht) n
  have hi : endpointGapTerm v t n =
      (gaussianMoment n*v^n-endpointMoment v n)*t^(2*n)/(2*n).factorial := by
    unfold endpointGapTerm gaussianMoment
    rw [mul_pow,div_pow,← pow_mul]
    field_simp
    <;> ring
  rw [hi]
  exact div_pos (mul_pos (sub_pos.mpr h) ht') hff

lemma endpointGap_partial_sharp_strict (v t : ℝ) (hv0 : lowerSq ≤ v)
    (hv1 : v ≤ upperSq) (ht : t ≠ 0) :
    (t^2/2)^2*sharpGapPolynomial v (t^2/2) <
      Real.exp (v*t^2/2)-endpointMGF v t := by
  have htail (n : ℕ) (hn : n ∉ Finset.range 8) : 0 ≤ endpointGapTerm v t n := by
    have hh : 8 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    exact endpointGapTerm_nonneg v t hv0 hv1 n (by omega)
  have h := sum_le_hasSum (Finset.range 8) htail (endpointGap_hasSum v t)
  rw [show 8=7+1 from rfl, Finset.sum_range_succ, endpointGap_sum_seven] at h
  have hp := endpointGapTerm_pos v t hv0 hv1 ht 7 (by norm_num)
  linarith

lemma sharpGapPolynomial_high (v z : ℝ) (hv : 1 ≤ v) (hz : 0 ≤ z) :
    z^2/105 ≤ sharpGapPolynomial v z := by
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
  have hv0 : 0 ≤ v := by linarith
  have hf5 := (fifth_deficit_pos v hv0).le
  have hvm : 0 ≤ v-1 := sub_nonneg.mpr hv
  have hf6 : 0 ≤ v^6-198*v/385+109/385 := by
    have hid : v^6-198*v/385+109/385 =
        (v-1)*(v^5+v^4+v^3+v^2+v+187/385)+296/385 := by ring
    rw [hid]
    positivity
  unfold sharpGapPolynomial gapPolynomial
  nlinarith [mul_nonneg hf3 hz, mul_nonneg (sub_nonneg.mpr hf4) (sq_nonneg z),
    mul_nonneg hf5 (pow_nonneg hz 3), mul_nonneg hf6 (pow_nonneg hz 4),sq_nonneg (v-1)]

lemma sharpGapPolynomial_bound (v z : ℝ) (hv0 : lowerSq ≤ v) (hz : 0 ≤ z) :
    z^2/1575 ≤ sharpGapPolynomial v z := by
  rcases le_total v 1 with hv|hv
  · exact sharpGapPolynomial_lower v z (lowerSq_ge_eleven_twentieth.trans hv0) hv hz
  · have hh := sharpGapPolynomial_high v z hv hz
    nlinarith [sq_nonneg z]

lemma endpoint_sharp_gap (v t : ℝ) (hv0 : lowerSq ≤ v) (hv1 : v ≤ upperSq) :
    t^8/25200 ≤ Real.exp (v*t^2/2)-endpointMGF v t := by
  have hp := sharpGapPolynomial_bound v (t^2/2) hv0 (by positivity)
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg (t^2/2))
  calc
    _ = (t^2/2)^2*((t^2/2)^2/1575) := by ring
    _ ≤ _ := hm.trans (endpointGap_partial_sharp v t hv0 hv1)

lemma endpoint_sharp_gap_strict (v t : ℝ) (hv0 : lowerSq ≤ v)
    (hv1 : v ≤ upperSq) (ht : t ≠ 0) :
    t^8/25200 < Real.exp (v*t^2/2)-endpointMGF v t := by
  have hp := sharpGapPolynomial_bound v (t^2/2) hv0 (by positivity)
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg (t^2/2))
  calc
    _ = (t^2/2)^2*((t^2/2)^2/1575) := by ring
    _ < _ := hm.trans_lt (endpointGap_partial_sharp_strict v t hv0 hv1 ht)

/-- The sharp uniform eighth-order bound, including the full chord interiority remainder. -/
theorem normalized_sharp_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) (t : ℝ) :
    interiority μ*t^4/24+t^8/25200 ≤
      Real.exp (variance μ*t^2/2)-mgf μ t := by
  have hv := variance_mem hμ
  have h1 := endpoint_sharp_gap (variance μ) t hv.1 hv.2
  have h2 := endpoint_mgf_gap hμ hs t
  linarith

/-- Every nonzero parameter gives a strict sharp quantitative bound. -/
theorem normalized_sharp_gap_strict (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) (t : ℝ) (ht : t ≠ 0) :
    interiority μ*t^4/24+t^8/25200 <
      Real.exp (variance μ*t^2/2)-mgf μ t := by
  have hv := variance_mem hμ
  have h1 := endpoint_sharp_gap_strict (variance μ) t hv.1 hv.2 ht
  have h2 := endpoint_mgf_gap hμ hs t
  linarith

end SupportCriterion
