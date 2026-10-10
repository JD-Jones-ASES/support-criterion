module

public import SupportCriterion.LawGap

@[expose] public section

open MeasureTheory

namespace SupportCriterion

noncomputable def scaleLaw (μ : Measure ℝ) (c : ℝ) : Measure ℝ :=
  Measure.map (fun x => c * x) μ

instance scaleLaw_isProbabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    IsProbabilityMeasure (scaleLaw μ c) := by unfold scaleLaw; infer_instance

lemma scaleLaw_symmetric {μ : Measure ℝ} (hs : Symmetric μ) (c : ℝ) :
    Symmetric (scaleLaw μ c) := by
  unfold Symmetric scaleLaw at *
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ => -(c*x)) = (fun x => c*x) ∘ (fun x => -x) := by
    funext x; simp
  change Measure.map (fun x => -(c*x)) μ = _
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), hs]

lemma moment_scaleLaw (μ : Measure ℝ) (c : ℝ) (n : ℕ) :
    moment (scaleLaw μ c) n = c ^ n * moment μ n := by
  unfold moment scaleLaw
  rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
  simp only [mul_pow]
  rw [integral_const_mul]

lemma variance_scaleLaw (μ : Measure ℝ) (c : ℝ) :
    variance (scaleLaw μ c) = c ^ 2 * variance μ := moment_scaleLaw μ c 2

lemma fourthDeficit_scaleLaw (μ : Measure ℝ) (c : ℝ) :
    fourthDeficit (scaleLaw μ c) = c ^ 4 * fourthDeficit μ := by
  rw [fourthDeficit, variance_scaleLaw, moment_scaleLaw, fourthDeficit]
  ring

lemma mgf_scaleLaw (μ : Measure ℝ) (c t : ℝ) :
    mgf (scaleLaw μ c) t = mgf μ (c*t) := by
  unfold mgf scaleLaw
  rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  congr 1
  ring

lemma sharpRatio_pos : 0 < sharpRatio := by unfold sharpRatio; positivity

lemma lowerSq_mul_sharpRatio_sq : lowerSq * sharpRatio ^ 2 = upperSq := by
  have h32 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hr : sharpRatio ^ 2 = 5 + 2 * Real.sqrt 6 := by
    unfold sharpRatio
    nlinarith
  rw [hr]
  unfold lowerSq upperSq
  nlinarith [sqrt_six_sq]

lemma scaleLaw_normalizedSupport {μ : Measure ℝ} {a b : ℝ}
    (ha : 0 < a) (hμ : BandSupport μ a b) (hr : b / a ≤ sharpRatio) :
    NormalizedSupport (scaleLaw μ (Real.sqrt lowerSq / a)) := by
  unfold NormalizedSupport scaleLaw
  rw [ae_map_iff (by fun_prop) (by measurability)]
  filter_upwards [hμ] with x hx
  have hs : 0 < Real.sqrt lowerSq := Real.sqrt_pos.2 lowerSq_pos
  have hc : 0 < Real.sqrt lowerSq / a := div_pos hs ha
  have hu : b ≤ a * sharpRatio := by
    have := (div_le_iff₀ ha).1 hr
    nlinarith
  have hxl : a ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x]
  have hxu : x ^ 2 ≤ a ^ 2 * sharpRatio ^ 2 := by
    have hxb : |x| ≤ a * sharpRatio := hx.2.trans hu
    have := mul_self_le_mul_self (abs_nonneg x) hxb
    nlinarith [sq_abs x]
  have hs2 := Real.sq_sqrt lowerSq_nonneg
  have hc2 : (Real.sqrt lowerSq / a) ^ 2 * a ^ 2 = lowerSq := by
    field_simp
    exact hs2
  have hcup : (Real.sqrt lowerSq / a) ^ 2 * (a ^ 2 * sharpRatio ^ 2) = upperSq := by
    calc
      _ = ((Real.sqrt lowerSq / a) ^ 2 * a ^ 2) * sharpRatio ^ 2 := by ring
      _ = lowerSq * sharpRatio ^ 2 := by rw [hc2]
      _ = upperSq := lowerSq_mul_sharpRatio_sq
  constructor
  · have := mul_le_mul_of_nonneg_left hxl (sq_nonneg (Real.sqrt lowerSq/a))
    simpa only [mul_pow, hc2] using this
  · have := mul_le_mul_of_nonneg_left hxu (sq_nonneg (Real.sqrt lowerSq/a))
    simpa only [mul_pow, hcup] using this

lemma band_fourthDeficit_nonneg {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}
    (ha : 0 < a) (hμ : BandSupport μ a b) (hr : b / a ≤ sharpRatio) :
    0 ≤ fourthDeficit μ := by
  have hn := fourthDeficit_nonneg (scaleLaw_normalizedSupport ha hμ hr)
  rw [fourthDeficit_scaleLaw] at hn
  exact nonneg_of_mul_nonneg_right hn (pow_pos (div_pos (Real.sqrt_pos.2 lowerSq_pos) ha) 4)

lemma band_gap_of_normalized_gap {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℝ}
    (ha : 0 < a)
    (hgap : ∀ s : ℝ,
      fourthDeficit (scaleLaw μ (Real.sqrt lowerSq / a)) * s ^ 4 / 48000 + s ^ 8 / 64000 ≤
        Real.exp (variance (scaleLaw μ (Real.sqrt lowerSq / a)) * s ^ 2 / 2) -
          mgf (scaleLaw μ (Real.sqrt lowerSq / a)) s)
    (t : ℝ) :
    fourthDeficit μ * t ^ 4 / 48000 + a ^ 8 / (64000 * lowerSq ^ 4) * t ^ 8 ≤
      Real.exp (variance μ * t ^ 2 / 2) - mgf μ t := by
  let c := Real.sqrt lowerSq / a
  have hc : c ≠ 0 := ne_of_gt (div_pos (Real.sqrt_pos.2 lowerSq_pos) ha)
  have h := hgap (t / c)
  change fourthDeficit (scaleLaw μ c) * (t/c)^4 / 48000 + (t/c)^8 / 64000 ≤
    Real.exp (variance (scaleLaw μ c) * (t/c)^2 / 2) - mgf (scaleLaw μ c) (t/c) at h
  rw [fourthDeficit_scaleLaw, variance_scaleLaw, mgf_scaleLaw] at h
  have he : c ^ 2 * variance μ * (t/c)^2 / 2 = variance μ * t^2 / 2 := by
    field_simp
  have hfour : c ^ 4 * fourthDeficit μ * (t/c)^4 / 48000 =
      fourthDeficit μ * t^4 / 48000 := by
    field_simp
  have height : (t/c)^8 / 64000 = a^8 / (64000 * lowerSq^4) * t^8 := by
    dsimp [c]
    rw [div_pow, div_pow, show (8:ℕ) = 2*4 by norm_num,
      pow_mul (Real.sqrt lowerSq), Real.sq_sqrt lowerSq_nonneg]
    field_simp
  rw [he, hfour, height, mul_div_cancel₀ _ hc] at h
  exact h

lemma band_gap_of_endpoint_bound
    (hendpoint : ∀ (v t : ℝ), lowerSq ≤ v → v ≤ upperSq →
      (v - 1) ^ 2 * t ^ 4 / 16000 + t ^ 8 / 64000 ≤
        Real.exp (v * t ^ 2 / 2) - endpointMGF v t)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}
    (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b / a ≤ sharpRatio) (t : ℝ) :
    fourthDeficit μ * t ^ 4 / 48000 + a ^ 8 / (64000 * lowerSq ^ 4) * t ^ 8 ≤
      Real.exp (variance μ * t ^ 2 / 2) - mgf μ t := by
  apply band_gap_of_normalized_gap ha
  intro s
  exact normalized_gap_of_endpoint_bound hendpoint (scaleLaw_normalizedSupport ha hμ hr)
    (scaleLaw_symmetric hs _) s

lemma band_strict_of_gap {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}
    (ha : 0 < a) (hμ : BandSupport μ a b) (hr : b / a ≤ sharpRatio)
    (t : ℝ) (ht : t ≠ 0)
    (hgap : fourthDeficit μ * t ^ 4 / 48000 + a ^ 8 / (64000 * lowerSq ^ 4) * t ^ 8 ≤
      Real.exp (variance μ * t ^ 2 / 2) - mgf μ t) :
    mgf μ t < Real.exp (variance μ * t ^ 2 / 2) := by
  have hd := band_fourthDeficit_nonneg ha hμ hr
  have hfour : 0 ≤ fourthDeficit μ * t ^ 4 / 48000 := by positivity
  have hp : 0 < t ^ 8 := by
    simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero ht) 4
  have hterm : 0 < a ^ 8 / (64000 * lowerSq ^ 4) * t ^ 8 :=
    mul_pos (div_pos (pow_pos ha 8) (mul_pos (by norm_num) (pow_pos lowerSq_pos 4))) hp
  linarith

lemma mgf_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] : mgf μ 0 = 1 := by
  simp [mgf]

end SupportCriterion
