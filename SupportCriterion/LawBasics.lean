module

public import SupportCriterion.Constants
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

open MeasureTheory

namespace SupportCriterion

lemma integrable_of_bandSupport {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b : ℝ} (hμ : BandSupport μ a b) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc (-b) b)).image hf).isBounded.exists_norm_le
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [hμ] with x hx
  exact hC _ (Set.mem_image_of_mem f (abs_le.mp hx.2))

lemma integrable_of_normalizedSupport {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : NormalizedSupport μ) {f : ℝ → ℝ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc (-Real.sqrt upperSq) (Real.sqrt upperSq))).image hf).isBounded.exists_norm_le
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [hμ] with x hx
  exact hC _ (Set.mem_image_of_mem f ((abs_le.mp (Real.abs_le_sqrt hx.2))))

lemma integrable_pow {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : NormalizedSupport μ) (n : ℕ) : Integrable (fun x : ℝ => x ^ n) μ :=
  integrable_of_normalizedSupport hμ (by fun_prop)

lemma integrable_exp {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : NormalizedSupport μ) (t : ℝ) : Integrable (fun x => Real.exp (t * x)) μ :=
  integrable_of_normalizedSupport hμ (by fun_prop)

lemma integrable_cosh {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : NormalizedSupport μ) (t : ℝ) : Integrable (fun x => Real.cosh (t * x)) μ :=
  integrable_of_normalizedSupport hμ (by fun_prop)

lemma integrable_interiority {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : NormalizedSupport μ) :
    Integrable (fun x => (x ^ 2 - lowerSq) * (upperSq - x ^ 2)) μ :=
  integrable_of_normalizedSupport hμ (by fun_prop)

lemma variance_mem {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) : lowerSq ≤ variance μ ∧ variance μ ≤ upperSq := by
  constructor
  · simpa [variance, moment] using
      integral_mono_ae (integrable_const lowerSq) (integrable_pow hμ 2) (hμ.mono fun _ hx => hx.1)
  · simpa [variance, moment] using
      integral_mono_ae (integrable_pow hμ 2) (integrable_const upperSq) (hμ.mono fun _ hx => hx.2)

lemma interiority_nonneg {μ : Measure ℝ} (hμ : NormalizedSupport μ) : 0 ≤ interiority μ := by
  apply integral_nonneg_of_ae
  filter_upwards [hμ] with x hx
  exact mul_nonneg (sub_nonneg.2 hx.1) (sub_nonneg.2 hx.2)

lemma interiority_identity {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) : interiority μ = 6 * variance μ - 3 - moment μ 4 := by
  have hid : (fun x : ℝ => (x ^ 2 - lowerSq) * (upperSq - x ^ 2)) =
      (fun x : ℝ => 6 * x ^ 2 - 3 - x ^ 4) := by
    funext x
    calc
      _ = (lowerSq + upperSq) * x ^ 2 - lowerSq * upperSq - x ^ 4 := by ring
      _ = _ := by rw [lowerSq_add_upperSq, lowerSq_mul_upperSq]
  have hi6 : Integrable (fun x : ℝ => 6 * x ^ 2 - 3) μ :=
    ((integrable_pow hμ 2).const_mul 6).sub (integrable_const 3)
  rw [interiority, hid, integral_sub hi6 (integrable_pow hμ 4),
    integral_sub ((integrable_pow hμ 2).const_mul 6) (integrable_const 3), integral_const_mul]
  simp [variance, moment]

lemma fourthDeficit_identity {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    fourthDeficit μ = 3 * (variance μ - 1) ^ 2 + interiority μ := by
  rw [interiority_identity hμ, fourthDeficit]
  ring

lemma fourthDeficit_nonneg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) : 0 ≤ fourthDeficit μ := by
  rw [fourthDeficit_identity hμ]
  nlinarith [sq_nonneg (variance μ - 1), interiority_nonneg hμ]

lemma interiority_eq_zero_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    interiority μ = 0 ↔ ∀ᵐ x ∂μ, x ^ 2 = lowerSq ∨ x ^ 2 = upperSq := by
  have hn : 0 ≤ᵐ[μ] fun x => (x ^ 2 - lowerSq) * (upperSq - x ^ 2) := by
    filter_upwards [hμ] with x hx
    exact mul_nonneg (sub_nonneg.2 hx.1) (sub_nonneg.2 hx.2)
  rw [interiority, integral_eq_zero_iff_of_nonneg_ae hn (integrable_interiority hμ)]
  constructor
  · intro h
    filter_upwards [h] with x hx
    rcases mul_eq_zero.mp hx with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h).symm
  · intro h
    filter_upwards [h] with x hx
    rcases hx with h | h <;> simp [h]

lemma fourthDeficit_eq_zero_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    fourthDeficit μ = 0 ↔ variance μ = 1 ∧ interiority μ = 0 := by
  rw [fourthDeficit_identity hμ]
  have := interiority_nonneg hμ
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (variance μ - 1)]
  · rintro ⟨h, hd⟩
    simp [h, hd]

lemma integral_neg_eq {μ : Measure ℝ} (hμ : Symmetric μ) {f : ℝ → ℝ}
    (hf : Continuous f) : (∫ x, f (-x) ∂μ) = ∫ x, f x ∂μ := by
  rw [← integral_map_of_stronglyMeasurable (by fun_prop) hf.stronglyMeasurable, hμ]

lemma mgf_eq_integral_cosh {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) (t : ℝ) :
    mgf μ t = ∫ x, Real.cosh (t * x) ∂μ := by
  have hn : (∫ x, Real.exp (-(t * x)) ∂μ) = mgf μ t := by
    simpa [mgf] using integral_neg_eq hs (f := fun x => Real.exp (t * x)) (by fun_prop)
  have hi : Integrable (fun x => Real.exp (-(t * x))) μ :=
    integrable_of_normalizedSupport hμ (by fun_prop)
  simp only [Real.cosh_eq]
  rw [integral_div, integral_add (integrable_exp hμ t) hi, hn]
  simp [mgf]

end SupportCriterion
