module

public import SupportCriterion.LawBasics
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section

open MeasureTheory

namespace SupportCriterion

private lemma pow_chord {y : ℝ} (hy : lowerSq ≤ y ∧ y ≤ upperSq) (n : ℕ) :
    y ^ n ≤ (1 - (y - lowerSq) / (upperSq - lowerSq)) * lowerSq ^ n +
      ((y - lowerSq) / (upperSq - lowerSq)) * upperSq ^ n := by
  let p := (y - lowerSq) / (upperSq - lowerSq)
  have hp : 0 ≤ p := div_nonneg (sub_nonneg.2 hy.1) upperSq_sub_lowerSq_pos.le
  have hp1 : p ≤ 1 := (div_le_one upperSq_sub_lowerSq_pos).2 (by linarith [hy.2])
  have hmix : (1 - p) * lowerSq + p * upperSq = y := by
    dsimp [p]
    field_simp [ne_of_gt upperSq_sub_lowerSq_pos]
    ring
  have hc := (convexOn_pow (𝕜 := ℝ) n).2 lowerSq_nonneg upperSq_nonneg
    (sub_nonneg.2 hp1) hp (by ring : (1-p)+p=1)
  simpa only [smul_eq_mul, hmix] using hc

private lemma even_sqrt_pow (t y : ℝ) (hy : 0 ≤ y) (n : ℕ) :
    (t * Real.sqrt y) ^ (2 * n) = t ^ (2 * n) * y ^ n := by
  rw [mul_pow, pow_mul (Real.sqrt y), Real.sq_sqrt hy]

private lemma chord_term_nonneg {x : ℝ}
    (hx : lowerSq ≤ x ^ 2 ∧ x ^ 2 ≤ upperSq) (t : ℝ) (n : ℕ) :
    0 ≤ (1 - (x ^ 2 - lowerSq) / (upperSq - lowerSq)) *
      ((t * Real.sqrt lowerSq) ^ (2*n) / (2*n).factorial) +
      ((x ^ 2 - lowerSq) / (upperSq - lowerSq)) *
      ((t * Real.sqrt upperSq) ^ (2*n) / (2*n).factorial) -
      (t * x) ^ (2*n) / (2*n).factorial := by
  rw [even_sqrt_pow t lowerSq lowerSq_nonneg n,
    even_sqrt_pow t upperSq upperSq_nonneg n, mul_pow, pow_mul x]
  have ht : 0 ≤ t ^ (2*n) / ((2*n).factorial : ℝ) := by
    rw [pow_mul]
    positivity
  have hc := mul_nonneg ht (sub_nonneg.2 (pow_chord hx n))
  convert hc using 1 <;> ring

lemma pointwise_strong_chord {x : ℝ}
    (hx : lowerSq ≤ x ^ 2 ∧ x ^ 2 ≤ upperSq) (t : ℝ) :
    (x ^ 2 - lowerSq) * (upperSq - x ^ 2) * t ^ 4 / 24 ≤
      endpointMGF (x ^ 2) t - Real.cosh (t*x) := by
  let p := (x ^ 2 - lowerSq) / (upperSq - lowerSq)
  let f : ℕ → ℝ := fun n =>
    (1-p) * ((t * Real.sqrt lowerSq) ^ (2*n) / (2*n).factorial) +
    p * ((t * Real.sqrt upperSq) ^ (2*n) / (2*n).factorial) -
    (t*x) ^ (2*n) / (2*n).factorial
  have hs : HasSum f (endpointMGF (x ^ 2) t - Real.cosh (t*x)) := by
    exact (((Real.hasSum_cosh (t * Real.sqrt lowerSq)).mul_left (1-p)).add
      ((Real.hasSum_cosh (t * Real.sqrt upperSq)).mul_left p)).sub (Real.hasSum_cosh (t*x))
  have hle := sum_le_hasSum ({2} : Finset ℕ)
    (fun n _ => chord_term_nonneg hx t n) hs
  have hf : f 2 = (x ^ 2 - lowerSq) * (upperSq - x ^ 2) * t ^ 4 / 24 := by
    dsimp [f, p]
    rw [even_sqrt_pow t lowerSq lowerSq_nonneg 2,
      even_sqrt_pow t upperSq upperSq_nonneg 2]
    norm_num
    field_simp [ne_of_gt upperSq_sub_lowerSq_pos]
    ring
  simp only [Finset.sum_singleton] at hle
  change f 2 ≤ endpointMGF (x ^ 2) t - Real.cosh (t*x) at hle
  rwa [hf] at hle

lemma endpoint_mgf_gap {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) (t : ℝ) :
    interiority μ * t ^ 4 / 24 ≤ endpointMGF (variance μ) t - mgf μ t := by
  have hi : Integrable (fun x => (x ^ 2 - lowerSq) * (upperSq - x ^ 2) * t ^ 4 / 24) μ :=
    integrable_of_normalizedSupport hμ (by fun_prop)
  have he : Integrable (fun x => endpointMGF (x ^ 2) t - Real.cosh (t*x)) μ :=
    integrable_of_normalizedSupport hμ (by unfold endpointMGF; fun_prop)
  have hbound := integral_mono_ae hi he (hμ.mono fun x hx => pointwise_strong_chord hx t)
  have hleft : (∫ x, (x ^ 2 - lowerSq) * (upperSq - x ^ 2) * t ^ 4 / 24 ∂μ) =
      interiority μ * t ^ 4 / 24 := by rw [integral_div, integral_mul_const]; rfl
  have hright : (∫ x, endpointMGF (x ^ 2) t - Real.cosh (t*x) ∂μ) =
      endpointMGF (variance μ) t - mgf μ t := by
    rw [integral_sub (integrable_of_normalizedSupport hμ (by unfold endpointMGF; fun_prop))
      (integrable_cosh hμ t), ← mgf_eq_integral_cosh hμ hs t]
    congr 1
    have hp : Integrable (fun x : ℝ => (x ^ 2 - lowerSq) / (upperSq - lowerSq)) μ :=
      integrable_of_normalizedSupport hμ (by fun_prop)
    unfold endpointMGF
    rw [integral_add (integrable_of_normalizedSupport hμ (by fun_prop))
      (integrable_of_normalizedSupport hμ (by fun_prop)), integral_mul_const,
      integral_mul_const, integral_sub (integrable_const 1)
      hp,
      integral_div, integral_sub (integrable_pow hμ 2) (integrable_const lowerSq)]
    simp [variance, moment]
  rwa [hleft, hright] at hbound

end SupportCriterion
