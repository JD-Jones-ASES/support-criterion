module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Tactic

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace SupportCriterion

lemma cosh_taylor_four :
    (fun t : ℝ => Real.cosh t - (1 + t ^ 2 / 2 + t ^ 4 / 24))
      =o[𝓝 0] (fun t : ℝ => t ^ 4) := by
  have h := taylor_isLittleO_univ (x₀ := 0) (n := 4) Real.contDiff_cosh
  have ht (t : ℝ) : taylorWithinEval Real.cosh 4 Set.univ 0 t =
      1 + t ^ 2 / 2 + t ^ 4 / 24 := by
    have h2 : iteratedDeriv 2 Real.cosh = Real.cosh := Real.iteratedDeriv_even_cosh 1
    have h3 : iteratedDeriv 3 Real.cosh = Real.sinh := Real.iteratedDeriv_odd_cosh 1
    have h4 : iteratedDeriv 4 Real.cosh = Real.cosh := Real.iteratedDeriv_even_cosh 2
    simp [taylor_within_apply, Finset.sum_range_succ, iteratedDerivWithin_univ,
      h2, h3, h4, Real.deriv_cosh]
    <;> ring
  simpa only [ht, sub_zero] using h

lemma exp_taylor_two :
    (fun t : ℝ => Real.exp t - (1 + t + t ^ 2 / 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have h := taylor_isLittleO_univ (x₀ := 0) (n := 2) Real.contDiff_exp
  have ht (t : ℝ) : taylorWithinEval Real.exp 2 Set.univ 0 t =
      1 + t + t ^ 2 / 2 := by
    simp [taylor_within_apply, Finset.sum_range_succ, iteratedDerivWithin_univ,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
    <;> ring
  simpa only [ht, sub_zero] using h

lemma cosh_mul_taylor_four (a : ℝ) :
    (fun t : ℝ => Real.cosh (a * t) -
      (1 + a ^ 2 * t ^ 2 / 2 + a ^ 4 * t ^ 4 / 24))
      =o[𝓝 0] (fun t : ℝ => t ^ 4) := by
  have h := cosh_taylor_four.comp_tendsto
    (show Tendsto (fun t : ℝ => a * t) (𝓝 0) (𝓝 0) by
      have hc : ContinuousAt (fun t : ℝ => a * t) 0 := by fun_prop
      simpa using hc.tendsto)
  have hb : (fun t : ℝ => (a * t) ^ 4) =O[𝓝 0] (fun t : ℝ => t ^ 4) := by
    simpa only [mul_pow] using (isBigO_refl (fun t : ℝ => t ^ 4) (𝓝 0)).const_mul_left (a ^ 4)
  apply (h.trans_isBigO hb).congr_left
  intro t
  dsimp
  ring

lemma exp_mul_sq_taylor_four (a : ℝ) :
    (fun t : ℝ => Real.exp (a * t ^ 2) -
      (1 + a * t ^ 2 + a ^ 2 * t ^ 4 / 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 4) := by
  have h := exp_taylor_two.comp_tendsto
    (show Tendsto (fun t : ℝ => a * t ^ 2) (𝓝 0) (𝓝 0) by
      have hc : ContinuousAt (fun t : ℝ => a * t ^ 2) 0 := by fun_prop
      simpa using hc.tendsto)
  have hb : (fun t : ℝ => (a * t ^ 2) ^ 2) =O[𝓝 0] (fun t : ℝ => t ^ 4) := by
    convert (isBigO_refl (fun t : ℝ => t ^ 4) (𝓝 0)).const_mul_left (a ^ 2) using 1
    ext t
    ring
  apply (h.trans_isBigO hb).congr_left
  intro t
  dsimp
  ring

lemma eventually_pos_of_pos_fourth_coefficient {f : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (h : (fun t => f t - c * t ^ 4) =o[𝓝 0] (fun t => t ^ 4)) :
    ∃ ε > 0, ∀ t : ℝ, 0 < |t| → |t| < ε → 0 < f t := by
  have he := h.bound (show 0 < c / 2 by positivity)
  rcases Metric.eventually_nhds_iff.mp he with ⟨ε, hε, he⟩
  refine ⟨ε, hε, ?_⟩
  intro t ht hte
  have hb := he (show dist t 0 < ε by simpa [Real.dist_eq] using hte)
  have ht4 : 0 < t ^ 4 := by
    simpa only [← pow_mul] using sq_pos_of_ne_zero (pow_ne_zero 2 (abs_pos.mp ht))
  simp only [Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht4)] at hb
  have := (abs_le.mp hb).1
  nlinarith

lemma exp_mul_sq_taylor_two (a : ℝ) :
    (fun t : ℝ => Real.exp (a * t ^ 2) - (1 + a * t ^ 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have hp : (fun t : ℝ => t ^ 4) =o[𝓝 0] (fun t : ℝ => t ^ 2) :=
    isLittleO_pow_pow (by norm_num)
  have h := (exp_mul_sq_taylor_four a).trans hp
  apply (h.add (hp.const_mul_left (a ^ 2 / 2))).congr_left
  intro t
  ring

lemma eventually_pos_of_pos_second_coefficient {f : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (h : (fun t => f t - c * t ^ 2) =o[𝓝 0] (fun t => t ^ 2)) :
    ∃ ε > 0, ∀ t : ℝ, 0 < |t| → |t| < ε → 0 < f t := by
  have he := h.bound (show 0 < c / 2 by positivity)
  rcases Metric.eventually_nhds_iff.mp he with ⟨ε, hε, he⟩
  refine ⟨ε, hε, ?_⟩
  intro t ht hte
  have hb := he (show dist t 0 < ε by simpa [Real.dist_eq] using hte)
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero (abs_pos.mp ht)
  simp only [Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht2)] at hb
  have := (abs_le.mp hb).1
  nlinarith

end SupportCriterion
