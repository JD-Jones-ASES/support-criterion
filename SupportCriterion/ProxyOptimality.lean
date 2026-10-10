module

public import SupportCriterion.LawBasics
public import SupportCriterion.TaylorAux
public import Mathlib.Probability.Moments.MGFAnalytic

@[expose] public section

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace SupportCriterion

lemma symmetric_mean_zero {μ : Measure ℝ} (hs : Symmetric μ) :
    (∫ x : ℝ, x ∂μ) = 0 := by
  have h := integral_neg_eq hs (f := fun x : ℝ => x) continuous_id
  change (∫ x : ℝ, -x ∂μ) = ∫ x : ℝ, x ∂μ at h
  rw [integral_neg] at h
  linarith

lemma mgf_taylor_two_of_bandSupport {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a b : ℝ} (hμ : BandSupport μ a b) (hs : Symmetric μ) :
    (fun t : ℝ => mgf μ t - (1 + variance μ * t ^ 2 / 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have hdom : ProbabilityTheory.integrableExpSet (fun x : ℝ => x) μ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact integrable_of_bandSupport hμ (by fun_prop)
  have hd0 : (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet (fun x : ℝ => x) μ) := by
    simp [hdom]
  have hc : ContDiff ℝ 2 (ProbabilityTheory.mgf (fun x : ℝ => x) μ) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact (ProbabilityTheory.analyticAt_mgf (by simp [hdom])).contDiffAt
  have h := taylor_isLittleO_univ (x₀ := 0) (n := 2) hc
  have ht (t : ℝ) :
      taylorWithinEval (ProbabilityTheory.mgf (fun x : ℝ => x) μ) 2 Set.univ 0 t =
        1 + variance μ * t ^ 2 / 2 := by
    simp [taylor_within_apply, iteratedDerivWithin_univ,
      ProbabilityTheory.iteratedDeriv_mgf_zero hd0, symmetric_mean_zero hs,
      variance, moment]
    <;> ring
  simpa only [ht, sub_zero, mgf, ProbabilityTheory.mgf] using h

/-- A Gaussian quadratic proxy for a symmetric bounded law is at least its
actual variance. -/
theorem proxyOptimality {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a b τ : ℝ} (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hbound : ∀ t : ℝ, mgf μ t ≤ Real.exp (τ * t ^ 2 / 2)) :
    variance μ ≤ τ := by
  by_contra hn
  have hτ : τ < variance μ := lt_of_not_ge hn
  have hm := mgf_taylor_two_of_bandSupport hμ hs
  have he := exp_mul_sq_taylor_two (τ / 2)
  have hh : (fun t : ℝ => mgf μ t - Real.exp (τ * t ^ 2 / 2) -
      ((variance μ - τ) / 2) * t ^ 2) =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
    apply (hm.sub he).congr_left
    intro t
    ring_nf
  obtain ⟨ε, hε, hg⟩ := eventually_pos_of_pos_second_coefficient
    (div_pos (sub_pos.mpr hτ) (by norm_num)) hh
  have heps : 0 < |ε / 2| := abs_pos.mpr (ne_of_gt (by positivity))
  have heps' : |ε / 2| < ε := by rw [abs_of_pos (by positivity)]; linarith
  have hf := hg (ε / 2) heps heps'
  have hb := hbound (ε / 2)
  linarith

end SupportCriterion
