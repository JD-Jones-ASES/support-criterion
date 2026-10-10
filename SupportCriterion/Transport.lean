module

public import SupportCriterion.EndpointLaw
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SupportCriterion

/-- Ordinary probability couplings with the stated marginals. -/
def Couplings (μ ν : Measure ℝ) : Set (Measure (ℝ × ℝ)) :=
  {π | IsProbabilityMeasure π ∧ Measure.map Prod.fst π = μ ∧
    Measure.map Prod.snd π = ν}

/-- The nonnegative extended transport cost; it never uses the default value of a
nonintegrable Bochner integral. -/
noncomputable def transportCost (π : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ z, edist z.1 z.2 ∂π

/-- The extended first Wasserstein distance is the infimum over all couplings. -/
noncomputable def wassersteinOneExtended (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ⨅ π ∈ Couplings μ ν, transportCost π

/-- Real first Wasserstein distance. Finiteness is established separately wherever
this real-valued quantity is used. -/
noncomputable def wassersteinOne (μ ν : Measure ℝ) : ℝ :=
  (wassersteinOneExtended μ ν).toReal

lemma couplings_nonempty (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : (Couplings μ ν).Nonempty := by
  refine ⟨μ.prod ν, inferInstance, ?_, ?_⟩
  · simp
  · simp

lemma wassersteinOneExtended_le_cost {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (hπ : π ∈ Couplings μ ν) : wassersteinOneExtended μ ν ≤ transportCost π :=
  iInf_le_of_le π (iInf_le_of_le hπ le_rfl)

lemma coupling_integrable_left {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (hπ : π ∈ Couplings μ ν) (hμ : Integrable (fun x : ℝ => x) μ) :
    Integrable Prod.fst π := by
  have hm : Integrable (fun x : ℝ => x) (Measure.map Prod.fst π) := by
    rwa [hπ.2.1]
  exact hm.comp_measurable measurable_fst

lemma coupling_integrable_right {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (hπ : π ∈ Couplings μ ν) (hν : Integrable (fun x : ℝ => x) ν) :
    Integrable Prod.snd π := by
  have hm : Integrable (fun x : ℝ => x) (Measure.map Prod.snd π) := by
    rwa [hπ.2.2]
  exact hm.comp_measurable measurable_snd

lemma coupling_cost_ne_top {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (hπ : π ∈ Couplings μ ν) (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) : transportCost π ≠ ⊤ :=
  ne_of_lt (lintegral_edist_lt_top (coupling_integrable_left hπ hμ)
    (coupling_integrable_right hπ hν))

lemma wassersteinOneExtended_ne_top (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) : wassersteinOneExtended μ ν ≠ ⊤ := by
  obtain ⟨π, hπ⟩ := couplings_nonempty μ ν
  exact ne_top_of_le_ne_top (coupling_cost_ne_top hπ hμ hν)
    (wassersteinOneExtended_le_cost hπ)

lemma mean_distance_le_wassersteinOne (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) :
    |(∫ x, x ∂μ) - (∫ x, x ∂ν)| ≤ wassersteinOne μ ν := by
  have he : edist (∫ x, x ∂μ) (∫ x, x ∂ν) ≤ wassersteinOneExtended μ ν := by
    apply le_iInf
    intro π
    apply le_iInf
    intro hπ
    have h := edist_integral_le_lintegral_edist (coupling_integrable_left hπ hμ)
      (coupling_integrable_right hπ hν)
    rw [← integral_map (φ := Prod.fst) (f := fun x : ℝ => x) measurable_fst.aemeasurable (by fun_prop),
      ← integral_map (φ := Prod.snd) (f := fun x : ℝ => x) measurable_snd.aemeasurable (by fun_prop), hπ.2.1, hπ.2.2] at h
    exact h
  have h := ENNReal.toReal_mono (wassersteinOneExtended_ne_top μ ν hμ hν) he
  simpa [wassersteinOne, edist_dist, Real.dist_eq] using h

/-- The scalar maximization that converts the constructive transport estimate to
its sharp local modulus. -/
lemma sharp_local_modulus_scalar {δ h : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2)
    (hh : 0 ≤ h) (hh' : 3 * h ^ 2 ≤ δ) :
    h + (δ - 3 * h ^ 2) / Real.sqrt 6 ≤ Real.sqrt (δ / 3) := by
  have hs : Real.sqrt (δ / 3) ^ 2 = δ / 3 := Real.sq_sqrt (by positivity)
  have hsnonneg : 0 ≤ Real.sqrt (δ / 3) := Real.sqrt_nonneg _
  have hhs : h ≤ Real.sqrt (δ / 3) := by nlinarith
  have hsmall : Real.sqrt 6 * Real.sqrt (δ / 3) ≤ 1 := by
    have hnonneg : 0 ≤ Real.sqrt 6 * Real.sqrt (δ / 3) := by positivity
    have hs6 : (Real.sqrt 6 * Real.sqrt (δ / 3)) ^ 2 = 2 * δ := by
      rw [mul_pow, sqrt_six_sq, hs]
      ring
    nlinarith
  apply (mul_le_mul_iff_right₀ sqrt_six_pos).mp
  have hprod : 0 ≤ (Real.sqrt (δ / 3) - h) *
      (Real.sqrt 6 - 3 * (Real.sqrt (δ / 3) + h)) := by
    apply mul_nonneg (sub_nonneg.mpr hhs)
    have : 6 * Real.sqrt (δ / 3) ≤ Real.sqrt 6 := by
      have hm := mul_le_mul_of_nonneg_left hsmall sqrt_six_pos.le
      nlinarith [sqrt_six_sq]
    nlinarith
  field_simp [ne_of_gt sqrt_six_pos]
  nlinarith

end SupportCriterion
