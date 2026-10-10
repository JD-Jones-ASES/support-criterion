module

public import SupportCriterion.TransportStability

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SupportCriterion

instance squaredLaw_isProbabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (squaredLaw μ) := by unfold squaredLaw; infer_instance

lemma squaredLaw_intervalSupport {μ : Measure ℝ} (hμ : NormalizedSupport μ) :
    ∀ᵐ y ∂squaredLaw μ, lowerSq ≤ y ∧ y ≤ upperSq := by
  exact (ae_map_iff (by fun_prop) (by measurability)).mpr hμ

lemma integral_squaredLaw (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ y, f y ∂squaredLaw μ) = ∫ x, f (x ^ 2) ∂μ :=
  integral_map (by fun_prop) hf.aestronglyMeasurable

lemma squaredLaw_mean (μ : Measure ℝ) :
    (∫ y, y ∂squaredLaw μ) = variance μ :=
  integral_squaredLaw μ _ continuous_id

lemma squaredLaw_reference : squaredLaw criticalLaw = twoEndpointLaw referenceWeight :=
  squaredLaw_endpointLaw 1

lemma squaredLaw_transport_finite (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    (Couplings (squaredLaw μ) (squaredLaw criticalLaw)).Nonempty ∧
    (∀ π ∈ Couplings (squaredLaw μ) (squaredLaw criticalLaw), transportCost π ≠ ⊤) ∧
    wassersteinOneExtended (squaredLaw μ) (squaredLaw criticalLaw) ≠ ⊤ := by
  have hi := integrable_of_intervalSupport (squaredLaw_intervalSupport hμ) continuous_id
  have hi0 := integrable_of_intervalSupport
    (squaredLaw_intervalSupport criticalLaw_normalizedSupport) continuous_id
  exact ⟨couplings_nonempty _ _, fun _ hπ => coupling_cost_ne_top hπ hi hi0,
    wassersteinOneExtended_ne_top _ _ hi hi0⟩

lemma squaredLaw_transport_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
      |variance μ - 1| + interiority μ / Real.sqrt 6 := by
  have h := endpointChoice_transport_bound (squaredLaw μ) (squaredLaw_intervalSupport hμ)
  rw [← squaredLaw_reference, squaredLaw_mean,
    integral_squaredLaw μ _ (by fun_prop)] at h
  change wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
    |variance μ - 1| + 2 * interiority μ / (upperSq - lowerSq) at h
  rw [upperSq_sub_lowerSq] at h
  have he : 2 * interiority μ / (2 * Real.sqrt 6) = interiority μ / Real.sqrt 6 := by ring
  rwa [he] at h

/-- Sharp local stability for the squared law, in the ordinary first Wasserstein
metric. It holds for every law in the normalized bands. -/
lemma sharp_local_stability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hδ : fourthDeficit μ ≤ 1 / 2) :
    wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
      Real.sqrt (fourthDeficit μ / 3) := by
  have hid := fourthDeficit_identity hμ
  have hd0 := interiority_nonneg hμ
  have hh : 3 * |variance μ - 1| ^ 2 ≤ fourthDeficit μ := by rw [sq_abs]; linarith
  have h := sharp_local_modulus_scalar (fourthDeficit_nonneg hμ) hδ (abs_nonneg _) hh
  have he : fourthDeficit μ - 3 * |variance μ - 1| ^ 2 = interiority μ := by rw [sq_abs]; linarith
  rw [he] at h
  exact (squaredLaw_transport_bound μ hμ).trans h

lemma attaining_variance_mem {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) :
    lowerSq ≤ 1 + Real.sqrt (δ / 3) ∧ 1 + Real.sqrt (δ / 3) ≤ upperSq := by
  have hs := Real.sq_sqrt (show 0 ≤ δ / 3 by positivity)
  have hs0 := Real.sqrt_nonneg (δ / 3)
  have hs1 : Real.sqrt (δ / 3) ≤ 1 := by nlinarith
  constructor
  · linarith [lowerSq_lt_one]
  · have : 3 < upperSq := by unfold upperSq; linarith [sqrt_six_pos]
    linarith

/-- The endpoint law of mean `1 + sqrt (δ/3)` attains the local modulus for every
`δ` in the full stated interval. -/
lemma sharp_local_stability_attained {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) :
    let μ := endpointLaw (1 + Real.sqrt (δ / 3))
    IsProbabilityMeasure μ ∧ Symmetric μ ∧ NormalizedSupport μ ∧
      fourthDeficit μ = δ ∧
      wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) = Real.sqrt (δ / 3) := by
  dsimp only
  let μ := endpointLaw (1 + Real.sqrt (δ / 3))
  have hv := attaining_variance_mem hδ hδ'
  have hprob : IsProbabilityMeasure μ := endpointLaw_isProbabilityMeasure _ hv
  letI : IsProbabilityMeasure μ := hprob
  have hsup : NormalizedSupport μ := endpointLaw_normalizedSupport _
  have hdef : fourthDeficit μ = δ := by
    rw [endpointLaw_fourthDeficit _ hv]
    have hs := Real.sq_sqrt (show 0 ≤ δ / 3 by positivity)
    nlinarith
  refine ⟨hprob, endpointLaw_symmetric _, hsup, hdef, ?_⟩
  apply le_antisymm
  · have h := sharp_local_stability μ hsup (by rwa [hdef])
    rwa [hdef] at h
  · have hi := integrable_of_intervalSupport (squaredLaw_intervalSupport hsup) continuous_id
    have hi0 := integrable_of_intervalSupport
      (squaredLaw_intervalSupport criticalLaw_normalizedSupport) continuous_id
    have h := mean_distance_le_wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) hi hi0
    rw [squaredLaw_mean, squaredLaw_mean, criticalLaw_variance,
      endpointLaw_variance _ hv, add_sub_cancel_left, abs_of_nonneg (Real.sqrt_nonneg _)] at h
    exact h

end SupportCriterion
