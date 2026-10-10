module

public import SupportCriterion.EndpointLaw
public import SupportCriterion.LawBasics

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SupportCriterion

lemma symmetric_singleton (μ : Measure ℝ) (hμ : Symmetric μ) (x : ℝ) :
    μ {-x} = μ {x} := by
  have h := congrArg (fun ν : Measure ℝ => ν {x}) hμ
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)] at h
  convert h using 1
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor <;> intro hy <;> linarith

lemma endpoint_support_four_nodes {μ : Measure ℝ}
    (hs : ∀ᵐ x ∂μ, x ^ 2 = lowerSq ∨ x ^ 2 = upperSq) :
    ∀ᵐ x ∂μ, x ∈ ({Real.sqrt lowerSq, -Real.sqrt lowerSq,
      Real.sqrt upperSq, -Real.sqrt upperSq} : Finset ℝ) := by
  filter_upwards [hs] with x hx
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hA := Real.sq_sqrt lowerSq_nonneg
  have hB := Real.sq_sqrt upperSq_nonneg
  rcases hx with hx | hx
  · rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hx.trans hA.symm) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hx.trans hB.symm) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

lemma symmetric_endpoint_decomposition (μ : Measure ℝ) (hμ : Symmetric μ)
    (hs : ∀ᵐ x ∂μ, x ^ 2 = lowerSq ∨ x ^ 2 = upperSq) :
    μ = μ {Real.sqrt lowerSq} • Measure.dirac (Real.sqrt lowerSq) +
      μ {Real.sqrt lowerSq} • Measure.dirac (-Real.sqrt lowerSq) +
      μ {Real.sqrt upperSq} • Measure.dirac (Real.sqrt upperSq) +
      μ {Real.sqrt upperSq} • Measure.dirac (-Real.sqrt upperSq) := by
  have hA : 0 < Real.sqrt lowerSq := Real.sqrt_pos.mpr lowerSq_pos
  have hB : 0 < Real.sqrt upperSq := Real.sqrt_pos.mpr upperSq_pos
  have hAB : Real.sqrt lowerSq ≠ Real.sqrt upperSq := by
    intro h
    have := congrArg (fun x : ℝ => x ^ 2) h
    simp only [Real.sq_sqrt lowerSq_nonneg, Real.sq_sqrt upperSq_nonneg] at this
    exact ne_of_lt lowerSq_lt_upperSq this
  have h := Measure.ae_mem_finset_iff.mp (endpoint_support_four_nodes hs)
  simpa [Finset.sum_insert, hAB, ne_of_gt hA, ne_of_gt hB,
    show Real.sqrt lowerSq ≠ -Real.sqrt lowerSq by linarith,
    show Real.sqrt lowerSq ≠ -Real.sqrt upperSq by linarith,
    show -Real.sqrt lowerSq ≠ Real.sqrt upperSq by linarith,
    show -Real.sqrt lowerSq ≠ -Real.sqrt upperSq by intro h; apply hAB; linarith,
    show Real.sqrt upperSq ≠ -Real.sqrt upperSq by linarith,
    symmetric_singleton μ hμ, add_assoc] using h

lemma eq_criticalLaw_of_endpoint_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Symmetric μ)
    (hs : ∀ᵐ x ∂μ, x ^ 2 = lowerSq ∨ x ^ 2 = upperSq)
    (hv : variance μ = 1) : μ = criticalLaw := by
  let c := μ {Real.sqrt lowerSq}
  let d := μ {Real.sqrt upperSq}
  have hcfinite : c ≠ ⊤ := measure_ne_top μ _
  have hdfinite : d ≠ ⊤ := measure_ne_top μ _
  have hdec := symmetric_endpoint_decomposition μ hμ hs
  have hmass : 2 * c.toReal + 2 * d.toReal = 1 := by
    have h := congrArg (fun ν : Measure ℝ => (ν Set.univ).toReal) hdec
    simp only [measure_univ, ENNReal.toReal_one, Measure.add_apply,
      MeasurableSet.univ, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      smul_eq_mul, mul_one] at h
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)] at h
    dsimp [c, d]
    linarith
  have hsecond : 2 * c.toReal * lowerSq + 2 * d.toReal * upperSq = 1 := by
    have hi (x : ℝ) : Integrable (fun x : ℝ => x ^ 2) (μ {x} • Measure.dirac x) :=
      (integrable_dirac (by simp)).smul_measure (measure_ne_top μ _)
    have hi' (x y : ℝ) : Integrable (fun x : ℝ => x ^ 2) (μ {x} • Measure.dirac y) :=
      (integrable_dirac (by simp)).smul_measure (measure_ne_top μ _)
    unfold variance moment at hv
    rw [hdec, integral_add_measure (((hi _).add_measure (hi' _ _)).add_measure (hi _))
      (hi' _ _), integral_add_measure ((hi _).add_measure (hi' _ _)) (hi _),
      integral_add_measure (hi _) (hi' _ _)] at hv
    simp only [integral_smul_measure, integral_dirac, smul_eq_mul, neg_sq,
      Real.sq_sqrt lowerSq_nonneg, Real.sq_sqrt upperSq_nonneg] at hv
    dsimp [c, d]
    linarith
  have hc : c.toReal = (1 - referenceWeight) / 2 := by
    unfold referenceWeight
    field_simp [ne_of_gt upperSq_sub_lowerSq_pos]
    nlinarith [congrArg (fun z : ℝ => z * upperSq) hmass, hsecond]
  have hd : d.toReal = referenceWeight / 2 := by
    unfold referenceWeight
    field_simp [ne_of_gt upperSq_sub_lowerSq_pos]
    nlinarith [congrArg (fun z : ℝ => z * lowerSq) hmass, hsecond]
  have hc' : c = ENNReal.ofReal (1 - referenceWeight) * (1 / 2 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hcfinite, hc, div_eq_mul_inv,
      ENNReal.ofReal_mul (sub_nonneg.mpr referenceWeight_lt_one.le)]
    norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hd' : d = ENNReal.ofReal referenceWeight * (1 / 2 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hdfinite, hd, div_eq_mul_inv,
      ENNReal.ofReal_mul referenceWeight_pos.le]
    norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hdec]
  change c • _ + c • _ + d • _ + d • _ = _
  rw [hc', hd']
  simp only [criticalLaw, endpointLaw, referenceWeight, symmetricTwoPoint,
    smul_add, smul_smul, add_assoc]

lemma fourthDeficit_eq_zero_iff_criticalLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hsym : Symmetric μ) :
    fourthDeficit μ = 0 ↔ μ = criticalLaw := by
  constructor
  · intro h
    obtain ⟨hv, hd⟩ := (fourthDeficit_eq_zero_iff hμ).mp h
    exact eq_criticalLaw_of_endpoint_support μ hsym ((interiority_eq_zero_iff hμ).mp hd) hv
  · rintro rfl
    exact criticalLaw_fourthDeficit

end SupportCriterion
