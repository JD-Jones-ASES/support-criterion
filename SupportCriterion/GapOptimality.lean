module

public import SupportCriterion.TaylorAux
public import SupportCriterion.LawEndpoint
public import SupportCriterion.EndpointMoments

@[expose] public section

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace SupportCriterion

lemma cosh_taylor_eight :
    (fun t : ℝ => Real.cosh t -
      (1 + t^2/2 + t^4/24 + t^6/720 + t^8/40320))
      =o[𝓝 0] (fun t : ℝ => t^8) := by
  have h := taylor_isLittleO_univ (x₀ := 0) (n := 8) Real.contDiff_cosh
  have ht (t : ℝ) : taylorWithinEval Real.cosh 8 Set.univ 0 t =
      1 + t^2/2 + t^4/24 + t^6/720 + t^8/40320 := by
    have h2 := Real.iteratedDeriv_even_cosh 1
    have h3 := Real.iteratedDeriv_odd_cosh 1
    have h4 := Real.iteratedDeriv_even_cosh 2
    have h5 := Real.iteratedDeriv_odd_cosh 2
    have h6 := Real.iteratedDeriv_even_cosh 3
    have h7 := Real.iteratedDeriv_odd_cosh 3
    have h8 := Real.iteratedDeriv_even_cosh 4
    simp [taylor_within_apply, iteratedDerivWithin_univ,
      h2, h3, h4, h5, h6, h7, h8, Real.deriv_cosh]
    ring
  simpa only [ht, sub_zero] using h

lemma exp_taylor_four :
    (fun t : ℝ => Real.exp t - (1+t+t^2/2+t^3/6+t^4/24))
      =o[𝓝 0] (fun t : ℝ => t^4) := by
  have h := taylor_isLittleO_univ (x₀ := 0) (n := 4) Real.contDiff_exp
  have ht (t : ℝ) : taylorWithinEval Real.exp 4 Set.univ 0 t =
      1+t+t^2/2+t^3/6+t^4/24 := by
    simp [taylor_within_apply, iteratedDerivWithin_univ,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
    ring
  simpa only [ht, sub_zero] using h

lemma cosh_mul_taylor_eight (a : ℝ) :
    (fun t : ℝ => Real.cosh (a*t) -
      (1+a^2*t^2/2+a^4*t^4/24+a^6*t^6/720+a^8*t^8/40320))
      =o[𝓝 0] (fun t : ℝ => t^8) := by
  have h := cosh_taylor_eight.comp_tendsto
    (show Tendsto (fun t : ℝ => a*t) (𝓝 0) (𝓝 0) by
      have hc : ContinuousAt (fun t : ℝ => a*t) 0 := by fun_prop
      simpa using hc.tendsto)
  have hb : (fun t : ℝ => (a*t)^8) =O[𝓝 0] (fun t : ℝ => t^8) := by
    simpa only [mul_pow] using (isBigO_refl (fun t : ℝ => t^8) (𝓝 0)).const_mul_left (a^8)
  apply (h.trans_isBigO hb).congr_left
  intro t
  dsimp
  ring

noncomputable def sharpVariancePath (t : ℝ) : ℝ := 1-t^2/15

noncomputable def endpointTaylorEight (v t : ℝ) : ℝ :=
  1+v*t^2/2+(6*v-3)*t^4/24+(33*v-18)*t^6/720+(180*v-99)*t^8/40320

@[fun_prop] lemma sharpVariancePath_continuous : Continuous sharpVariancePath := by
  unfold sharpVariancePath
  fun_prop

lemma endpointMGF_path_taylor_eight :
    (fun t : ℝ => endpointMGF (sharpVariancePath t) t -
      endpointTaylorEight (sharpVariancePath t) t) =o[𝓝 0] (fun t : ℝ => t^8) := by
  let p : ℝ → ℝ := fun t => (sharpVariancePath t-lowerSq)/(upperSq-lowerSq)
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hl : (fun t => (1-p t)) =O[𝓝 0] (fun _ : ℝ => (1:ℝ)) :=
    ((continuous_const.sub hp).continuousAt.tendsto).isBigO_one ℝ
  have hu : p =O[𝓝 0] (fun _ : ℝ => (1:ℝ)) := hp.continuousAt.tendsto.isBigO_one ℝ
  have h := (hl.mul_isLittleO (cosh_mul_taylor_eight (Real.sqrt lowerSq))).add
    (hu.mul_isLittleO (cosh_mul_taylor_eight (Real.sqrt upperSq)))
  simp only [one_mul] at h
  apply h.congr_left
  intro t
  dsimp [p]
  have ha := Real.sq_sqrt lowerSq_nonneg
  have hb := Real.sq_sqrt upperSq_nonneg
  have ha4 : (Real.sqrt lowerSq)^4 = lowerSq^2 := by rw [show (4:ℕ)=2*2 from rfl, pow_mul, ha]
  have hb4 : (Real.sqrt upperSq)^4 = upperSq^2 := by rw [show (4:ℕ)=2*2 from rfl, pow_mul, hb]
  have ha6 : (Real.sqrt lowerSq)^6 = lowerSq^3 := by rw [show (6:ℕ)=2*3 from rfl, pow_mul, ha]
  have hb6 : (Real.sqrt upperSq)^6 = upperSq^3 := by rw [show (6:ℕ)=2*3 from rfl, pow_mul, hb]
  have ha8 : (Real.sqrt lowerSq)^8 = lowerSq^4 := by rw [show (8:ℕ)=2*4 from rfl, pow_mul, ha]
  have hb8 : (Real.sqrt upperSq)^8 = upperSq^4 := by rw [show (8:ℕ)=2*4 from rfl, pow_mul, hb]
  simp only [ha, hb, ha4, hb4, ha6, hb6, ha8, hb8]
  have h1 := endpointMoment_one (sharpVariancePath t)
  have h2 := endpointMoment_two (sharpVariancePath t)
  have h3 := endpointMoment_three (sharpVariancePath t)
  have h4 := endpointMoment_four (sharpVariancePath t)
  simp only [endpointMoment] at h1 h2 h3 h4
  unfold endpointMGF endpointTaylorEight
  rw [mul_comm t (Real.sqrt lowerSq), mul_comm t (Real.sqrt upperSq)]
  linear_combination -(t^2/2)*h1 -(t^4/24)*h2 -(t^6/720)*h3 -(t^8/40320)*h4

noncomputable def pathExpTaylor (t : ℝ) : ℝ :=
  let x := sharpVariancePath t*t^2/2
  1+x+x^2/2+x^3/6+x^4/24

lemma path_exp_taylor_eight :
    (fun t : ℝ => Real.exp (sharpVariancePath t*t^2/2)-pathExpTaylor t)
      =o[𝓝 0] (fun t : ℝ => t^8) := by
  have hc : Continuous (fun t : ℝ => sharpVariancePath t*t^2/2) := by fun_prop
  have h := exp_taylor_four.comp_tendsto
    (show Tendsto (fun t : ℝ => sharpVariancePath t*t^2/2) (𝓝 0) (𝓝 0) by
      simpa [sharpVariancePath] using (hc.continuousAt (x := 0)).tendsto)
  have hb : (fun t : ℝ => (sharpVariancePath t/2)^4) =O[𝓝 0]
      (fun _ : ℝ => (1:ℝ)) := by
    have hb : Continuous (fun t : ℝ => (sharpVariancePath t/2)^4) := by fun_prop
    exact hb.continuousAt.tendsto.isBigO_one ℝ
  have hpow : (fun t : ℝ => (sharpVariancePath t*t^2/2)^4) =O[𝓝 0]
      (fun t : ℝ => t^8) := by
    convert hb.mul (isBigO_refl (fun t : ℝ => t^8) (𝓝 0)) using 1 <;>
      ext t <;> ring
  exact h.trans_isBigO hpow

lemma endpoint_gap_path_expansion :
    (fun t : ℝ => Real.exp (sharpVariancePath t*t^2/2) -
      endpointMGF (sharpVariancePath t) t - t^8/25200)
      =o[𝓝 0] (fun t : ℝ => t^8) := by
  let r : ℝ → ℝ := fun t => -1/8400+41*t^2/648000-t^4/324000+t^6/19440000
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hp : (fun t : ℝ => t^10) =o[𝓝 0] (fun t : ℝ => t^8) :=
    isLittleO_pow_pow (by norm_num)
  have hrem := (hr.continuousAt.tendsto.isBigO_one ℝ).mul_isLittleO hp
  simp only [one_mul] at hrem
  apply ((path_exp_taylor_eight.sub endpointMGF_path_taylor_eight).add hrem).congr_left
  intro t
  dsimp [r, pathExpTaylor, endpointTaylorEight, sharpVariancePath]
  ring

lemma sharpVariancePath_admissible_eventually :
    ∀ᶠ t : ℝ in 𝓝 0, lowerSq ≤ sharpVariancePath t ∧ sharpVariancePath t ≤ upperSq := by
  have h := sharpVariancePath_continuous.continuousAt (x := 0)
  have hA : lowerSq < sharpVariancePath 0 := by simpa [sharpVariancePath] using lowerSq_lt_one
  have hB : sharpVariancePath 0 < upperSq := by simpa [sharpVariancePath] using one_lt_upperSq
  filter_upwards [h.eventually (Ioo_mem_nhds hA hB)] with t ht
  exact ⟨ht.1.le,ht.2.le⟩

lemma coefficient_le_of_eventual_lower {f : ℝ → ℝ} {c C : ℝ} (n : ℕ)
    (hexp : (fun t => f t-C*t^n) =o[𝓝 0] (fun t : ℝ => t^n))
    (hlower : ∀ᶠ t : ℝ in 𝓝 0, c*t^n ≤ f t) : c ≤ C := by
  by_contra hn
  have hc : 0 < (c-C)/2 := by linarith
  have he := (hexp.bound hc).and hlower
  rcases Metric.eventually_nhds_iff.mp he with ⟨ε,hε,he⟩
  have ht : 0 < ε/2 := by positivity
  have htε : dist (ε/2) 0 < ε := by rw [Real.dist_eq,sub_zero,abs_of_pos ht]; linarith
  have hb := he htε
  have htn : 0 < (ε/2)^n := pow_pos ht n
  simp only [Real.norm_eq_abs,abs_of_pos htn] at hb
  have hab := (abs_le.mp hb.1).2
  nlinarith [hb.2]

/-- No larger universal eighth-order coefficient is possible, even allowing
the witnessing symmetric endpoint law to vary with the MGF parameter. -/
theorem sharp_gap_coefficient_le (c : ℝ)
    (h : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], NormalizedSupport μ →
      Symmetric μ → ∀ t : ℝ,
        c*t^8 ≤ Real.exp (variance μ*t^2/2)-mgf μ t) : c ≤ 1/25200 := by
  apply coefficient_le_of_eventual_lower 8
    (f := fun t => Real.exp (sharpVariancePath t*t^2/2)-endpointMGF (sharpVariancePath t) t)
  · simpa only [div_eq_mul_inv,one_mul,mul_comm (25200:ℝ)⁻¹] using endpoint_gap_path_expansion
  · filter_upwards [sharpVariancePath_admissible_eventually] with t ht
    letI := endpointLaw_isProbabilityMeasure (sharpVariancePath t) ht
    have hl := h (endpointLaw (sharpVariancePath t))
      (endpointLaw_normalizedSupport _) (endpointLaw_symmetric _) t
    rwa [endpointLaw_variance _ ht,endpointLaw_mgf _ ht] at hl

/-- The extremizing endpoint path has the sharp normalized ratio in the
punctured limit at zero. -/
theorem endpoint_gap_path_ratio_tendsto :
    Tendsto (fun t : ℝ =>
      (Real.exp (sharpVariancePath t*t^2/2)-endpointMGF (sharpVariancePath t) t)/t^8)
      (𝓝[≠] 0) (𝓝 (1/25200)) := by
  have h : Tendsto (fun t : ℝ => (Real.exp (sharpVariancePath t*t^2/2) -
      endpointMGF (sharpVariancePath t) t-t^8/25200)/t^8) (𝓝[≠] 0) (𝓝 0) :=
    endpoint_gap_path_expansion.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have h' := h.add_const (1/25200:ℝ)
  simp only [zero_add] at h'
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  field_simp [ht0]
  <;> ring

/-- The path consists of admissible symmetric probability laws near zero. -/
theorem sharp_gap_path_laws_admissible :
    ∀ᶠ t : ℝ in 𝓝 0,
      IsProbabilityMeasure (endpointLaw (sharpVariancePath t)) ∧
      NormalizedSupport (endpointLaw (sharpVariancePath t)) ∧
      Symmetric (endpointLaw (sharpVariancePath t)) := by
  filter_upwards [sharpVariancePath_admissible_eventually] with t ht
  exact ⟨endpointLaw_isProbabilityMeasure _ ht,
    endpointLaw_normalizedSupport _,endpointLaw_symmetric _⟩

/-- Sharpness expressed through the ordinary MGF and second moment of the
actual endpoint probability laws, rather than just their scalar formula. -/
theorem sharp_gap_path_law_ratio_tendsto :
    Tendsto (fun t : ℝ =>
      (Real.exp (variance (endpointLaw (sharpVariancePath t))*t^2/2)-
        mgf (endpointLaw (sharpVariancePath t)) t)/t^8)
      (𝓝[≠] 0) (𝓝 (1/25200)) := by
  apply endpoint_gap_path_ratio_tendsto.congr'
  filter_upwards [sharpVariancePath_admissible_eventually.filter_mono nhdsWithin_le_nhds]
    with t ht
  rw [endpointLaw_variance _ ht,endpointLaw_mgf _ ht]

lemma symmetricTwoPoint_one_support : NormalizedSupport (symmetricTwoPoint 1) := by
  unfold NormalizedSupport symmetricTwoPoint
  rw [ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure <;>
    simp [lowerSq_lt_one.le,one_lt_upperSq.le]

lemma symmetricTwoPoint_one_variance : variance (symmetricTwoPoint 1) = 1 := by
  unfold variance moment
  rw [integral_symmetricTwoPoint]
  norm_num

lemma symmetricTwoPoint_one_mgf (t : ℝ) : mgf (symmetricTwoPoint 1) t = Real.cosh t := by
  unfold mgf
  rw [integral_symmetricTwoPoint]
  simp [Real.cosh_eq]

lemma symmetricTwoPoint_one_interiority : interiority (symmetricTwoPoint 1) = 2 := by
  unfold interiority
  rw [integral_symmetricTwoPoint]
  norm_num
  nlinarith [lowerSq_add_upperSq,lowerSq_mul_upperSq]

lemma symmetricTwoPoint_one_gap_expansion :
    (fun t : ℝ => Real.exp (t^2/2)-Real.cosh t-t^4/12)
      =o[𝓝 0] (fun t : ℝ => t^4) := by
  apply ((exp_mul_sq_taylor_four (1/2)).sub cosh_taylor_four).congr_left
  intro t
  ring

/-- The support-interiority coefficient is individually optimal. -/
theorem interiority_gap_coefficient_le (c : ℝ)
    (h : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], NormalizedSupport μ →
      Symmetric μ → ∀ t : ℝ,
        c*interiority μ*t^4 ≤ Real.exp (variance μ*t^2/2)-mgf μ t) : c ≤ 1/24 := by
  have hc : 2*c ≤ (1/12:ℝ) := by
    apply coefficient_le_of_eventual_lower 4
      (f := fun t => Real.exp (t^2/2)-Real.cosh t)
    · simpa only [div_eq_mul_inv,one_mul,mul_comm (12:ℝ)⁻¹] using symmetricTwoPoint_one_gap_expansion
    · apply Filter.Eventually.of_forall
      intro t
      have hl := h (symmetricTwoPoint 1) symmetricTwoPoint_one_support
        (symmetricTwoPoint_symmetric 1) t
      rw [symmetricTwoPoint_one_variance,symmetricTwoPoint_one_mgf,
        symmetricTwoPoint_one_interiority] at hl
      simpa only [one_mul,mul_comm c 2] using hl
  linarith

/-- A positive intrinsic fourth-deficit coefficient is incompatible with the
sharp eighth-order coefficient in a simultaneous universal lower bound. -/
theorem sharp_gap_intrinsic_coefficient_nonpos (c : ℝ)
    (h : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], NormalizedSupport μ →
      Symmetric μ → ∀ t : ℝ,
        t^8/25200+c*fourthDeficit μ*t^4 ≤ Real.exp (variance μ*t^2/2)-mgf μ t) : c ≤ 0 := by
  have hc : (1/25200:ℝ)+c/75 ≤ 1/25200 := by
    apply coefficient_le_of_eventual_lower 8
      (f := fun t => Real.exp (sharpVariancePath t*t^2/2)-endpointMGF (sharpVariancePath t) t)
    · simpa only [div_eq_mul_inv,one_mul,mul_comm (25200:ℝ)⁻¹] using endpoint_gap_path_expansion
    · filter_upwards [sharpVariancePath_admissible_eventually] with t ht
      letI := endpointLaw_isProbabilityMeasure (sharpVariancePath t) ht
      have hl := h (endpointLaw (sharpVariancePath t))
        (endpointLaw_normalizedSupport _) (endpointLaw_symmetric _) t
      rw [endpointLaw_variance _ ht,endpointLaw_mgf _ ht,endpointLaw_fourthDeficit _ ht] at hl
      convert hl using 1
      unfold sharpVariancePath
      ring
  linarith

end SupportCriterion
