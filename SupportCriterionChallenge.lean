module

public import Mathlib

/-! Independent principal statements and ordinary definitions for the support criterion.
Only this statement file contains proof holes; the Solution supplies every proof.
-/
@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace SupportCriterion

noncomputable def lowerSq : ℝ := 3 - Real.sqrt 6
noncomputable def upperSq : ℝ := 3 + Real.sqrt 6
noncomputable def sharpRatio : ℝ := Real.sqrt 3 + Real.sqrt 2
noncomputable def referenceWeight : ℝ := (1 - lowerSq) / (upperSq - lowerSq)

def Symmetric (μ : Measure ℝ) : Prop := Measure.map (fun x : ℝ => -x) μ = μ

def NormalizedSupport (μ : Measure ℝ) : Prop :=
  ∀ᵐ x ∂μ, lowerSq ≤ x ^ 2 ∧ x ^ 2 ≤ upperSq

def BandSupport (μ : Measure ℝ) (a b : ℝ) : Prop :=
  ∀ᵐ x ∂μ, a ≤ |x| ∧ |x| ≤ b

noncomputable def moment (μ : Measure ℝ) (n : ℕ) : ℝ := ∫ x, x ^ n ∂μ
noncomputable def variance (μ : Measure ℝ) : ℝ := moment μ 2
noncomputable def fourthDeficit (μ : Measure ℝ) : ℝ := 3 * (variance μ) ^ 2 - moment μ 4
noncomputable def interiority (μ : Measure ℝ) : ℝ :=
  ∫ x, (x ^ 2 - lowerSq) * (upperSq - x ^ 2) ∂μ
noncomputable def mgf (μ : Measure ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (t * x) ∂μ
noncomputable def endpointMGF (v t : ℝ) : ℝ :=
  (1 - (v - lowerSq) / (upperSq - lowerSq)) * Real.cosh (t * Real.sqrt lowerSq) +
  ((v - lowerSq) / (upperSq - lowerSq)) * Real.cosh (t * Real.sqrt upperSq)

noncomputable def symmetricTwoPoint (x : ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac x + (1 / 2 : ℝ≥0∞) • Measure.dirac (-x)
noncomputable def endpointLaw (v : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - (v - lowerSq) / (upperSq - lowerSq)) •
    symmetricTwoPoint (Real.sqrt lowerSq) +
  ENNReal.ofReal ((v - lowerSq) / (upperSq - lowerSq)) •
    symmetricTwoPoint (Real.sqrt upperSq)
noncomputable def criticalLaw : Measure ℝ := endpointLaw 1
noncomputable def squaredLaw (μ : Measure ℝ) : Measure ℝ := Measure.map (fun x : ℝ => x ^ 2) μ


noncomputable def counterexampleLaw (R : ℝ) : Measure ℝ :=
  ENNReal.ofReal (R ^ 2 / (R ^ 2 + 1)) • symmetricTwoPoint 1 +
    ENNReal.ofReal (1 / (R ^ 2 + 1)) • symmetricTwoPoint R

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

theorem normalized_quantitative_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) (t : ℝ) :
    fourthDeficit μ*t^4/48000+t^8/64000 ≤
      Real.exp (variance μ*t^2/2)-mgf μ t := by sorry

theorem scaled_quantitative_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b/a ≤ sharpRatio) (t : ℝ) :
    fourthDeficit μ*t^4/48000+a^8/(64000*lowerSq^4)*t^8 ≤
      Real.exp (variance μ*t^2/2)-mgf μ t := by sorry

theorem universal_support_criterion (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b/a ≤ sharpRatio) (t : ℝ) :
    mgf μ t ≤ Real.exp (variance μ*t^2/2) := by sorry

theorem universal_strict (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b/a ≤ sharpRatio) (t : ℝ) (ht : t ≠ 0) :
    mgf μ t < Real.exp (variance μ*t^2/2) := by sorry

theorem variance_proxy_optimality (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b τ : ℝ) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hbound : ∀ t : ℝ, mgf μ t ≤ Real.exp (τ*t^2/2)) : variance μ ≤ τ := by sorry

theorem sharp_universal_ratio (R : ℝ) (hR : sharpRatio < R) :
    IsProbabilityMeasure (counterexampleLaw R) ∧ Symmetric (counterexampleLaw R) ∧
    BandSupport (counterexampleLaw R) 1 R ∧
    ∃ ε > 0, ∀ t : ℝ, 0 < |t| → |t| < ε →
      Real.exp (variance (counterexampleLaw R)*t^2/2) < mgf (counterexampleLaw R) t := by sorry

theorem fourth_deficit_decomposition (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    fourthDeficit μ = 3*(variance μ-1)^2+interiority μ := by sorry

theorem critical_law_rigidity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) :
    fourthDeficit μ = 0 ↔ μ = criticalLaw := by sorry

theorem squared_transport_finiteness (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    (Couplings (squaredLaw μ) (squaredLaw criticalLaw)).Nonempty ∧
    (∀ π ∈ Couplings (squaredLaw μ) (squaredLaw criticalLaw), transportCost π ≠ ⊤) ∧
    wassersteinOneExtended (squaredLaw μ) (squaredLaw criticalLaw) ≠ ⊤ := by sorry

theorem squared_transport_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
      |variance μ-1|+interiority μ/Real.sqrt 6 := by sorry

theorem sharp_local_transport (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hδ : fourthDeficit μ ≤ 1/2) :
    wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
      Real.sqrt (fourthDeficit μ/3) := by sorry

theorem local_transport_attainment (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) :
    let μ := endpointLaw (1+Real.sqrt (δ/3))
    IsProbabilityMeasure μ ∧ Symmetric μ ∧ NormalizedSupport μ ∧ fourthDeficit μ = δ ∧
      wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) = Real.sqrt (δ/3) := by sorry


theorem normalized_sharp_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) (t : ℝ) :
    interiority μ*t^4/24+t^8/25200 ≤
      Real.exp (variance μ*t^2/2)-mgf μ t := by sorry

theorem normalized_sharp_gap_strict (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) (hs : Symmetric μ) (t : ℝ) (ht : t ≠ 0) :
    interiority μ*t^4/24+t^8/25200 <
      Real.exp (variance μ*t^2/2)-mgf μ t := by sorry

theorem scaled_sharp_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 < a) (hμ : BandSupport μ a b) (hs : Symmetric μ)
    (hr : b/a ≤ sharpRatio) (t : ℝ) :
    a^8/(25200*lowerSq^4)*t^8 ≤
      Real.exp (variance μ*t^2/2)-mgf μ t := by sorry

theorem sharp_gap_coefficient_le (c : ℝ)
    (h : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], NormalizedSupport μ →
      Symmetric μ → ∀ t : ℝ,
        c*t^8 ≤ Real.exp (variance μ*t^2/2)-mgf μ t) : c ≤ 1/25200 := by sorry

theorem interiority_gap_coefficient_le (c : ℝ)
    (h : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], NormalizedSupport μ →
      Symmetric μ → ∀ t : ℝ,
        c*interiority μ*t^4 ≤ Real.exp (variance μ*t^2/2)-mgf μ t) : c ≤ 1/24 := by sorry

theorem sharp_gap_intrinsic_coefficient_nonpos (c : ℝ)
    (h : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], NormalizedSupport μ →
      Symmetric μ → ∀ t : ℝ,
        t^8/25200+c*fourthDeficit μ*t^4 ≤ Real.exp (variance μ*t^2/2)-mgf μ t) : c ≤ 0 := by sorry

theorem global_squared_transport (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) ≤
      Real.sqrt (fourthDeficit μ/3) := by sorry

theorem fourth_deficit_range (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NormalizedSupport μ) :
    0 ≤ fourthDeficit μ ∧ fourthDeficit μ ≤ 2*upperSq^2 := by sorry

theorem global_transport_attainment (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 2*upperSq^2) :
    let μ := endpointLaw (1+Real.sqrt (δ/3))
    IsProbabilityMeasure μ ∧ Symmetric μ ∧ NormalizedSupport μ ∧ fourthDeficit μ = δ ∧
      wassersteinOne (squaredLaw μ) (squaredLaw criticalLaw) = Real.sqrt (δ/3) := by sorry

theorem mgf_definition (μ : Measure ℝ) (t : ℝ) :
    mgf μ t = ∫ x, Real.exp (t*x) ∂μ := by sorry

theorem variance_definition (μ : Measure ℝ) :
    variance μ = ∫ x, x^2 ∂μ := by sorry

theorem fourthDeficit_definition (μ : Measure ℝ) :
    fourthDeficit μ = 3*(∫ x, x^2 ∂μ)^2 - ∫ x, x^4 ∂μ := by sorry

theorem interiority_definition (μ : Measure ℝ) :
    interiority μ = ∫ x, (x^2-lowerSq)*(upperSq-x^2) ∂μ := by sorry

theorem symmetric_definition (μ : Measure ℝ) :
    Symmetric μ ↔ Measure.map (fun x : ℝ => -x) μ = μ := by sorry

theorem normalizedSupport_definition (μ : Measure ℝ) :
    NormalizedSupport μ ↔ ∀ᵐ x ∂μ, lowerSq ≤ x^2 ∧ x^2 ≤ upperSq := by sorry

theorem bandSupport_definition (μ : Measure ℝ) (a b : ℝ) :
    BandSupport μ a b ↔ ∀ᵐ x ∂μ, a ≤ |x| ∧ |x| ≤ b := by sorry

theorem criticalLaw_definition :
    criticalLaw = ENNReal.ofReal (1-referenceWeight) • symmetricTwoPoint (Real.sqrt lowerSq) +
      ENNReal.ofReal referenceWeight • symmetricTwoPoint (Real.sqrt upperSq) := by sorry

theorem symmetricTwoPoint_definition (x : ℝ) :
    symmetricTwoPoint x = (1/2:ℝ≥0∞) • Measure.dirac x + (1/2:ℝ≥0∞) • Measure.dirac (-x) := by sorry

theorem counterexampleLaw_definition (R : ℝ) :
    counterexampleLaw R = ENNReal.ofReal (R^2/(R^2+1)) • symmetricTwoPoint 1 +
      ENNReal.ofReal (1/(R^2+1)) • symmetricTwoPoint R := by sorry

theorem squaredLaw_definition (μ : Measure ℝ) :
    squaredLaw μ = Measure.map (fun x : ℝ => x^2) μ := by sorry

theorem wassersteinOne_definition (μ ν : Measure ℝ) :
    wassersteinOne μ ν = (⨅ π ∈ {π : Measure (ℝ × ℝ) |
      IsProbabilityMeasure π ∧ Measure.map Prod.fst π = μ ∧ Measure.map Prod.snd π = ν},
      ∫⁻ z, edist z.1 z.2 ∂π).toReal := by sorry

end SupportCriterion
