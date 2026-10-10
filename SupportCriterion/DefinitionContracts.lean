module

public import SupportCriterion.Sharpness
public import SupportCriterion.Transport

@[expose] public section

/-! Explicit ordinary semantics for the quantities in the principal contract. -/
open MeasureTheory
open scoped ENNReal

namespace SupportCriterion

theorem mgf_definition (μ : Measure ℝ) (t : ℝ) :
    mgf μ t = ∫ x, Real.exp (t*x) ∂μ := rfl

theorem variance_definition (μ : Measure ℝ) :
    variance μ = ∫ x, x^2 ∂μ := rfl

theorem fourthDeficit_definition (μ : Measure ℝ) :
    fourthDeficit μ = 3*(∫ x, x^2 ∂μ)^2 - ∫ x, x^4 ∂μ := rfl

theorem interiority_definition (μ : Measure ℝ) :
    interiority μ = ∫ x, (x^2-lowerSq)*(upperSq-x^2) ∂μ := rfl

theorem symmetric_definition (μ : Measure ℝ) :
    Symmetric μ ↔ Measure.map (fun x : ℝ => -x) μ = μ := Iff.rfl

theorem normalizedSupport_definition (μ : Measure ℝ) :
    NormalizedSupport μ ↔ ∀ᵐ x ∂μ, lowerSq ≤ x^2 ∧ x^2 ≤ upperSq := Iff.rfl

theorem bandSupport_definition (μ : Measure ℝ) (a b : ℝ) :
    BandSupport μ a b ↔ ∀ᵐ x ∂μ, a ≤ |x| ∧ |x| ≤ b := Iff.rfl

theorem criticalLaw_definition :
    criticalLaw = ENNReal.ofReal (1-referenceWeight) • symmetricTwoPoint (Real.sqrt lowerSq) +
      ENNReal.ofReal referenceWeight • symmetricTwoPoint (Real.sqrt upperSq) := rfl

theorem symmetricTwoPoint_definition (x : ℝ) :
    symmetricTwoPoint x = (1/2:ℝ≥0∞) • Measure.dirac x + (1/2:ℝ≥0∞) • Measure.dirac (-x) := rfl

theorem counterexampleLaw_definition (R : ℝ) :
    counterexampleLaw R = ENNReal.ofReal (R^2/(R^2+1)) • symmetricTwoPoint 1 +
      ENNReal.ofReal (1/(R^2+1)) • symmetricTwoPoint R := rfl

theorem squaredLaw_definition (μ : Measure ℝ) :
    squaredLaw μ = Measure.map (fun x : ℝ => x^2) μ := rfl

theorem wassersteinOne_definition (μ ν : Measure ℝ) :
    wassersteinOne μ ν = (⨅ π ∈ {π : Measure (ℝ × ℝ) |
      IsProbabilityMeasure π ∧ Measure.map Prod.fst π = μ ∧ Measure.map Prod.snd π = ν},
      ∫⁻ z, edist z.1 z.2 ∂π).toReal := rfl

end SupportCriterion
