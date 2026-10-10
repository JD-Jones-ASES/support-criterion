module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

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

end SupportCriterion
