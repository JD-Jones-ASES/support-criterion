module

public import SupportCriterion.EndpointLaw
public import SupportCriterion.LawBasics

@[expose] public section

open MeasureTheory

namespace SupportCriterion

lemma endpointLaw_mgf (v : ℝ) (hv : lowerSq ≤ v ∧ v ≤ upperSq) (t : ℝ) :
    mgf (endpointLaw v) t = endpointMGF v t := by
  unfold mgf
  rw [integral_endpointLaw _ v hv]
  simp only [mul_neg, endpointMGF, Real.cosh_eq]

lemma moment_odd_eq_zero {μ : Measure ℝ} (hs : Symmetric μ) (n : ℕ) :
    moment μ (2*n+1) = 0 := by
  have hn := integral_neg_eq hs (f := fun x => x^(2*n+1)) (by fun_prop)
  have hf : (fun x : ℝ => (-x)^(2*n+1)) = (fun x : ℝ => -(x^(2*n+1))) := by
    funext x
    simp [pow_add, pow_mul]
  rw [hf, integral_neg] at hn
  unfold moment
  linarith

end SupportCriterion
