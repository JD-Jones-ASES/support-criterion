module

public import Mathlib.Tactic
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! Exact polynomial underlying the uniform endpoint MGF estimate. -/
namespace SupportCriterion

noncomputable def gapPolynomial (v z : ℝ) : ℝ :=
  (v - 1)^2 / 2 + (v^3 - 11*v/5 + 6/5)*z/6 +
  (v^4 - 12*v/7 + 33/35)*z^2/24 + (v^5 - 109*v/105 + 4/7)*z^3/120

noncomputable def compactPolynomial (w r : ℝ) : ℝ :=
  1/2 - 73*r/30 + 23*r^2/6 - 19*r^3/10 +
  w*(7*r/2 - 35*r^2/3 + 4361*r^3/450) +
  w^2*(-7*r/6 + 175*r^2/12 - 22267*r^3/900) +
  w^3*(-49*r^2/6 + 147*r^3/4) + w^4*(49*r^2/24 - 245*r^3/8) +
  343*w^5*r^3/24 - 343*w^6*r^3/120

noncomputable def shiftedPolynomial (w r : ℝ) : ℝ :=
  compactPolynomial w r - ((1-r)^3 + 49*r^2*(1-r))/4000

end SupportCriterion
