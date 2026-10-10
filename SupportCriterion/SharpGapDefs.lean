module

public import SupportCriterion.CertificateDefs
public import SupportCriterion.EndpointMoments

@[expose] public section

/-! Sixth endpoint comparison coefficient and its rational compactification.
The sharp eighth-order estimate is separate from the older intrinsic-deficit estimate. -/
namespace SupportCriterion

lemma endpointMoment_six (v : ℝ) : endpointMoment v 6 = 5346*v-2943 := by
  rw [show 6=4+2 from rfl,endpointMoment_rec,endpointMoment_five,endpointMoment_four]
  ring

noncomputable def sharpGapPolynomial (v z : ℝ) : ℝ :=
  gapPolynomial v z + (v^6 - 198*v/385 + 109/385)*z^4/720

noncomputable def sharpCompactPolynomial (w r : ℝ) : ℝ :=
  (1-r)^4/2 + 5/4*(-4/5+3*w-w^2)*r*(1-r)^3 +
  (75/32*((1-w)^4-12*(1-w)/7+33/35)-1/28)*r^2*(1-r)^2 +
  225/64*w*((1-w)^5-109*(1-w)/105+4/7)*r^3*(1-r) +
  1125/256*w^2*((1-w)^6-198*(1-w)/385+109/385)*r^4

end SupportCriterion
