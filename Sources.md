# Mathematical sources and scope

Primary-source audit checked 2026-10-10. The statements below distinguish
the universal support theorem from related moment, mixture, and
quadrature results. This is a bounded literature comparison.

The theorem and its explanation are in [Note.md](Note.md); the full
mathematical argument is in [Proof.md](Proof.md). The sources below provide
the related published results and background.

## Strict sub-Gaussianity

**Arbel, Marchal, Nguyen.** *On strict sub-Gaussianity, optimal proxy
variance and symmetry for bounded random variables*, ESAIM: Probability
and Statistics 24 (2020), 39–55.
[Published record](https://www.numdam.org/articles/10.1051/ps/2019018/);
[arXiv:1901.09188v1](https://arxiv.org/pdf/1901.09188v1).

Proposition 3.2 gives necessary cumulant conditions; Proposition 3.3 gives
Gaussian domination of all even moments as a sufficient condition for
symmetric laws. The universal band theorem requires more than that
sufficient condition: its endpoint law of variance `9/10` satisfies
`E X⁶ = 117/10 > 15(9/10)³`, while the full MGF remains dominated.

**Bobkov, Chistyakov, Götze.** *Strictly subgaussian probability
distributions*, Electronic Journal of Probability 29 (2024), paper 62.
[Published record](https://doi.org/10.1214/24-EJP1120);
[arXiv:2308.01749v1](https://arxiv.org/pdf/2308.01749v1).

Proposition 2.4 proves mixture closure for centered strictly sub-Gaussian
components of the **same variance**. Theorems 1.2–1.3 instead impose
conditions on complex zeros of characteristic functions. The support
criterion here allows arbitrary amplitude mixtures with varying component
variances; neither cited result directly provides that conclusion.

**Ostrovsky, Sirota.** *Subgaussian and strictly subgaussian random
variable* (2014), [arXiv:1406.3933v1](https://arxiv.org/pdf/1406.3933v1).

Theorem 2.1 also requires common variance for mixture closure. Its
discussion records the symmetric three-point example, including the
threshold for its mass at zero. Mixture closure must retain its variance
hypothesis.

**Atouani, Marchal, Arbel.** *Optimal sub-Gaussian variance proxy for
3-mass distributions* (2025),
[arXiv:2510.06132v1](https://arxiv.org/pdf/2510.06132v1).

Theorem 3.1 treats masses `p,1−2p,p` on `−a,0,a`; the optimal proxy is
the variance exactly when `p≥1/6`. This is a different support geometry.
The present theorem does not classify all three-point or four-point laws.

## Fourth moments and the support threshold

**Fujii, Izumino, Nakamoto, Seo.** *Operator inequalities related to
Cauchy–Schwarz and Hölder–McCarthy inequalities*, Nihonkai Mathematical
Journal 8 (1997), 117–122.
[Author-uploaded paper](https://www.researchgate.net/publication/254210690_Operator_Inequalities_Related_To_Cauchy-Schwarz_And_Holder-McCarthy_Inequalities).

The introduction records the Kantorovich inequality and an equivalent
second-moment form. Its scalar specialization gives, for `0<m≤Y≤M`,

```math
\frac{\mathbb EY^2}{(\mathbb EY)^2}
\le\frac{(M+m)^2}{4mM}.
```

This follows directly from `EY²≤(M+m)EY−mM` and maximizing over the mean.
Taking `Y=X²` yields the threshold `(b/a)²≤5+2√6` for a universal
nonpositive fourth cumulant. The support theorem establishes sufficiency
for the entire MGF under symmetry; a nonpositive fourth cumulant alone
does not suffice for general laws.

## Gaussian quadrature

**Wu, Yang.** *Polynomial methods in statistical inference: theory and
practice*, Foundations and Trends in Communications and Information
Theory 17(4) (2020).
[Publisher record](https://doi.org/10.1561/0100000095);
[arXiv:2104.07317v2](https://arxiv.org/pdf/2104.07317v2).

In the pinned PDF, Remark 2.7.2 identifies quadrature nodes through
orthogonal polynomials, and §2.7.1, Lemma 2.7.3 proves Gaussian moment
domination and 1-sub-Gaussianity of the Gaussian quadrature law. These
statements apply directly to the distinguished four-node law here.
The arXiv HTML conversion renumbers these as Remark 2.7.7 and Lemma 2.7.8;
the citations above use the PDF numbering. Arbitrary endpoint weights do
not retain the quadrature moment identities.

**Kotekal.** *Variance estimation in compound decision theory under
boundedness*, NeurIPS 2024.
[Published paper](https://papers.nips.cc/paper_files/paper/2024/file/a7667ee5d545a43d2f0fda98863c260e-Paper-Conference.pdf).
Appendix D, Lemmas 6–7 records the node identification and Gaussian moment
domination, citing Wu–Yang.

**NIST Digital Library of Mathematical Functions.**
[§3.5(v)](https://dlmf.nist.gov/3.5#v) gives Gaussian quadrature exactness
and remainder formulas; [§18.3](https://dlmf.nist.gov/18.3) distinguishes
Hermite normalizations. The relevant polynomial is the probabilists'
`He₄(x)=x⁴−6x²+3`, for Gaussian weight `exp(−x²/2)`.

## Concentration consequences

**Howard, Ramdas, McAuliffe, Sekhon.** *Time-uniform Chernoff bounds via
nonnegative supermartingales*, Probability Surveys 17 (2020).
[arXiv:1808.03204v8](https://arxiv.org/pdf/1808.03204v8).

Definition 1, Lemma 1, and equation (2.12) supply the general exponential
supermartingale framework. Lemma 3(d) treats conditional symmetry using
realized squared increments. The support criterion permits actual
conditional variances in the Gaussian MGF bound. Conditional and
time-uniform applications remain explanatory material unless separately
listed among the verified declarations.
