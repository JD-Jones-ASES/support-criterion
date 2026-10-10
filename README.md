# support-criterion

A sharp universal support criterion for symmetric sub-Gaussian laws, with
quantitative separation, critical-law rigidity and sharp local transport stability.

If a real random variable has a law symmetric about zero and
`0 < a ≤ |X| ≤ b` almost surely, then

```math
\frac ba\le\sqrt3+\sqrt2
\quad\Longrightarrow\quad
\mathbb E e^{tX}\le\exp\!\left(\frac{t^2\mathbb EX^2}{2}\right)
\qquad(t\in\mathbb R).
```

The proxy is the actual variance and is optimal. The inequality is strict
for every nonzero `t`. Every larger support ratio admits an explicit
symmetric four-point counterexample. The theorem includes discrete,
continuous and mixed probability laws.

Set `A = 3−√6`, `B = 3+√6`. For normalized squared support in `[A,B]`,
write `v = EX²`, `δ = 3v²−EX⁴`, and `d = E[(X²−A)(B−X²)]`. The package gives

```math
\delta=3(v-1)^2+d,\qquad
 e^{vt^2/2}-\mathbb Ee^{tX}
 \ge\frac{\delta t^4}{48000}+\frac{t^8}{64000}.
```

Zero fourth deficit identifies one probability law: the four-node Gaussian
quadrature law `X₀`, with total outer-node weight `(√6−2)/(2√6)`.
For `0 ≤ δ ≤ 1/2`, the squared laws obey

```math
W_1(\mathcal L(X^2),\mathcal L(X_0^2))\le\sqrt{\delta/3}.
```

This transport bound is attained for every deficit in the stated interval.
The support ratio and transport modulus are sharp; the displayed MGF
constants are certified and are not asserted optimal.

The proof reduces arbitrary laws to endpoint mixtures by a strengthened
convex chord inequality. An exact moment recurrence controls the entire
infinite tail; a rational Bernstein certificate handles the remaining
polynomial. The transport proof constructs a coupling and bounds the
ordinary Wasserstein distance defined by the infimum over all couplings.

- [Note.md](Note.md): theorem statements and explanation.
- [Proof.md](Proof.md): full mathematical argument and quadrature connection.
- [Sources.md](Sources.md): primary sources and precise comparisons.
- [Applications.md](Applications.md): concentration applications.
- [Asymptotics.md](Asymptotics.md): written local worst-law asymptotics.
- [SupportCriterionChallenge.lean](SupportCriterionChallenge.lean): independent Mathlib-only principal statements and concrete definitions.
- [SupportCriterionSolution.lean](SupportCriterionSolution.lean): proved implementation.
- [VERIFICATION.md](VERIFICATION.md): exact build, contract and kernel-replay evidence.
- [Disclosure.md](Disclosure.md): production and review disclosure.

The Lean version and all dependencies are pinned. Build and replay the exact
supporting certificate with:

```sh
lake build
python3 scripts/generate_certificate.py --check
python3 scripts/independent_certificate_check.py
python3 scripts/check_sources.py
python3 scripts/audit_axioms.py
```

The repository is private. Publication and submission remain separate steps.
