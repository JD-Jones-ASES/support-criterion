# Conditional symmetry and variance-based concentration

These written applications are outside the principal formal contract. They
are consequences of the
[sharp support theorem](Proof.md), using the standard exponential
supermartingale argument. The concentration machinery is classical;
the support criterion makes
the actual conditional variance a valid proxy. Write $R_*=\sqrt3+\sqrt2$.

## Random amplitudes

Every symmetric real random variable with $\Pr(X=0)=0$ has the same law as
$\varepsilon H$, where $H=|X|>0$ and the independent sign
$\varepsilon$ takes each value $\pm1$ with probability one half.
Indeed symmetry gives, for every Borel set $C\subset(0,\infty)$,
$\Pr(H\in C,\operatorname{sgn}X=1)=\Pr(H\in C)/2$.

Consequently an arbitrary mixture of centered two-point laws is strictly
sub-Gaussian whenever all amplitudes lie in a band of ratio at most
$\sqrt3+\sqrt2$. Its exact proxy is $\mathbb EH^2$, although the
component variances $H^2$ need not agree. Merely averaging the usual
bound $\cosh(tH)\le e^{t^2H^2/2}$ would not prove this, because
Jensen's inequality goes in the wrong direction for that average.

## Independent sums and linear forms

Let $X_1,\ldots,X_n$ be independent symmetric variables, each obeying
its own positive support band with ratio at most $R_*$. For every
deterministic real coefficient vector $c$, multiplication of the
individual MGF bounds gives


```math
\mathbb E\exp\!\left(t\sum_i c_iX_i\right)
\le\exp\!\left(\frac{t^2}{2}\sum_i c_i^2\mathbb EX_i^2\right).
```


The proxy on the right is the variance of the sum, and is optimal by its
second-order Taylor coefficient. Zero coefficients cause no difficulty.
For $V=\sum_i c_i^2\mathbb EX_i^2>0$ and $u>0$, the usual Chernoff
argument yields


```math
\Pr\!\left(\left|\sum_i c_iX_i\right|\ge u\right)
\le2e^{-u^2/(2V)}.
```


The sum need not satisfy a two-band support condition itself. For example,
two independent fair signs have a sum with an atom at zero. The extension
uses independence and multiplication of MGFs, not preservation of bands.

## Conditionally symmetric increments

Let $(\mathcal F_n)$ be a filtration and let $D_n$ be integrable,
$\mathcal F_n$-measurable real increments. Assume each conditional law
of $D_n$ given $\mathcal F_{n-1}$ is symmetric about zero and has a
regular conditional distribution. Suppose finite, positive,
$\mathcal F_{n-1}$-measurable radii $a_n,b_n$ satisfy almost surely


```math
a_n\le |D_n|\le b_n,\qquad b_n/a_n\le R_*.
```


Set


```math
S_n=\sum_{i=1}^n D_i,\qquad
v_n=\mathbb E[D_n^2\mid\mathcal F_{n-1}],\qquad
V_n=\sum_{i=1}^n v_i.
```


The conditional variances are finite almost surely since
$v_n\le b_n^2$. Symmetry and integrability give
$\mathbb E[D_n\mid\mathcal F_{n-1}]=0$. Applying the support theorem
to almost every conditional law, for each fixed real $\lambda$, gives


```math
\mathbb E[e^{\lambda D_n}\mid\mathcal F_{n-1}]
\le e^{\lambda^2v_n/2}.
```


The same reasoning permits predictable real weights $c_n$: replace
$D_n$ by $c_nD_n$, on the event $c_n\ne0$, and use zero directly
on its complement. Assume integrability when calling the weighted sum a
martingale; the conditional MGF and nonnegative-process argument otherwise
can be stated without this terminology.

For fixed $\lambda$, the process


```math
M_n(\lambda)=\exp\{\lambda S_n-\lambda^2V_n/2\},\qquad M_0=1,
```


is a nonnegative supermartingale. To see this, factor out the measurable
$M_{n-1}$ and use the conditional MGF bound. Conditional expectation for nonnegative variables
is legitimate before integrability is known, and induction gives
$\mathbb EM_n\le1$, establishing integrability as well.

For every fixed $\lambda>0$ and $0<\delta<1$, Ville's inequality
therefore proves


```math
\Pr\!\left(\exists n\ge1:
S_n\ge\frac\lambda2V_n+\frac{\log(1/\delta)}\lambda\right)
\le\delta.
```


One can prove the required version of Ville directly: stop at the first
crossing of $M_n\ge1/\delta$, truncate the stopping time at a
deterministic $N$, use $\mathbb EM_{\tau\wedge N}\le1$, and let
$N$ increase. No unbounded optional-stopping assertion is assumed.

In particular, for deterministic $u>0$, $v>0$, choose
$\lambda=u/v$. The event $S_n\ge u,V_n\le v$ forces
$M_n\ge e^{u^2/(2v)}$, giving


```math
\Pr(\exists n\ge1:S_n\ge u,\ V_n\le v)\le e^{-u^2/(2v)}.
```


Applying the same argument to $-S_n$ gives the two-sided version with
factor two. The variance budget $v$ in this crossing bound is a fixed deterministic value;
one cannot replace it after observing the path and keep the same bound
without further argument. The preceding affine boundary in $V_n$ is already valid at every
time simultaneously.

## What this connection adds

The variance process here is the sum of **conditional variances**. General
conditional symmetry also gives classical self-normalized bounds involving
the sum of realized squared increments, which is a different random
process. The support-ratio hypothesis supplies the conditional MGF bound with the former.
Neither process is universally smaller than the other on each sample path.

Howard, Ramdas, McAuliffe and Sekhon,
[arXiv:1808.03204v8](https://arxiv.org/abs/1808.03204v8),
*Time-uniform Chernoff bounds via nonnegative supermartingales* (journal
version: Probability Surveys 17, 2020), provides the general framework:
Definition 1, Lemma 1 and equation (2.12); Lemma 3(d) treats conditional
symmetry with realized quadratic variation. The arXiv version inspected
was revised 2025-12-17. The displayed consequences above are derived here
from the conditional MGF bound.

These results do not remove symmetry, cover arbitrary dependence, prove
matrix concentration, or give a plug-in bound for estimated variance.
Those would require separate statements and arguments.
