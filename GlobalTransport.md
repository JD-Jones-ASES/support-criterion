# Global sharp transport stability

This proof gives the exact squared-law modulus over the full feasible deficit
range. The general interval inequality, its equality classification, higher
Wasserstein orders and the signed-law consequence are written supplements.
The normalized first-order bound, deficit range and attainment have their
formal status recorded in [VERIFICATION.md](VERIFICATION.md).

## General theorem

Let `0<a<b`, let `Y` be supported almost surely on `[a,b]`, and define

```math
\alpha=\frac{b}{a+b},\qquad p=\frac{a}{a+b},\qquad
\nu_* = \alpha\delta_a+p\delta_b,\qquad
m_* = \int y\,d\nu_*=\frac{2ab}{a+b}.
```

Write `m=EY`, `q=EY²`,

```math
d=\mathbb E[(Y-a)(b-Y)]=(a+b)m-ab-q\ge0,
\qquad \sigma^2=q-m^2\ge0.
```

Then

```math
\boxed{W_1(\mathcal L(Y),\nu_*)^2
\le m^2-\frac{4ab}{(a+b)^2}q.}
```

Equality holds if and only if `Y` is almost surely constant or `Y` is supported on `{a,b}` almost surely.

The proof gives an explicit coupling cost `C` and the stronger comparison

```math
W_1(\mathcal L(Y),\nu_*)^2\le C^2
\le m^2-\frac{4ab}{(a+b)^2}q,
```

with an exact nonnegative remainder in the second inequality.

### Upper-mean branch

Suppose `m≥m*`. Conditional on `Y=y`, set `Z=b` with probability

```math
\gamma(y)=\frac{p(y-a)}{m-a},
```

and set `Z=a` otherwise. The denominator is positive because

```math
m-a\ge m_*-a=p(b-a)>0.
```

It follows that `0≤γ(y)≤1` on `[a,b]`. Also `Eγ(Y)=p`, so `Z` has law `ν*`. Such a coupling can be constructed on the product with an independent uniform random variable, or directly as the measure-valued endpoint kernel.

Its cost is

```math
\begin{aligned}
C_+&=\mathbb E\bigl[(1-\gamma(Y))(Y-a)+\gamma(Y)(b-Y)\bigr]\\
&=m-\frac{2p(q-am)}{m-a}\\
&=m-m_*+\frac{2pd}{m-a}.
\end{aligned}
```

In particular `C+≥0`. Expanding both sides and using `p=a/(a+b)` yields

```math
\boxed{
m^2-\frac{4ab}{(a+b)^2}q-C_+^2
=\frac{4p^2d\sigma^2}{(m-a)^2}\ge0.}
```

Since this is the cost of an actual coupling, `W₁≤C+`, proving the result in this branch.

### Lower-mean branch

Suppose `m≤m*`. Conditional on `Y=y`, set `Z=a` with probability

```math
\eta(y)=\frac{\alpha(b-y)}{b-m},
```

and set `Z=b` otherwise. Here

```math
b-m\ge b-m_* = \alpha(b-a)>0,
```

so `0≤η≤1`, and `Eη(Y)=α`. The coupling again has second marginal `ν*`.

Its cost is

```math
C_-=m_*-m+\frac{2\alpha d}{b-m},
```

and the exact remainder is

```math
\boxed{
m^2-\frac{4ab}{(a+b)^2}q-C_-^2
=\frac{4\alpha^2d\sigma^2}{(b-m)^2}\ge0.}
```

This proves the other branch. Both formulas are valid and agree at `m=m*`.

### Equality classification

If equality holds in the final transport inequality, then the relevant remainder vanishes. All prefactors and denominators are strictly positive. Hence `dσ²=0`.

If `σ²=0`, then `Y` is almost surely constant. If `d=0`, the nonnegative random variable `(Y−a)(b−Y)` vanishes almost surely, which means `Y∈{a,b}` almost surely.

Both classes do attain equality:

- If `Y≡y`, its coupling to `ν*` is fixed, with cost `α(y−a)+p(b−y)=(b−a)y/(a+b)`. Substitution gives equality.
- For an endpoint law of mean `m`, `q=(a+b)m−ab`, and the exact transport cost is `|m−m*|`. Any coupling costs at least the difference of means, and moving only the surplus endpoint mass attains that cost. Again substitution gives equality.

This also shows that the affine coupling is itself optimal for every equality law, even though it need not be optimal for a general law.

## Specialization to support-criterion

Take

```math
A=3-\sqrt6,\quad B=3+\sqrt6,\quad
Y=X^2,\quad m=v=\mathbb EX^2,
```

so `A+B=6`, `AB=3`, and

```math
\alpha=B/6,\quad p=A/6,\quad m_*=1,\quad
\nu_*=\mathcal L(X_0^2),\quad \frac{4AB}{(A+B)^2}=\frac13.
```

With `δ=3v²−EX⁴`, the global theorem is

```math
\boxed{W_1(\mathcal L(X^2),\mathcal L(X_0^2))
\le\sqrt{\delta/3}.}
```

There is no small-deficit assumption. Symmetry is not needed for the squared-law statement.

The exact coupling-cost identities become

```math
\delta-3C_+^2=
\frac{12p^2d\,\mathbb E[(Y-v)^2]}{(v-A)^2}
\qquad(v\ge1),
```

and

```math
\delta-3C_-^2=
\frac{12\alpha^2d\,\mathbb E[(Y-v)^2]}{(B-v)^2}
\qquad(v\le1).
```

The equality cases are exactly the endpoint-supported squared laws and the constant squared laws. For symmetric `X`, these correspond respectively to arbitrary symmetric mixtures on `±√A,±√B`, and fair two-point laws `±√y` with `y∈[A,B]`.

### Exact global deficit range and modulus

Every admissible deficit belongs to

```math
0\le\delta\le 2B^2=30+12\sqrt6.
```

Indeed `q≥v²` gives `δ≤2v²≤2B²`. Conversely, for any `δ` in this interval, choose the endpoint law with mean

```math
v=1+\sqrt{\delta/3}.
```

The identity `3(B−1)²=2B²` ensures `1≤v≤B`, so the endpoint law exists. It has deficit `3(v−1)²=δ` and exact transport cost `v−1=√(δ/3)`.

Thus the sharp modulus at every feasible deficit is exactly `√(δ/3)`. The earlier local bound follows as a special case. Retaining the exact
affine coupling cost removes the small-deficit restriction.

### Every finite Wasserstein order

Let `L=B−A=2√6`. For every real `r≥1`, bounded support and an optimal `W₁` coupling give

```math
W_r(\mathcal L(Y),\nu_*)^r
\le L^{r-1}W_1(\mathcal L(Y),\nu_*)
\le L^{r-1}\sqrt{\delta/3}.
```

An optimal `W₁` coupling exists here; it can be exhibited by assigning the lowest `α` quantile of `Y` to `A` and the highest `p` quantile to `B`, splitting a boundary atom as needed. Equivalently, one may choose couplings with costs decreasing to the `W₁` infimum and apply `|y-z|^r≤L^(r−1)|y-z|` before taking the infimum, which avoids using existence.

Therefore

```math
\boxed{W_r(\mathcal L(Y),\nu_*)
\le L^{1-1/r}(\delta/3)^{1/(2r)}\qquad(r\ge1).}
```

At every feasible deficit, the endpoint law with mean `1+√(δ/3)` attains this bound: the required displaced mass is `(v−1)/L` and it travels distance `L`. Thus the bound is the exact global modulus for every finite Wasserstein order.

For `r>1`, the equality cases are exactly the endpoint laws. If equality holds, equality must also hold in the `W₁` estimate, leaving only endpoint laws or point masses. For an interior point mass, all positive distances are strictly less than `L`, making the power inequality strict. Endpoint point masses are already included among endpoint laws.

There is no vanishing uniform `W∞` modulus: any endpoint law with a different endpoint weight from `ν*` has `W∞=L`, even for arbitrarily small positive deficit. The exact uniform modulus is zero at deficit zero and `L` at every feasible positive deficit.

### Unsquared consequence

For symmetric laws, couple signs identically and apply the `1/(2√A)` Lipschitz bound for the square-root map on `[A,B]`. This gives

```math
W_1(\mathcal L(X),\mathcal L(X_0))
\le\frac{1}{2\sqrt A}\sqrt{\delta/3}
```

for all admissible deficits. No optimality is asserted for this final factor.

## Mathematical context

The general inequality refines the classical Kantorovich moment bound by
retaining an explicit transport term. The exact remainders prove the result
using only nonnegative interiority and variance. [Sources.md](Sources.md)
records the bounded literature comparison; no worldwide priority claim or
human specialist review is asserted.
