# Optimal eighth-order MGF separation

Let `A=3−√6`, `B=3+√6`, and let `X` have any symmetric probability law
with `A≤X²≤B` almost surely. Write `v=EX²` and
`d=E[(X²−A)(B−X²)]`. Then for every real `t`,

```math
 e^{vt^2/2}-\mathbb Ee^{tX}
 \ge \frac{d t^4}{24}+\frac{t^8}{25200}.
```

Both coefficients are optimal and hold together. The proof below establishes
the inequality for all parameters; the exact finite certificate is not a
numerical sample. [VERIFICATION.md](VERIFICATION.md) records the separate
formal and replay status. The earlier intrinsic-deficit bound in
[Proof.md](Proof.md#8-a-global-quantitative-gap-for-every-law) is retained.

## Endpoint polynomial and the entire tail

Let `M_v(t)` be the MGF of the symmetric endpoint law with second moment `v`.
The endpoint moments and comparison coefficients from [Proof.md](Proof.md) are

```math
 s_0=1,\quad s_1=v,\quad s_n=6s_{n-1}-3s_{n-2},\qquad
 f_n(v)=v^n-\frac{s_n(v)}{(2n-1)!!}.
```

In addition to the coefficients through degree five already used there,

```math
 f_6(v)=v^6-\frac{198}{385}v+\frac{109}{385}.
```

Put `z=t²/2` and

```math
 P_6(v,z)=\sum_{n=2}^6\frac{f_n(v)}{n!}z^{n-2},\qquad
 Q(v,z)=P_6(v,z)-\frac{z^2}{1575}.
```

The recurrence proof gives `f_n(v)>0` for every `n≥5` and `v∈[A,B]`.
Absolute convergence therefore gives

```math
 e^{vz}-M_v(t)
 =z^2P_6(v,z)+\sum_{n=7}^{\infty}\frac{f_n(v)}{n!}z^n
 \ge z^2P_6(v,z).
```

It remains to show `Q≥0`. For `v≥1`, all coefficients are nonnegative
and `f₄(v)≥8/35`, so the stronger endpoint gap `z⁴/105` holds.

## Exact certificate for the remaining interval

For `11/20≤v<1`, put `w=1−v` and

```math
 r=\frac{z}{z+(15/2)w},\qquad
 R(w,r)=\frac{(1-r)^4}{w^2}
 Q\!\left(1-w,\frac{15wr}{2(1-r)}\right).
```

Cancellation yields a polynomial of bidegree `(8,4)`. Its useful factored form is

```math
\begin{aligned}
R(w,r)={}&\tfrac12(1-r)^4
 +\tfrac54(-\tfrac45+3w-w^2)r(1-r)^3\\
 &+\left(\tfrac{75}{32}f_4(1-w)-\tfrac1{28}\right)r^2(1-r)^2\\
 &+\tfrac{225}{64}w f_5(1-w)r^3(1-r)
 +\tfrac{1125}{256}w^2 f_6(1-w)r^4.
\end{aligned}
```

Divide `[0,9/20]×[0,1]` into the 64 closed cells

```math
 [9i/160,9(i+1)/160]\times[j/8,(j+1)/8],\qquad 0\le i,j<8.
```

If the local monomial coefficients are `c_ab`, the degree-`(8,4)`
tensor Bernstein coefficients are

```math
 \beta_{k\ell}=\sum_{a\le k,\ b\le\ell}
 c_{ab}\frac{\binom{k}{a}}{\binom8a}
       \frac{\binom{\ell}{b}}{\binom4b}.
```

All 2,880 coefficients are nonnegative. Exactly seven vanish; the minimum
positive coefficient is `27/1835008`. Their canonical coefficient digest is
`e94c6c378471cf27f639f7aef4de4a114683a37136d6ebd98a84eda1edfded61`.
The generator reconstructs the polynomial and re-expands each cell identity.
The independent checker instead reduces powers modulo `y²−6y+3`, interpolates
in the tensor Bernstein basis, and uses de Casteljau subdivision. Both use
exact rational arithmetic and check the complete cell identities. The digest
identifies data; the mathematical premises are the identities and signs.

Nonnegative basis functions prove `R≥0` everywhere in the closed rectangle.
For every finite `z≥0` and `w>0`, the inverse substitution has `0≤r<1`.
The positive factor `w²/(1−r)⁴` then gives `Q≥0`. At `w=0` use directly

```math
 Q(1,z)=\frac{2z^2}{225}+\frac{z^3}{225}+\frac{37z^4}{34650}\ge0.
```

The polynomial boundary is independently consistent with

```math
 R(0,r)=\tfrac12(1-r)^2(1-2r)^2.
```

The edge `r=1` has no finite preimage for positive `w`; `z=0` maps to `r=0`.
Since `A>11/20`, the certificate covers all required variances. Thus

```math
 e^{vt^2/2}-M_v(t)\ge\frac{z^4}{1575}=\frac{t^8}{25200}.
```

The positive tail makes this endpoint inequality strict for `t≠0`.

## Every law and the original scale

The strengthened chord reduction already proves

```math
 M_v(t)-\mathbb Ee^{tX}\ge\frac{d t^4}{24}.
```

Adding gives the claimed bound for arbitrary discrete, continuous or mixed
symmetric laws. Applying it to `√A X/a` at parameter `at/√A` also gives

```math
 e^{t^2\mathbb EX^2/2}-\mathbb Ee^{tX}
 \ge \frac{a^8}{25200(3-\sqrt6)^4}t^8
```

whenever `0<a≤|X|≤b` and `b/a≤√3+√2`. This pure eighth-order coefficient
is sharp uniformly at the critical support ratio.

## Optimality and the intrinsic-deficit obstruction

For the eighth-order coefficient, choose endpoint laws depending on `t`, with

```math
 v_t=1-\frac{t^2}{15}=1-\frac{2z}{15}.
```

For all sufficiently small nonzero `t` these are admissible and have `d=0`.
The convergent endpoint expansion gives

```math
 e^{v_tt^2/2}-M_{v_t}(t)=\frac{t^8}{25200}+O(t^{10}),
```

because the coefficient of `z⁴` is

```math
 \frac{2}{225}-\frac{4}{225}+\frac1{105}=\frac1{1575}.
```

Consequently every universal eighth-order coefficient is at most `1/25200`.
For the interiority coefficient, fair `X=±1` has `v=1`, `d=2`, and

```math
 e^{t^2/2}-\cosh t=\frac{t^4}{12}+O(t^6).
```

A universal coefficient of `dt⁴` is therefore at most `1/24`.

These sharp coefficients cannot be inserted into the older intrinsic bound
by replacing its denominator `64000`. Along the endpoint path,
`δ_t=3(v_t−1)²=t⁴/75`. A proposed lower bound
`t⁸/25200+cδ_t t⁴` with `c>0` would imply, after division by `t⁸` and passage
to zero, `1/25200≥1/25200+c/75`. Thus the sharp interiority bound and the
older intrinsic bound are separate valid estimates; their maximum is valid.
The more detailed fixed-parameter optimizer expansion remains in
[Asymptotics.md](Asymptotics.md).
