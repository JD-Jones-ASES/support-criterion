# A sharp universal support criterion

Let a real random variable `X` have a law symmetric about zero. Suppose
`0 < a ≤ |X| ≤ b` almost surely. This project establishes that

```math
b/a\le \sqrt3+\sqrt2
\quad\Longrightarrow\quad
\mathbb E e^{tX}\le \exp(t^2\mathbb EX^2/2)
\qquad(t\in\mathbb R).
```

The ratio is the exact universal threshold: every larger ratio admits a
symmetric four-point counterexample. The Gaussian variance proxy is the
actual variance, and the displayed inequality is strict for every nonzero
`t`. Arbitrary discrete, continuous, and mixed laws are included.

The conventional term *strictly sub-Gaussian* means that the optimal proxy
equals the variance. Strict inequality away from zero is an additional
conclusion here. The theorem concerns amplitude mixtures: mixing fair
signs with different amplitudes retains the variance proxy whenever the
amplitudes lie in the specified band.

## Normalization and quantitative statements

Set

```math
A=3-\sqrt6,\qquad B=3+\sqrt6,\qquad
v=\mathbb EX^2,\qquad
d=\mathbb E[(X^2-A)(B-X^2)],\qquad
\delta=3v^2-\mathbb EX^4.
```

When `A ≤ X² ≤ B` almost surely,

```math
\delta=3(v-1)^2+d\ge0.
```

The sharp quantitative estimate is

```math
e^{vt^2/2}-\mathbb Ee^{tX}
\ge \frac{d}{24}t^4+\frac{t^8}{25200}.
```

Both coefficients are optimal. [SharpGap.md](SharpGap.md) gives the exact
certificate and limiting examples. The separate intrinsic-deficit estimate is

```math
e^{vt^2/2}-\mathbb Ee^{tX}
\ge \frac{\delta}{48000}t^4+\frac{t^8}{64000}.
```

The constants in this intrinsic estimate are certified; no optimality is
asserted for them. In particular, the sharp eighth-order constant cannot
replace `1/64000` while retaining a positive `δt⁴` term. In the original scale its right side is

```math
\frac{3(\mathbb EX^2)^2-\mathbb EX^4}{48000}t^4
+\frac{a^8}{64000(3-\sqrt6)^4}t^8.
```

The only symmetric law in the normalized bands with `δ = 0` is

```math
\Pr(X_0=\pm\sqrt A)=\frac{1-p_0}{2},\qquad
\Pr(X_0=\pm\sqrt B)=\frac{p_0}{2},\qquad
p_0=\frac{\sqrt6-2}{2\sqrt6}.
```

This is equality in the fourth-moment inequality. Its MGF inequality is
still strict at every nonzero parameter.

For the ordinary Wasserstein distance of order one, the sharp global
stability statement concerns the **squared laws**:

```math
0\le\delta\le30+12\sqrt6
\quad\Longrightarrow\quad
W_1(\mathcal L(X^2),\mathcal L(X_0^2))\le\sqrt{\delta/3}.
```

This is the entire feasible deficit range. At every value an endpoint law
attains equality, so the displayed modulus is exact throughout. Symmetry
is unnecessary for this squared-law theorem.
Here `W₁` is the infimum of expected absolute distance over all couplings
of the two laws; bounded support makes its cost finite.

## Proof of the universal bound

Scaling by `√A/a` puts the squared variable in `[A,B]`, since
`B/A = (√3+√2)²`. For fixed `t`, the function

```math
g_t(y)=\cosh(t\sqrt y)=\sum_{n\ge0}\frac{t^{2n}y^n}{(2n)!}
```

is convex for nonnegative `y`. Its chord, integrated using symmetry,
reduces the MGF to that of the symmetric law on `±√A, ±√B` with the same
second moment `v`. Denote this endpoint MGF by `M_v(t)` and its even
moments by `s_n`. They satisfy

```math
s_0=1,\quad s_1=v,\quad s_n=6s_{n-1}-3s_{n-2}.
```

Write `f_n(v) = vⁿ − s_n/(2n−1)!!`. Then

```math
f_2=(v-1)^2,\quad
f_3=v^3-11v/5+6/5,\quad
f_4=v^4-12v/7+33/35,\quad
f_5=v^5-109v/105+4/7.
```

Tangent bounds for `v⁵` at `2/3` and `3/4` show that `f₅ > 0` for
nonnegative `v`, splitting at `v=4/5`. Since `B/A < 11`, the estimate
`s_{n+1} ≤ B s_n` propagates `f_n > 0` to all `n ≥ 5` and all
`v ∈ [A,B]`. With `z=t²/2`, the convergent MGF difference is

```math
e^{vz}-M_v(t)=\sum_{n\ge2}\frac{f_n(v)}{n!}z^n.
```

For `v ≥ 1` all these coefficients are nonnegative. For `A ≤ v ≤ 1`,
the first four terms are `z² P(v,z)`, where

```math
P(v,z)=\frac{(v-1)^2}{2}+\frac{f_3(v)}6z
       +\frac{f_4(v)}{24}z^2+\frac{f_5(v)}{120}z^3.
```

The finite certificate proves

```math
P(v,z)\ge\frac{(v-1)^2+z^2}{4000}\qquad(z\ge0).
```

Specifically, put `w=1−v`, `r=z/(z+7w)` when `w>0`. After cancellation,
the expression

```math
R_+(w,r)=\frac{(1-r)^3}{w^2}
 P\!\left(1-w,\frac{7wr}{1-r}\right)
-\frac{(1-r)^3+49r^2(1-r)}{4000}
```

is a polynomial of bidegree `(6,3)`. Its tensor Bernstein coefficients
are nonnegative on each of the 64 rational rectangles

```math
[9i/160,9(i+1)/160]\times[j/8,(j+1)/8],\qquad 0\le i,j<8.
```

Nonnegative basis functions prove the inequality throughout each cell.
The case `w=0` follows from `P(1,z)=z²/105+z³/225`. The finite coefficient
identities and their signs are proof obligations; a numerical check or
certificate hash is not a mathematical premise.

The chord comparison also has the quantitative remainder

```math
M_v(t)-\mathbb Ee^{tX}\ge d\,t^4/24,
```

because `g_t(y)−t⁴y²/24` is convex. Combining this with the endpoint
estimate and `δ=3(v−1)²+d` gives the retained intrinsic-deficit gap.
The sharp `1/25200` estimate uses the additional sixth moment and separate
bidegree-`(8,4)` certificate in [SharpGap.md](SharpGap.md).

## Sharpness and rigidity

For any `R > √3+√2`, put `q=R²` and `p=1/(q+1)`. Give each of `±1`
mass `(1−p)/2`, and each of `±R` mass `p/2`. Its second and fourth
moments are `2q/(q+1)` and `q`, so

```math
\mathbb EX^4-3(\mathbb EX^2)^2
=\frac{q(q^2-10q+1)}{(q+1)^2}>0.
```

The difference between its MGF and the variance-matched Gaussian MGF
therefore has a positive fourth-order leading term at zero. It violates
the bound at every sufficiently small nonzero parameter. The
second-order Taylor coefficient likewise shows that no valid Gaussian
proxy can be smaller than the second moment of any centered bounded law.

For rigidity, the nonnegative identity `δ=3(v−1)²+d` forces `v=1` and
`d=0` when `δ=0`. Vanishing of `d` puts the squared law on `{A,B}`;
its mean fixes the endpoint weights. Symmetry fixes the split between
positive and negative atoms, giving the stated measure `law(X₀)`.

## Stability proof

For `Y=X²`, randomly round `y∈[A,B]` to `B` with probability
`(y−A)/(B−A)` and to `A` otherwise. This preserves the mean and has
conditional cost `2(y−A)(B−y)/(B−A)`. Adjusting the resulting endpoint
weights to the reference law costs exactly `|v−1|`. Consequently

```math
W_1(\mathcal L(Y),\mathcal L(X_0^2))
\le |v-1|+d/\sqrt6.
```

Keeping the exact affine coupling cost yields the stronger global bound.
Put `p=A/6`, `α=B/6`, and `q=EX⁴`. In the branch `v≥1`, assign `y` to
`B` with probability `p(y−A)/(v−A)`; in the other branch assign it to
`A` with probability `α(B−y)/(B−v)`. The resulting costs are

```math
 C_+=v-1+\frac{2pd}{v-A},\qquad
 C_-=1-v+\frac{2\alpha d}{B-v}.
```

Their exact remainders satisfy

```math
 \delta-3C_+^2=\frac{12p^2d(q-v^2)}{(v-A)^2}\ge0,\qquad
 \delta-3C_-^2=\frac{12\alpha^2d(q-v^2)}{(B-v)^2}\ge0.
```

Thus `W₁≤√(δ/3)` without a small-deficit restriction. The endpoint law of
mean `1+√(δ/3)` exists for every feasible deficit because
`3(B−1)²=2B²`. It attains the bound: moving excess endpoint mass costs
exactly the difference of means, a lower bound for every coupling.
[GlobalTransport.md](GlobalTransport.md) gives the full proof and its
written equality and higher-order extensions.

## Gaussian quadrature and applications

The four support nodes of `X₀` are the roots of the probabilists' Hermite
polynomial `x⁴−6x²+3`. This law is the four-node Gaussian quadrature for
the standard normal measure. It agrees with that measure on polynomials
of degree at most seven and has eighth moment `81`, while the Gaussian
eighth moment is `105`. Its MGF gap begins with `t⁸/1680`.
Gaussian-quadrature sub-Gaussianity is established in the literature;
[Sources.md](Sources.md) records the specific statements. The universal
theorem additionally controls every endpoint weight and every magnitude
distribution in the bands.

Independent sums and deterministic linear forms inherit the bound by
multiplication of their MGFs. If such a sum `S` has variance `V>0`, the
usual Chernoff argument gives `Pr(|S|≥u)≤2 exp(−u²/(2V))` for every `u>0`.
Conditional versions use the same support theorem on each conditional
law and the standard exponential supermartingale construction. These
applications do not require the resulting sum itself to remain in a
positive magnitude band.

[Proof.md](Proof.md) gives the full mathematical argument, and
[VERIFICATION.md](VERIFICATION.md) specifies the formal scope and completed
checks. The optimized local worst-law asymptotic and full conditional
concentration development are written supplements. The optimal eighth-order
MGF-gap coefficient is resolved by the separate sharp certificate.
