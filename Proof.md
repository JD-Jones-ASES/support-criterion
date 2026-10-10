# Sharp universal support criterion

This manuscript gives the probability theorem, its finite certificate, and
the rigidity and stability results. [VERIFICATION.md](VERIFICATION.md) records
which formal declarations and replays have passed. [Sources.md](Sources.md)
provides the primary-source comparisons.

## The sharp theorem

Let $X$ be a real random variable whose law is symmetric about zero.
Suppose that $0<a\le |X|\le b<\infty$ almost surely. If


```math
\frac ba\le R_*:=\sqrt3+\sqrt2,
```


then, for every real $t$,


```math
\mathbb E e^{tX}\le
\exp\!\left(\frac{t^2\mathbb E X^2}{2}\right).
```


The inequality is strict for $t\ne0$. Its quadratic variance proxy is
optimal, and the universal support-ratio constant cannot be increased.
The law may be discrete, continuous or mixed; no density, finite-support
or independence assumption is made. Symmetry supplies $\mathbb EX=0$.

Here “strictly sub-Gaussian” has the conventional meaning that the optimal
proxy is the actual variance. Strictness of (1) away from zero is an
additional conclusion, not the definition of that terminology.

## 1. Reduce every law to the critical four endpoints

Put


```math
A=3-\sqrt6,\qquad B=3+\sqrt6.
```


These numbers obey $A+B=6$, $AB=3$,
$B/A=5+2\sqrt6=R_*^2$, and $A>11/20$.
Replacing $X$ by $\sqrt A X/a$ places $X^2$ in $[A,B]$.
Proving (1) after this scaling proves the original statement for all real
$t$, including when $a=b$.

For fixed $t$, the entire power series


```math
g_t(y)=\cosh(t\sqrt y)=\sum_{n=0}^\infty\frac{t^{2n}y^n}{(2n)!}
```


is convex on $[0,\infty)$: termwise second differentiation is valid
on compact intervals and every resulting coefficient is nonnegative.
The chord bound on $[A,B]$, symmetry and $v=\mathbb EX^2$ give


```math
\mathbb Ee^{tX}=\mathbb E\cosh(tX)
\le (1-p)\cosh(t\sqrt A)+p\cosh(t\sqrt B),
\qquad p=\frac{v-A}{B-A}.
```


The right side is the MGF of a symmetric four-point law with the same
variance $v$. It suffices to prove (1) for every such law, where
$A\le v\le B$. For $t\ne0$, $g_t$ is strictly convex, so equality
in (2) forces $X^2\in\{A,B\}$ almost surely.

## 2. Control the infinite tail by the endpoint recurrence

For this endpoint law write $s_n=\mathbb EX^{2n}$. Since each squared
endpoint solves $y^2-6y+3=0$,


```math
s_0=1,\quad s_1=v,\quad s_n=6s_{n-1}-3s_{n-2}\quad(n\ge2).
```


Define $f_n(v)=v^n-s_n/(2n-1)!!$, with $(-1)!!=1$. Directly,


```math
\begin{aligned}
f_0=f_1&=0,\\
f_2&=(v-1)^2,\\
f_3&=v^3-\frac{11}{5}v+\frac65,\\
f_4&=v^4-\frac{12}{7}v+\frac{33}{35},\\
f_5&=v^5-\frac{109}{105}v+\frac47.
\end{aligned}
```


First, $f_5(v)>0$ for every $v\ge0$. Convexity gives
$v^5\ge5c^4v-4c^5$ for every $c\ge0$. Taking $c=2/3$ for
$0\le v\le4/5$ yields


```math
f_5(v)\ge\frac{76}{1701}-\frac{143}{2835}v
\ge\frac{184}{42525}>0.
```


Taking $c=3/4$ for $v\ge4/5$ yields


```math
f_5(v)\ge\frac{14621}{26880}v-\frac{677}{1792}
\ge\frac{7709}{134400}>0.
```


Next, $B/A<11$. For $v\ge A$ and $n\ge5$,
$B<(2n+1)v$, while $s_{n+1}\le Bs_n$ because $X^2\le B$.
Induction from (4) proves


```math
s_n<(2n-1)!!v^n\quad\hbox{and hence}\quad f_n(v)>0
\qquad(n\ge5).
```


Thus the entire infinite tail, not a finite sampled segment, is controlled.
For $v\ge1$, $f_3,f_4$ are nonnegative as well: their derivatives
are positive there and $f_3(1)=0$, $f_4(1)=8/35$.

## 3. Reduce the remaining MGF comparison to a polynomial

Let $z=t^2/2$. Both exponential series converge absolutely for every
real $t$, and bounded support permits integration term by term. Since
$(2n)!=2^n n!(2n-1)!!$,


```math
e^{vz}-\mathbb Ee^{tX}
=\sum_{n=2}^\infty\frac{f_n(v)}{n!}z^n.
```


For $v\ge1$, (3)–(5) prove positivity of (6) whenever $z>0$.
For $A\le v\le1$, it is enough to prove


```math
P(v,z):=\frac{(v-1)^2}{2}
+\frac{f_3(v)}6z+\frac{f_4(v)}{24}z^2+\frac{f_5(v)}{120}z^3
\ge0\qquad(z\ge0),
```


because (6) is $z^2P(v,z)$ plus the nonnegative tail from $n=6$.
By (5), that tail is strictly positive for $z>0$. Thus even a
non-strict certificate for (7) proves strictness in (1).

## 4. An exact certificate for the finite polynomial

Set $w=1-v$. The needed range lies in $0\le w\le9/20$, since
$\sqrt6<49/20$. For $w>0$, put


```math
r=\frac{z}{z+7w}\in[0,1),\qquad z=\frac{7wr}{1-r}.
```


After cancellation the rational expression


```math
R(w,r)=\frac{(1-r)^3}{w^2}
 P\!\left(1-w,\frac{7wr}{1-r}\right)
```


is the following polynomial of bidegree $(6,3)$:


```math
\begin{aligned}
R={}&\frac12-\frac{73}{30}r+\frac{23}{6}r^2-\frac{19}{10}r^3\\
&+w\left(\frac72r-\frac{35}{3}r^2+\frac{4361}{450}r^3\right)\\
&+w^2\left(-\frac76r+\frac{175}{12}r^2-\frac{22267}{900}r^3\right)\\
&+w^3\left(-\frac{49}{6}r^2+\frac{147}{4}r^3\right)
+w^4\left(\frac{49}{24}r^2-\frac{245}{8}r^3\right)\\
&+\frac{343}{24}w^5r^3-\frac{343}{120}w^6r^3.
\end{aligned}
```


For the quantitative form, certify the shifted polynomial


```math
R_+(w,r)=R(w,r)-\frac{(1-r)^3+49r^2(1-r)}{4000}.
```


Partition the rectangle into the 64 closed cells


```math
[9i/160,9(i+1)/160]\times[j/8,(j+1)/8],\qquad 0\le i,j<8.
```


On each cell put $w=9(i+x)/160$, $r=(j+y)/8$. Write
$R_+=\sum_{a,b}c_{ab}x^ay^b$. Its tensor Bernstein coefficients are


```math
\beta_{kl}=\sum_{a\le k,b\le l}c_{ab}
\frac{\binom ka}{\binom6a}\frac{\binom lb}{\binom3b},
\qquad 0\le k\le6,\quad0\le l\le3.
```


The generator [scripts/generate_certificate.py](scripts/generate_certificate.py)
reconstructs every coefficient from the endpoint moment recurrence and checks
every cell identity using exact rational arithmetic. All 1,792 coefficients
are nonnegative, with one zero and minimum positive coefficient


```math
\frac{437058894911}{966367641600000}.
```


The ordered canonical coefficient strings have SHA256
`93bb378759a066ecee34980c00e7a4a1cb518cd0044f658fddc48a216b8e3523`.
The digest identifies the data; the proof consists of the polynomial
identities and coefficient signs. The Lean certificate modules prove these
identities and signs directly in the kernel, including all cell boundaries.
Every Bernstein basis term is nonnegative on the unit square, so
$R_+\ge0$ on the full rectangle. Since the subtracted polynomial is
nonnegative, this also gives $R\ge0$.

Multiplying the shifted inequality by $w^2/(1-r)^3$ gives


```math
P(v,z)\ge\frac{(v-1)^2+z^2}{4000}\qquad(A\le v<1,\ z\ge0).
```


The inverse substitution covers every finite $z\ge0$ for $w>0$.
At $w=0$, use $P(1,z)=z^2/105+z^3/225$ directly. This proves
both the base inequality and the quantitative strengthening, with no
restriction to sampled parameter values.

## 5. Optimality and sharpness

For any centered nonzero bounded random variable, the Taylor expansion at
zero shows that a valid Gaussian proxy $\tau^2$ must satisfy
$\tau^2\ge\mathbb EX^2$. Hence (1) uses the optimal proxy.

For any ratio $R>R_*$, put $q=R^2$ and choose the symmetric law


```math
\Pr(X=\pm1)=\frac{1-p}{2},\qquad
\Pr(X=\pm\sqrt q)=\frac p2,\qquad p=\frac1{q+1}.
```


It has $\mathbb EX^2=2q/(q+1)$, $\mathbb EX^4=q$, and


```math
\mathbb EX^4-3(\mathbb EX^2)^2
=\frac{q(q^2-10q+1)}{(q+1)^2}>0.
```


The difference between its MGF and the variance-matched Gaussian MGF is
this positive quantity times $t^4/24$, plus $O(t^6)$. Thus (1) fails
for all sufficiently small nonzero $t$. This gives a counterexample
at every larger support ratio, rather than only along a selected sequence.


## 6. Normalization and an exact fourth-cumulant identity

Write


```math
A=3-\sqrt6,\qquad B=3+\sqrt6.
```


In the normalized results below, let $X$ be symmetric about zero with
$A\le X^2\le B$ almost surely, and put


```math
v=\mathbb EX^2,\quad
 d=\mathbb E[(X^2-A)(B-X^2)],\quad
 \kappa_4=\mathbb EX^4-3v^2.
```


Then $d\ge0$, and the identity $A+B=6,AB=3$ gives


```math
\boxed{-\kappa_4=3(v-1)^2+d.}
```


Indeed, $d=6v-3-\mathbb EX^4$. Thus equality in the Gaussian
fourth-moment inequality holds if and only if both $v=1$ and
$d=0$. The latter equality forces $X^2\in\{A,B\}$ almost surely,
because its nonnegative defining integrand vanishes only at the endpoints.
Symmetry therefore forces the unique law


```math
\mathbb P(X_0=\pm\sqrt A)=\frac{1-p_0}{2},\qquad
 \mathbb P(X_0=\pm\sqrt B)=\frac{p_0}{2},\qquad
 p_0=\frac{\sqrt6-2}{2\sqrt6}.
```


For every other fixed law in these bands, the fourth cumulant is strictly
negative. Analyticity of the bounded-law MGF consequently yields


```math
e^{vt^2/2}-\mathbb Ee^{tX}
 =\frac{3(v-1)^2+d}{24}\,t^4+O(t^6).
```


This identifies separately the effects of variance displacement and mass
inside the squared-support interval. In particular, Gaussian fourth-moment
contact in these bands already forces sixth-moment contact; there is no
separate family with fourth-order contact but a different sixth moment.

## 7. Sharp local stability of the squared law

Let $Y=X^2$, $Y_0=X_0^2$, and $\delta=-\kappa_4$.
Define $W_1$ as the infimum of $\mathbb E|U-V|$ over couplings
of the two indicated laws. Then


```math
\boxed{
 W_1(\mathcal L(Y),\mathcal L(Y_0))
 \le |v-1|+\frac{2d}{B-A}
 \le\sqrt{\frac\delta3}+\frac\delta{\sqrt6}.}
```


To prove this, given $Y=y$, randomly set $\widehat Y=B$ with
probability $(y-A)/(B-A)$ and $\widehat Y=A$ otherwise. This
coupling preserves the conditional mean and satisfies


```math
\mathbb E[|Y-\widehat Y|\mid Y=y]
 =\frac{2(y-A)(B-y)}{B-A}.
```


The endpoint law $\widehat Y$ has mean $v$. Moving its excess
endpoint mass to the other endpoint couples it to $Y_0$ at cost
exactly $|v-1|$. Combine these couplings and use the triangle
inequality. The second bound follows from (1), $d\le\delta$, and
$B-A=2\sqrt6$.

For small fourth-cumulant deficit, the exact local modulus is sharper:


```math
\boxed{W_1(\mathcal L(Y),\mathcal L(Y_0))
        \le\sqrt{\delta/3}\qquad(0\le\delta\le1/2).}
```


To see this, set $h=|v-1|$. The first bound in (S) and (1) give
$W_1\le h+(\delta-3h^2)/\sqrt6$, where
$0\le h\le\sqrt{\delta/3}$. The function on the right has derivative
$1-\sqrt6 h$. It is therefore increasing throughout this interval
when $\delta\le1/2$, and its maximum is $\sqrt{\delta/3}$.

For every $\delta\in[0,1/2]$, an endpoint law with mean
$v=1+\sqrt{\delta/3}$ attains (S1). This variance belongs to
$[A,B]$, its interiority moment is zero, and its cumulant deficit is
exactly $\delta$. Its transport distance from $Y_0$ is exactly
$|v-1|$: every coupling has cost at least the difference of means,
and moving endpoint mass attains that lower bound. Thus (S1) is the
sharp local modulus over the whole distribution class at each indicated
value of $\delta$, not just an asymptotic coefficient.

Symmetric signs can be coupled identically, and the square-root map is
$1/(2\sqrt A)$-Lipschitz on $[A,B]$. Consequently (S) also gives


```math
W_1(\mathcal L(X),\mathcal L(X_0))
 \le\frac{1}{2\sqrt A}
       \left(\sqrt{\frac\delta3}+\frac\delta{\sqrt6}\right).
```


For $\delta\le1/2$, the parenthesis can be replaced by $\sqrt{\delta/3}$ using (S1). No optimal constant is asserted for this last, unsquared-law bound.

## 8. A global quantitative gap for every law

The main proof compares the endpoint law of variance $v$ with its
Gaussian MGF. In its notation, $z=t^2/2$ and


```math
\begin{aligned}
P(v,z)={}&\frac{(v-1)^2}{2}
 +\frac{v^3-11v/5+6/5}{6}z\\
 &+\frac{v^4-12v/7+33/35}{24}z^2
 +\frac{v^5-109v/105+4/7}{120}z^3.
\end{aligned}
```


For $A\le v\le1$, the same exact Bernstein construction proves the
stronger estimate


```math
\boxed{P(v,z)\ge\frac{(v-1)^2+z^2}{4000}}
 \qquad(z\ge0).
```


Here are the precise extra certificate data. Set $w=1-v$ and
$z=7wr/(1-r)$. If


```math
R(w,r)=\frac{(1-r)^3}{w^2}
       P\!\left(1-w,\frac{7wr}{1-r}\right),
```


then certify


```math
R_+(w,r)=R(w,r)-\frac{(1-r)^3+49r^2(1-r)}{4000}
 \ge0
```


on $[0,9/20]\times[0,1]$. The 64 cells are
$[9i/160,9(i+1)/160]\times[j/8,(j+1)/8]$,
$0\le i,j<8$. Every coefficient in the tensor Bernstein basis of
bidegree $(6,3)$ is nonnegative. Among the 1,792 coefficients there
is one zero; the minimum positive coefficient is


```math
\frac{437058894911}{966367641600000}.
```


The SHA256 of the ordered canonical Fraction strings, separated by newlines,
is `93bb378759a066ecee34980c00e7a4a1cb518cd0044f658fddc48a216b8e3523`.
The identity in (5), after multiplication by $w^2/(1-r)^3$, gives
exactly (4). At $w=0$, use
$P(1,z)=z^2/105+z^3/225$ directly.
The exact generator and Lean certificate modules retain this finite calculation.

Let $M_v(t)$ denote the endpoint-law MGF. The main proof's nonnegative
Taylor tail and (4) imply


```math
e^{vt^2/2}-M_v(t)
 \ge\frac{(v-1)^2t^4}{16000}+\frac{t^8}{64000}.
```


For $v\ge1$, the same estimate follows without (5): the second and
fourth coefficients in the $z$-series are at least
$(v-1)^2/2$ and $1/105$, respectively, and every other coefficient
is nonnegative. Thus (6) holds for every $v\in[A,B]$.

There is also a quantitative endpoint reduction. The function
$g(y)=\cosh(t\sqrt y)$ satisfies


```math
g''(y)\ge\frac{t^4}{12}\qquad(y\ge0),
```


by differentiating its power series. Consequently
$g(y)-t^4y^2/24$ is convex. Its chord on $[A,B]$ gives


```math
M_v(t)-\mathbb Ee^{tX}\ge\frac{d\,t^4}{24}.
```


Combining (6)–(7) proves the quantitative theorem


```math
\boxed{
 e^{vt^2/2}-\mathbb Ee^{tX}
 \ge t^4\left(\frac{(v-1)^2}{16000}+\frac d{24}\right)
       +\frac{t^8}{64000}.}
```


In particular, (1) implies the simpler intrinsic form


```math
\boxed{
 e^{vt^2/2}-\mathbb Ee^{tX}
 \ge\frac{-\kappa_4}{48000}t^4+\frac{t^8}{64000}.}
```


The numerical constants in (8)–(9) are certified, not asserted optimal.
For every admissible law the MGF inequality is strict at every $t\ne0$;
its only equality parameter is $t=0$.

For the original support condition $0<a\le|X|\le b$ with
$b/a\le\sqrt3+\sqrt2$, apply (9) to $\sqrt A\,X/a$.
With $v=\mathbb EX^2$ and the original fourth cumulant, this yields


```math
\boxed{
 e^{vt^2/2}-\mathbb Ee^{tX}
 \ge\frac{-\kappa_4(X)}{48000}t^4
    +\frac{a^8}{64000(3-\sqrt6)^4}t^8.}
```


The scaling cancellation in the fourth-cumulant term is exact.

## 9. Why the exceptional law is Gaussian quadrature

The polynomial


```math
H(x)=x^4-6x^2+3
```


is the monic probabilists' fourth Hermite polynomial. Its roots are precisely
$\pm\sqrt A,\pm\sqrt B$. The probabilists' normalization is important:
the relevant Gaussian weight is $e^{-x^2/2}$, not $e^{-x^2}$.
[NIST DLMF, Table 18.3.1](https://dlmf.nist.gov/18.3#T1) records the two
normalizations; [DLMF §3.5(v)](https://dlmf.nist.gov/3.5#v) records Gaussian
quadrature at orthogonal-polynomial roots and its degree-of-exactness rule.

Here the quadrature identification can be checked directly. If $Z$ is
standard Gaussian, then $\mathbb E[H(Z)q(Z)]=0$ for every polynomial
$q$ of degree at most three, using the normal moments and parity.
Every polynomial $f$ of degree at most seven has a division
$f=Hq+r$, with $\deg q\le3$ and $\deg r\le3$.
The law $X_0$ from (2) and $Z$ agree on all moments through degree
three, while $H(X_0)=0$ almost surely. Therefore


```math
\mathbb E f(X_0)=\mathbb E f(Z)\qquad(\deg f\le7).
```


Thus (2) is exactly the four-node Gaussian quadrature law for the standard
normal measure. In particular,


```math
\mathbb EX_0^2=1,\quad \mathbb EX_0^4=3,\quad
 \mathbb EX_0^6=15,\quad \mathbb EX_0^8=81.
```


The standard normal eighth moment is 105. Hence


```math
e^{t^2/2}-\mathbb Ee^{tX_0}
 =\frac{t^8}{1680}+O(t^{10}),
```


and the same leading coefficient holds for
$t^2/2-\log\mathbb Ee^{tX_0}$.

There is a direct quadrature proof of strict sub-Gaussianity for this one
law. Let $h$, of degree at most seven, interpolate $f$ and $f'$
at the four roots of $H$. Hermite's interpolation remainder gives


```math
f(x)-h(x)=\frac{f^{(8)}(\xi_x)}{8!}H(x)^2.
```


If $f\in C^8(\mathbb R)$, $\mathbb E|f(Z)|<\infty$, and
$f^{(8)}\ge0$, integrating and using (11) yields
$\mathbb Ef(Z)\ge\mathbb Ef(X_0)$. For $f(x)=e^{tx}$ and
$t\ne0$, the remainder is positive away from the four nodes, giving
strict inequality. This is the usual Gaussian-quadrature remainder mechanism;
it is consistent with the general error formula in
[DLMF equations 3.5.19–20](https://dlmf.nist.gov/3.5#E19).

The quadrature observation explains the special constant and moment contact.
It does not prove the all-weights support-ratio theorem: varying the endpoint
weights destroys Gaussian quadrature exactness. The main proof and (5)
control that variation. No new claim is made for the classical quadrature
law's own sub-Gaussianity. Wu–Yang,
[*Polynomial methods in statistical inference: theory and practice*,
§2.7.1, Remark 2.7.2 and Lemma 2.7.3](https://arxiv.org/pdf/2104.07317v2),
identify the Hermite nodes and explicitly prove Gaussian even-moment domination
and sub-Gaussianity for Gaussian quadrature measures. Kotekal also records
this result in [*Variance estimation in compound decision theory under
boundedness* (NeurIPS 2024), Appendix D, Lemma 7](https://papers.nips.cc/paper_files/paper/2024/file/a7667ee5d545a43d2f0fda98863c260e-Paper-Conference.pdf).
These prior results handle the distinguished quadrature weights; they do not
by themselves handle all weights on the same four nodes.
