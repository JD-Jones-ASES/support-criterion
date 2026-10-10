# Local asymptotics of the worst endpoint law

The full optimizer expansion is a written supplement. The sharp global
coefficient is proved in [SharpGap.md](SharpGap.md); its formal status is
recorded in [VERIFICATION.md](VERIFICATION.md). Here $`M_v(t)`$ is
the endpoint-mixture MGF of variance $`v`$ from [Proof.md](Proof.md), with
$`A=3-\sqrt6`$ and $`B=3+\sqrt6`$.

Let $`\mathcal C`$ be all symmetric laws with squared support inside
$`[A,B]`$. For fixed nonzero $`t`$, the chord argument shows that


```math
\sup_{X\in\mathcal C}
 \left(\log\mathbb Ee^{tX}-\frac{t^2\mathbb EX^2}{2}\right)
 =\max_{v\in[A,B]}G(v,t),
```


where $`G(v,t)=\log M_v(t)-vt^2/2`$.
The endpoint MGF is affine in $`v`$, and its slope is positive;
therefore $`G`$ is strictly concave in $`v`$.

Put $`z=t^2/2`$, and write the analytic endpoint series as


```math
M_v(t)=u(z)+v\,d_1(z),\qquad H_1(z)=d_1(z)/z.
```


The notation $`d_1`$ here is an analytic coefficient, distinct from the
support-interiority moment $`d=\mathbb E[(X^2-A)(B-X^2)]`$.
The recurrence $`s_n=6s_{n-1}-3s_{n-2}`$, $`s_0=1,s_1=v`$, determines
these functions. Since $`d_1(z)=z+O(z^2)`$, the interior maximizer
extends analytically to zero and is


```math
v_*(z)=\frac1z-\frac{u(z)}{d_1(z)}
 =1-\frac{2z}{15}+\frac{4z^2}{105}
    -\frac{4z^3}{315}+\frac{8z^4}{1575}+O(z^5).
```


As $`v_*(0)=1\in(A,B)`$, it is the unique global maximizer for all
sufficiently small nonzero $`t`$. In $`t`$-coordinates,


```math
v_*(t)=1-\frac{t^2}{15}+\frac{t^4}{105}
           -\frac{t^6}{630}+\frac{t^8}{3150}+O(t^{10}).
```


Substitution gives the exact local expansion


```math
\begin{aligned}
 \max_{v\in[A,B]}G(v,t)
 &=\log H_1(z)-1+\frac{u(z)}{H_1(z)}\\
 &=-\frac{z^4}{1575}+O(z^6)
  =\boxed{-\frac{t^8}{25200}+O(t^{12})}.
\end{aligned}
```


The $`z^5`$, equivalently $`t^{10}`$, coefficient vanishes. These
coefficients follow from ordinary division and logarithm of convergent
power series; the exact moment recurrence suffices to replay them.

The expansion of the maximum distinguishes a fixed exceptional law from the worst law
allowed to depend on $`t`$. The latter has variance slightly below one.
It also shows that any universal inequality
$`e^{vt^2/2}-\mathbb Ee^{tX}\ge c\,t^8`$ on $`\mathcal C`$ must
have $`c\le1/25200`$. The exact certificate in [SharpGap.md](SharpGap.md) proves that
$`c=1/25200`$ holds globally. Hence this coefficient is optimal, with no
nonzero-parameter obstruction. The simpler endpoint path
$`v_t=1-t^2/15`$ suffices for optimality and does not require the full
optimizer classification developed here.
