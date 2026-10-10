# Rényi and Tsallis entropy monotonicity for Bernoulli sums

Standalone written proof, 2026-10-10.

**Status.** This document gives the complete written argument for
Hillion–Johnson Conjecture 4.4. The private Lean implementation contains the
full two entropy theorems and the finite inverse-score inequality. The written
argument, local compilation, and exact-commit Linux verification are separate
evidence; [VERIFICATION.md](VERIFICATION.md) defines the acceptance gate.
Independent AI-agent audits and symbolic checks do not constitute external
peer review. See [Note.md](Note.md) for attribution and source comparisons.

All monotonicity statements below concern **coin parameters**. The entropy
order is fixed when two distributions are compared. The argument treats
arbitrary finite dimension, every real order in `[0,2]`, and all zero and
fair parameter boundaries. No computational census is a proof input.

The source is Erwan Hillion and Oliver Johnson,
[*A proof of the Shepp–Olkin entropy monotonicity conjecture*,
arXiv:1810.09791v1](https://arxiv.org/abs/1810.09791v1),
*Electronic Journal of Probability* 24 (2019), article 126,
[DOI 10.1214/19-EJP380](https://doi.org/10.1214/19-EJP380).
Their mixing coefficients, Appendix A identities, Shannon theorem and
equality mechanism are explicitly retained below. The weighted-pair
association argument uses the classical correlation mechanism described
in Note.md and proves its required finite instance directly.

## 1. The distribution, entropies, and coordinate reduction

For `n>=0` and `p=(p_1,...,p_n)` define

```math
P_p(z)=\prod_{i=1}^n(1-p_i+p_i z)=\sum_{k=0}^n g_p(k)z^k.
```

Expanding the product identifies the coefficient with

```math
g_p(k)=\sum_{A\subseteq\{1,\ldots,n\},\ |A|=k}
       \prod_{i\in A}p_i\prod_{i\notin A}(1-p_i).
```

Thus `g_p` is the distribution of the sum of independent Bernoulli
variables: each product is the probability of the corresponding binary
outcome. For `0<=p_i<=1`, the coefficients are nonnegative and sum to
`P_p(1)=1`. On `[0,1/2]^n`, delete the zero parameters. If `m` parameters
remain, every coefficient from 0 through `m` is positive and all others
vanish. This follows term by term from the subset formula. The empty
product is the point mass at zero. All coefficient sequences below are
extended by zero on **integer** indices outside their stated support.

For a finite probability vector `f` write

```math
H_q(f)=\begin{cases}
\log|\{k:f_k>0\}|,&q=0,\\
-\sum_{f_k>0}f_k\log f_k,&q=1,\\
\log(\sum_k f_k^q)/(1-q),&q>0,\ q\ne1,
\end{cases}
\qquad
T_q(f)=\begin{cases}
|\{k:f_k>0\}|-1,&q=0,\\
-\sum_{f_k>0}f_k\log f_k,&q=1,\\
(\sum_k f_k^q-1)/(1-q),&q>0,\ q\ne1.
\end{cases}
```

Here `0^q=0` only for `q>0`; support, rather than a padded power sum,
defines order zero. All logarithms are natural.

**Main theorem.** If `0<=p_i<=r_i<=1/2` for every coordinate, then

```math
H_q(g_p)\le H_q(g_r),\qquad T_q(g_p)\le T_q(g_r)
\quad\text{for every real }0\le q\le2.
```

Fix a background law `g` on `0,...,N` and a target parameter `t`.
Write `f_k(t)=(1-t)g_k+t g_{k-1}` and

```math
s_k=g_{k-1}+g_k,\qquad d_k=g_{k-1}-g_k,\qquad
D_q(g)=\sum_{k=0}^{N+1}d_ks_k^{q-1}.
```

For `q>0`, a zero pair contributes zero. On a positive support and for
`0<t<1`, ordinary differentiation gives

```math
T_q'(t)=\frac{q}{1-q}\sum_kd_k f_k(t)^{q-1},\qquad
T_q''(t)=-q\sum_kd_k^2 f_k(t)^{q-2}\le0\quad(q\ne1),
```

and `T_1'(t)=-sum d_k log f_k(t)`,
`T_1''(t)=-sum d_k^2/f_k(t)<=0`. Consequently the midpoint signs

```math
D_q(g)\ge0\quad(0<q<1),\qquad
D_q(g)\le0\quad(1<q<2)
```

imply a nonnegative Tsallis derivative on `0<t<=1/2`, since
`T_q'(1/2)=q 2^(1-q)D_q/(1-q)` and the derivative decreases with `t`.
Finite-law continuity extends comparisons to `t=0`. For `q!=1`, the
map `T -> log(1+(1-q)T)/(1-q)` has positive derivative
`1/(1+(1-q)T)` on its domain; hence the same comparisons hold for
Rényi entropy. Raising coordinates one at a time suffices.

Conversely, failure of a positive-order comparison within `(0,1)`
produces a negative coordinate derivative somewhere on a positive
coordinate interval, after deleting zero background coins. Coordinate
concavity then makes the midpoint derivative negative, hence `D_q<0`.
The mean-value theorem may be applied after a small positive truncation
of a zero endpoint, using continuity. This justifies the failure reduction
without differentiating at support loss.

For a fixed positive order, `|d_k s_k^(q-1)|<=s_k^q`; this proves
continuity at a zero pair, uniformly when `q` lies in a compact subinterval
of `(0,infinity)`. At a fixed finite law, the limit as `q->1` of both
entropies is Shannon entropy: differentiate the finite positive-mass
power sum, with zero masses contributing identically zero. At order two,
`T_2'(t)=(1-2t)sum d_k^2>=0` follows by telescoping. At order zero,
`H_0(g_p)=log(m(p)+1)` and `T_0(g_p)=m(p)`, where `m(p)` counts positive
parameters. These endpoint statements already have their full closed-cube
scope.

## 2. Bernoulli coefficients, strict minors, and the mixing grid

For positive parameters less than one, write each factor as `u_i+v_i z`,
with `u_i,v_i>0`. Its Toeplitz coefficient matrix is upper bidiagonal,
with diagonal `u_i` and superdiagonal `v_i`. Each minor is nonnegative:
in a nonzero determinant the ordered matching of rows to columns is the
only possible matching, and its factors are positive. Finite
Cauchy–Binet gives nonnegative minors of the Toeplitz matrix of the
product polynomial. All needed indices can be truncated to a finite
range before using that identity.

For `r` consecutive rows and columns shifted together by `k`, where
`0<=k<=N`, one Cauchy–Binet term advances every row by one through `k`
factors and leaves every row fixed through the others. Its product is
strictly positive. Thus the contiguous minors of sizes two and three
used below are strict, including the two outer minors. In particular
`g_k^2>g_{k-1}g_{k+1}` on the interior support; boundary minors equal
positive endpoint powers.

There is also a useful real-rooted coefficient argument. For a
nonconstant real-rooted polynomial `F`,
`F'(t)^2-F(t)F''(t)>=0`; away from roots it equals
`F(t)^2 sum_j(t-root_j)^(-2)`, and continuity handles roots. Rolle's
theorem applies to all derivatives. Evaluating the inequality for
`F^(k)` at zero proves, for three consecutive same-sign nonzero
coefficients `A_k,A_(k+1),A_(k+2)`,

```math
A_{k+1}^2\ge\frac{k+2}{k+1}A_kA_{k+2}>A_kA_{k+2}.
```

The coefficients `g_k-g_{k-1}` of `(1-z)P(z)` therefore have strictly
log-concave positive and negative branches. Strict log-concavity of `g`
ensures there is a positive branch followed by a negative one, with
at most one intervening zero. Each branch has unimodal absolute values.

We next give the coefficient identities behind Hillion–Johnson Appendix
A, so they are not assumed as unexplained structural properties. If
`P_i` omits coin `i`, direct product differentiation gives the bivariate
polynomial identity

```math
(x-y)\sum_i p_i(1-p_i)P_i(x)P_i(y)
=xP'(x)P(y)-yP'(y)P(x).
```

Extract coefficients at adjacent and distance-two diagonals. For the
omitted coefficients `h_i`, set
`L_i(k)=h_i(k)^2-h_i(k-1)h_i(k+1)` and
`V_i(k)=h_i(k)h_i(k+1)-h_i(k-1)h_i(k+2)`. The resulting identities are

```math
\sum_i p_i(1-p_i)L_i(k)=g_kg_{k+1},\qquad
\sum_i p_i(1-p_i)V_i(k)=2g_kg_{k+2}.
```

For example the first is the coefficient of `x^(k+1)y^k`; the second
is that of `x^(k+2)y^k`. Let
`a=g_(k-1), b=g_k, c=g_(k+1), d=g_(k+2)`, and put

```math
U=b^2c+abd-2ac^2,\qquad V=bc^2+acd-2b^2d,
\qquad
\Delta_i(k)=\det\begin{pmatrix}
h_i(k)&h_i(k+1)&h_i(k+2)\\
h_i(k-1)&h_i(k)&h_i(k+1)\\
h_i(k-2)&h_i(k-1)&h_i(k)
\end{pmatrix}.
```

Multiply the first coefficient identity at `k` and `k-1` by `b` and
`d`, and subtract `c` times the second identity at `k-1`. This gives
`U=sum_i p_i(1-p_i)[b L_i(k)+d L_i(k-1)-c V_i(k-1)]`.
Substitute `g_j=(1-p_i)h_i(j)+p_i h_i(j-1)` inside each bracket;
expanding its six cubic terms gives `(1-p_i)Delta_i(k)`.
The reflected calculation gives the second identity below:

**(B1)**

```math
U=\sum_i p_i(1-p_i)^2\Delta_i(k),\qquad
V=\sum_i p_i^2(1-p_i)\Delta_i(k).
```

This proves precisely the published cubic identities, including boundary
indices without dividing by an omitted coefficient. For `0<=k<N`, each
`Delta_i(k)>0` by the strict three-row minor construction. Thus `U,V>0`
for positive parameters. When every parameter is at most one half,
`U-V=sum_i p_i(1-p_i)(1-2p_i)Delta_i(k)>=0`.

Define the mixing grid

```math
\alpha_k=\frac{g_{k-1}}{g_{k-1}+g_k},\quad
\beta_k=\alpha_k-\tfrac12,\qquad 0\le k\le N+1.
```

The two-row minors give `0=alpha_0<...<alpha_(N+1)=1`.
The difference of two successive grid gaps has numerator

```math
(c+d)(b^2-ac)-(a+b)(c^2-bd)=U-V
```

and a positive common denominator. Thus the grid is concave on the
half cube. If any parameter is biased, (B1) in fact makes every gap
drop strict. Only nonstrict concavity and its fair equality case are
needed below.


## 3. Harmonic lowering: all orders from one to two

In this section `n` denotes support length, so the last index is `n-1`.


### The finite-sequence theorem

Let `n>=1`, let `g_0,...,g_{n-1}>0`, and extend by `g_{-1}=g_n=0`. Define

```math
\alpha_k=\frac{g_{k-1}}{g_{k-1}+g_k},\qquad
\beta_k=\alpha_k-\frac12\qquad(0\le k\le n).
```

Assume

```math
0=\alpha_0<\alpha_1<\cdots<\alpha_n=1,
\qquad
\alpha_{k+1}-\alpha_k\le\alpha_k-\alpha_{k-1}.
```

Then, for every real `q` in `[1,2]` and every integer `m>=1`,

**(1)**

```math
K_{q,m}(g):=\sum_{k=0}^{n-1}g_k^q
       (\beta_{k+1}^{2m}-\beta_k^{2m})\le0.
```

The proof is simultaneous induction in all `m`, with induction parameter
the length `n`. There is no finite-dimensional cutoff and no interpolation
in the order parameter.

### The lowering operation preserves the mixing-grid hypotheses

Suppose `n>=2`. Put

```math
\delta_k=\alpha_{k+1}-\alpha_k\quad(0\le k<n),
\qquad
h_j=g_{j+1}\alpha_{j+1}
   =g_j(1-\alpha_{j+1})\quad(0\le j<n-1).
```

The balance identity in the definition of `h` follows directly from that
of `alpha`. Every `h_j` is positive. Extend `h_{-1}=h_{n-1}=0`. Its mixing
grid is

**(2)**

```math
\gamma_k=\frac{h_{k-1}}{h_{k-1}+h_k}
        =\frac{\alpha_k}{1-\delta_k},
\qquad x_k=\gamma_k-\frac12\quad(0\le k<n).
```

All denominators in (2) are positive because `n>=2` and all original gaps
are positive. The endpoints are `gamma_0=0` and `gamma_{n-1}=1`.
The interior odds are
`gamma_k/(1-gamma_k)=alpha_k/(1-alpha_{k+1})`, so `gamma` is strictly
increasing.

Here is a direct proof that it is concave. Any three consecutive new
grid points have the form

```math
\frac{A}{1-a},\quad
\frac{A+a}{1-b},\quad
\frac{A+a+b}{1-c},
```

where `a>=b>=c>0` are three consecutive old gaps and
`0<=A<=L:=1-a-b-c`. Their concavity difference

```math
E(A)=\frac{2(A+a)}{1-b}-\frac A{1-a}-\frac{A+a+b}{1-c}
```

is affine in `A`. At the two ends of its permitted interval,

**(3)**

```math
\begin{aligned}
E(0)&=\frac{(a-b)(1-b)+2a(b-c)}{(1-b)(1-c)}\ge0,\\
E(L)&=\frac{(b-c)(1-b)+2c(a-b)}{(1-a)(1-b)}\ge0.
\end{aligned}
```

Thus `E(A)>=0`; if `L=0`, the first endpoint calculation suffices.
For a new grid with only its two endpoints, concavity is vacuous.
Consequently the sequence `h`, of length `n-1`, satisfies the same
strict-increase and concavity assumptions as `g`.

### A positive even kernel

For fixed `q` in `[1,2]`, define

**(4)**

```math
E_q(x)=\frac{2x}{(1/2+x)^q-(1/2-x)^q},\qquad
E_q(0)=\frac{2^{q-1}}q.
```

On `[-1/2,1/2]`, this is an even function with an absolutely convergent
power series in `x^2` whose coefficients are nonnegative. At `q=1,2`,
it is the constant one. For `1<q<2`, this follows explicitly by writing

```math
\frac{(1+\sqrt z)^q-(1-\sqrt z)^q}{2q\sqrt z}
=1-B_q(z),
```

where `B_q` has positive coefficients and
`0<B_q(1)=1-2^{q-1}/q<1`. Therefore
`1/(1-B_q(z))=sum_{r>=0}B_q(z)^r` has nonnegative coefficients and
converges absolutely up to `z=1`. Substituting `z=4x^2` proves the claim,
including both outer endpoints. The boundary convergence follows by monotone convergence of the
positive coefficients of B_q and the displayed endpoint value; the
geometric sum is bounded by 1/(1-B_q(1)). Its power-series coefficient
rearrangement is justified by nonnegativity.

Fix an integer `m>=1`. For `0<delta<1` define, initially at `x!=0`,

**(5)**

```math
H_\delta(x)=
\frac{((1-\delta)x+\delta/2)^{2m}
      -((1-\delta)x-\delta/2)^{2m}}
 {(1-\delta)^q[(1/2+x)^q-(1/2-x)^q]}.
```

Give (5) its continuous value at zero. It is an even function. Expanding
only its polynomial numerator gives

**(6)**

```math
H_\delta(x)=E_q(x)
 \sum_{j=0}^{m-1}\binom{2m}{2j+1}
 (1-\delta)^{2m-2j-1-q}
 (\delta/2)^{2j+1}x^{2m-2j-2}.
```

Every coefficient in the finite polynomial factor is positive.
Consequently, for each fixed `delta`, there are nonnegative coefficients
`c_l(delta)` with

**(7)**

```math
H_\delta(x)=\sum_{l=0}^\infty c_l(\delta)x^{2l},
\qquad
\sum_{l=0}^\infty c_l(\delta)4^{-l}<\infty.
```

No monotonicity of the individual coefficients `c_l(delta)` is claimed
or needed.

### Pointwise monotonicity in the gap

For each fixed `|x|<=1/2`, the function `delta -> H_delta(x)` is
nondecreasing on `(0,1)`. In fact the following argument proves this
monotonicity for every `q>=1`; the upper restriction `q<=2` is needed
for the nonnegative series (7).

By evenness it suffices first to take `0<x<=1/2`. Set

```math
p=2m,\qquad y=2x\in(0,1],\qquad
t=\frac\delta{1-\delta},\qquad
D(t)=(t+y)^p-(t-y)^p>0.
```

The part of (5) depending on `delta` is a positive constant times

**(8)**

```math
\frac{D(t)}{(1+t)^{p-q}}.
```

We claim

**(9)**

```math
\frac{D'(t)}{D(t)}\ge\frac{p-1}{t+y}.
```

If `0<t<=y`, then `p` is even, so
`D'(t)=p[(t+y)^{p-1}+(y-t)^{p-1}]` and
`D(t)<=(t+y)^p`. This gives the stronger bound
`D'(t)/D(t)>=p/(t+y)`.

If `t>=y`, use the elementary integral identities

```math
D(t)=p\int_{t-y}^{t+y}u^{p-1}\,du,
\qquad
D'(t)=p(p-1)\int_{t-y}^{t+y}u^{p-2}\,du.
```

Throughout this nonnegative integration interval,
`u^{p-1}<=(t+y)u^{p-2}`. This proves (9), also for `p=2`.
Since `y<=1`, it follows that

**(10)**

```math
\frac{d}{dt}\log\frac{D(t)}{(1+t)^{p-q}}
\ge\frac{p-1}{t+y}-\frac{p-q}{1+t}
\ge\frac{q-1}{1+t}\ge0.
```

Thus (8) is nondecreasing, and `t` is increasing in `delta`.
At `x=0`, take the continuous limit in (6); a pointwise limit of these
nondecreasing functions is nondecreasing. Negative `x` follows by evenness.

### The exact identity and the sign threshold

Write the centered lowered grid as in (2). The old endpoints of the
`k`th interval are

```math
\beta_k=(1-\delta_k)x_k-\delta_k/2,
\qquad
\beta_{k+1}=(1-\delta_k)x_k+\delta_k/2.
```

Also,

```math
\begin{aligned}
h_{k-1}^q-h_k^q
 &=g_k^q[\alpha_k^q-(1-\alpha_{k+1})^q]\\
 &=g_k^q(1-\delta_k)^q
          [(1/2+x_k)^q-(1/2-x_k)^q].
\end{aligned}
```

Combining these identities with (5) gives

**(11)**

```math
K_{q,m}(g)=
\sum_{k=0}^{n-1}(h_{k-1}^q-h_k^q)H_{\delta_k}(x_k).
```

When `x_k=0`, both the mass difference and the original even-power
difference vanish, so (11) holds using the continuous value of `H`.

The grid `x_k` is strictly increasing from `-1/2` to `1/2`, and

```math
\mathrm{sign}(h_{k-1}^q-h_k^q)=\mathrm{sign}(x_k).
```

Meanwhile the gaps `delta_k` are nonincreasing. Let `k_-` be the largest
index with `x_k<0`, and choose `delta_*:=delta_{k_-}`. This is a number
strictly between zero and one. For all terms with negative coefficient
in (11), `delta_k>=delta_*`; for all terms with positive coefficient,
`delta_k<=delta_*`. Pointwise monotonicity from (10) therefore gives the
termwise signed comparison

**(12)**

```math
(h_{k-1}^q-h_k^q)H_{\delta_k}(x_k)
\le (h_{k-1}^q-h_k^q)H_{\delta_*}(x_k).
```

Terms with zero coefficient cause no restriction. Summing (12) and
reindexing the finite sum yields

**(13)**

```math
K_{q,m}(g)\le
\sum_{k=0}^{n-2}h_k^q
 [H_{\delta_*}(x_{k+1})-H_{\delta_*}(x_k)].
```

This comparison uses monotonicity of the whole kernel at fixed `x`.
It does not require coefficientwise monotonicity in `delta`, which
would be false in general.

### Completion of the simultaneous induction

Fix any `q` in `[1,2]`. For `n=1`, both endpoint even powers are equal,
so (1) holds with equality for every `m>=1`.

Assume that (1) holds for every positive sequence of length `n-1` with
the required mixing-grid hypotheses, and every integer moment index.
For a sequence `g` of length `n`, the lowered sequence `h` satisfies
those hypotheses by (2)--(3). Substitute the nonnegative series (7),
with the fixed gap `delta_*`, into (13). The constant term cancels and
the result is

**(14)**

```math
K_{q,m}(g)\le
\sum_{l=1}^\infty c_l(\delta_*) K_{q,l}(h)\le0.
```

The series manipulation includes the two outer grid points. Indeed,
`|K_{q,l}(h)|<=4^{-l} sum h_k^q`, and (7) gives absolute convergence.
Every summand in the last series is nonpositive by the induction
hypothesis and the nonnegativity of `c_l`. This proves (1), simultaneously
for all `m`, at length `n`, and completes the induction.


To transfer this to the entropy functional, put
`E_q(x)=2x/[(1/2+x)^q-(1/2-x)^q]` as above. Reindexing gives

```math
D_q(g)=\sum_{k=0}^{n-1}g_k^q
       [E_q(\beta_{k+1})-E_q(\beta_k)].
```

For `1<q<2`, the nonconstant even coefficients of `E_q` are nonnegative.
Substitution gives a nonnegative, absolutely convergent combination of
the `K_(q,m)<=0` just proved, hence `D_q<=0`. Indeed the absolute value
of `K_(q,m)` is bounded by `4^(-m)sum g_k^q`, and the endpoint series
is summable. Section 1 now proves both entropy comparisons for
`1<q<2`; the Shannon limit and direct order-two identity include
both endpoints. Zero parameters are deleted or handled by continuity.

## 4. Strict Shannon midpoint and equality

We need a strict statement in addition to the weak Shannon limit.
For a positive law define

```math
J_1(g)=-\sum_kd_k\log s_k.
```

This is the Shannon derivative after adding a fair target coin. Write
`f_k=s_k/2`, `y_k=2 beta_k`. Finite telescoping, followed by the
absolutely convergent logarithmic expansion, gives

```math
J_1(g)=-\sum_{m=1}^{\infty}
\frac{2}{2m(2m+1)}\sum_k f_k y_k^{2m+1}.
```

To verify this, substitute `g_(k-1)=2 alpha_k f_k` and
`g_k=2(1-alpha_k)f_k` in the telescoping logarithmic sum. The resulting
scalar function is
`alpha log alpha-(1-alpha)log(1-alpha)`; subtracting its linear
part makes no change because `sum f_k(alpha_k-1/2)=0`.
The coefficients shown above are the Taylor coefficients of that
scalar function. They are absolutely summable even at `y=+-1`.
Furthermore

```math
4\sum_k f_k\beta_k^{2m+1}
=\sum_{k=0}^{N}g_k(\beta_{k+1}^{2m}-\beta_k^{2m})=K_{1,m}\le0
```

by harmonic lowering. Thus every term of the series for `J_1` is
nonnegative.

For strictness it suffices to inspect the cubic term. With
`delta_k=alpha_(k+1)-alpha_k`, the balance identity
`g_k alpha_k=g_(k-1)(1-alpha_k)` gives by finite reindexing

```math
K_{1,1}=\sum_{k=1}^{N}g_k\alpha_k(\delta_k-\delta_{k-1})\le0.
```

Every multiplier is positive. Equality forces all grid gaps equal,
hence `alpha_k=k/(N+1)`. The coefficient ratios then identify `g`
as `Bin(N,1/2)`. Equivalently, its mean is `N/2`, and a half-cube
Bernoulli representation can have that mean only if all its `N`
positive parameters are fair. Therefore `J_1(g)>0` for every positive
nonfair half-cube law, and `J_1=0` for the fair law. This is the equality
mechanism of Hillion–Johnson Theorem 3.6, equations (19)–(21), here
combined with the already proved harmonic moment signs.

## 5. A strict fair-coordinate derivative

The next lemma is needed uniformly on compact order bands. It applies
to any finite log-concave background, rather than only to a fair one.


Let `h` be a nonzero finitely supported nonnegative log-concave sequence
with contiguous positive support, extended by zero to all integers. For each
integer `k`, put

```math
a=h_{k-2},\quad b=h_{k-1},\quad c=h_k,\qquad
A=\frac{a+2b+c}{2},\quad B=\frac{c-a}{2},\quad L=b^2-ac.
```

Terms with `A=0` are defined to be zero. Then

**(1)**

```math
\boxed{\quad \sum_k (L-qB^2)A^{q-2}>0.\quad}
```

Positive scaling of `h` scales this expression by the same factor to
power `q`, so probability normalization is immaterial to its sign.

### The scalar correction

For `x>0`, `x!=1`, define

**(2)**

```math
f_q(x)=q2^{-q}\frac{(x-1)^2(x+1)^{2q-2}}{x^q-1},
\qquad f_q(1)=0.
```

This has a smooth extension at one. Indeed, divide one factor `x-1`
by `x^q-1`; the resulting quotient is smooth and positive near one.
In particular,

**(3)**

```math
f_q'(1)=2^{q-2},\qquad
x^q f_q(1/x)=-f_q(x),\qquad f_q(0):=\lim_{x\downarrow0}f_q(x)=-q2^{-q}.
```

Write

**(4)**

```math
\mathcal A=\frac{x+2+y}{2},\quad
K_q(x,y)=\left[1-xy-\frac q4(x-y)^2\right]\mathcal A^{q-2},
\qquad J_q(x,y)=K_q(x,y)+f_q(x)+f_q(y).
```

The needed local statement is

**(5)**

```math
J_q(x,y)\ge0\quad(x,y\ge0,\ xy\le1),
\qquad J_q(x,y)>0\quad\text{if }xy<1.
```

For positive variables, direct substitution gives

**(6)**

```math
J_q(x,1/x)=0.
```

The mixed derivative has an elementary factorization:

**(7)**

```math
\frac{\partial^2J_q}{\partial x\partial y}
=-\frac{(q-2)(q-1)}{16}\mathcal A^{q-4}
 \left[(q-2)(x-y)^2+4xy-4\right].
```

It is nonnegative on `xy<=1`, and strictly positive on `xy<1`, because
`0<q<1`.

The boundary normal derivative also has the required sign. Set

```math
U=x^q,\quad S=2^{-q}(x+1)^{2q-3}x^{1-q},\qquad
W=Uqx-Uq-2Ux+qx^2-qx+2x.
```

For `x!=1`, differentiation and simplification give

**(8)**

```math
\left.\frac{\partial J_q}{\partial x}\right|_{(x,1/x)}
=-S\frac{W^2}{x^2(U-1)^2(x+1)}\le0.
```

At `x=1`, the derivative is zero: the derivative of `K_q` is
`-2^(q-2)` and (3) supplies its opposite. Thus the boundary sign in
(8) holds everywhere. By symmetry it holds for the partial derivative
with respect to `y` as well.

Fix positive `x,y` with `xy<1`. Integrating the strictly positive
mixed derivative in (7), with `y` fixed, gives

**(9)**

```math
(J_q)_y(x,y)<(J_q)_y(1/y,y)\le0.
```

For fixed `x`, integrate this strict negative derivative from `y` to
`1/x`; (6) gives `J_q(x,y)>0`. This proves (5) for positive variables.
The extension to zero coordinates follows by continuity. It remains
strict there: by symmetry (9) also says `(J_q)_x<0` in the interior,
so `J_q(0,y)>=J_q(epsilon,y)>0` for `y>0` and sufficiently small
positive `epsilon`. For `x=y=0`, compare to a pair of sufficiently
small positive coordinates in the same way. This completes (5).

### Telescoping, zero entries, and strictness

Define the homogeneous flux

```math
F_q(a,b)=b^q f_q(a/b)\quad(a,b>0),
```

with the continuous boundary values

**(10)**

```math
F_q(0,b)=-q2^{-q}b^q,\quad
F_q(a,0)=q2^{-q}a^q,\quad F_q(0,0)=0.
```

The second boundary limit follows directly from (2), or from its
antisymmetry in (3). For `b>0`, put `x=a/b`, `y=c/b`.
Log-concavity gives `xy<=1`, and (3)--(5) yield

**(11)**

```math
(L-qB^2)A^{q-2}+F_q(a,b)-F_q(b,c)
=b^qJ_q(a/b,c/b)\ge0.
```

If `b=0`, log-concavity and contiguous support imply `ac=0`.
If, for example, `a=0,c>0`, the first term in (11) equals
`-q2^(-q)c^q` and the flux difference equals `q2^(-q)c^q`.
The other endpoint case is the same; an all-zero triple contributes
zero. Hence (11) holds for every index.

The flux differences sum to zero because `h` is finitely supported.
The earliest positive value of `b` has `a=0`, so its corrected term
is strictly positive by (5). Consequently the sum is strictly positive,
proving (1). There is no nonzero finite equality case in `0<q<1`.

### Exact fair-coordinate consequence and its boundary

Let `h` now be normalized, and put `g_p=(1-p)h+p shift(h)`. With

```math
\mathcal D_q(g)=\sum_k(g_{k-1}-g_k)(g_{k-1}+g_k)^{q-1},
```

omitting all-zero terms, direct differentiation of the finite sum gives

**(12)**

```math
\left.\frac{d}{dp}\mathcal D_q(g_p)\right|_{p=1/2}
=-2\sum_k(L-qB^2)A^{q-2}<0.
```

Thus every finite log-concave background has the strict fair-coordinate
derivative sign, uniformly by compactness on any closed order band in
`(0,1)`.


## 6. Small backgrounds, without a computational certificate

For two background coins `u,v in [0,1/2]`, put
`A=(1-u)(1-v)`, `B=u(1-v)+v(1-u)`, and `C=uv`.
Bringing the four terms over a common denominator gives

```math
-\frac A{A+z}+\frac{A-B}{A+B+z}
+\frac{B-C}{B+C+z}+\frac C{C+z}
=\frac{B(A-C)[2AC+z(A-B+C)]}
{(A+z)(A+B+z)(B+C+z)(C+z)}\ge0 \quad(z>0),
```

because `A-C=1-u-v>=0` and `A-B+C=(1-2u)(1-2v)>=0`.
This includes zero parameters, so covers all backgrounds with at most
two positive coins. For `-1<a<0`, let
`c_a=int_0^infinity t^a/(1+t) dt`, which is finite and positive.
Substitution `z=st` gives

```math
s^a=c_a^{-1}\int_0^\infty\frac{z^a}{s+z}\,dz.
```

Apply this with `a=q-1` to the finite resolvent sum. All integrals
converge individually for positive adjacent masses; zero pairs vanish.
It follows that `D_q>=0` for `0<q<1`. Thus a minimal negative
background must have at least three positive coins.

This consolidation uses this analytic base case in place of the earlier
five-total-coin polynomial certificate. The later classification and
curvature arguments require only `N>=3`: the pure case uses a perturbation
of three coins, and the singleton case has a repeated group of at least two coins.
No finite certificate or dimension census is needed.

## 7. One biased coin among fair coins: the moment comparison

We will exclude a remaining fair-face contact using a strict sign for
`D_q(Bin(m,1/2)+Bern(p))`, `0<p<1/2`, `0<q<1`.
This section supplies its full moment-comparison dependency.


### A complete beta-binomial moment-ratio theorem

First, fix `N>=2` and `a>0`, and let `K` have the symmetric
beta-binomial law

```math
\Pr(K=k)=\frac{N!}{(2a)_N}
             \frac{(a)_k(a)_{N-k}}{k!(N-k)!},
\qquad 0\le k\le N.
```

Put `X=(N-2K)/N`, `A_ell=E[X^(2ell)]`, and define `b_ell=(2ell+1)(A_ell/A_(ell+1)-1)`.
**Then `b_ell` is nonincreasing for all integer `ell>=0`.**
In particular `a=1` is the uniform distribution on the grid, exactly
the escort endpoint `q=0`. Taking `a -> infinity` also includes the
fair-binomial law, the endpoint `q=1`.

The proof uses three standard classical identities, with their
application given below: the
[Gegenbauer generating function](https://dlmf.nist.gov/18.12.E4), its
[derivative formula](https://dlmf.nist.gov/18.9.E19), and
[separation of consecutive orthogonal-polynomial zeros](https://dlmf.nist.gov/18.2.vi).
The weight for `C_m^(lambda)` is `(1-x^2)^(lambda-1/2)` on `(-1,1)`;
here `lambda=a+1>1`, so that orthogonality and zero separation apply.
Euler's [sine product](https://dlmf.nist.gov/4.22.E1) supplies the
infinite products used below. These are source inputs, not claims of
new classical theory.

#### A coefficient comparison lemma

Suppose

```math
U(z)=\prod_{j=1}^{L}(1+u_jz),\qquad
V(z)=\prod_{j=1}^{L}(1+v_jz),\qquad 0<u_j\le v_j.
```

Then the ratio `[z^ell]U/[z^ell]V` is nonincreasing in `ell`.
To see this, increase one factor from `1+uz` to `1+vz`, leaving
the other factors as `H(z)=sum h_ell z^ell`. Its nonnegative
coefficients are log-concave by Newton's inequalities. Hence
`h_(ell-1)/h_ell` is nondecreasing wherever defined. The new coefficient
divided by the old coefficient is

```math
\frac{h_\ell+v h_{\ell-1}}{h_\ell+u h_{\ell-1}},
```

which is nondecreasing in that ratio when `v>=u`. The first and last
indices obey the same comparison by their limiting values. Increasing
the factors one at a time proves the assertion. Zero factor parameters
are allowed by limits, with statements about ratios restricted to
positive denominators.

The same assertion holds for locally uniformly convergent infinite
products with `sum_j u_j<infinity`, `sum_j v_j<infinity`, and
`0<=u_j<=v_j`: apply the finite result to equal-length truncations,
clear denominators, and pass to each fixed pair of coefficients.

#### The two entire functions encoding the ratios

Write `Y=N-2K` and use the unnormalized moment-generating function

**(7)**

```math
M(t)=\sum_{k=0}^N\frac{(a)_k(a)_{N-k}}{k!(N-k)!}e^{(N-2k)t}
    =C_N^{(a)}(\cosh t).
```

The equality follows by extracting the coefficient of `z^N` in
`(1-e^t z)^(-a)(1-e^(-t)z)^(-a)`. Its value at zero is positive;
dividing by it gives the probability moment-generating function.

Define the even entire functions

```math
F(t)=N^2M(t)-M''(t),\qquad G(t)=M'(t)/t,
```

where the singularity in `G` at zero is removed. Directly weighting the
sum in (7) by `N^2-(N-2k)^2=4k(N-k)` gives

**(8)**

```math
F(t)=4a^2 C_{N-2}^{(a+1)}(\cosh t),\qquad
G(t)=2a\frac{\sinh t}{t}C_{N-1}^{(a+1)}(\cosh t).
```

For the first identity, cancel `k(N-k)` against the two factorials,
use `(a)_k=a(a+1)_(k-1)`, and replace `k` by `k-1`. The second
identity is the Gegenbauer derivative formula and the chain rule.

If `m_(2ell)` denotes the unnormalized `Y` moment in (7), then

**(9)**

```math
\frac{[t^{2\ell}]F(t)}{[t^{2\ell}]G(t)}
=(2\ell+1)\left(\frac{N^2m_{2\ell}}{m_{2\ell+2}}-1\right)
=b_\ell.
```

In particular, no additional factor of `N^2` appears outside the ratio.

For `N=2`, `F` is a positive constant. Formula (9) then gives
`b_0>=0` and `b_ell=0` for every `ell>=1`, proving this case.
Assume henceforth that `N>=3`.

#### Comparing the product factors

Let `m=N-2` and `lambda=a+1`. The roots of `C_m^(lambda)` and
`C_(m+1)^(lambda)` are simple, in `(-1,1)`, and strictly interlace.
On each interval `(j*pi,(j+1)*pi)` for integer `j>=0`, the function
`cos y` traverses `(-1,1)` monotonically in one direction. Consequently
the `m+1` zeros of `C_(m+1)^(lambda)(cos y)` bracket the `m` zeros
of `C_m^(lambda)(cos y)`, with a zero of the higher degree first and
last. There is also a zero of `sin y` at the right endpoint.
There are no shared endpoint zeros, since the Gegenbauer polynomials
do not vanish at `+1` or `-1`.

List in increasing order the positive numbers `eta_j` for which
`F(i eta_j)=0`, and the positive numbers `xi_j` for which
`G(i xi_j)=0`. Counting the zeros interval by interval as above proves

**(10)**

```math
0<\xi_j\le\eta_j\qquad(j\ge1).
```

These lists contain all the zeros: if `cosh t` equals a real number
strictly between `-1` and `1`, then `t` is purely imaginary. Each
factor has linearly growing zero locations, so the squared reciprocal
locations are summable.

For completeness, Euler's sine product and
`cosh t-cos theta=2 sin((theta+it)/2)sin((theta-it)/2)` give, for
`0<theta<pi`,

```math
\frac{\cosh t-\cos\theta}{1-\cos\theta}
=\left(1+\frac{t^2}{\theta^2}\right)
 \prod_{j=1}^{\infty}
 \left(1+\frac{t^2}{(2\pi j-\theta)^2}\right)
 \left(1+\frac{t^2}{(2\pi j+\theta)^2}\right),
\qquad
\frac{\sinh t}{t}
=\prod_{j=1}^{\infty}\left(1+\frac{t^2}{\pi^2j^2}\right).
```

Factoring the Gegenbauer polynomials into their real roots therefore
gives locally uniformly convergent products

```math
\frac{F(t)}{F(0)}=\prod_{j\ge1}(1+t^2/\eta_j^2),\qquad
\frac{G(t)}{G(0)}=\prod_{j\ge1}(1+t^2/\xi_j^2).
```

Both constants are positive. Apply the coefficient lemma with
`z=t^2`, `u_j=eta_j^(-2)`, and `v_j=xi_j^(-2)`. Equation (10)
orders the factors in the required direction, and (9) proves the
beta-binomial theorem.


#### Finite Chebyshev alternative to the infinite products

The same coefficient comparison has a finite-polynomial proof, which is
used in the formalization. It retains the actual beta-binomial moments
and requires no convergence theorem for an infinite product.
For an integer `L>=1`, set

```math
h_L(z)=1+\frac{z}{2L^2},\qquad
P_L(z)=C_N^{(a)}(T_L(h_L(z))),
```

where `T_L(cos theta)=cos(L theta)` is the Chebyshev polynomial.
The symmetric finite sum (7) gives the polynomial identity

```math
P_L(z)=\sum_{k=0}^N w_k(a)T_{|N-2k|L}(h_L(z)),\qquad
w_k(a)=\frac{(a)_k(a)_{N-k}}{k!(N-k)!}.
```

For example, this follows first at `x=cosh t` from (7), symmetry of
the weights, and `T_j(cosh t)=cosh(jt)`, and hence as a polynomial
identity; composing with `T_L` uses `T_j(T_L(x))=T_(jL)(x)`.
Let `c_(L,d,r)=[z^r]T_(dL)(h_L(z))`. Differentiating
`T_j(cos theta)=cos(j theta)` twice gives the polynomial identity
`(1-x^2)T_j''(x)-xT_j'(x)+j^2T_j(x)=0`. Expanding this
identity at `1` gives exactly

```math
c_{L,d,0}=1,\qquad
(r+1)(2r+1)c_{L,d,r+1}
 =\frac{d^2-r^2/L^2}{2}\,c_{L,d,r}.
```

Induction on each fixed `r` therefore gives
`c_(L,d,r) -> d^(2r)/(2r)!` as `L->infinity`, including `d=0`.
This proves all needed coefficient limits directly from a finite
recurrence.

Put `m=N-2>=1` and `lambda=a+1`, and form

```math
F_L(z)=4a^2 C_m^{(\lambda)}(T_L(h_L(z))),\qquad
G_L(z)=2P_L'(z)
 =\frac{2a}{L}U_{L-1}(h_L(z))
                 C_{m+1}^{(\lambda)}(T_L(h_L(z))).
```

The latter identity uses the ordinary Gegenbauer derivative formula,
`T_L'=L U_(L-1)`, and the chain rule. In particular all displayed
normalizing constants are positive. These are finite analogues of
`F(sqrt z)` and `G(sqrt z)` in (8).

Use the angle lists in (10), now truncated to
`eta_j<L*pi` and `xi_j<L*pi`. There are exactly `mL` angles of
the first kind and `(m+2)L-1` of the second. The final sine angle
`L*pi` is excluded; the other `L-1` multiples of `pi` supply precisely
the zeros of the `U_(L-1)` factor. Under the strictly decreasing map

```math
r_L(\theta)=2L^2(\cos(\theta/L)-1),\qquad 0<\theta<L\pi,
```

these lists give distinct negative zeros of `F_L` and `G_L`.
They exhaust the respective polynomial degrees. Thus exact polynomial
factorization, normalized by the positive values at zero, yields

```math
\frac{F_L(z)}{F_L(0)}
 =\prod_{j=1}^{mL}(1+u_{L,j}z),\qquad
\frac{G_L(z)}{G_L(0)}
 =\prod_{j=1}^{(m+2)L-1}(1+v_{L,j}z),
```

where
`u_(L,j)=1/[2L^2(1-cos(eta_j/L))]` and
`v_(L,j)=1/[2L^2(1-cos(xi_j/L))]`.
The inequality `xi_j<=eta_j` gives `u_(L,j)<=v_(L,j)`.
Append `2L-1` zero parameters to the first product and apply the finite
coefficient lemma. Restoring the positive constant terms gives, for
all `r>=0`,

```math
[z^{r+1}]F_L\,[z^r]G_L
 \le [z^r]F_L\,[z^{r+1}]G_L.
```

Both cross-products vanish when the index is at or above the degree
of `G_L`. For the remaining indices the finite product comparison
applies directly.

Write `mu_(2r)=sum_k w_k(a)(N-2k)^(2r)`. The coefficient limits above,
and the exact shifted-shape identity behind (8), give

```math
[z^r]F_L\longrightarrow
 \frac{N^2\mu_{2r}-\mu_{2r+2}}{(2r)!},\qquad
[z^r]G_L\longrightarrow\frac{\mu_{2r+2}}{(2r+1)!}.
```

Passing to the limit in the cross inequality is now an inequality
between real sequences. The limiting `G` coefficients are positive
because of the two endpoint atoms. Dividing by them and using
`mu_(2r)=N^(2r) sum_k w_k(a)Y_k^r` recovers (9) and proves the
beta-binomial moment-ratio theorem. This route also verifies that no
extra factor of `N^2` survives outside the moment ratio.


The classical zero-separation input has the usual elementary
orthogonality proof. Rodrigues' expression for the Gegenbauer polynomial
is a nonzero constant times
`(1-x^2)^(1/2-lambda) (d/dx)^m (1-x^2)^(m+lambda-1/2)`.
Integration by parts shows orthogonality to all lower degree polynomials
against the positive weight `(1-x^2)^(lambda-1/2)` on `(-1,1)`;
all boundary terms vanish for the values `lambda>1` used here. If it
had fewer than `m` simple sign-changing zeros there, the product of the
corresponding linear factors would have degree below `m` and its weighted
inner product with the polynomial would have one strict sign,
a contradiction. The three-term recurrence of this orthogonal family
has a positive coefficient on the preceding polynomial, obtained from
the ratio of positive squared norms after monic normalization. Evaluating
that recurrence at consecutive zeros and inducting proves strict
interlacing. Its generating and derivative identities follow by
coefficient differentiation of `(1-2xz+z^2)^(-lambda)`.
Euler's sine product and the paired gamma product used next are standard
classical analytic product identities, with exact source links retained.


### Binomial-escort moment-ratio theorem

Let `N>=2`, `0<=q<=1`, and, for `k=0,...,N`, set

`Y_k=((N-2k)/N)^2`, `w_k=binomial(N,k)^q`,

`A_l=sum_k w_k Y_k^l`, `b_l=(2l+1)(A_l/A_(l+1)-1)`.

Use `Y^0=1`, including at zero. All moments are positive because of the
endpoint atoms `Y=1`.

**Theorem.** `b_l>=b_(l+1)` for every integer `l>=0`.

For `N=2`, one has `A_l=2` for every `l>=1`, so `b_l=0` for `l>=1`
and `b_0>=0`. For the rest of the proof suppose `N>=3`. The case `q=0`
is the preceding beta-binomial theorem at shape `a=1`; the case
`q=1` follows by taking `a->infinity` there. Hence assume `0<q<1`.

Write the symmetric beta-binomial weights, up to any common positive
normalization, as

`v_k(a)=binomial(N,k) Gamma(k+a) Gamma(N-k+a)`, `a>=1`.

For every fixed `a`, their corresponding sequence `b_l^B` is
nonincreasing by the preceding beta-binomial theorem.

### Matching one tilted mean

For a fixed `l>=0`, define the `Y^l`-tilted law by masses proportional
to `w_k Y_k^l`, omitting nodes with zero tilted weight. Let its mean be

`r_l(q)=A_(l+1)/A_l`.

The distinct retained values of `Y` contain at least two points when
`N>=3`; for even `N`, the zero node is simply omitted when `l>0`.
The function `binomial(N,k)` is strictly decreasing as a function of
the distinct `Y` values. Exponential tilting therefore gives

`d r_l(q)/dq = Cov_(q,l)(Y, log binomial(N,K)) < 0`.

This can also be read as a finite pairwise covariance sum: each product
`(Y_i-Y_j)(log C_i-log C_j)` is nonpositive, and one is strictly negative.
Consequently `r_l(q)` lies strictly between the tilted means for the
uniform count law (`q=0`) and the fair binomial count law (`q=1`).

The beta-binomial tilted mean is continuous in `a>=1`. At `a=1` it is
the uniform-count tilted mean, since `v_k(1)=N!` is constant in `k`.
As `a->infinity`, the normalized weights tend to the fair binomial
weights, since `Gamma(a+k)/Gamma(a)` is the finite rising factorial
`(a)_k`. Thus, by the intermediate value theorem, some finite `a>1`
has exactly the same tilted mean as the CMB law:

`r_l^B(a)=r_l(q)`.

No uniqueness or monotonicity of this matching shape is needed.

### The density ratio has at most one valley

Let `c=(N+2)/2`, `h=a-1>0`, and `t=N sqrt(Y)/2`. The CMB/BB ratio,
apart from a positive constant independent of `k`, is

```
[Gamma(k+1) Gamma(N-k+1)]^(1-q)
 / [Gamma(k+a) Gamma(N-k+a)].
```

The even gamma expansion gives its logarithm as `constant+H(Y)`, where

```
H(Y)=sum_{r>=1} d_r Y^r,
d_r=(N/2)^(2r)/r * [(1-q) S_r(c)-S_r(c+h)],
S_r(c)=sum_{j>=0} (c+j)^(-2r).
```

Indeed the unordered pair `{k+1,N-k+1}` is `{c-t,c+t}`, and

`log Gamma(c+t)+log Gamma(c-t)-2 log Gamma(c)
 =sum_{r>=1} S_r(c) t^(2r)/r`.

This identity follows by taking the logarithm of the paired Euler
product for gamma; the underlying product is
[NIST DLMF 5.8.1](https://dlmf.nist.gov/5.8.E1). Specifically,
`Gamma(c+t)Gamma(c-t)/Gamma(c)^2
 =product_{j>=0}(1-t^2/(c+j)^2)^(-1)` for `|t|<c`.
Both the series and all its termwise derivatives
converge uniformly on `0<=Y<=1`: the nearest singularity lies at
`Y=(1+2/N)^2>1`.

We next prove that `S_r(c+h)/S_r(c)` strictly decreases in `r` and tends
to zero. More generally put

`R(s)=sum_j(c+h+j)^(-s) / sum_j(c+j)^(-s)`, `s>1`.

Let `pi_s(j)` be proportional to `(c+j)^(-s)`, and put
`z_j=(c+j)/(c+h+j)`. The sequence `z_j` strictly increases in `j`
and lies in `(0,1)`. If `s_2>s_1>1`, the density ratio
`pi_(s_2)(j)/pi_(s_1)(j)` decreases in `j`. The elementary opposing
covariance inequality gives

```
R(s_2)=E_(s_2)[z_j^(s_2)]
      <E_(s_2)[z_j^(s_1)]
      <=E_(s_1)[z_j^(s_1)]=R(s_1).
```

Also, by integral comparison for a decreasing function,

```
R(s) <= (c/(c+h))^s [1+(c+h)/(s-1)] -> 0.
```

It follows that the coefficient signs of `H` have at most one change,
from negative to positive, and are eventually strictly positive. The
same is true of the nonzero coefficients of `H'`. This implies that
`H'` has at most one zero in `(0,1)`, crossed from negative to positive.
For completeness, if its negative coefficients are below degree `M`
and its positive coefficients have degree at least `M`, divide `H'(y)`
by `y^M`. Every negative lower-degree term then has nonnegative
derivative, and every positive higher-degree term does also. The
quotient is increasing, strictly so unless it is a positive constant.
If there are no negative coefficients, `H'>0` immediately.

Thus `H`, and also any positive constant times `exp(H)`, decreases and
then increases, allowing either monotone case. In particular every
strict sublevel set of the CMB/BB density ratio is an interval. Tilting
both laws by the same `Y^l` changes only the constant in this ratio,
and omits the same zero nodes, so the same conclusion applies to the
two normalized tilted laws.


#### Finite adjacent-ratio alternative to the gamma expansion

For the actual finite grid, the interval-sublevel conclusion also has
an elementary proof using adjacent weights. This is the route used in
the formalization. Keep the weights
`w_k(a)=(a)_k(a)_(N-k)/(k!(N-k)!)`, and define

```math
L_k=q\log\binom Nk-\log w_k(a),\qquad
A(x)=\log(1+x)-\log(1-x).
```

Assume `a>1`. For `0<=k<floor(N/2)`, let

```math
x_k=\frac{N-2k-1}{N+1},\qquad
c=\frac{N+1}{N+2a-1}.
```

Then `0<x_k<1`, `0<c<1`, and the two elementary weight recurrences give

```math
L_{k+1}-L_k
 =\log\frac{a+N-k-1}{a+k}
   -(1-q)\log\frac{N-k}{k+1}
 =A(cx_k)-(1-q)A(x_k).
```

Here `A(x)=2 atanh(x)`, but only its logarithmic expression is needed.
The quotient `A(cx)/A(x)` is strictly decreasing for `0<x<1`.
Indeed the derivative quotient is

```math
\frac{(A(cx))'}{A'(x)}
 =\frac{c(1-x^2)}{1-c^2x^2},\qquad
\frac{d}{dx}\frac{c(1-x^2)}{1-c^2x^2}
 =\frac{-2c(1-c^2)x}{(1-c^2x^2)^2}<0.
```

To justify the implication for the original quotient, use Cauchy's
mean value theorem on `[0,x]` and `[x,y]`, where `0<x<y<1`.
Since both functions vanish at zero and `A'>0`, their two secant
quotients equal derivative quotients at points `u in (0,x)` and
`v in (x,y)`. The first is strictly larger. Since `A(y)>A(x)>0`,
rearrangement gives `A(cx)/A(x)>A(cy)/A(y)`.

As `k` increases, `x_k` decreases, so
`A(cx_k)/A(x_k)-(1-q)` increases. Since `A(x_k)>0`, the adjacent
increments of `L_k` have at most one change from negative to positive.
Consequently `L_k` has interval sublevels on `0,...,floor(N/2)`.
For an explicit finite argument, if `i<=j<=k` and `L_j>L_i`, some
adjacent increment between `i` and `j` is positive. Every later
increment is then nonnegative, so `L_k>=L_j`. Thus always
`L_j<=max(L_i,L_k)`.

Finally `L_(N-k)=L_k`, and `Y_k` is strictly decreasing as a function
of the folded index `min(k,N-k)`. Reversing this finite order preserves
interval sublevels, so the conclusion holds on the squared grid,
including the repeated reflected nodes. Exponentiating and multiplying
by a positive normalization preserve it as well. The common `Y^l`
tilt cancels from the density ratio at every retained node; when
`l>0`, the central zero-weight node is omitted from both laws.
This proves exactly the density property required below. This finite
argument in fact permits every real `q`; the matching step uses only
`0<q<1`.

### Matched mean and one valley imply the required second-moment order

Here is the finite comparison lemma used in the last step. Let `P,Q`
be probability laws on the same finite ordered real support, with
strictly positive masses there, the same mean, and `P(y)/Q(y)` having
interval sublevel sets. Then

`E_P[Y^2]>=E_Q[Y^2]`.

To prove it, let `Delta(y)=P(y)-Q(y)`. Its strictly negative entries
form one consecutive block. If all entries vanish the claim is
immediate. Otherwise the equal mass and mean require a positive entry
on each side of this block: if all positive entries were on only one
side, the signed first moment could not be zero after subtracting a
constant separating that side from the negative block. Choose two
cutpoints `u<v` separating the negative block from the positive
entries on its two sides. Then

`Delta(y)(y-u)(y-v)>=0` for every support point,

and summing gives

`sum_y Delta(y)y^2=sum_y Delta(y)(y-u)(y-v)>=0`,

since both the total mass and first moment of `Delta` vanish. Zero
entries and omitted zero-weight nodes cause no difficulty.

Apply this lemma with `P` the CMB `Y^l`-tilted law and `Q` its matching
beta-binomial tilted law. Their first moments are `r_l^C=r_l^B>0`,
while their second moments satisfy

`A_(l+2)^C/A_l^C >= A_(l+2)^B/A_l^B`.

Dividing by their common first moment yields

`r_(l+1)^C>=r_(l+1)^B`.

Therefore

```
b_(l+1)^C=(2l+3)(1/r_(l+1)^C-1)
         <=(2l+3)(1/r_(l+1)^B-1)
         =b_(l+1)^B <= b_l^B=b_l^C.
```

This proves the theorem. The matching shape may depend on `N,q,l`;
that dependence is harmless because each comparison proves precisely
one consecutive moment inequality.


### The signed midpoint bridge and strict positivity


Let `N>=2`. The remaining law `g` is the sum of one Bernoulli coin of
parameter `p in [0,1/2]` and `N-2` fair coins. The target coin, whose
derivative is evaluated, is fair. Put

```math
\delta=1-2p,\qquad
B_k=2^{-N}\binom Nk,\qquad x_k=(N-2k)/N.
```

Substitution of the binomial coefficient ratios gives

```math
s_k=2B_k(1+\delta x_k),\qquad
d_k=2B_k\left[-x_k+\delta\frac{1-Nx_k^2}{N-1}\right].
```

Fix `0<q<1`, and define the positive even moments

```math
M_\ell=\sum_{k=0}^N B_k^q x_k^{2\ell}\qquad(\ell\ge0),
```

where `x_k^0=1`, including at a central zero. Pairing `k` with `N-k`
and expanding `(1+delta x)^(q-1)` gives, initially for `0<=delta<1`,

**(3)**

```math
\begin{aligned}
D_q(\delta)
&=\frac{2^q\delta}{N-1}\sum_{\ell=0}^{\infty}a_\ell\delta^{2\ell},\\
a_\ell
&=\binom{q-1}{2\ell}
 \left[M_\ell-
   \left(1+\frac{(N-1)q}{2\ell+1}\right)M_{\ell+1}\right].
\end{aligned}
```

For clarity, the coefficient calculation uses
`binom(q-1,2ell+1)=binom(q-1,2ell)(q-1-2ell)/(2ell+1)`.
The even binomial coefficients in (3) are strictly positive.

The series is absolutely convergent even at `delta=1`. Indeed,

```math
0<\binom{q-1}{2\ell}
=\prod_{j=1}^{2\ell}(1-q/j)\le(2\ell+1)^{-q}.
```

The last inequality follows from `log(1-u)<=-u` and
`sum_{j=1}^L 1/j>=log(L+1)`. The two outer nodes have `x_k^2=1`,
while every other node has `x_k^2<=rho<1`. Hence
`M_ell-M_(ell+1)=O(rho^ell)`, and (3) has a summable bound of the form
`O((ell+1)^(-q)rho^ell)+O((ell+1)^(-q-1))`.

At `delta=1`, the biased coin is deterministic, and the remaining
nonzero law is symmetric. Thus `D_q(1)=0`. Continuity is legitimate
even for the vanishing boundary mass: `|d_k s_k^(q-1)|<=s_k^q`, which
tends to zero with `s_k`. Taking the limit in (3) therefore shows

**(4)**

```math
\sum_{\ell=0}^{\infty}a_\ell=0.
```

Define

**(5)**

```math
b_\ell=(2\ell+1)\left(\frac{M_\ell}{M_{\ell+1}}-1\right).
```

The sequence `(b_ell)` is nonincreasing for this binomial escort
law by the comparison just proved, so the sign of `a_ell` changes
at most once, from positive to negative. This follows because

```math
\mathrm{sign}(a_\ell)
=\mathrm{sign}(b_\ell-(N-1)q).
```

Also `b_ell -> 0`, by the same exponential decay of the non-endpoint
moments. Thus the coefficients are eventually negative. A convergent
series whose coefficients have this single-change pattern and sum to
zero satisfies
`sum a_ell delta^(2ell)>=0` for `0<=delta<=1`: the smaller powers
multiply the nonnegative coefficients, and the larger powers multiply
the nonpositive ones. Equation (3) proves the required
low-order sign for the entire one-biased-plus-fair family.

In fact the sign is strict for `0<delta<1`. Since the coefficients
sum to zero and their tail is strictly negative, at least one coefficient
is positive. Choose a separating index `L` with `a_l>=0` before it
and `a_l<0` afterwards. Then

```math
\sum_l a_l\delta^{2l}
=\sum_l a_l(\delta^{2l}-\delta^{2L})>0.
```

All summands are nonnegative and every tail summand is positive.
Absolute convergence justifies the subtraction. Thus
`D_q(Bin(m,1/2)+Bern(p))>0` for every `m>=0`, `0<p<1/2` and
`0<q<1`, including the point-mass fair background.


#### Strictness from the boundary limit alone

The absolute endpoint summation above is valid, but it is unnecessary
for the sign conclusion. The formalization uses the following shorter
argument. Let
`S(delta)=(N-1)D_q(delta)/(2^q delta)` for `0<delta<1`.
Equation (3) is a convergent power series for `S` at every such point.
The actual finite-law continuity just proved gives
`S(delta)->0` as `delta->1` from below, independently of any statement
about summing the series at `1`.

Choose `L` so that `a_l>=0` for `l<L` and `a_l<=0` for `l>=L`,
with `a_(L+1)<0`; the eventually strictly negative tail permits this
choice. For `0<x<y<1`, convergence at these two interior points gives

```math
S(x)y^{2L}-S(y)x^{2L}
 =\sum_{l\ge0}a_l
       (x^{2l}y^{2L}-y^{2l}x^{2L})>0.
```

Each summand is nonnegative: the parenthesis is nonnegative for
`l<L` and nonpositive for `l>=L`. The term at `l=L+1` is strictly
positive. Holding `x` fixed and taking `y->1` first gives `S(x)>=0`.
Next choose any fixed `y in (x,1)`; the same strict cross inequality,
now using `S(y)>=0`, gives `S(x)>0`. Thus the actual boundary limit
and the interior series already prove the required strict midpoint
sign. There is no use of (4) or of absolute convergence at the endpoint
in this alternative.


## 8. Uniform order windows and support-changing boundaries


### Statement and normalization

**Theorem.** For every integer `N>=1`, there exist
`eta_N,zeta_N in (0,1/2]`
such that, for every pair of parameter vectors satisfying
`0<=u_i<=v_i<=1/2`, both Rényi and Tsallis entropy obey

**(U1)**

```math
H_q\!\left(\sum_{i=1}^N\mathrm{Bern}(u_i)\right)
\le H_q\!\left(\sum_{i=1}^N\mathrm{Bern}(v_i)\right),
\qquad q\in[0,\eta_N]\cup[1-\zeta_N,2],
```

and the same inequality with `T_q` in place of `H_q`. All summands are
independent. Zero and fair parameters are included. The `[1,2]` part
was proved in Section 3.
No dimension-independent positive lower bound on either width is asserted.

For a probability sequence `g` extended by zero, write

**(U2)**

```math
s_k=g_{k-1}+g_k,\qquad d_k=g_{k-1}-g_k,\qquad
D_q(g)=\sum_k d_k s_k^{q-1}.
```

For `q>0`, a zero adjacent pair contributes zero. For a positive
sequence on its actual finite support, also define the auxiliary
`D_0=sum_k d_k/s_k` on its nonzero adjacent pairs. This auxiliary value
is the limit in order for a fixed positive support; it is **not** an
order-zero entropy derivative and need not be continuous when support
points disappear.

We prove, for every `n>=0`, that there is a number
`theta_n in (0,1/2]` such that `D_q(g)>=0` for every `n`-coin law
with parameters in `[0,1/2]` and every `0<q<=theta_n`.
On that interval, equality holds exactly when every parameter is in
`{0,1/2}`: after removing zero coins, the law is fair binomial.
At `n=0`, `g=(1)` and `D_q=0`; take `theta_0=1/2`.
The interval at zero will use `eta_N=theta_(N-1)`. A normalized
functional below supplies the separate interval below one.

### Strict positivity at auxiliary order zero

Suppose `n>=1` and all parameters are in `(0,1/2]`. Put
`w_i=p_i/(1-p_i) in (0,1]` and `g_k=g_0 e_k(w)`, where `e_k` is
the elementary symmetric polynomial. Counting subsets gives

**(U3)**

```math
k e_k(w)=\sum_{|A|=k-1}w_A\sum_{i\notin A}w_i
\le(n-k+1)e_{k-1}(w),\qquad 1\le k\le n.
```

Consequently `alpha_k=g_(k-1)/(g_(k-1)+g_k)>=k/(n+1)`.
If any parameter is strictly below one half, the inequality is strict:
for every `k` there is a positive-weight `(k-1)`-subset omitting that
parameter, with strictly deficient inner sum. The endpoint scores are
`2alpha_0-1=-1` and `2alpha_(n+1)-1=1`. Therefore

**(U4)**

```math
D_0(g)=2\sum_{k=1}^n
 \left(\alpha_k-\frac{k}{n+1}\right)>0
```

unless all coins are fair. On the positive-support region, `D_q` is
jointly smooth in the coin parameters and the real order near zero.
Thus every positive nonfair parameter vector has a neighborhood and
a positive order interval on which `D_q>0`.

### A neighborhood of the fair vector

At the all-fair vector, symmetry gives `D_q=0` for every real `q`.
The zero-order coordinate derivatives there are strictly negative.
To see this, omit coin `i` and write its remaining law as `h`. For a
varied parameter `p`, set

```math
a=h_{k-2},\quad b=h_{k-1},\quad c=h_k,\qquad
s=pa+b+(1-p)c,\quad d=pa+(1-2p)b-(1-p)c.
```

Direct differentiation gives

**(U5)**

```math
\partial_p(d/s)=-\frac{2(b^2-ac)}{s^2}.
```

At the fair vector, `h` is a fair binomial law, so every numerator
`b^2-ac` is nonnegative; at `k=1` it equals `h_0^2>0`.
In fact, binomial substitution and summation give the exact value

**(U6)**

```math
\left.\partial_{p_i}D_0\right|_{p=(1/2,\ldots,1/2)}
=-\frac8n\sum_{k=1}^n\frac{k}{n+1}
 \left(1-\frac{k}{n+1}\right)
=-\frac{4(n+2)}{3(n+1)}<0.
```

All adjacent masses remain bounded away from zero on a sufficiently
small neighborhood of this vector. Joint continuity of the finitely
many coordinate derivatives therefore gives a one-sided fair cube and
`q_fair>0` on which all `partial_(p_i) D_q<0`, simultaneously for
`0<=q<=q_fair`. Raise each coordinate to one half within that cube.
The value decreases to zero, so its starting value is nonnegative,
strictly positive unless every coin was already fair. This supplies
the required local order interval at the only zero of (U4).

### Uniform control when small coins are added

The following estimate handles the support change without interchanging
the limits of the order and the small parameters.

**Boundary lemma.** Let `h=(h_0,...,h_m)` be a probability vector with
`h_j>=c>0` for all `j`, where `c<=1`. Let `r` be the law of finitely
many additional independent Bernoulli variables with parameters `a_i`
and total `epsilon=sum_i a_i<=1/4`. Put `g=h*r`. For every
`0<q<=1/2`, if `epsilon>0`,

**(U7)**

```math
D_q(g)\ge D_q(h)-C\epsilon+B\sqrt\epsilon,
\qquad C=\frac{16}{c},\quad
B=\frac13\sqrt{\frac c2}.
```

If `epsilon=0`, then `g=h` and their functionals are equal.
In particular `D_q(g)>=D_q(h)` for all these orders whenever

**(U8)**

```math
0\le\epsilon\le\min\left\{\frac14,
 \left(\frac{B}{2C}\right)^2\right\}
=\min\left\{\frac14,\frac{c^3}{18432}\right\}.
```

There is no Poisson-binomial requirement on the positive core `h` in
this lemma. Its proof uses that structure only for the added small law.

**Old pairs.** Coupling to the event that every added coin is zero gives
`r_0>=1-epsilon`, `g_j>=r_0 h_j`, and
`sum_j |g_j-h_j|<=2epsilon`, with `h` zero-extended. The old pairs
have indices `0,...,m+1`. Their adjacent sums, along the line segment
between `h` and `g`, are at least `c/2`.
For `Phi_q(a,b)=(a-b)(a+b)^(q-1)`, put `y=(a-b)/(a+b)`.
Its partial derivatives are

**(U9)**

```math
\partial_a\Phi_q=s^{q-1}[1+(q-1)y],\qquad
\partial_b\Phi_q=s^{q-1}[-1+(q-1)y].
```

Since `|y|<=1`, `s>=c/2` and `0<q<=1/2`, both absolute values
are at most `4/c`. Each coefficient change occurs in at most two old
pairs. Thus the total old-pair loss is at most
`(4/c)·2·sum_j |g_j-h_j|<=16epsilon/c`.

**New pairs.** Let `omega=sum_i a_i/(1-a_i)<=2epsilon`. The
elementary-symmetric counting identity for the small law implies

**(U10)**

```math
(j+1)r_{j+1}\le\omega r_j\quad(j\ge0),\qquad
g_{m+j+1}\le\frac{\omega}{j+1}g_{m+j}\quad(j\ge0).
```

For the second inequality, expand
`g_(m+j)=sum_(i=0)^m h_(m-i) r_(j+i)` and use the first termwise.
It includes zero coefficients beyond the support. In particular every
new difference `g_(k-1)-g_k` with `k>=m+2` is nonnegative.
Moreover

**(U11)**

```math
g_{m+1}\ge h_m r_1\ge c(1-\epsilon)\epsilon
\ge c\epsilon/2,
\qquad g_{m+2}\le\tfrac12 g_{m+1}.
```

Here `r_1=r_0 omega` and `omega>=epsilon`. The first new pair
therefore has score at least `1/3` and adjacent mass at least
`c epsilon/2`. Its contribution is at least
`(c epsilon/2)^q/3 >= sqrt(c epsilon/2)/3`, because
`0<c epsilon/2<=1` and `q<=1/2`. Every later pair contributes
nonnegatively. Combining this gain with the old-pair bound proves
(U7). Under (U8), `Cepsilon<=B sqrt(epsilon)/2`, which proves the
claimed domination. This argument includes `m=0`, repeated small
parameters, and additional zero parameters.

### Covering the entire parameter cube

Fix `n>=1`.
Consider a boundary vector with exactly `m<n` positive coordinates.
If its positive core is nonfair, (U4) supplies a core neighborhood
and a positive order cutoff on which `D_q(h)>0`. If that core is
all-fair, (U5)--(U6) supply a core neighborhood and a positive order
cutoff with `D_q(h)>=0`. If `m=0`, the core is the fixed point mass
and `D_q(h)=0` for every order under consideration.

Shrink the core neighborhood so that its positive coordinates stay
bounded away from zero; all its mass coefficients then have a common
lower bound `c>0`. The other `n-m` coordinates have arbitrarily small
total `epsilon`. Choose that total to satisfy (U8). The boundary lemma
gives `D_q(g)>=D_q(h)>=0` throughout the resulting neighborhood,
for every positive order up to the smaller of the core cutoff and
`1/2`. If all additional coordinates are zero, use its equality case.
This argument uses only the already proved local positive-core facts,
not an induction hypothesis or a global lower-dimensional theorem.

Every point of the compact cube `[0,1/2]^n` now has a relative open
neighborhood and a positive order cutoff on which the desired sign
holds: use the boundary argument when some coordinate is zero,
(U4) and continuity at positive nonfair points, and (U5)--(U6) near
the all-fair vector. A finite subcover exists. Take `theta_n` to be
the minimum of its finitely many positive cutoffs and `1/2`.
This is positive and works on the entire closed cube,
without requiring continuity of `D_0`
across a support change.

The same cover proves the stated equality characterization. Positive
nonfair core neighborhoods have a strict sign, and the fair-core
neighborhood has a strict sign away from its all-fair point. When any
added small coin is positive, (U8) leaves a strictly positive gain
`B sqrt(epsilon)/2`. When all those coins are zero, only the core
remains. Conversely, any collection of zero and fair coins has a
symmetric mass sequence and therefore `D_q=0`.

### A second uniform interval below order one

Because `sum_k d_k=0`, the normalized functional can be written
without a singular constant:

**(U13)**

```math
J_q(g)=\frac{D_q(g)}{1-q}
 =\sum_k d_k W_{1-q}(s_k),\qquad
W_\alpha(s)=\frac{s^{-\alpha}-1}{\alpha},\quad
W_0(s)=-\log s.
```

The extension at `q=1` is `J_1=-sum_k d_k log s_k`; it is not
the identically zero functional `D_1`. Zero adjacent pairs contribute
zero for `q>=1/2`, including `q=1`, by the continuous scalar extension.
On every positive fixed support, `J_q` and its parameter derivatives
are jointly smooth through order one.

For every positive nonfair half-cube law, Section 4 proves `J_1(g)>0`.
That strict statement is essential here: the identically zero `D_1` and
the weak Shannon limit would not suffice.

#### The fair gradient at the Shannon endpoint

There is also a direct negative-gradient proof at the fair vector.
Put `M=n+1>=2` and let `K` have law `Bin(M-2,1/2)`. Differentiating
the finite logarithmic sum, using the same `s,d` as in (U5), gives

**(U14)**

```math
\left.\partial_{p_i}J_1\right|_{\rm fair}
=2E\log\frac{K+2}{K+1}-\frac4M.
```

Indeed, `partial_(p_i)d` is the second difference of the omitted
fair law, while `partial_(p_i)s=2d` at this vector.
The second term is `-2 sum d_k^2/s_k=-4/M`. For the first term,
two finite summations by parts give the logarithm of
`(K+2)(M-K)/[(K+1)(M-K-1)]`; symmetry of `K` gives twice the
expectation in (U14).

An elementary integral bounds this expectation strictly:

**(U15)**

```math
E\log\frac{K+2}{K+1}
=\int_0^1\frac{1-x}{-\log x}
       \left(\frac{1+x}{2}\right)^{M-2}\,dx
<\frac2M(1-2^{-M}).
```

For example, integrate `1/t` from `k+1` to `k+2` and use
`1/t=int_0^1 x^(t-1) dx` to obtain the integral identity for each
integer `k`; finite summation then gives (U15). For `0<x<1`,
strict convexity of `t -> x^t` gives
`(1-x)/(-log x)=int_0^1 x^t dt < (1+x)/2`.
Integrating the resulting polynomial proves the strict upper bound.
Thus (U14) is less than `-4/(M 2^M)<0`.
Joint continuity gives a one-sided neighborhood of the fair vector
and a positive width below one on which every coordinate derivative
of `J_q` stays negative. Integrating to the fair vector gives the
nonnegative sign, strictly away from that vector, just as before.

#### The boundary estimate uniform through order one

Keep the core and added-coin hypotheses of the boundary lemma. For
`q in [1/2,1]`, normalized probability laws have `0<s<=1`, and

**(U16)**

```math
0\le-\log s\le W_{1-q}(s)\le s^{-1}-1,\qquad
|W_{1-q}'(s)|=s^{q-2}.
```

The lower bound follows from `e^x>=1+x`; the upper bound follows
from convexity of `alpha -> s^(-alpha)` on `[0,1]`, or its limit
at zero. Each partial derivative of `(a-b)W_(1-q)(a+b)` has
absolute value at most `W_(1-q)(s)+s^(q-1)<=2/s`.
On the old pairs this is at most `4/c`, so their total loss is
again at most `16epsilon/c`.

Every new pair is decreasing by (U10), hence contributes
nonnegatively to `J_q`. For the first one, (U11) gives
`d>=c epsilon/4`. Its adjacent mass is at most `epsilon`: either
of its two possible totals exceeds the maximum `m` of the core,
so their combined probability is at most the probability that
some added coin is one. Therefore (U16) gives

**(U17)**

```math
J_q(g)\ge J_q(h)-\frac{16}{c}\epsilon
 +\frac c4\epsilon\log(1/\epsilon),
\qquad \frac12\le q\le1.
```

For `0<epsilon<=min(1/4,exp(-128/c^2))` the gain strictly
dominates the loss. For `epsilon=0`, the two functionals are equal.
This includes a point-mass core and arbitrarily many added small
or zero coins. No division by `1-q` remains in the estimate.

The same finite-cover argument now applies with `J_1` in place
of `D_0`: use Section 4 strictness at positive nonfair cores,
(U14)--(U15) at fair cores, the trivial point-mass core, and
(U17) at support-changing boundaries. It gives, for every `n`,
some `rho_n in (0,1/2]` such that `J_q(g)>=0` throughout the
closed `n`-coin half-cube for `1-rho_n<=q<=1`.
For `n=0`, take `rho_0=1/2` directly.
The strict local arguments also give equality exactly when all
parameters lie in `{0,1/2}`. The width is nonexplicit and depends
only on the dimension. Take `zeta_N=rho_(N-1)` and use the
coordinate reduction in Section 1, together with Section 3, to obtain
the stated entropy intervals.


## 9. The actual mass gradient has at most three sign changes


Fix 0<q<1, N>=1, and positive masses g_0,...,g_N whose probability
polynomial is a product of N Bernoulli factors with parameters in (0,1).
Use zero extension. Put

D_q(g)=sum_k (g_(k-1)-g_k)(g_(k-1)+g_k)^(q-1),
B_k=partial D_q/partial g_k, 0<=k<=N.

**Theorem.** After zero entries are deleted, B has the sign pattern
negative, positive, negative, positive, with any blocks allowed to be
empty. In particular V(B)<=3. The theorem does not require the half-cube
restriction. For positive half-cube laws, B is not identically zero.

### A scalar threshold and its strict monotonicity

For b>0 write

`F_b(t)=[q b+(2-q)t](b+t)^(q-2)`, t>=0.

Then

B_k=F_b(c)-F_b(a),
F_b'(t)=(2-q)(1-q)(b-t)(b+t)^(q-3),                    (G1)

where a=g_(k-1), b=g_k, c=g_(k+1). Thus F_b increases strictly up
to t=b and decreases strictly thereafter. On an increasing triple
0<=a<b<c there is a unique c_*(a,b)>b with F_b(c_*)=F_b(a), and B is
positive, zero or negative as c is below, equal to or above c_*.

Put x=(b-a)/(b+a), so 0<x<=1. At the zero let
y=(c_*-b)/(c_*+b). Define alpha=1-q and
H(r)=(1-alpha r)(1+r)^alpha. Direct substitution in (G1) gives

H(x)=H(-y),
integral_0^x t/(1+t)^q dt = integral_0^y t/(1-t)^q dt. (G2)

The right integral is strictly increasing in y in (0,1). Existence
also follows from F_b; and (G2) implies 0<y<x, since the right integrand
is strictly larger than the left at the same positive argument.

Set u=1/x>=1 and v=1/y>u. Changing variables in (G2) yields

integral_u^infinity phi_+(t)dt
 = integral_v^infinity phi_-(t)dt,
phi_+(t)=t^(q-3)(t+1)^(-q),
phi_-(t)=t^(q-3)(t-1)^(-q).                           (G3)

The densities are positive and integrable on these tails. In particular
v>u>=1, so no singular endpoint is used. Write c0=v-u. For a fixed shift
c>0 define rho_c(t)=phi_-(t+c)/phi_+(t), t>=1. When 0<c<=1,

sign (log rho_c)'(t)
 = sign [(3c-2q)t(t+c)-(3-q)c(1-c)].                  (G4)

All denominators omitted in this sign statement are strictly positive.
For c=2q/3 the expression is strictly negative, and rho_c(t) tends to
1 as t tends to infinity; hence rho_c>1 everywhere. For c=1,
rho_1(t)=((t+1)/t)^(2q-3)<1 everywhere. Comparing the two tail integrals
in (G3) with these fixed shifts proves

2q/3<c0<1.                                           (G5)

For every fixed c in that interval, the expression in (G4) strictly
increases with t and has at most one zero. Also
log rho_c(t)=(2q-3c)/t+O(t^(-2)), so rho_c approaches 1 from below.
Consequently, if rho_c(u)<=1, then rho_c(t)<1 for all t>u: before its
possible minimum it decreases, and after the minimum it increases to
1 from below. This would make the right tail in (G3), after translation
by c, strictly smaller than the left tail. At the actual shift c0,
tail equality therefore forces

phi_-(v)>phi_+(u).

Implicit differentiation of (G3) now gives

v'(u)=phi_+(u)/phi_-(v)<1.

Thus c0=v-u strictly decreases with u, or strictly increases with x.
Define

kappa_q(x)=c0/(2-c0).

This is a strictly increasing function on 0<x<=1 (continuous at x=1,
with the derivative understood from the left). Its bounds from (G5)
are q/(3-q)<kappa_q(x)<1.

At the zero triple, elementary substitution gives

(b^2-a c_*)/[b(a-2b+c_*)]
 = (x-y)/(2xy-x+y) = c0/(2-c0)=kappa_q(x).            (G6)

In particular its numerator and denominator are both strictly positive.
For any increasing triple with J=a-2b+c>0 and T=b^2-ac>0,
kappa=T/(bJ) strictly decreases as c increases at fixed a,b:

partial_c kappa=-(b-a)^2/[b(a-2b+c)^2]<0.

Thus, with x=(b-a)/(b+a),

sign B_k = sign [kappa-kappa_q(x)]                    (G7)

on this increasing convex part of a strictly log-concave sequence.
If instead J<=0 on an increasing triple, B_k>0 directly: writing
r=b-a>0, t=c-b>0, one has r>=t, and (G1) integrates to

B_k/[(2-q)(1-q)]
 = integral_0^r w/(2b-w)^(3-q)dw
   -integral_0^t w/(2b+w)^(3-q)dw >0.                 (G8)

### The Poisson-binomial cubic gate

For four consecutive coefficients a=g_(k-1), b=g_k, c=g_(k+1),
d=g_(k+2), k=0,...,N-1, define

U=b^2 c+a b d-2a c^2,
V=b c^2+a c d-2b^2 d.

The identities proved in Section 2, attributed to Hillion–Johnson
Appendix A (33)–(34), read

U=sum_i p_i(1-p_i)^2 Delta_i(k),
V=sum_i p_i^2(1-p_i) Delta_i(k),                       (G9)

where h_i is the omitted-coin coefficient law and

Delta_i(k)=det[[h_i(k),h_i(k+1),h_i(k+2)],
               [h_i(k-1),h_i(k),h_i(k+1)],
               [h_i(k-2),h_i(k-1),h_i(k)]].

These determinants are strictly positive for every k=0,...,N-1.
Indeed they are contiguous three-row Toeplitz minors of N-1 positive
Bernoulli factors; the bidiagonal Cauchy--Binet proof shifts all three
rows in k of those factors and keeps them fixed in the others. This
also proves the boundary identities Delta_i(0)=h_i(0)^3 and
Delta_i(N-1)=h_i(N-1)^3. For N=1 the omitted law is the point mass
and the sole determinant is 1. Hence U+V>0.

When J=a-2b+c and J'=b-2c+d are both positive, direct subtraction gives

kappa_(k+1)-kappa_k
 = (c-b)(U+V)/(bc J J').                              (G10)

Thus kappa strictly increases on every increasing positive-J block.
This strict increase is the normalization required by the scalar threshold.

### Assemble the sign pattern

Strict log-concavity makes g unimodal, with at most two equal adjacent
maximum values. The positive first-difference branch is strictly
log-concave: its coefficients are a same-sign branch of the real-rooted
polynomial (1-z)P(z). The real-rooted derivative argument in Section 2 proves this assertion,
including the initial zero-extension edge. Consequently J>0 on the increasing side
is an initial block; after that block, increasing triples have J<=0.

Within the initial block, x_k=(g_k-g_(k-1))/(g_k+g_(k-1)) strictly
decreases with k, by strict log-concavity of g. Therefore (G10) and
the strict increase of kappa_q imply that
kappa_k-kappa_q(x_k) strictly increases. By (G7), the gradient signs
there are a negative block followed by a positive block, with at most
one zero between them. Equation (G8) makes every subsequent increasing
triple positive. Cases c=b>a are also strictly positive by (G1).

Reflecting g reverses and negates B. Applying the same result to the
reflected increasing tail proves that the original decreasing tail
has a negative block followed by a positive block. Cases a=b>c are
strictly negative. At a single strict mode, both a and c are below b,
so (G1) makes sign B equal sign(c-a). A two-point plateau contributes
one positive entry and then one negative entry. These central cases
join the two tails with at most one positive-to-negative change.
The full pattern is therefore negative, positive, negative, positive,
with empty blocks and zero entries allowed. This proves V(B)<=3.

### Nonvanishing on the positive half cube

For p_i<=1/2 let w_i=p_i/(1-p_i)<=1. If B_0 is nonzero, there is
nothing to prove. If B_0=0, then a=0, b=g_0 and c=g_1 form the zero
triple above. Equation (G6) and kappa_q(1)<1 give c/b>3, in particular
u=g_1/g_0=sum_i w_i>2. Thus N>=3 and

g_2/g_0=e_2(w)=(u^2-sum_i w_i^2)/2>=u(u-1)/2>1.

If g_2<=g_1, then g_0<g_2<=g_1 and (G1) gives B_1>0 directly.
If g_2>g_1 and J_1<=0, use (G8). If g_2>g_1 and J_1>0,
the strict increase in (G10), together with x_1<x_0=1, gives
B_1>0 by (G7). Thus B is never identically zero. For N=1,2,
the alternative B_0=0 was already ruled out by u<=N<=2.
The degree-zero point mass is separate and has D_q=B_0=0.


## 10. Shift annihilation and variation under convolution

Let `H(z)=sum h_k z^k` be a product of `M` positive Bernoulli factors.
Suppose a nonzero vector `B=(B_0,...,B_N)`, `N=M+r`, satisfies
`sum_k h_(k-j)B_k=0` for `0<=j<=r`. Then `V(B)>=r+1`, where zeros
are removed before sign changes are counted. Here is the full argument.


Let `T_(j,k)=h_(k-j)`, `0<=j<=r`, `0<=k<=N`.

Every minor of T is nonnegative. Indeed its Toeplitz extension is a
product of M upper bidiagonal matrices with positive diagonal 1-p and
superdiagonal p. Each factor is totally nonnegative, as is their product
by finite Cauchy--Binet. Truncation to indices 0,...,N suffices.

Every maximal minor of T is strictly positive. For chosen columns
k_0<...<k_r, put b_j=k_j-j. Then
0<=b_0<=...<=b_r<=M. At step l=0,...,M use indices
j+min(l,b_j). They are strictly increasing and each stays or advances
one place at each step. This produces a strictly positive product of
bidiagonal minors in Cauchy--Binet. All other summands are nonnegative.
When M=0, the only maximal minor is the identity determinant.

It would be incorrect to claim that every minor of T is strict: its
edge entries can vanish. Here is the explicit repair. Let
C_(i,j)=1/(i+j+1), 0<=i,j<=r. This square Hilbert matrix is strictly
totally positive by the Cauchy determinant formula. Any k chosen
columns of T are linearly independent, because they extend to a
positive maximal minor. Some k-row minor on those columns is therefore
nonzero, and hence positive by total nonnegativity. Cauchy--Binet now
shows that every k-minor of A=CT is strictly positive. The matrix C is
invertible, so A and T have the same kernel.

For a vector v, let V(v) count sign changes after deleting zero entries.
A strictly totally positive R by L matrix A has the elementary property

Av=0, v!=0  ==>  V(v)>=R.                              (Z4)

Here is a proof to fix the zero-entry convention. If v has s<R sign
changes, choose integer cuts c_1<...<c_s between successive nonzero sign
blocks. Restrict A to its first s+1 rows, write its columns as C_k,
and put U_j=C_(c_j)+C_(c_j+1). Then
w_k=det[U_1,...,U_s,C_k] has sign (-1)^(s-j) when exactly j cuts are
strictly smaller than k. Multilinearity gives no oppositely signed
terms; at least one term is nonzero by choosing the left column at cuts
to the left of k and the right column at cuts to its right. This remains
valid for adjacent cuts. For s=0 use the positive first row. After one
overall sign change, v_k w_k>0 at every nonzero v_k. Expansion in the
last column puts w in the row span of A, contradicting Av=0.

Apply (Z4) with `R=r+1`. Since the kernels of `A` and `T`
coincide, this proves the asserted shift-annihilation bound.


### Positive convolution preserves sign orientation at equality

Write H(z)=sum_l h_l z^l. Put `u_j=sum_l h_l B_(j+l)`.
This is a composition of the maps

(v_0,...,v_M) -> ((1-p)v_0+p v_1,...,(1-p)v_(M-1)+p v_M)

for the coin factors of H, each with 0<p<1. For any real finite v,
with zero entries deleted when counting signs, each such map satisfies
V(output)<=V(v). Indeed insert each weighted average between its two
inputs. The inserted value has one of their signs, or is zero, so this
interleaved sequence has exactly V(v) sign changes. Deleting all the
original entries cannot increase the count.

Moreover, if the nonzero output has exactly V(v) sign changes, its
first and last nonzero signs equal the respective signs of v. If its
last sign differed, the interleaved sequence would have at least one
additional sign change after the last retained nonzero output entry;
deleting this terminal block would strictly lower the count. The
first endpoint is identical. Iteration proves both assertions for H.
When H=1, they are identities.


## 11. A first contact on a compact order band

Suppose the theorem fails. Section 1 and the already proved orders
`[1,2]` and zero give a negative `D_q` at some `0<q<1`. Choose the
smallest number `N` of positive background coins among all such failures.
Section 6 gives `N>=3`; every law with fewer positive coins has
`D_q>=0` at every order in `(0,1)`.

Set `F(q,p)=D_q(g_p)` for `p in [0,1/2]^N`. The uniform windows in
Section 8 give a compact band `[a,b]` inside `(0,1)` containing every
possible negative order, with neighborhoods of its endpoints free of
negative values. `F` is jointly continuous on this band and the cube,
since each summand has absolute value at most `s^q` and `q>=a>0`.

Negative points stay uniformly away from zero-coordinate faces. Near a
point of such a face, split its positive core `h` from its small added
coins, whose parameters sum to `epsilon`. All core masses are at least
some `c>0` in a relative neighborhood. The old/new pair proof of (U7)
works uniformly for `q in [a,b]`, with its new-pair gain replaced by

**(L1)**

```math
D_q(g)\ge D_q(h)-16\epsilon/c+B_b\epsilon^b,
\qquad B_b=(c/2)^b/3>0.
```

Indeed the score of the first new pair is at least `1/3`, its adjacent
mass at least `c epsilon/2`, and the later new pairs are nonnegative.
Minimality of `N` gives `D_q(h)>=0`. Since `b<1`, the last term
dominates the linear loss for sufficiently small positive `epsilon`.
A finite cover of the compact union of zero faces supplies one positive
lower bound on every coordinate of every negative point. This explicitly
controls the new tail rather than using a support-discontinuous order-zero
limit.

Negative points also stay uniformly away from the all-fair corner.
There `F=0` by reflection. Section 5 makes every coin partial derivative
strictly negative for `q in [a,b]`. Compactness and continuity give a
one-sided fair box and `kappa>0` on which all partials are at most
`-kappa`. Integrating to the corner within that box gives

```math
F(q,p)\ge\kappa\sum_i(1/2-p_i)>0
```

away from the corner itself. This excludes a corner neighborhood;
it makes no unsupported claim about all faces having a fair coordinate.

Let `M(q)=min_p F(q,p)`. Compactness and joint continuity make `M`
continuous; the fair corner ensures `M(q)<=0`. The nonempty open set
`{q:M(q)<0}` lies away from the endpoints. Its infimum `q_*` is
interior and satisfies `M(q_*)=0`. Choose negative orders tending to
`q_*` from above and a minimizing parameter vector at each. A convergent
subsequence tends to `p_*`, and the two exclusions show that every
coordinate of `p_*` is positive and at least one is biased. Continuity
then gives

**(L2)**

```math
F(q_*,p_*)=0,\qquad F(q_*,p)\ge0\quad
(p\in[0,1/2]^N).
```

The contact lies on positive support. All interior coordinate derivatives
vanish, their Hessian is positive semidefinite, and the partial derivative
at each fair coordinate is nonpositive because decreasing it is
admissible. The order derivative is also nonpositive, though the later
contradiction does not use it. All these conditions belong to the full
fixed-`N` cube; fair coordinates have not been deleted or incorrectly
made stationary.

## 12. Classifying the parameter pattern at contact

Fix the contact and write `q=q_*`, `P(z)=prod_i f_(p_i)(z)`,
`f_a(z)=1-a+az`, `xi_a=-(1-a)/a`. Let `B=grad_g D_q` and let
`L(V)=sum B_k [z^k]V`. Section 9 makes `B` nonzero with at most three
changes; its only possible three-change orientation is `-,+,-,+`.
Homogeneity and stationarity give

**(O1)**

```math
L(P)=qD_q=0,\qquad L((z-1)P_i)=0,
\qquad L(P_i)=L(zP_i)=0
```

for every interior omitted coin. If two equal interior coins are
perturbed oppositely, their polynomial product is
`f_a^2-t^2(z-1)^2`. The first mass derivative vanishes, so local
minimality implies

**(O2)**

```math
C_a=L((z-1)^2P/f_a^2)\le0.
```

If `c=1/2` is a fair coordinate, its one-sided condition instead gives

**(O3)**

```math
L(P_c)=-\tfrac12\partial_cF\ge0.
```

### At most two distinct interior values

Select one factor from each of `r` distinct interior groups, leaving
`P=H Q`. The polynomials `Q/f_a` form a basis of degree at most `r-1`:
evaluation at the distinct roots isolates their coefficients. Equations
(O1) annihilate `H` times this basis and its one-step shifts; together
with Euler they annihilate `H z^j` for `0<=j<=r`. The shift bound
in Section 10 gives `V(B)>=r+1`, so `r<=2`.

### At most one interior value repeats

Select two factors from each of `t` distinct repeated interior groups,
so `Q=prod_a f_a^2`. Define `ell(V)=L(HV)` on degree at most `2t`.
It annihilates `Q` and every `Q/f_a`. These span exactly the
polynomials divisible by `P_0=prod_a f_a` in that degree range:
after division by `P_0`, the polynomials `P_0/f_a` span degree at most
`t-1`, and `P_0` adds degree `t`. Thus

**(O4)**

```math
\ell(V)=\sum_a w_a V(\xi_a),\qquad
w_a=\frac{a^2 C_a}{\prod_{b\ne a}f_b(\xi_a)^2}\le0.
```

For the weight formula, (O1) applied to `P/f_a` and `P` implies
`L(P/f_a^2)=a^2 C_a` by writing `f_a=1+a(z-1)` twice. Evaluation
of `Q/f_a^2` isolates the `a`th weight. If one weight is negative,
`ell(z^j)` strictly alternates for `0<=j<=2t`, forcing
`V(B)>=2t`. If every weight vanishes, all `2t+1` shifts vanish,
forcing `V(B)>=2t+1`. Either conclusion contradicts `V(B)<=3` when
`t>=2`.

### The singleton lies below the repeated bias

If `p` repeats and `a!=p` is a singleton, choose `Q=f_p^2 f_a`.
On degree at most three, (O1) annihilates `Q,Q/f_p,Q/f_a`, which
span all polynomials divisible by `f_p`. Hence

```math
\ell(V)=wV(\xi_p),\qquad w=p^3C_p/(p-a).
```

If `C_p=0`, four consecutive shifts vanish, impossible. Thus `C_p<0`.
The four moments `w xi_p^j` alternate. They are a positive convolution
of `B`; equality in the variation count forces their first sign to be
negative. Consequently `w<0`, whence `p>a`.

### No fair factor can coexist with a repeated interior value

Choose `Q=f_p^2 f_c`, `c=1/2`. Euler and interior stationarity
annihilate `Q,Q/f_p`, giving

```math
\ell(V)=wV(\xi_p)+vV(-1).
```

Equation (O3) gives `v(1-2p)^2>=0`, so `v>=0`.
Equation (O2) reads `w p^(-2) f_c(xi_p)<=0`; since
`f_c(xi_p)=(2p-1)/(2p)<0`, it gives `w>=0`.
If both vanish, the four-shift bound is contradicted. Otherwise the
four moments alternate `+,-,+,-`, contradicting the negative-first
three-change orientation preserved by positive convolution.

### No fair factor can coexist with two distinct interior values

Choose `Q=f_a f_b f_c`, `a!=b`, `c=1/2`. The three annihilated
polynomials `Q,Q/f_a,Q/f_b` span all cubics divisible by `f_c`.
Thus `ell(V)=wV(-1)`. Equation (O3) gives
`w(1-2a)(1-2b)>=0`, hence `w>=0`. A zero weight contradicts the
four-shift bound; a positive weight gives the forbidden alternating
orientation again.

If a fair factor remains, these exclusions leave at most one interior
coin. The all-fair case was excluded during localization, and the
one-biased-plus-fair strict sign in Section 7 contradicts `D_q=0`.
Therefore **all parameters are interior**. Since `N>=3`, at most two
distinct values and at most one repeated group leave exactly

**(O5)**

```math
g=\mathrm{Bin}(N,p),\quad\text{or}\quad
g=\mathrm{Bin}(N-1,p)+\mathrm{Bern}(a),
\qquad0<a<p<1/2.
```

In both cases all coin first derivatives vanish and the full coin
Hessian is positive semidefinite. No resolvent inequality has been
assumed in this classification.

## 13. Curvature forces two strict contact signs

Write `H` for the Hessian in the positive mass coordinates, and set

```math
M_2=L((k^2g_k)_k),\qquad
C_q(g)=\sum_{k=1}^N d_k s_k^{q-3}g_{k-1}g_k.
```

We use `C_q` for this cubic edge kernel to avoid confusing it with
the normalized functional `J_q=D_q/(1-q)` of Section 8.


### A mass-Hessian identity

For every direction v supported on {0,...,N},

    H[v,v]=(q-1)L(v^2/g)
      -(q-1)(q-2) sum_(k=1)^N d_k s_k^(q-3)
       (g_k v_(k-1)-g_(k-1)v_k)^2/(g_(k-1)g_k).      (C3)

All displayed divisions use positive masses. The two outer edges have
zero residual and are handled separately, not by a zero-over-zero
convention. To prove (C3), apply the following identity to each interior
edge, with Phi(a,b)=(a-b)(a+b)^(q-1):

    Hess Phi[(u,v),(u,v)]
      -(q-1)(Phi_a u^2/a+Phi_b v^2/b)
    =-(q-1)(q-2)(a-b)(a+b)^(q-3)(bu-av)^2/(ab).

At an outer edge Phi is either a^q or -b^q, and the first term on the
right of (C3) already equals its Hessian. Summing proves the identity.
Homogeneity also gives

    L(g)=qD(g),  H[g,v]=(q-1)L(v).                    (C4)

In particular, zero value and stationarity make the relevant cross
terms with the scaling direction vanish.

### Pure binomial contacts have strict splitting curvature

Let f_p(z)=1-p+pz and P=f_p^N. Put

    C=L((z-1)^2 f_p^(N-2)).

Opposite perturbations of two equal coins leave the first mass derivative
zero and give second derivative -2C. Local minimality therefore gives
C<=0. In fact C<0.

For if C=0, perturb three coins by t,t,-2t. This is admissible in both
directions for small t, and exactly

    P(t)=f_p^N-3t^2(z-1)^2 f_p^(N-2)
                    -2t^3(z-1)^3 f_p^(N-3).

With T=L((z-1)^3 f_p^(N-3)), smoothness on the positive support gives
D(P(t))=-3Ct^2-2Tt^3+O(t^4). The nonlinear mass-Hessian contribution
starts at order four. Thus a local minimum with C=0 forces T=0.

After factoring f_p^(N-3), Euler's identity, first stationarity, C=0
and T=0 annihilate respectively

    f_p^3, (z-1)f_p^2, (z-1)^2 f_p, (z-1)^3.

These form a basis of all polynomials of degree at most three: in the
coordinate w=z-1, f_p=1+pw, the coefficient matrix is triangular with
unit diagonal. Consequently four consecutive shifts of f_p^(N-3)
are annihilated, forcing V(B)>=4. This contradicts the gradient theorem.
The argument uses exactly the base-case bound N>=3 established above.

Now write v_p=p(1-p), K_k=k-Np, and M2=L((k^2 g_k)_k). Along the common
binomial parameter,

    g'_k=g_k K_k/v_p,
    g''_k=g_k[K_k^2-(1-2p)K_k-Nv_p]/v_p^2.

Zero value and stationarity imply L(g)=L((kg_k)_k)=0. Hence

    L(g'')=M2/v_p^2,
    C=M2/[N(N-1)v_p^2]<0.                            (C5)

For the mass direction (kg_k)_k the residual in (C3) is exactly C_q.
Combining (C3)--(C5) and the chain rule yields

    d^2/dp^2 D(Bin(N,p))
      =[q M2-(q-1)(q-2)C_q(g)]/[p^2(1-p)^2].         (C6)

The left side is nonnegative at a coin minimum, whereas qM2<0 and
(q-1)(q-2)>0. Therefore C_q(g)<0.


### Singleton contacts: the exact quadratic moment

Let `P=f_p^(N-1) f_a`, where `0<a<p<1/2` and `N>=3`, and put
`H=f_p^(N-3)`. Section 12 has already proved, on polynomials of
degree at most three,

    ell(V)=L(HV)=w V(xi_p),   w<0,
    C_p=ell((z-1)^2 f_a)<0.

There is a direct polynomial route from this strict splitting sign to
`M_2<0`. For every generating polynomial `P=sum g_k z^k`,

    z P'=sum k g_k z^k,
    z^2 P''=sum k(k-1)g_k z^k.

Stationarity gives `L(zP')=0`, hence `M_2=L(z^2P'')`. The exact
second derivative is

**(C7)**

```math
P''=(N-1)(N-2)p^2 H f_a+2(N-1)pa H f_p.
```

The second term vanishes after multiplication by `z^2` and application
of `L`, because `z^2 f_p` has degree three and vanishes at `xi_p`.
Moreover `xi_p=-(1-p)/p` and `xi_p-1=-1/p`, so

**(C8)**

```math
\ell(z^2 f_a)=(1-p)^2\ell((z-1)^2 f_a)
             =(1-p)^2 C_p.
```

Substitution therefore gives the exact contact identity

**(C9)**

```math
M_2=(N-1)(N-2)p^2(1-p)^2 C_p<0.
```

Every factor multiplying `C_p` is strictly positive when `N>=3`.
In particular the argument includes `N=3`, where `H=1`. This derives
the required second moment from the same root-evaluation identity used
to classify the singleton; it requires no additional cubic-moment sign
argument.


### The common odds tilt

For either contact form, change every odds value by the factor `e^t`:

```math
p_i(t)=\frac{p_i e^t}{1-p_i+p_i e^t},\qquad
g_k(t)=\frac{e^{tk}g_k}{\sum_j e^{tj}g_j}.
```

All parameters are interior, so this path is admissible for both signs
of small `t`. Stationarity, zero value and homogeneity remove the
normalizer from its first two derivatives. In particular `L(kg)=0`,
and the mass-Hessian identity gives

```math
0\le\frac{d^2}{dt^2}D_q(g(t))\big|_{0}
=H[kg,kg]+L(k^2g)
=qM_2-(q-1)(q-2)C_q(g).
```

The adjacent determinant in the residual is
`g_k (k-1)g_(k-1)-g_(k-1)kg_k=-g_(k-1)g_k`.
Since `M_2<0`, `q>0`, and `(q-1)(q-2)>0`, this proves

**(C10)**

```math
M_2<0,\qquad C_q(g)<0.
```

These signs hold at the classified zero contact. No unconditional
cubic-sign assertion for arbitrary Poisson-binomial laws is needed.

## 14. A finite inverse-score association inequality


Let Y take distinct values -1<=y_0<...<y_d<=1 with probabilities mu_i>0,
let E Y=0, and let m_2=E Y^2>0 and m_3=E Y^3. Let 0<=alpha<1.
Let x_i=phi(y_i), where phi is increasing and convex on [y_0,y_d].
It suffices that its sampled secant slopes have these properties, or that
the polygonal interpolant is increasing and convex. Put

```
V(y)=1-alpha*y^2, A=E V=1-alpha*m_2, c=E[Y X],
Cstar=A E[Y X^2]-2c E[X V(Y)], X=phi(Y).
```

Then

```
Cstar >= (m_3/m_2) [Var(X)+alpha*c^2].                 (A1)
```

In particular, if m_3>0 and X is nonconstant, then Cstar>0.
Translations of X do not change either side. No symmetry, log-concavity
or escort formula is assumed for the probabilities in this inequality.

### Ordered-pair identities

For i<j define

```
w_ij=mu_i mu_j (y_j-y_i)^2 (1-alpha*y_i*y_j),
f_ij=y_i+y_j,
h_ij=[(x_j-x_i)/(y_j-y_i)]^2.
```

Every w_ij is positive. Direct finite expansion, using E Y=0, gives

```
W:=sum_(i<j) w_ij =m_2(1+alpha*m_2),
sum_(i<j) w_ij f_ij =(1+alpha*m_2)m_3,
sum_(i<j) w_ij h_ij =Var(X)+alpha*c^2,
sum_(i<j) w_ij f_ij h_ij =Cstar.                      (A2)
```

Thus (A1) is exactly nonnegative covariance of f and h under the
probability weights w_ij/W.

### Positive association on the ordered-pair support

The kernel K(a,b)=(b-a)^2(1-alpha*a*b) for -1<=a<b<=1 obeys

```
partial_a partial_b log K
 =2/(b-a)^2-alpha/(1-alpha*a*b)^2>0.                  (A3)
```

Indeed

```
(1-alpha*a*b)^2-alpha*(b-a)^2
 =(1-alpha*a^2)(1-alpha*b^2)>0.
```

All denominators are positive. Integrating (A3) on a rectangle gives,
whenever a<a'<b<b',

```
K(a,b)K(a',b') >= K(a,b')K(a',b).                    (A4)
```

Only rectangles contained in a<b are needed. The factors mu_i mu_j
cancel in this inequality.

Here is an elementary association argument which also handles the
triangular support i<j. Regard the normalized pair weights as the joint
law of I,J. Given I=i, the law of J is supported on j>i with weights
mu_j K(y_i,y_j). For i<i', restrict the first conditional law to j>i'.
On this common support the likelihood ratio
K(y_i',y_j)/K(y_i,y_j) is nondecreasing in j by (A4).
Consequently the conditional law of J given I=i' stochastically dominates
that restricted first law. To see this without invoking an ordering
result, if pi_j are the first probabilities and R_j is the increasing
likelihood ratio, then for every increasing t_j,

```
E_pi[R t]-E_pi[R] E_pi[t]
 =sum_(j<k) pi_j pi_k (R_k-R_j)(t_k-t_j)>=0.
```

Dividing by E_pi[R] proves the stated comparison. Conditioning the first
law on j>i' only removes indices smaller than every retained index, so
that restricted law in turn stochastically dominates the original first
law. Hence J given I=i is stochastically increasing in i. This argument
also covers a one-point common support. Empty rows carry no probability
and are omitted.

For any two functions F(i,j),G(i,j) increasing separately in i and j,
their conditional covariance given I=i is nonnegative by the same
one-dimensional Chebyshev identity. Also E[F|I=i] and E[G|I=i] increase
with i. Explicitly, for i<i', restricting the old row to j>i' can only
increase its mean of F(i,j); on that common support F(i',j)>=F(i,j);
and the new row stochastically dominates the restricted old row when
applied to the increasing function F(i',j). The same three steps apply
to G, so no value on the absent triangle j<=i is required.
Applying Chebyshev again to these two conditional means,
and using the finite total-covariance identity, gives

```
Cov(F(I,J),G(I,J))>=0.                               (A5)
```

This does not order pairs by their center i+j, nor does it claim that
pair centers totally order secant slopes.

The function f_ij=y_i+y_j is increasing in each index. Convexity of phi
makes its secant slope (x_j-x_i)/(y_j-y_i) nondecreasing in each endpoint.
The slope is nonnegative because phi is increasing, so its square h_ij
is likewise increasing in each index. Apply (A5) to f and h and then
(A2). This proves (A1). If m_3>0 and X is nonconstant, its right side
is strictly positive since Var(X)>0.


For completeness, the four pair expansions can all be checked by
introducing an independent copy `(Y',X')` and taking one half of the
expectation of each symmetric zero-diagonal polynomial. They are
`(Y-Y')^2(1-alpha YY')`, its product with `Y+Y'`,
`(X-X')^2(1-alpha YY')`, and its product with `Y+Y'`.
For the first, the unweighted term gives `m_2` and the correction gives
`alpha m_2^2`, since `E Y=0`. The second gives `m_3+alpha m_2m_3`.
The third gives `Var(X)+alpha c^2` because the two terms involving
`E Y` vanish. The last expansion gives
`(1-alpha m_2)E[YX^2]-2E[YX](E X-alpha E[Y^2X])`.
Thus no pair-count normalization or mean-zero correction is implicit.

## 15. Excluding the contact and proving the theorem

At the contact set

```math
Z=\sum_{k=0}^{N+1}s_k^q,\quad
\mu_k=s_k^q/Z,\quad Y_k=d_k/s_k,\quad
X_k=k-(N+1)/2,\quad \alpha=1-q.
```

Every weight is positive, including the two outer edges. The score grid
in Section 2 makes `Y_k` strictly increasing from `-1` to `1` and
concave in `k`. Therefore the polygonal inverse `phi(Y_k)=X_k` is
increasing and convex: its successive slopes are
`1/(Y_(k+1)-Y_k)`, nondecreasing by concavity. This covers the entire
edge support. We have `E Y=D_q/Z=0`, `m_2>0`, and `Var(X)>0`.
The cubic edge identity gives

```math
C_q(g)/Z=\tfrac14E[Y(1-Y^2)]=-m_3/4.
```

Hence (C10) implies `m_3>0`.

Here are the exact remaining escort identities. On a single edge write
`u=g_(k-1)`, `v=g_k`, `s=u+v`, `y=(u-v)/s`, and
`x=k-(N+1)/2`. Differentiating
`Phi(u,v)=(u-v)(u+v)^(q-1)` in the centered first mass direction
`((x-1/2)u,(x+1/2)v)` gives

```math
s^q\{qxy-[1-(1-q)y^2]/2\}.
```

The corresponding linear functional on the centered squared mass
direction `((x-1/2)^2u,(x+1/2)^2v)` gives

```math
s^q\{qy(x^2+1/4)-x[1-(1-q)y^2]\}.
```

Summing and using `L(g)=L(kg)=0`, plus `E Y=0`, yields

**(ES1)**

```math
A:=1-\alpha m_2=2q c>0,\qquad c=E[YX],
\qquad M_2/Z=qE[YX^2]-E[X(1-\alpha Y^2)].
```

Positivity of `A` follows from `m_2<=1` and `alpha<1`; thus `c>0`.
The left side of the finite inequality (A1) is now

```math
A E[YX^2]-2cE[X(1-\alpha Y^2)]=2c M_2/Z<0.
```

Its right side is strictly positive because `m_3>0`, `m_2>0`,
`Var(X)>0` and `alpha>=0`. This contradiction excludes both contact
forms. The compact first-contact construction therefore excludes every
negative `D_q` in every finite dimension for `0<q<1`.

Section 1 transfers the midpoint sign to coordinatewise monotonicity,
including zero parameters by continuity. Section 3 covers `[1,2]`,
and support counting covers zero. Increasing coordinates successively
proves the main theorem with exactly its stated quantifiers. The empty
sum has entropy zero at every order and is included separately.

## 16. Quantitative gain, equality, and the fair maximum

The following are written consequences of the theorem; their presence
here does not claim that they have been formalized. No optimal-constant
claim is made beyond the explicit one-coin order-two equality check.
Fix `n>=1` and vectors satisfying `0<=p_i<=r_i<=1/2` throughout
this section.


### A quantitative coordinate comparison

For every `0<q<=2`, the gain bound **(E1)** is

```math
T_q(S(r))-T_q(S(p))\ \ge\
\frac{6q}{n(n+1)(n+2)}
\sum_{i=1}^n\left[
\left(\frac12-p_i\right)^2-
\left(\frac12-r_i\right)^2\right].
```

This includes `q=1`, where `T_1=H_1` is Shannon entropy.

Fix a coordinate and let `g` be the law of its `n-1` background coins.
Keep all `n` slots `g_0,...,g_(n-1)`, allowing zero entries, and use zero
extension. Set

```math
d_k=g_{k-1}-g_k\quad(0\le k\le n),\qquad
f_k(t)=(1-t)g_k+t g_{k-1}.
```

Telescoping and normalization give

```math
\sum_{k=0}^n\left(k-\frac n2\right)d_k=1,
\qquad
\sum_{k=0}^n\left(k-\frac n2\right)^2
   =\frac{n(n+1)(n+2)}{12}.
```

Therefore Cauchy--Schwarz gives the dimension-only lower bound **(E2)**:

```math
\sum_{k=0}^n d_k^2\ge\frac{12}{n(n+1)(n+2)}.
```

For `0<t<=1/2`, delete deterministic zero background coins to identify
the actual support. All `f_k(t)` on this support are positive, including
the two outer masses. Slots outside it have both `f_k(t)=0` and `d_k=0`
and are omitted from differentiated sums. For `q!=1`, differentiation of
`T_q=(sum f_k^q-1)/(1-q)` gives **(E3)**:

```math
\frac{d^2}{dt^2}T_q(f(t))
  =-q\sum_{k:f_k(t)>0}d_k^2 f_k(t)^{q-2}
  \le -\frac{12q}{n(n+1)(n+2)},
```

because `0<f_k(t)<=1` and `q<=2`. At `q=1`, differentiate
`-sum f_k log f_k` directly, using `sum d_k=0`; the second derivative
is `-sum d_k^2/f_k(t)` and obeys the same bound.

The established monotonicity theorem implies that the left derivative
at `t=1/2` is nonnegative. The derivative exists there because the
actual support stays positive in a neighborhood of that point.
Integrating (E3) backwards gives

```math
\frac{d}{dt}T_q(f(t))
  \ge\frac{12q}{n(n+1)(n+2)}\left(\frac12-t\right).
```

Integrate this from `a` to `b`, where `0<a<=b<=1/2`. The resulting
inequality also holds at `a=0` by finite-law entropy continuity; no
derivative at a support-changing endpoint is used. Finally, increase
the coordinates from `p` to `r` one at a time. Each background obeys
the same bound (E2), so the coordinate inequalities telescope to (E1).

For a normalization check, at `n=1,q=2`,

```math
T_2(\mathrm{Bern}(t))
 =\frac12-2\left(\frac12-t\right)^2,
```

so (E1) is exact in this case. This does not assert sharpness for other
dimensions or orders.

#### A corresponding Rényi bound

For `q!=1`, the increasing change of variable between the entropies is

```math
H_q=\frac{\log(1+(1-q)T_q)}{1-q},\qquad
\frac{dH_q}{dT_q}=\frac1{\sum_k f_k^q}.
```

For a law on at most `n+1` points, concavity of `x^q` gives
`sum f_k^q<=(n+1)^(1-q)` when `0<q<1`. When `1<q<=2`,
`f_k^q<=f_k` gives `sum f_k^q<=1`. These bounds remain valid throughout
the scalar interval between the two Tsallis values, since
`1+(1-q)T` is affine in `T`. Thus (E1) also gives **(E4)**:

```math
H_q(S(r))-H_q(S(p))\ \ge\
\frac{6q\,(n+1)^{-\max(1-q,0)}}{n(n+1)(n+2)}
\sum_{i=1}^n\left[
\left(\frac12-p_i\right)^2-
\left(\frac12-r_i\right)^2\right],
```

with `q=1` supplied by (E1).

### Equality, the fair maximum, and thinning

For `0<q<=2`, equality in either coordinatewise entropy comparison
holds exactly when `p=r`. Indeed, every summand on the right of (E1)
is nonnegative and it is positive whenever `p_i<r_i`. The increasing
Rényi/Tsallis change of variable preserves strictness. This proof also
covers zero parameters and an increase ending at a fair coin.

At `q=0`, let `m(p)` be the number of strictly positive parameters.
The support is exactly `{0,...,m(p)}`. Consequently equality at order
zero holds exactly when `m(p)=m(r)`, even when `p!=r`.

The unique maximum of either entropy on `[0,1/2]^n` at every
`0<q<=2` is attained at the fair vector, whose count law is
`Bin(n,1/2)`. Equation (E1) yields the explicit deficit **(E5)**:

```math
T_q(\mathrm{Bin}(n,1/2))-T_q(S(p))
 \ge\frac{6q}{n(n+1)(n+2)}
       \sum_{i=1}^n\left(\frac12-p_i\right)^2.
```

At order zero every vector with all coordinates positive attains the
maximum; uniqueness is false there.

Reflection gives a second cube: for `0<=q<=2`, if `1/2<=p_i<=r_i<=1`, then
`H_q(S(r))<=H_q(S(p))` and likewise for Tsallis entropy.
Indeed, `S(p)` has the same entropy as `n-S(p)`, whose law is
`S(1-p)`, and `0<=1-r_i<=1-p_i<=1/2`. The same strictness statement
holds for `0<q<=2`. This reflection does not yield a theorem
for arbitrary mixtures of coordinates on different sides of `1/2`.

A direct application is independent thinning of rare successes.
For fixed `p_i<=1/2`, retain each Bernoulli success independently with
probability `theta`. The retained count has law `S(theta p)`.
Its Rényi and Tsallis entropies increase with `theta` for every
`q in [0,2]`; for `0<q<=2` they increase strictly when `theta` increases
and some `p_i>0`. This concerns thinning probabilities, and does not
claim a new general entropy theorem for arbitrary added noise.


## 17. Optional association supplements

These supplements are outside the initial finite-law formal contract and
are unnecessary for the entropy theorem.


### Extend the finite association parameter interval

The inverse-score inequality in the proof assumes `0<=alpha<1`.
It in fact holds for every `-1<=alpha<=1` with all its other hypotheses
retained. Explicitly, let `Y` be a finite random variable in `[-1,1]`,
`E Y=0`, and `m_2=E Y^2>0`. Let `X=phi(Y)` for an increasing convex
function `phi`, and write `m_3=E Y^3`, `c=E[YX]`. Then **(E6)** is

```math
(1-\alpha m_2)E[YX^2]
 -2cE[X(1-\alpha Y^2)]
 \ge\frac{m_3}{m_2}
           \bigl(\mathrm{Var}(X)+\alpha c^2\bigr)
       \qquad(-1\le\alpha\le1).
```

Here increasing may mean nondecreasing. Zero probabilities may first
be removed and repeated support nodes combined.

For `-1<alpha<0`, the same ordered-pair kernel as in Section 14,

```math
K(a,b)=(b-a)^2(1-\alpha ab),\qquad -1\le a<b\le1,
```

is strictly positive, and

```math
\partial_a\partial_b\log K(a,b)
 =\frac2{(b-a)^2}-\frac\alpha{(1-\alpha ab)^2}>0.
```

Thus the identical conditional-likelihood-ratio argument and the same
four pair identities prove (E6). The interval `0<=alpha<1` is Section 14. For a fixed law and transform, both sides of (E6) are
continuous, indeed affine, in `alpha`; taking limits supplies `-1` and
`1`. This endpoint passage does not divide by a potentially vanishing
pair weight at `alpha=-1`.

The strict consequence also extends: if `m_3>0` and
`Var(X)>0`, the left side of (E6) is strictly positive. Since `E Y=0`,
Cauchy--Schwarz gives `c^2<=m_2 Var(X)`. Moreover `m_3>0` forces
`m_2<1`: equality `m_2=1` would put `Y` on `{−1,1}`, and zero mean
would then imply `m_3=0`. Consequently, throughout `-1<=alpha<=1`,

```math
\mathrm{Var}(X)+\alpha c^2
 \ge\mathrm{Var}(X)-c^2
 \ge(1-m_2)\mathrm{Var}(X)>0.
```

The extension changes no contact hypothesis and does not assert an
unconditional third-moment sign for Poisson-binomial escorts.

### A continuous-law supplement

Equation (E6) also holds for an arbitrary random variable `Y` in
`[-1,1]` with `E Y=0`, `E Y^2>0`, provided `phi` is continuous,
increasing and convex on `[-1,1]`. Continuity on this compact interval
makes `phi` bounded and uniformly continuous.

For each uniform finite grid containing both endpoints, round `Y`
randomly to its two adjacent grid nodes, with the barycentric
probabilities that preserve the conditional mean. Call the result
`Y_m`, with mesh tending to zero. Then

```math
E[Y_m\mid Y]=Y,\qquad E Y_m=0,\qquad
|Y_m-Y|\le\mathrm{mesh}_m,\qquad
E Y_m^2\ge E Y^2>0.
```

Apply the finite theorem to `X_m=phi(Y_m)`. Uniform continuity and
boundedness show that every moment in (E6) converges to its counterpart
for `(Y,phi(Y))`; the denominator tends to the positive number `E Y^2`.
Passing to the limit proves (E6), including `alpha=±1`. The strict
consequence follows again from Cauchy--Schwarz and `m_3>0`.

This is a separate measure-theoretic corollary. It is unnecessary for
the finite Bernoulli-sum theorem and should not delay its formalization.


## 18. Proof and verification boundary

The proof above is linear: coefficient identities and mixing-grid
concavity feed the harmonic theorem and scalar sign variation; the
strict Shannon result and explicit small-coin estimates localize a
first contact; positive convolution and omission identities classify
it; the contact curvature identities and finite pair association then
contradict it. The one-biased-plus-fair boundary exclusion explicitly
includes the beta-binomial and binomial-escort moment comparison.

The base case in Section 6 and the direct cubic identity in Section 4
are stated consolidation choices. The former reduces the necessary
small-background input to an elementary two-coin resolvent identity;
the latter obtains the published Shannon equality mechanism using the
harmonic theorem's already established order-one moment signs. Neither
change deletes a required boundary or turns a numerical check into a
universal proof.

The written proof uses ordinary real analysis, finite linear algebra,
compactness, and real-rooted polynomials. Its original analytic route also
uses the cited classical Euler products. The Lean implementation follows
the finite Chebyshev and adjacent-ratio alternatives proved in Section 7,
and therefore does not require those infinite-product inputs. Every input
of the chosen route is proved within the pinned permitted library closure:
first-contact existence, sampled-score convexity, the actual moment
comparison, Shannon strictness, and the convergent harmonic series all
appear as proved dependencies, not assumptions of the principal theorem.
The final contact contradiction alone would be insufficient coverage.

The private development's actual compiled theorem inventory and validation
record determine its formal status. This manuscript does not certify a
Linux build, Comparator agreement, axiom audit, exported-proof replay,
public release, submission, registration, novelty, or human peer review.
