# Note on scope, provenance, and formalization

Date: 2026-10-10. Repository: **renyi-monotonicity**. Lean package:
**renyiMonotonicity**. Namespace: **RenyiMonotonicity**.

This private project develops a Lean formalization of the written proof in
[Proof.md](Proof.md). The mathematical claim is coordinatewise monotonicity
in the Bernoulli parameters, with the entropy order held fixed. For every
finite `n`, every real `0<=q<=2`, and every `0<=p_i<=r_i<=1/2`, the Rényi
and Tsallis entropies of the corresponding independent Bernoulli sums do
not decrease. Orders zero and one use support cardinality and Shannon
entropy, respectively. Zero and fair parameters are part of the claim.

The written argument is complete. The principal entropy theorem is **not
yet a fully verified Lean theorem**. Compiled partial results, proof
architecture, a declaration containing unresolved hypotheses, and the
mathematical manuscript are different deliverables. Only the actual source
and exact-commit verification record establish the formalization's status.
Private creation does not imply public release, Palomar submission or
registration. Independent AI-agent audits are not human peer review.

## Mathematical provenance

The problem is Conjecture 4.4 of Erwan Hillion and Oliver Johnson,
[*A proof of the Shepp–Olkin entropy monotonicity conjecture*,
arXiv:1810.09791v1](https://arxiv.org/abs/1810.09791v1),
*Electronic Journal of Probability* 24 (2019), article 126,
[DOI 10.1214/19-EJP380](https://doi.org/10.1214/19-EJP380).
Their paper supplies the original conjecture, Shannon monotonicity,
orders zero and two, and counterexamples for every order above two.
Its Proposition 2.8, Appendix A identities (33)–(34), and Theorem 3.6
with the equality argument (19)–(21) are essential attributed antecedents.
Proof.md derives the coefficient identities and mixing-grid inequality,
and includes the strict Shannon midpoint argument rather than importing
them as unproved certificates.

The written argument received independent AI-agent mathematical review and
exact symbolic checks. These are supporting written-proof evidence and do not
certify a Lean proof, external review, priority, or publication. JD Jones is the
responsible human author and maintainer; [Disclosure.md](Disclosure.md) records
the actual AI contributions. No human specialist review is claimed.

The proof combines first-contact localization, an actual mass-gradient
three-change theorem, omission and splitting identities, contact curvature,
and the finite inequality

```math
(1-\alpha E[Y^2])E[YX^2]
-2E[YX]E[X(1-\alpha Y^2)]
\ge \frac{E[Y^3]}{E[Y^2]}
\left(\operatorname{Var}(X)+\alpha E[YX]^2\right).
```

Here `Y` is a finite law on `[-1,1]`, `E Y=0`, `E Y^2>0`,
`0<=alpha<1`, and `X=phi(Y)` for an increasing convex function.
The ordered-pair weights are
`mu_i mu_j (y_j-y_i)^2(1-alpha y_i y_j)` for `i<j`.
The particular moment identity and its entropy-contact application are the
features requiring a specific prior-art comparison. Positive association
itself is classical: see Fortuin–Kasteleyn–Ginibre,
[*Correlation inequalities on some partially ordered sets*](https://doi.org/10.1007/BF01651330),
*Communications in Mathematical Physics* 22 (1971), 89–103, and
Karlin–Rinott,
[*Classes of orderings of measures and related correlation inequalities.
I. Multivariate totally positive distributions*](https://doi.org/10.1016/0047-259X(80)90065-2),
*Journal of Multivariate Analysis* 10 (1980), 467–498.
The proof supplies a finite conditional-likelihood-ratio and Chebyshev
argument on the triangular support; it does not assume a new general
association principle or claim that these sources contain this exact
moment inequality.

The harmonic-lowering argument covers `[1,2]` by a positive endpoint-
convergent kernel series. The low-order localization needs a separate
strict Shannon input. The fair-face exclusion also has a substantial
analytic dependency: a beta-binomial moment-ratio theorem, a binomial-
escort comparison with a matching tilted mean, and a signed midpoint
series. These arguments are all present in Proof.md. The beta-binomial
step uses classical Gegenbauer identities and zero interlacing, plus
Euler products; their exact source links and applications are given there.
No finite numerical census replaces any of these universal statements.

## Consolidation decisions

The standalone proof preserves the full parameter and entropy-order
quantifiers and makes two explicit simplifications to its dependency
closure:

1. The elementary two-background-coin resolvent identity implies that a
   minimal negative background has `N>=3`. This is sufficient for every
   subsequent classification and curvature step. The pure-binomial
   strict-splitting argument needs three coins; the singleton argument
   needs the three annihilated moments and has a repeated group when
   `N>=3`. Thus the earlier five-total-coin polynomial certificate and
   later finite dimension improvements are unnecessary here. The
   consolidation received a separate scope check of these requirements.
2. The strict Shannon result uses the published cubic equality mechanism
   and the harmonic-lowering theorem's proved `q=1` moment signs. It does
   not attempt to infer strictness from a weak Shannon entropy limit.

The proof uses `D_q=sum d_k s_k^(q-1)` throughout, correcting the older
index convention `D_(q-1)` used in some development notes. The cubic edge
kernel is denoted `C_q` to distinguish it from the normalized near-Shannon
functional `J_q=D_q/(1-q)`. The source's stronger resolvent conjecture,
unconditional cubic signs, failed positive-mixture proposal, and optional
singleton curvature conjecture are not proof assumptions. No historical
research-stage status label is needed to navigate the standalone proof.

## Comparison with adjacent literature

The dated 2026-10-10 source audit made the following distinctions. This
is a bounded literature comparison, not an exhaustive novelty certificate.

| Source | Relationship to the present statement |
|---|---|
| Hillion–Johnson, [entropy concavity](https://arxiv.org/abs/1503.01570v1), published in *Bernoulli* 23 (2017), 3638–3649, [DOI 10.3150/16-BEJ860](https://doi.org/10.3150/16-BEJ860) | Joint Shannon concavity is a separate statement from coordinatewise parameter monotonicity. The conjecture numbering should not be interchanged. |
| Wang, [*The Sharp Rényi and Tsallis Threshold in the Shepp–Olkin Concavity Problem*, arXiv:2609.27433v1](https://arxiv.org/abs/2609.27433v1), 2026-09-23 | The preprint claims joint concavity for `0<q<=1` and failure above one in mixed-sign directions; it explicitly distinguishes monotonicity. These claims are adjacent context and have not been independently verified here. |
| Madiman–Melbourne–Roberto, [*Bernoulli sums and Rényi entropy inequalities*, arXiv:2103.00896v2](https://arxiv.org/abs/2103.00896v2), 2024-03-15; *Bernoulli* 29 (2023), 1578–1599, [DOI 10.3150/22-BEJ1511](https://doi.org/10.3150/22-BEJ1511) | Entropy–variance comparisons, entropy-power inequalities and anti-concentration are application context; they do not supply the literal monotonicity theorem. The inspected v2 postdates the journal publication. |
| Buryak–Mishura, [*Convexity and robustness of the Rényi entropy*](https://doi.org/10.15559/21-VMSTA185), *VMSTA* 8 (2021), 387–412 | Existing binomial-to-Poisson entropy convergence must be distinguished from any future Poisson monotonicity application. No Poisson theorem is claimed here. |
| Raşa, [*Complete monotonicity of some entropies*, arXiv:1606.05520v2](https://arxiv.org/abs/1606.05520v2) | A further comparison source for parameterized binomial, Poisson and negative-binomial entropy families; the audit inspected metadata and abstract only. |
| Chan–Pak, [*Equality conditions for correlation inequalities*, arXiv:2607.06275v1](https://arxiv.org/abs/2607.06275v1) | A possible source for future association equality/stability work; its proofs were not audited and are not an input. |

No competing proof of the literal closed-half-cube, all-orders statement
was found in that targeted search. This does not establish a priority
claim: it was not a complete MathSciNet/zbMATH review, citation census,
unpublished-work survey, or proof audit of adjacent preprints. No author
was contacted. Refresh the dated comparison and exact source versions
before any public release or submission.

## Written extensions and formal scope

For `n>=1` and `0<q<=2`, Proof.md derives the quantitative gain

```math
T_q(g_r)-T_q(g_p)\ge
\frac{6q}{n(n+1)(n+2)}
\sum_i\left[(1/2-p_i)^2-(1/2-r_i)^2\right].
```

It is exact for `n=1,q=2`; general optimality is not claimed. It implies
positive-order equality exactly when `p=r`, and a unique fair-vector
maximizer on the half cube. At order zero, equality is equality of the
numbers of positive parameters, and every vector with all coordinates
positive maximizes the entropy. A corresponding Rényi gain, reflection,
and independent thinning follow as written corollaries.

The inverse-score inequality extends in the written supplement to
`-1<=alpha<=1`, and to bounded continuous increasing convex transforms
of general laws on `[-1,1]` by mean-preserving finite-grid approximation.
Those supplements are unnecessary for the finite Bernoulli theorem and
are outside the initial formal contract. None of these extensions is
asserted independently novel or formally verified merely by appearing
in the manuscript.

A verified formal release must cover the concrete Bernoulli coefficient
law and entropy definitions, every support and order boundary, all analytic
bridges, and the main monotonicity conclusions without extra assumptions.
It must pass the project's exact-source Linux build and selected
Comparator, permitted-axiom, and exported-proof replay checks. The only
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
A completed formal verification would still be distinct from novelty,
external peer review, public release, submission, and registration.
