# Rényi and Tsallis entropy monotonicity for Bernoulli sums

This Lean project proves coordinatewise monotonicity in the **coin
parameters**, for every entropy order in `[0,2]`. For independent Bernoulli sums,

```math
0\le p_i\le r_i\le\tfrac12
\quad\Longrightarrow\quad
H_q(S_p)\le H_q(S_r),\qquad T_q(S_p)\le T_q(S_r),\qquad 0\le q\le2.
```

The statements cover every finite dimension, including zero, and every zero or
fair parameter boundary. They give the full conclusion of Hillion–Johnson
Conjecture 4.4. [Proof.md](Proof.md) is the standalone mathematical argument;
[Note.md](Note.md) records sources, attribution, and the dated prior-art comparison.

The probability law is the coefficient of `∏ i, ((1-p i) + p i*X)`.
Its finite product-space interpretation, normalization, nonnegativity, and
support cardinality are proved in Lean. Order zero uses support cardinality
explicitly; order one uses Shannon entropy. The two principal entropy proofs
in [AllOrders.lean](RenyiMonotonicity/AllOrders.lean) have no additional
structural, analytic, or computational assumptions.

The third principal theorem is a reusable finite inverse-score inequality.
For a finite mean-zero `Y` in `[-1,1]`, positive second moment, increasing convex
sampled inverse scores `X`, and `0 ≤ α < 1`, it states

```math
(1-\alpha\mathbb E Y^2)\mathbb E[YX^2]
-2\mathbb E[YX]\mathbb E[X(1-\alpha Y^2)]
\ge \frac{\mathbb E Y^3}{\mathbb E Y^2}
\left(\mathrm{Var}(X)+\alpha(\mathbb E[YX])^2\right).
```

[InverseScore.lean](RenyiMonotonicity/InverseScore.lean) proves the kernel
lattice inequality, applies Mathlib's finite FKG theorem on ordered pairs,
and expands four exact finite moments. It also exposes
`inverse_score_association_convex` for an ordinary monotone convex function
on `[-1,1]`. Positive association is classical and is credited accordingly.

## Proof organization

For `[1,2]`, a positive harmonic-kernel series gives the midpoint sign;
Shannon entropy follows by continuity. For `(0,1)`, uniform zero-face and fair-corner estimates localize a first contact on the full closed cube. Exact
Bernoulli polynomial identities classify the contact, and the finite
inverse-score inequality excludes the interior families. The remaining
one-biased-plus-fair family is excluded using beta-binomial moment ratios,
a finite Chebyshev coefficient limit, an escort-law comparison, and a signed
series with an actual finite-law boundary limit. Coordinate concavity then
gives both entropy comparisons. Order zero is handled by the support theorem.

The written quantitative gain, equality characterization, unique fair
maximizer, and continuous-law association extensions are outside this initial
formal contract. Their manuscript proofs are not claims of Lean verification.

## Build and verify

The package `renyiMonotonicity` pins Lean `v4.35.0-rc3` and Mathlib
`a98628e16c11f5167f16124105ddce53efa9bfe5`.

```sh
lake exe cache get
lake build
python3 scripts/check_sources.py
python3 scripts/audit_axioms.py --config comparator.json
python3 scripts/audit_axioms.py --config supporting-audit.json
lake comparator --config comparator.json
```

`comparator.json` checks **three principal theorems and eight concrete
definition equations**. The Challenge contains three intentional statement
placeholders; Solution imports implementation modules only. All implementation
proofs use only `propext`, `Classical.choice`, and `Quot.sound`.

[VERIFICATION.md](VERIFICATION.md) describes the exact-commit acceptance gate,
its historical checkpoints, and the scope of each check. The
[Verify workflow](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/workflows/verify.yml)
records the full commit SHA and has separate Linux fresh-build and
Lean/NanoDa/con-ron replay jobs. Select the **full** contract when verifying
the entropy result; the historical association-only configuration is narrower.
A particular revision is accepted only when both jobs for that exact SHA succeed.

Supporting algebra and negative controls run with
`python3 scripts/exact_replay.py` and `python3 -O scripts/exact_replay.py`
(requires SymPy). These finite controls are outside the Lean proof inputs.

The repository is public. Formal verification, human peer review, novelty,
submission, and registration remain distinct. Palomar submission is planned.
[Disclosure.md](Disclosure.md)
records AI assistance and review boundaries.
