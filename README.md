# Rényi and Tsallis entropy monotonicity for Bernoulli sums

Coordinatewise monotonicity in the **coin parameters**, for every entropy
order in `[0,2]`, is the intended full result. For independent Bernoulli sums,

```math
0\le p_i\le r_i\le\tfrac12
\quad\Longrightarrow\quad
H_q(S_p)\le H_q(S_r),\qquad T_q(S_p)\le T_q(S_r),\qquad 0\le q\le2.
```

This private project develops the formalization of the written proof of
Hillion–Johnson Conjecture 4.4. **The full entropy formalization is in progress.**
The standalone [Proof.md](Proof.md) gives the mathematical argument;
[Note.md](Note.md) records sources, attribution, and the prior-art boundary.

The actual independent Bernoulli law is defined as the coefficient of
`∏ i, ((1-p i) + p i*X)`. The finite product-space interpretation,
normalization, nonnegativity, and exact support cardinality are proved in Lean.
Order zero uses support cardinality explicitly; order one uses Shannon entropy.
Zero and fair coin parameters belong to the intended principal contract.

The independent finite inverse-score inequality is implemented. For a finite
mean-zero `Y` in `[-1,1]`, positive second moment, increasing convex sampled
inverse scores `X`, and `0 ≤ α < 1`, it states

```math
(1-\alpha\mathbb E Y^2)\mathbb E[YX^2]
-2\mathbb E[YX]\mathbb E[X(1-\alpha Y^2)]
\ge \frac{\mathbb E Y^3}{\mathbb E Y^2}
\left(\operatorname{Var}(X)+\alpha(\mathbb E[YX])^2\right).
```

The proof establishes the kernel lattice inequality, applies Mathlib's finite
FKG theorem on the ordered-pair lattice, and expands four exact finite moments.
Positive association is classical; this proof does not assume the desired
covariance or entropy conclusion as a hypothesis.

The initial association package at `913f98bc9356fde887224d6ee29298d0d0024b80`
passed [Linux Comparator and all three kernel replays, plus a fresh build](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/runs/38045003972).
The subsequent supporting package at `6970e50f6c77da5f5ab5e178c5536a5545440e6c`
also passed its [exact Linux gate](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/runs/38046185752).
The harmonic package at `de55260cbb7cdfbdae023e5711a72676d22ecae9`
passed its [exact Linux gate](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/runs/38047633030).
It proves both entropy comparisons for every real
order in `[1,2]` on the full closed half cube, as well as order zero. It also
proves strict Shannon midpoint positivity, the actual mass-gradient bound of
three sign changes, and variation diminution with shift annihilation and
endpoint orientation for positive Bernoulli convolution. The unrestricted
range `(0,1)` remains unfinished; the full principal declarations are absent.

The next supporting increment supplies strict fair-coordinate derivatives,
including the normalized Shannon endpoint and a common neighborhood on each
compact positive order band. It also proves an explicit small-coin boundary
gain, actual stationary-contact restrictions and strict quadratic moments for
the classified families, and the finite escort contradiction. The
one-biased-plus-fair moment comparison, compact localization and final
low-order assembly are still in progress.

## Build and verify

The package `renyiMonotonicity` pins Lean `v4.35.0-rc3` and Mathlib
`a98628e16c11f5167f16124105ddce53efa9bfe5`.

```sh
lake exe cache get
lake build
python3 scripts/check_sources.py
python3 scripts/audit_axioms.py --config comparator-association.json
lake comparator --config comparator-association.json
```

`comparator.json` reserves the full contract of three principal theorems and eight definition equations: `renyi_monotone`,
`tsallis_monotone`, and `inverse_score_association`. It must not pass until the
first two proofs are implemented. `comparator-association.json` checks only the
completed independent association theorem and eight definition equations, and cannot establish the full conjecture.
[VERIFICATION.md](VERIFICATION.md) records the precise current coverage and
outstanding analytic obligations. The Challenge contains three intentional
statement placeholders; Solution never imports Challenge.

Supporting algebra and negative controls, outside all Lean proof inputs, run with
`python3 scripts/exact_replay.py` and `python3 -O scripts/exact_replay.py`
(requires SymPy). These finite controls are not coverage arguments.

Private development, exact-commit verification, publication, submission and
registration are separate stages. This repository has not been submitted.
[Disclosure.md](Disclosure.md) records AI assistance and review boundaries.
