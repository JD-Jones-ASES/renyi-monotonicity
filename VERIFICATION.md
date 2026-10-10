# Verification boundary

The full core is implemented: Rényi monotonicity, Tsallis monotonicity, and
finite inverse-score association. Local compilation and independent agent
source audits cover the complete proof closure. Acceptance of a particular
revision requires the exact-source Linux gate below; the workflow conclusion
and recorded commit SHA establish which revision passed.

## Contracts

- `comparator.json`: three principal theorems, namely full closed-cube Rényi
  and Tsallis monotonicity for every finite dimension and real order `[0,2]`,
  and finite inverse-score association with its literal hypotheses.
- `comparator-association.json`: the historical association-only contract.
  A pass of this narrower configuration cannot verify the entropy theorem.

Both configurations also compare eight concrete definition equations for the
Bernoulli coefficient law, entropy conventions, and finite expectation.
These equations are counted separately from the principal mathematical theorems.

The Challenge has three intentional statement placeholders. Every Solution
proof is implemented without placeholders, custom axioms, native Boolean
reduction, or imports from Challenge. `scripts/check_sources.py` checks source
policy, module headers, file-size limits, and dependency pins. The permitted
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Complete proof coverage

The concrete coefficient law has finite product-space semantics, nonnegative
masses, total mass one, and exact support. Separate definitions handle orders
zero and one, so padded zero atoms cannot change the support entropy.
`AllOrders.lean` exports both entropy conclusions without any assumed
association, moment-ratio, classification, boundary, or localization certificate.

The supporting closure includes the actual Bernoulli mixing grid and strict
log-concavity, harmonic lowering on `[1,2]`, strict Shannon midpoint positivity,
variation diminution with endpoint orientation, actual fair-coordinate
derivatives, uniform small-coin boundary control, full contact classification,
odds-tilt curvature, and finite escort contradiction. The low-order proof uses
the actual beta-binomial moment ratio, existence of the matching tilted mean,
the actual escort-density interval-sublevel comparison, and the one-biased
signed series. Finite Chebyshev approximants supply the required coefficient
limits; the signed series is summed only inside its convergence interval, with
the actual finite-law boundary limit supplying the endpoint.

The final localization is a strong induction on total dimension. It includes
empty active cores, zero-coordinate faces, mixed fair faces, and the all-fair
corner. A first contact found on the compact closure of negative parameters
is a minimum over the full closed cube. The final theorems quantify over all
finite dimensions, all real orders `[0,2]`, and literal `0 ≤ p ≤ r ≤ 1/2`.
Independent agents reviewed these boundaries, normalizations, and the full
statement/definition fidelity.

`supporting-audit.json` selects 164 supporting declarations for transitive
axiom auditing, including the conventional monotone/convex-function association
corollary. This is not a second Comparator contract. Independent kernel replay
covers the complete transitive dependency closure of the 11 declarations in
the selected full Comparator contract; separately audited declarations outside
that closure have source-build and axiom-audit evidence only.

The supporting Python replay passed both normally and under `-O`, including
27 literal probability controls and negative mutations. These computations
are not proof inputs or a finite substitute for universal quantifiers.

## Exact-commit Linux gate

The [Verify workflow](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/workflows/verify.yml)
defaults to the full contract. It records `GITHUB_SHA` and runs two independent
jobs on Ubuntu 24.04:

1. **kernel-replay** builds all committed sources, audits the selected principal
   and supporting declarations, compares Challenge against Solution, and checks
   the exported proof closure with Lean, NanoDa, and con-ron.
2. **fresh-build** separately installs the pinned dependencies, builds every
   project module from source, and runs both transitive-axiom audits.

Both jobs require tracked sources to remain unchanged and preserve private
verification logs as workflow artifacts. A green workflow for a different SHA,
an association-only pass, or a local build is insufficient for full acceptance.
The workflow run itself provides the immutable SHA, contract choice, individual
step results, and replay counts; consult it before describing any revision as
verified. The Analytic-Lab spin-out record links the accepted full run.

The kernel job uses the PalomarSubmission sandbox installer pinned at
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` and the three checkers supplied by
the pinned Lean toolchain. This use of verification tooling is not a submission
or registration.

## Historical checkpoints

All four earlier runs passed both jobs and preserved tracked sources, but
selected the association-only Comparator contract. They are supporting
milestones, not verification of the full entropy declarations:

| Exact source revision | Linux run | Scope of supporting source build and axiom audit |
|---|---|---|
| `913f98bc9356fde887224d6ee29298d0d0024b80` | [38045003972](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/runs/38045003972) | Initial finite association and concrete definitions |
| `6970e50f6c77da5f5ab5e178c5536a5545440e6c` | [38046185752](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/runs/38046185752) | 28 modules, 45 supporting declarations |
| `de55260cbb7cdfbdae023e5711a72676d22ecae9` | [38047633030](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/runs/38047633030) | 47 modules, 84 supporting declarations; entropy orders `[1,2]` and zero |
| `bfcb5d7a1f83eddf50d07e3d602aadcd0c68173c` | [38049298130](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/runs/38049298130) | 91 modules, 137 supporting declarations; fair-boundary and contact infrastructure |

## Reproduction and limits

```sh
lake exe cache get
lake build
python3 scripts/check_sources.py
python3 scripts/audit_axioms.py --config comparator.json
python3 scripts/audit_axioms.py --config supporting-audit.json
lake comparator --config comparator.json
```

The workflow adds the independent kernels and sandbox setup to this local
sequence. Mathlib is pinned at `a98628e16c11f5167f16124105ddce53efa9bfe5`,
matching Lean `v4.35.0-rc3`.

Quantitative gain, strict equality, unique fair maximization, and continuous-law
association are written extensions outside the initial formal contract.
No human specialist review, novelty certificate, public release, Palomar
submission, or registration is claimed by the formal verification checks.
