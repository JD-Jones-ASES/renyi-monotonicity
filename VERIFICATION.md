# Verification boundary

The repository is private and under active formalization. The full two entropy
monotonicity proofs are not yet implemented. No complete formal release,
publication, Palomar submission or registration is claimed.

## Contracts

- `comparator.json`: full closed-cube Rényi and Tsallis monotonicity for every
  finite dimension and real order `[0,2]`, plus finite inverse-score association.
  **Incomplete.** The first two Solution declarations are deliberately absent.
- `comparator-association.json`: the completed finite inverse-score inequality.
  This is an independent theorem with arbitrary finite positive laws and the
  actual ordered-node, zero-mean, positive-variance and secant hypotheses.

Both configurations also check eight concrete definition equations for the probability law, entropy conventions and finite expectation. These are definition contracts, not additional principal mathematical theorems.

The Challenge has three intentional statement placeholders. No implementation
module may contain proof placeholders, custom axioms, or native Boolean reduction.
The source validator enforces this distinction. Solution imports implementation
modules only.

## Current evidence

Local compilation has passed for the explicit Bernoulli-law definitions,
product-space semantics, normalization, support count, boundary/deletion results,
order-zero monotonicity, four moment identities and positive-support entropy
calculus. The finite association module has compiled with its full hypotheses.
The two exact supporting Python replay blocks passed both normally and under
`-O`, including 27 literal probability controls and negative mutations.

Linux Comparator, transitive axiom audits, Lean/NanoDa/con-ron replay, and a
separate fresh build for the first association candidate are pending. Only
exact full source SHAs and successful runs will be recorded as accepted evidence.
A passed build alone does not establish the unimplemented main theorems.

## Outstanding full-proof obligations

The remaining closure includes the scalar-threshold monotonicity theorem,
strict Toeplitz variation and mixing-grid structure, strict Shannon midpoint
positivity, convergent harmonic-lowering series, one-biased-plus-fair strict
positivity (including its moment/CMB comparison inputs), uniform order windows,
small-coin boundary estimates, compact first-contact localization, omission and
splitting classification, curvature/escort identities, the no-contact argument,
and the final endpoint and coordinatewise transfers.

The preferred quantitative gain, strict equality and fair-maximizer theorems
will be added only after the principal closure is complete and verified.

## Reproduction

```sh
lake exe cache get
lake build
python3 scripts/check_sources.py
python3 scripts/audit_axioms.py --config comparator-association.json
lake comparator --config comparator-association.json
```

The GitHub workflow offers `association` and `full` contracts and runs both a
kernel-replay job and a separate fresh-build job. Both record `GITHUB_SHA`, build
all project sources, and verify that tracked sources remain unchanged. A full
contract run currently must fail at the missing main declarations.

For independent kernels, the workflow uses the pinned PalomarSubmission sandbox
setup, Lean's exported-proof replay and the Lean toolchain's NanoDa and con-ron
checkers. The only permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The committed Mathlib revision exactly matches the Lean toolchain.
