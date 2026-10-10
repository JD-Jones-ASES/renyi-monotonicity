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

The initial association package at
[`913f98bc9356fde887224d6ee29298d0d0024b80`](https://github.com/JD-Jones-ASES/renyi-monotonicity/tree/913f98bc9356fde887224d6ee29298d0d0024b80)
passed [Linux run 38045003972](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/runs/38045003972):
Comparator, transitive permitted-axiom audits for its nine selected declarations,
Lean/NanoDa/con-ron replay, and a separate fresh build. Both jobs succeeded with
tracked sources unchanged. That exact baseline was the initial `main` revision.

Later development adds the full order-two endpoint, order-one limits, midpoint
continuity across support loss and the actual fair-coordinate derivative,
Hillion–Johnson cubic identities, actual ordered 2×2/3×3 minor positivity,
strict log-concavity, mixing-grid gap concavity and its equality case, the unique scalar
threshold with strict gap and κ monotonicity and its mass-gradient sign bridge,
the finite contact contradiction, an abstract compact first-contact theorem,
and the closed-cube coordinate transfer from the actual midpoint sign. These modules have compiled
locally and passed the next exact
[Linux gate at `6970e50f6c77da5f5ab5e178c5536a5545440e6c`](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/runs/38046185752).
Both jobs passed: all 28 committed Lean modules built from source, all 45
selected supporting-declaration axiom audits passed, and the association
Comparator closure again passed all three kernel replays. Tracked sources
remained unchanged. This exact development revision was promoted to `main`.
None of these results establishes the missing full entropy declarations.

## Outstanding full-proof obligations

The next locally compiled increment proves all-order `[1,2]` closed-cube
Rényi and Tsallis monotonicity, with Shannon obtained from the finite-law order
limit. The harmonic proof includes the actual Bernoulli mixing grid, lowering,
positive convergent kernel series, removable center, and support-loss limit.
Strict Shannon midpoint positivity follows by isolating the first nonconstant
term of that positive series and taking the order-one limit; no derivative of
an infinite series is assumed. The actual mass-gradient four-block pattern and
three-sign-change bound, small backgrounds of at most two coins, and a normalized
kernel continuous through order one are also implemented.

The convolution proof uses induction over positive Bernoulli averaging factors.
One-step averaging diminishes sign variations. Its nonzero kernel alternates at
every adjacent pair; this proves the lower variation bound under shift
annihilation. Interleaving proves endpoint orientation when variations are
preserved. These supporting theorems do not require an assumed total-positivity
certificate. The normalized adjacent-pair perturbation estimate is uniform on
orders `[0,1]` when its adjacent mass is bounded below.

This increment at `de55260cbb7cdfbdae023e5711a72676d22ecae9` passed
[Linux run 38047633030](https://github.com/JD-Jones-ASES/renyi-monotonicity/actions/runs/38047633030).
Both jobs succeeded: all 47 committed Lean modules built from source, all 84
selected supporting-declaration audits used only the permitted axioms, and the
association Comparator closure passed Lean, NanoDa and con-ron replay. Tracked
sources remained unchanged. The exact revision was promoted to private `main`.
Independent kernel replay still covers the association contract; the supporting
entropy proofs have source-build and transitive-axiom evidence.

The next supporting checkpoint adds strict fair-coordinate derivatives for
orders `(0,1)`, the normalized fair-vector derivative at Shannon order, and
joint gradient continuity giving a common neighborhood on each positive
compact order band. The small-coin boundary estimate is proved for actual
Bernoulli convolution, uniformly over `[0,1]`, with an explicit strict-gain
threshold. Actual polynomial omission and splitting restrictions, arbitrary
coordinate selection, stationary contact classification gates, cubic path
remainders, strict quadratic moments for the two contact families, and the
finite escort contradiction are implemented. The finite beta-binomial MGF
identification and Gegenbauer interlacing are supporting inputs to the still
unfinished one-biased-plus-fair comparison.

This checkpoint has local source-build evidence; its exact Linux gate will be
recorded after execution. The remaining `(0,1)` closure comprises the actual
one-biased-plus-fair strict positivity chain, compact first-contact localization,
common odds-tilt curvature, complete family selection and final assembly.
The complete all-order principal statements remain absent until these
obligations are proved.

The ordered-minor proofs use an elementary expansion under addition of a
Bernoulli factor. They assume neither total positivity nor a structural
certificate. `supporting-audit.json` selects supporting declarations for a
separate transitive axiom audit. This file is not a Comparator contract: the
independent-kernel replay still covers exactly the chosen Comparator closure.

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
