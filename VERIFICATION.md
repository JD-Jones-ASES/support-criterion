# Verification contract

The package selects **24 compared declarations**: twelve principal theorems
and twelve explicit definition contracts. The independent Challenge imports
only canonical Mathlib. Its proof holes state the contract; the Solution and
all implementation modules contain no proof holes or added axioms.

## Mathematical scope

| Principal declaration | Content |
|---|---|
| `universal_support_criterion` | MGF domination for every symmetric Borel probability law in every admissible positive band, for every real parameter. |
| `universal_strict` | Strict MGF inequality for every nonzero parameter. |
| `variance_proxy_optimality` | Every global quadratic Gaussian proxy is at least the actual variance. |
| `sharp_universal_ratio` | The explicit four-point counterexample for each larger ratio, with violation throughout a punctured neighborhood of zero. |
| `normalized_quantitative_gap` | Intrinsic fourth-deficit and eighth-order gap in the normalized bands. |
| `scaled_quantitative_gap` | The corresponding exact original-scale estimate. |
| `fourth_deficit_decomposition` | Exact decomposition into variance displacement and the nonnegative interiority moment. |
| `critical_law_rigidity` | Zero fourth deficit if and only if the probability law of X is the explicit critical law. |
| `squared_transport_finiteness` | Couplings exist, every coupling cost is finite, and the Wasserstein infimum is finite. |
| `squared_transport_bound` | Constructive transport bound by variance displacement and interiority. |
| `sharp_local_transport` | Ordinary squared-law W₁ bound for every deficit at most one half. |
| `local_transport_attainment` | An explicit attaining law for each deficit in the complete interval `[0,1/2]`. |

The twelve definition contracts expose the actual MGF integral, second and
fourth moments, interiority, symmetry, support, critical and counterexample
measures, symmetric two-point measure, squared pushforward, and the infimum
definition of ordinary Wasserstein distance. The corresponding finiteness
theorem justifies taking the real value of that extended infimum.

The transport upper bounds need only normalized squared support; the MGF
and rigidity theorems for X retain symmetry. `Applications.lean` identifies
the second-moment parameter with Mathlib's variance and provides supporting
sub-Gaussian, random-variable, independent-sum and Chernoff corollaries.
`QuadratureMoments.lean` gives the actual critical-law moment table through
degree eight. These supporting declarations build with the package and
receive the separate transitive-axiom audit. The selected statements are
exactly those listed in [comparator.json](comparator.json); Comparator checks
their dependency closure.

## Reproduction

- Lean: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- All transitive Git dependencies: exact revisions in `lake-manifest.json`.
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Compared declarations: 24; supporting axiom-audit declarations: 244.
- Formal sources: 37 Lean files; no source exceeds 10,000 lines.

```sh
lake build
python3 scripts/check_sources.py
python3 scripts/audit_axioms.py
python3 scripts/generate_certificate.py --check
python3 -O scripts/generate_certificate.py --check
python3 scripts/independent_certificate_check.py
python3 -O scripts/independent_certificate_check.py
python3 scripts/check_analytic_negative_controls.py
```

The generator checks 64 closed rectangles and 1,792 exact rational shifted
Bernstein coefficients. The independent checker derives endpoint moments
in `Q(sqrt(6))` and reconstructs coefficients through separate interpolation
matrices. Its negative controls reject a positive coefficient perturbation,
a negative coefficient and an omitted rectangle. Analytic controls require
the clean sources to compile and reject strengthened chord and fourth-deficit
constants at their actual proof steps. A process or import failure does not
count as a successful negative control.

These Python checks support the evidence trail. The formal certificate proves
the coefficient identities and signs in Lean's kernel, and the entire-series
and integral reductions establish the infinite quantifiers.

## Exact-commit Linux gate

The manual [verification workflow](.github/workflows/verify.yml) requires
an explicit full candidate SHA and checks it against both the checkout and
GitHub event. It runs two jobs:

1. Build every project module, run source/evidence checks and all axiom audits,
   then compare the independent statements and replay the selected Solution
   closure through Lean's kernel, NanoDa and con-ron.
2. Build all project sources and run the audits on a separate fresh Linux
   runner, using only the pinned Mathlib dependency cache.

Both jobs require tracked sources to remain unchanged. Logs and structured
records identify the exact SHA, compiler revision and binary digests. The
kernel runner uses the checkers bundled with the selected Lean release, with
two con-ron workers; it runs Comparator under bubblewrap. The saved intake
configuration is not modified to add the independent checkers.

The `verified/2026-10-10` tag identifies
`438600c1ae148abf353c5ff9898fc953f1528d30`, which passed both jobs in
[run 38069219096](https://github.com/JD-Jones-ASES/support-criterion/actions/runs/38069219096).
Subsequent documentation and source-metadata edits preserve every Lean file,
dependency pin, comparison contract, certificate, and verification script
from that revision. The exact-commit kernel evidence applies to the tagged
revision; the documentation changes were checked separately for metadata
validity, links, and GitHub rendering.
The workflow is repository verification, not a Palomar submission or an
official hardware-profile preflight.

## Review and boundary

Independent agent audits checked the universal quantifiers, actual measure
and transport meanings, normalization, the complete moment tail, all cell
edges, `w=0`, `z=0`, sharpness at every larger ratio, and attainment at every
stated deficit. No unresolved mathematical finding remained in those audits.
Production and human-review status are recorded in [Disclosure.md](Disclosure.md).

The source contract was checked against PalomarPolicy
`96b034cc31a72a63d4f4041911dce337a85c9a04`; the independent-kernel procedure
follows PalomarSubmission `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
Conditional/time-uniform concentration and optimized local asymptotics remain
written supplements. The numerical MGF constants are not asserted optimal.
