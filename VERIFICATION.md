# Verification contract

The expanded package is a **locally checked verification candidate** with
33 compared contracts and 353 supporting axiom audits. Its complete
51-module build and local checks passed. The earlier Linux run below
verifies only the original 24-contract source; a new exact-candidate Linux
comparison and independent-kernel replay is still required.

The package retains the original twelve principal theorems and twelve
explicit definition contracts, and adds nine principal statements listed below. The independent Challenge imports
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
| `normalized_sharp_gap` | Optimal eighth-order lower bound plus the sharp support-interiority contribution, for every normalized symmetric probability law. |
| `normalized_sharp_gap_strict` | Strictness of that strengthened lower bound for every nonzero parameter. |
| `scaled_sharp_gap` | The sharp pure eighth-order lower bound in the original positive-band scale. |
| `sharp_gap_coefficient_le` | No larger universal eighth-order coefficient is possible over actual normalized symmetric probability laws. |
| `interiority_gap_coefficient_le` | No larger universal support-interiority coefficient is possible. |
| `sharp_gap_intrinsic_coefficient_nonpos` | A universal intrinsic-deficit coefficient paired with the sharp eighth-order term must be nonpositive. |
| `global_squared_transport` | Ordinary squared-law W₁ bound without a small-deficit restriction or symmetry hypothesis. |
| `fourth_deficit_range` | Every normalized law has deficit in `[0,2B²]`, where `2B²=30+12√6`. |
| `global_transport_attainment` | An explicit attaining law for each deficit in that entire feasible range. |

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
- The comparison manifest and supporting-declaration inventory enumerate the
  exact selected and audited declarations.
- No Lean source exceeds 10,000 lines.

```sh
lake build
python3 scripts/check_sources.py
python3 scripts/audit_axioms.py
python3 scripts/generate_certificate.py --check
python3 -O scripts/generate_certificate.py --check
python3 scripts/independent_certificate_check.py
python3 -O scripts/independent_certificate_check.py
python3 scripts/check_analytic_negative_controls.py
python3 scripts/generate_sharp_gap_certificate.py --check
python3 -O scripts/generate_sharp_gap_certificate.py --check
python3 scripts/independent_sharp_gap_check.py
python3 -O scripts/independent_sharp_gap_check.py
python3 scripts/check_sharp_gap_negative_controls.py
python3 -O scripts/check_sharp_gap_negative_controls.py
```

The generator checks 64 closed rectangles and 1,792 exact rational shifted
Bernstein coefficients. The independent checker derives endpoint moments
in `Q(sqrt(6))` and reconstructs coefficients through separate interpolation
matrices. Its negative controls reject a positive coefficient perturbation,
a negative coefficient and an omitted rectangle. Analytic controls require
the clean sources to compile and reject strengthened chord and fourth-deficit
constants at their actual proof steps. A process or import failure does not
count as a successful negative control.

The sharp-gap certificate separately checks 64 closed rectangles and 2,880
rational coefficients, including seven zero coefficients. Its independent
checker derives moments by polynomial reduction, obtains global Bernstein
coefficients by tensor interpolation, and subdivides them with de Casteljau.
Six controls reject changed values, signs, missing coefficients, wrong cells,
a shifted polynomial and a missing cell. Both certificates and their
independent replays remain present.

These Python checks support the evidence trail. The formal certificate proves
the coefficient identities and signs in Lean's kernel, and the entire-series
and integral reductions establish the infinite quantifiers.

## Local extension checks — 2026-10-10

The complete package build passed all 9,029 Lake jobs. The expanded audit
passed for all 33 principal/definition contracts and 353 supporting
declarations, using only the three permitted axioms. Both old and new exact
certificate routes passed ordinarily and with Python optimization. The old
analytic mutation controls and all six new certificate controls passed.
Independent agent reviews checked the variable-law limits, all-law scopes,
transport finiteness, both affine branches, and full-range attainment.

The current official metadata/provenance validator passed. Python compilation,
source checks, Markdown links and fences, and whitespace checks passed. A
raw-declaration comparison matched all 22 shared definitions, 33 theorem
signatures and four generated proof declarations with zero mismatches. A
local MathML conversion checked all 350 mathematical expressions without
formula errors; this is not a new GitHub rendering check.

These are local build, mathematical and source checks. They do not substitute
for the sandboxed exact-commit Linux gate below. No submission or new external
human review is claimed.

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
The subsequent documentation revisions through
`b2aba5c092f26787cc06260994cb8e8d577ded86` preserved every Lean file,
dependency pin, comparison contract, certificate and verification script.
The sharp extensions change the formal payload, so the historical Linux
acceptance is not evidence for this expanded candidate. Its local checks
and subsequent exact-candidate Linux gate must be recorded separately.
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
written supplements. The general interval transport theorem, full equality
classification, higher Wasserstein orders and signed-law corollary are also
written supplements. The new eighth-order and interiority coefficients are
optimal; optimality is not asserted for the older intrinsic-deficit estimate.
