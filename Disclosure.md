# Production and review

The mathematical argument was developed in Analytic-Lab from a supplied
AI-assisted problem proposal. The proposal supplied the support ratio,
endpoint reduction and fourth-moment obstruction. The Lab work supplied the
complete tail argument, exact finite certificate and the extensions developed
in this package. The written source is pinned in `formalization.yaml`.

OpenAI Codex assisted with the Lean formalization, proof development, exact
certificate generation, source review and documentation. Separate agent
reviews checked the mathematical scope and the proof interfaces. These are
automated internal reviews. No human specialist review is asserted.

Python regenerates rational certificate data and checks supporting identities.
The formal proof does not trust a Python exit status: Lean verifies every
selected coefficient identity, sign and analytic implication. Exact toolchain,
source and independent-kernel verification records belong in
[VERIFICATION.md](VERIFICATION.md).
