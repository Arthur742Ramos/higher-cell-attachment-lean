# Source provenance

First-party author convention: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Responsible maintainers: Arthur Freitas Ramos,
David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz.
No invented contributor roles or mathematical novelty are claimed.

The actual quotient, open-cover and jointly continuous quotient-product radial
geometry generalize Arthur742Ramos/cell-attachment-lean exact commit
8883b95e8ace951e27c2bc86f95d02397787dd59. Its GroupoidQuotient, GroupQuotient and
HomotopyPi1 source is reused unchanged under Apache-2.0.

The all-object ordinary fundamental-groupoid open-cover pushout comes from
Arthur742Ramos/classical-svk-lean exact commit
874680e16db88b4a41daadf56eafbac79fd2f748, via that accepted Cell snapshot.
Inherited Basold-Bruin-Lawson subdivision source comes from
Dominique-Lawson/Directed-Topology-Lean-4 exact commit
009529606c66d37ef93b4b81b8587f71ce4d2c56. Their MIT notice is preserved in
Lean4/LICENSE.md. First-party source remains Apache-2.0.

SphereInfrastructure vendors only the required closure from Sebastian Kumar's
unmerged mathlib PR28246, Sebi-Kumar/mathlib4 exact commit
037ad801e1e5a5b7aa1750957c07f7769812effc. Original Apache2 author/copyright
notices and exact provenance are preserved. Narrow pin-compatibility adaptations
are documented in the files. HigherCellAttachment/Sphere only adapts dimension
conventions and exposes consequences; no independent sphere/SVK novelty is claimed.

Mathematical source: Allen Hatcher, Algebraic Topology, section1.2 Exercise6,
printed page53 in the live Cornell edition (PDF zero-based page61):
https://pi.math.cornell.edu/~hatcher/AT/AT..pdf#page=62 . The mixed-dimension scope
is an explicit strengthening. No discrete-complement application is claimed.

The source was reconstructed after an execution-host replacement by replaying
recorded authoring commands and immutable upstream files. Earlier successful
checks do not validate recovered bytes. All exact-toolchain/module/standalone,
axiom and direct kernel checks were rerun successfully. The official hosted
workflow and trusted rendering remain unperformed. No pre-loss checksum exists
for comparison.

Lean4/vendor-manifest.json preserves explicitly labeled historical pre-port hashes.
Lean4/shipped-manifest.json records actual current shipped bytes, unchanged from
the accepted Cell snapshot. Historical entries for all.lean and
directed_van_kampen.lean are intentionally not shipped in the minimal closure.
