# Fundamental groups of arbitrary higher-cell attachments

The complete theorem is verified locally on the exact Lean/mathlib pin. It
constructs the actual topological quotient and proves that the actual inclusion
induces a bijection on fundamental groups, with a multiplicative equivalence
whose underlying homomorphism is exactly that map.

For an arbitrary path-connected topological space X, a basepoint x₀, an index
type ι in an independent universe, dimensions d i ≥ 3 and continuous attaching
maps from the Euclidean unit spheres, the carrier is the boundary-generated
quotient of X and the dependent coproduct of closed Euclidean unit balls, with
its quotient topology. Mixed dimensions and the empty family are included.
No finite/countable/CW/Hausdorff/local-connectivity assumptions or supplied
retraction/simple-connectivity/kernel/quotient oracles are added.

The mathematical source is Hatcher, section 1.2 Exercise 6, printed page 53
in the live Cornell edition:
https://pi.math.cornell.edu/~hatcher/AT/AT..pdf#page=62
Mixed dimensions are an explicit strengthening of the fixed-dimensional source
statement. The exercise's separate discrete-complement application is outside
scope. No mathematical novelty, sphere novelty or SVK novelty is claimed.

## Proof

The actual quotient has an open cover by the complement of cell centers and
the disjoint cell interiors. A jointly continuous radial quotient-product
homotopy retracts the punctured neighborhood to X. Each overlap component has
an explicit radial homotopy equivalence to its unit sphere; the sphere is
simply connected for these dimensions. Interiors are contractible convex balls.
The actual all-object groupoid van Kampen pushout and the credited vertex-group
quotient bridge then use identity relators. Their normal closure is bottom.
Factorization through the proved neighborhood equivalence identifies exactly
the inclusion-induced homomorphism.

## Evidence and limits

Fresh exact-toolchain normal Lake build passed (3401 jobs), together with the
modular proof, independent Challenge, complete standalone Solution and the
empty/mixed/independent-universe examples. Six complete proof axiom closures
contain only propext, Classical.choice and Quot.sound. Direct Lean default and
paranoid kernels, NanoDa and ConRon in verified mode passed. Independent
source/statement/standalone fidelity review found no unresolved source blocker.
See reports/local-verification-results.json and reports/final-source-review.md.

The supported local Comparator from-export run reached its kernel stage after
comparison, but its overall verdict is blocked by the host's bubblewrap network
namespace restriction. No unsafe no-sandbox flag or security workaround was
used. The official isolated full workflow, trusted Challenge rendering and
registry submission remain separate, unperformed stages. A separate optional direct Lean4Lean probe is also blocked before declaration
checking by an incompatible module-header format; it is not reported as a pass.
No registry acceptance or human review is claimed.

After execution-host replacement, source was reconstructed from recorded
construction commands and immutable inputs, then all proof checks were rerun.
No pre-loss checksum existed, so byte-identical recovery is not asserted.

## Build and credits

Lean: leanprover/lean4:v4.35.0-rc2
mathlib: 065356127b1dc0016f66b7283ce0ce2c4055aa55

Use lake exe cache get, python scripts/generate_standalone.py and lake build.
The serial source-based build is python scripts/build_sources.py.
Challenge has one intentional target theorem hole; Solution has no admissions.
Comparator names HigherCellAttachment.higher_cell_attachment and no definition
holes. See PROVENANCE.md for all exact source snapshots, authors and licenses.
First-party/sphere code is Apache-2.0; inherited subdivision helpers preserve MIT.
