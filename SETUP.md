# Reproduction and remaining E2E steps

## Reproduce the proof

Lean leanprover/lean4:v4.35.0-rc2 and mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55 are pinned in the toolchain, Lakefile
and manifest. Use lake exe cache get, python scripts/generate_standalone.py,
lake build and python scripts/build_sources.py. The latter is a serial source
replay of all submitted modules. Run lake env lean reports/AuditSolution.lean
for complete standard-only axiom closures.

reports/local-verification-results.json records exact source/export hashes and
successful local gates. reports/export-targets.json derives primitive targets
from this exact toolchain's Lake/CLI/Check.lean; it includes quotient primitives,
the main theorem and the three permitted axioms. Export with leanexport and use
the bundled leanchecker, leanchecker-paranoid, nanoda_bin and con-ron --verified.
The NanoDa config forbids any additional axiom. Challenge has one intended
hole; Solution has no admissions. Comparator has no definition holes.

The current supported from-export Comparator run reached kernel execution
but failed to launch its bubblewrap network namespace: NETLINK_ROUTE socket
operation not permitted. This is recorded as blocked, not accepted. No unsafe
no-sandbox flag, system-network change or other security workaround was used.
The optional direct bundled Lean4Lean probe could not read the current module
header and is separately recorded as blocked before declaration checking.
Local direct kernel passes do not replace the official isolated build/export
or hosted resource-profile verdict.

## Publication

The authorized public source target is Arthur742Ramos/higher-cell-attachment-lean,
with arthurpalomar742 invited for Write access. Publication still requires a
supported owner-authenticated route. The execution-host replacement removed the
previous local owner CLI session; do not assume it survived or copy credentials.
No source repository has been created or pushed in this work as of this snapshot.

After the owner route is restored, publish the reviewed verified source, confirm
the exact remote commit and public visibility, and verify the requested Write
invitation. Source publication is independent of registry submission.

## Official mechanical preflight and rendering

Re-read https://submit.palomar-registry.org/llms.txt and the binding policy at
https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md before
any intake. Current checked policy commit:
96b034cc31a72a63d4f4041911dce337a85c9a04. Current checked official pipeline:
PalomarRegistry/PalomarSubmission commit65f0154ed776cd26c224254aa57b379137f28b0d.

The prepared guarded workflow pins both workflow reference and pipeline input
to that same commit, uses mode full and palomar-standard-v1, and binds the exact
dispatched source commit. Its security-approval input defaults false. Before
any conditional security step, get specific action-time approval for the exact
bubblewrap-binary-scoped AppArmor user-namespace profile on the disposable hosted
runner, if required. Do not disable AppArmor restrictions globally or change the
user's computer. The source-publication rule and E2E request do not grant this
security approval. The guarded workflow has not been dispatched.

A full mechanical status pass and successful trusted Challenge rendering remain
unperformed. Rendering must bind the frozen Challenge hash and approved official
renderer/toolchain-compatible revision. An ordinary Lake build or standalone
comparison is not equivalent to the required full reusable workflow.

## Ordinary registry intake is a separate decision

The live agent protocol requires user agreement on the repository, exact
40-character source commit, comparator.json and authorization-relationship claim
about the user before agent-driven intake. The established author list is Arthur
Freitas Ramos, David Barros Hulak and Ruy Jose Guerra Barretto de Queiroz; the responsible maintainers are Arthur
Freitas Ramos, David Barros Hulak and Ruy Jose Guerra Barretto de Queiroz. Include these exact metadata facts in the frozen
review. Do not open intake while waiting for that agreement or before hosted pass.

The permitted agent CLI proof uses a new public repository tag plus a fresh
secret gist, then immediately cleans both artifacts. Do not drive Palomar's
browser OAuth. If existing credentials cannot create the secret gist or the
repository refuses the tag, stop rather than expand scope or substitute weaker
proof. Private editorial review and its later explicit registration decision
remain separate from publication and mechanical verification. No registry
submission, acceptance or human review is claimed by this snapshot.
