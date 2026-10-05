# Final source-only review

Review date: 2026-10-04 (UTC); final evidence snapshot frozen at 23:17 UTC. Verdict: **source/statement/standalone fidelity passes this source-only review; no unresolved source blocker.**

This is an independent automated source and verification-evidence wording review. It is **not human review, kernel certification, a compiler run, or a new axiom audit**. No proof files were edited and no compiler or kernel jobs were run by this reviewer. The coordinating task reported successful exact-toolchain modular/standalone/full-Lake compilation, complete standard-only axiom closures, and direct Lean default/paranoid, NanoDa and verified ConRon checks. Available logs and source/export hashes were inspected as described below; their execution is not independently certified here. The overall supported from-export Comparator verdict is blocked at sandbox launch. A separate optional direct Lean4Lean probe is blocked at module-header reading before declaration checks; it is not a successful kernel gate. Official isolated hosted verification and trusted rendering remain unperformed. These hashes identify the reviewed recovered bytes, not pre-loss bytes: no pre-loss checksum exists.

## Scope and findings

- The target quantifies independently over X : Type u and the arbitrary index type ι : Type v, a dependent dimension function d, proofs of 3 ≤ d i, actual continuous sphere attaching maps, and x₀ : X. Its only topological hypotheses on X are TopologicalSpace and PathConnectedSpace. No finite/countable/nonempty family, CW, separation, local-connectivity, semilocal-simple-connectivity, supplied retraction, supplied simple-connectivity, kernel-exactness or quotient-oracle hypothesis appears.
- Raw is the actual topological sum X ⊕ Σ i, Disk (d i), with Disk the norm-≤1 Euclidean unit ball and Sphere the norm-=1 boundary in EuclideanSpace ℝ (Fin (d i)). AttachingRel has only its prescribed boundary generator. Space is Quot of that relation, using the inherited quotient topology. Its inclusion and inclusionPi1 are the actual quotient inclusion and FundamentalGroup.map, not substituted maps or quotient types. Algebraic normal forms are explicitly not asserted continuous.
- OpenCover proves openness of the center complement and all interiors, and their union is univ, directly by quotient preimages and the coproduct topology. Embeddings/CoverModels identify interiors and overlap with dependent coproducts of genuine open balls and punctured open balls. Annulus retracts within its own domain to radius 1/2; its actual homotopy equivalence transfers Kumar's proved sphere simple-connectivity. Interior triviality comes from convex-ball contractibility. Locally constant component indices prevent paths from switching indices, with no finiteness assumption.
- RawNeighborhood/Retraction/Deformation construct the punctured quotient map, prove the continuous retraction and jointly continuous radial homotopy using interval-product quotient descent, and obtain the neighborhood homotopy equivalence. No global openness of the quotient is assumed; no continuity claim is made for the center-extended algebraic readouts. NeighborhoodPi1 proves exact factorization of the inclusion-induced homomorphism.
- CoverPushout applies the actual ordinary all-object two-open-set fundamental-groupoid SVK theorem to the proved quotient cover. The inherited classical theorem constructs its pushout from interval/homotopy-grid descent and the indiscrete-preorder ordinary-path equivalence. The inherited Cell algebraic bridge proves surjectivity and kernel equality from the pushout and coordinates. GeometricPushout supplies all inputs, chooses generator r i = 1 from proved overlap-vertex Subsingleton, and proves the resulting normal closure is bottom. No geometric or algebraic conclusion is supplied as a caller hypothesis.
- Main proves Function.Bijective (inclusionPi1 f x₀). Its MulEquiv.ofBijective witness has E.toMonoidHom = inclusionPi1 f x₀ by rfl. Examples explicitly cover empty, fixed-dimensional and mixed 3/5 families and include independent-universe checks in both orders. These are source findings, not a new compilation claim.
- A read-only evaluation of the standalone generator, with all write expressions disabled, reproduced the current Solution and Challenge exactly. Solution contains the ordered 56-local-module dependency closure and imports only canonical Mathlib modules. The sole flattening scope adaptation splits upstream end Path.Homotopic into end Homotopic/end Path. Challenge contains exactly the actual Adjunction construction and Statement target, imports only four canonical Mathlib modules, never imports Solution, and has one deliberate theorem-level sorry. Solution and the entire local theorem closure contain no lexical sorry/admit/axiom/sorryAx, unsafe, extern or implemented_by bypass after comment stripping; no definition holes or custom axiom declarations were found. Reachability and source fidelity do not themselves constitute axiom or kernel certification.
- Byte comparisons against the recovered immutable Cell checkout at HEAD 8883b95e8ace951e27c2bc86f95d02397787dd59 matched all 3 CellAttachment, 5 ClassicalSVK and 29 Lean4 .lean files. The MIT notice also matches. Source provenance identifies ordinary SVK commit 874680e16db88b4a41daadf56eafbac79fd2f748 and Kumar's unmerged sphere PR 28246 commit 037ad801e1e5a5b7aa1750957c07f7769812effc, with original author/copyright notices preserved. This review did not independently fetch/revalidate those remote upstreams.
- README/PROVENANCE now accurately distinguish successful local reconstruction-era proof checks from the blocked overall Comparator and unperformed official hosted gates, credit Hatcher §1.2 Exercise 6, printed page 53, and explicitly identify mixed dimensions as a strengthening. They exclude the separate complement application and make no sphere/SVK or mathematical novelty claim. The established first-party names are Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; Arthur alone is responsible maintainer. No contribution roles are invented.

## Resolved metadata issue and remaining gates

The initial inherited Lean4/vendor-manifest.json hash mismatch was corrected without changing Lean source or historical hashes. It now explicitly labels every original hash historical, records shipped/not-shipped status, and points to Lean4/shipped-manifest.json. All 30 current shipped hashes in the latter were independently recomputed and matched; the mapping is exactly all 29 Lean4 directory source files plus Lean4.lean. All original upstream_sha256/vendored_sha256 values were checked against the accepted snapshot and preserved. The two omitted historical files, Lean4/all.lean and Lean4/directed_van_kampen.lean, are explicitly marked not shipped. PROVENANCE.md and PORTING.md now reconcile the historical/current distinction. This source metadata blocker is resolved.

## Final metadata and verification-evidence wording

README.md, PROVENANCE.md, SETUP.md, formalization.yaml, .github/workflows/palomar.yml and reports/local-verification-results.json were reviewed in their final snapshot. YAML files parsed successfully. No unsupported registry submission/acceptance, human-review, isolated-build provenance, hosted mechanical pass, trusted-render pass, or byte-identical pre-loss recovery claim was found. The formalization metadata limits its zero-admission count to Solution and explicitly excludes Challenge's deliberate theorem hole. Exact established first-party authors and the responsible-maintainer trio (Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz) are consistent across the metadata.

- The normal Lake log ends with “Build completed successfully (3401 jobs)” and includes Solution, Challenge and the empty/mixed/universe examples. Six complete axiom-closure outputs name the main theorem and relevant geometric/sphere results and contain only propext, Classical.choice and Quot.sound.
- NanoDa's log reports 39929 declarations with no typechecker errors and one axiom pretty-printer warning; its recorded configuration forbids additional axioms and does not enable unsafe all-axiom permission. Verified ConRon explicitly reports acceptance of 38092 declarations with one worker. Lean default/paranoid success and their exit codes are recorded in local-verification-results.json; their logs are empty, so those exit-code claims are attributed to the coordinating task's execution record rather than inferred from log text. No new kernel certification is claimed by this review.
- The JSON source hashes match the reviewed Solution and Challenge bytes exactly. Both recorded export hashes were independently recomputed from the available NDJSON exports and match: Challenge 9b0f3b0a17e02291e74cc10dc48d9ef9a61d6b87c342711bf0c505217522d598; Solution 1db6b84867d1d4b44c7a0e419c6d7efcc4384d66ea82f31cec91ecac7b32464f.
- The from-export Comparator log shows both NanoDa and Lean default launch failures caused by bubblewrap's NETLINK_ROUTE socket restriction. The recorded overall status is correctly blocked with exit code 1. Independent inspection of the pinned toolchain’s Lake/CLI/Check.lean confirms verifyMatch runs compareAt and checkAxioms before runKernels. Both normal and from-export dispatch reach this same flow, and the from-export branch uses supplied export paths without claiming a fresh sandboxed build. Lake/Check/Compare.lean checks exact theorem constant/type identity and equality of reachable non-hole declarations; Lake/Check/Axioms.lean traverses complete target dependencies against the whitelist. Reaching the observed kernel-launch message therefore establishes these preceding comparisons passed by control-flow inference, although the log does not print a separate comparison-pass line. This does not establish an accepted overall Comparator verdict or isolated-build provenance.
- The final optional bundled direct lean4lean Solution probe is separately recorded with exit code 1 at module-header reading. Its log reports an incompatible Solution.olean header and establishes a pre-declaration format blocker, not a checked declaration failure or an additional successful kernel. README, SETUP, formalization.yaml and local-verification-results.json now disclose it explicitly. This preserves the four actual reported direct passes (Lean default, Lean paranoid, NanoDa and verified ConRon) while keeping the overall isolated Comparator blocker distinct. The review does not infer the reason for the format incompatibility beyond the diagnostic.
- The additional dependency-heads.json records all nine current dependency HEADs, independently rechecked and matched, including the exact mathlib pin. All eight binaries listed in toolchain-binary-sha256.json were rehashed and match the available toolchain bytes. The recorded official-release archive SHA was not independently refetched in this review; its download provenance remains the coordinating task’s record. These records bind current bytes and pins without creating an official hosted verdict.
- The guarded workflow is prepared, not dispatched: it pins both reusable-workflow and pipeline inputs to commit 65f0154ed776cd26c224254aa57b379137f28b0d, requests full/palomar-standard-v1, binds github.repository/github.sha, and requires the security-approval input to be true before invoking the official workflow. That input defaults false. Neither source-publication authorization nor a prepared workflow supplies the missing action-time security approval.
- SETUP correctly records owner-authenticated public source publication and the requested Write invitation as pending. Hosted full verification and frozen-hash trusted Challenge rendering are separate unfinished gates. Ordinary agent-driven registry intake requires a separate exact-target user agreement, including the repository, source commit, comparator and authorization relationship, after hosted pass. No dispatch, credential expansion, security change, intake or acceptance is authorized or asserted by this source review.

No unresolved mathematical-source, standalone-fidelity or metadata-wording blocker was found. The operational blockers remain the separate optional Lean4Lean pre-check module format incompatibility, the unavailable isolated Comparator sandbox, pending owner publication route, official hosted verification/security approval as required, trusted rendering and separate exact-target intake agreement. Do not present this source-only review as human or kernel approval.

## Exact reviewed SHA-256 hashes

This is the frozen final source/evidence snapshot. The companion final-source-review-hashes.json contains the same repository file/hash mapping. Later metadata edits require a refreshed or explicitly superseded review hash; theorem source edits require re-review. Export hashes are recorded above; the large export files are not included in this per-source/log inventory.

- `CellAttachment/GroupQuotient.lean`: `4dabfe6c6a8f55cb0cdee2816fdfe2e97f285adcece7473cec5861a36d35b2f4`
- `CellAttachment/GroupoidQuotient.lean`: `69f3373ce4e759963c12e1388400c12ee25e59b5c3df2a818f6a1085e491a3ee`
- `HigherCellAttachment/Adjunction.lean`: `221b1a66744a49cfdfc2d60836cd3e88e00a5e7133fdbcc1677ac457f3f4a3bf`
- `HigherCellAttachment/NormalForm.lean`: `5a11a27c7f13a437f5cdf9b15a355d9b419e447793103df9bd921eb1ce31a627`
- `SphereInfrastructure/VanKampen.lean`: `607e8d105210618ab5d738e9fcf786308a41bd31db8403db55f4fe90d987b4ac`
- `SphereInfrastructure/PartialEquiv.lean`: `1c3df09ead2e8b7c206141949de2bbd743988f43a14eb768e4f1cdbea7262b42`
- `SphereInfrastructure/SimplyConnectedSphere.lean`: `447375ffb40f018fea4ef34f4653719fb6afabffc5bd054568f79395ea04e666`
- `HigherCellAttachment/Sphere.lean`: `2ee75633b40183a5b94e67651f87a2085cf77fd351bf022c942d82f8592961c3`
- `HigherCellAttachment/Annulus.lean`: `8a4e75c54d7a319246bca6feeea9af52c90d4924c778d8478d2d40c3fa80fb6a`
- `HigherCellAttachment/OpenCover.lean`: `15699c533ce5de55f2c6564c4e139e86e89fe61c920c8b1686d6b99dafee7f7c`
- `HigherCellAttachment/Embeddings.lean`: `07b97fe3bd26761b37c0285ee3e2e663a4040b9af52bb6f61a7997788f81cc29`
- `Lean4/fraction.lean`: `060de7497f411e122753d06dd9c3c3c14436108b4fa2081aa99a47e7179a85cf`
- `Lean4/cover_lemma.lean`: `f2ba7026f35de6afa537a3d994bc0a92c9cb6fe9f3820f7507e544a0841806c4`
- `Lean4/directed_space.lean`: `4673c5af561b9f7885df848bc2f7574bb0370d995ac61b17ac11daaa1b09478a`
- `Lean4/directed_map.lean`: `49d678568366e295f2ac4b82fdb9f6a420c04107bebe22f3b933c66037eb75cf`
- `Lean4/monotone_path.lean`: `ddaaa0f2b7779a32bf8e0fe58ba59535e391e2629ae9cd3bd953c7cdb2ef1890`
- `Lean4/constructions.lean`: `6b180fa47df74cdcfad85b974070e172f55bdf0024e4173a406b0134c1820ce7`
- `Lean4/directed_unit_interval.lean`: `8b528ed495376ec69c75bb7d6a61357f4ddb55c080c33ddfb9b9e8573dc3d822`
- `Lean4/unit_interval_aux.lean`: `7b283d6274646029a16ffda978227eb9025aef3a10e7dc13f1f36e9ae1487e59`
- `Lean4/dipath.lean`: `1685feb92973fc9ee02d3852055fbd722e9c144db5f8cb646c432637c2752572`
- `Lean4/dTop.lean`: `a46ef4d00ed0d0ca52d50f2a364ae1d80cbe652d07d0321b5671dc387742ecb1`
- `Lean4/interpolate.lean`: `27b85588011ce98ce587b79351219d5cfcece95af614a05c84929f1bb638fd4e`
- `Lean4/SplitPath/split_path.lean`: `5fa4dd412731741524d6b7fb618b2af40fc1ad83d65845dfa7a690de6d08f6ab`
- `Lean4/SplitPath/split_dipath.lean`: `11630adb363910e1be8a1019dc8cd425f83719097074507e8a886fd2aa83b1cc`
- `Lean4/stretch_path.lean`: `1111443c26be36f6a945bc0c1cdd579c5f42d100f1522e8709a8fdb466d195b0`
- `Lean4/directed_homotopy.lean`: `f4bad6a0f8e12bbc102bed90be530caf05116410e4403f96438f55b4f8cafc64`
- `Lean4/trans_refl.lean`: `82bce6a92a231a637b93ff23618f30c7127c09941d712e908aaa9b2c4521e39c`
- `Lean4/directed_path_homotopy.lean`: `3f490742118e2af100443486474e2a78aab5ea597793fe0d1a84abc0223e4013`
- `Lean4/fundamental_category.lean`: `77c4d24695a2cc8b0980b5786bbd21f8de5fd4a8d30e46068733fd54157ee7bb`
- `Lean4/dipath_subtype.lean`: `8b03ea6ea42097e030640804cfc82be676a4bbb2ffd4ee3d87fa16ebc2ef8c79`
- `Lean4/fraction_equalities.lean`: `8c7afe75c5614190d8ac1dfbddf7b99f26a7781c5bc549489b1b1ae9927e4e46`
- `Lean4/SplitPath/split_properties.lean`: `35e45d941d1cca210a3f5323b50f7ed9051c8799e7cf376a40e3ea973e06d4ba`
- `Lean4/path_cover.lean`: `b6c92ea78575d71b7d98956c245c99d679386a0d808f57ced4a966d922a18a3b`
- `Lean4/split_dihomotopy.lean`: `f9b7449495a8341ab392497774e7ec3de247795010031dfa9d0445143be5020f`
- `Lean4/dihomotopy_cover.lean`: `a19af32b2d963949181377beb78f3b1de519728a54bb1c146f6fb80229c53561`
- `Lean4/pushout_alternative.lean`: `d3a64debf3085d2a810f0790d483684ea800e9929850970633bd2feb46c13053`
- `Lean4/dihomotopy_flip.lean`: `fe55d63b75f68fb859ee532c32389360f3e9be9515730ac8fed361064d23c3d3`
- `Lean4/dihomotopy_to_path_dihomotopy.lean`: `6d603200ba482df50d111273126589b9914a87f6bfb881ef40157025a072146d`
- `Lean4/morphism_aux.lean`: `d0a454ef1fc7337b365dde3db8a43266a24eccc2cfa6be1ee14cb6957e8f633f`
- `Lean4/path_descent_helpers.lean`: `40b253fa5c9e39e6021bc7d29c1a6cfe8d5f4870cbbcc5ccfc48702d7aaaddec`
- `ClassicalSVK/Bridge/Categories.lean`: `91955dbf027b64ad5476efff7083dd294eac9184ea4377553619f371ba918625`
- `ClassicalSVK/Bridge/Naturality.lean`: `ffacb3e5f3997980277687d0df3a128e76e16ffeeedc3b668a40ed867a813622`
- `ClassicalSVK/Bridge/Naturality2.lean`: `ee0fd2d627bd842c269e482cde99c53eb4a71f3e79731efee7590ed79dd999ab`
- `ClassicalSVK/Bridge/Iso.lean`: `c70795aba04e7bb4f5d878bedfaed69e01a6b6129f24d3b288602a89388eeb6b`
- `ClassicalSVK/Pushout.lean`: `1fe2ee191814fd9053f8b011bd81a52b8a08da0872c1dc97e11a978364bfb39a`
- `HigherCellAttachment/CoverPushout.lean`: `ed64c0c1481b431b8e4ff84b18cb53fb69e827650fc3502c880f9cbbbc8a16d7`
- `HigherCellAttachment/Radial.lean`: `93442e8b0a0d3ab189e828f830540121482f548edb1c330608ea5070f12a4cb7`
- `HigherCellAttachment/RawNeighborhood.lean`: `73071de74fe1aab0c38e67466ce8180648ef13d95bff6a70f98d13955d42b0d7`
- `HigherCellAttachment/Retraction.lean`: `e8b246765fdc563ab25b62705b732a5a18f13a65dd52860bd99c15804d97f796`
- `HigherCellAttachment/CoverModels.lean`: `df03f3263cc0b8de5364cc80904a792d820ece9a6206357cd750e0a4dcf72107`
- `HigherCellAttachment/Deformation.lean`: `85983ba1940518928213e7aa479b5c29873395cec1c3e5a66fce17b752adb8e0`
- `CellAttachment/HomotopyPi1.lean`: `0d17b7f2b3ee806b4ad6f1f505861ea1dee4860873d823f311fb34e268e14322`
- `HigherCellAttachment/NeighborhoodPi1.lean`: `8622fd7e2ad89fe537a7a74af4e863124ba86b5423f61bee05b3e287218a18c6`
- `HigherCellAttachment/GeometricPushout.lean`: `2cd3cd8431d8c4f0ae37c78a590afd7c81c038eb9a8e67e2e26685194e9e2be9`
- `HigherCellAttachment/Statement.lean`: `43124cfea982118fde5bf5595ba73a06bfc58a78feb033758f60c853e09f66ef`
- `HigherCellAttachment/Main.lean`: `0ae51862491a7e55bf02ff27244728f03064484aa167ad3a6f4c56711834c7e3`
- `Challenge.lean`: `6b8881b81d2c3e317770806923269ee15c4aa01dde0e36f3b73f3b41c4153c2f`
- `Solution.lean`: `19766fec40044fbbfb001248a277204681bc0de358f4f6b6183b2da80659d462`
- `HigherCellAttachment/Examples.lean`: `da5821f006f25594a7a896a884399631d2610ef5492aa6057965ff558b79a131`
- `scripts/generate_standalone.py`: `fd8df77c4e6ff1698e13a42992a29c369ce239dcb9e8262bdcb07bbd9891931e`
- `README.md`: `8961b71e69adcff150dd6020c9cbc87967fa0f1ef95466fdc05676e622d72587`
- `PROVENANCE.md`: `39b55428559675287c33469069e0898bd6a430b8802d884a83fe9516d47a10b0`
- `LICENSE`: `5f3751276afe718ffa78ec1fc61490d4185712554bcb6a90059416dc424ce9a6`
- `Lean4/LICENSE.md`: `2ced362d7ffbb9c04bb1f7471d63fc4a96e148a4358eca72afbd860367f41a2d`
- `Lean4/vendor-manifest.json`: `10867a87310427aea50528e13b2d4d7141f01812d4d625c98681407472378fb7`
- `lakefile.toml`: `2cf628e04bc3784d619d907f36181a6dd65b180a6729348fdad90726f4934e68`
- `lake-manifest.json`: `6f75f0f6f3f8ba51ccc5e5e809502655b31f3c31efa35878aef50586372fb04b`
- `lean-toolchain`: `8dc8d6f560141069d9073e370611716ef77ada0da8ffa37e2149f44b2e63ac7a`
- `comparator.json`: `1f1d9772e3c3b73a12a97bf8106811d7756976c85c6c791084cfb4378a84f7d2`
- `Lean4/PORTING.md`: `8e020573da92105879100e1e7ea0538ed282824af367a4e7c4d1ad5bc4840b04`
- `reports/standalone-manifest.txt`: `e42c7bfbe4a99ff92f13f622f91bf9ca420e7eb5d5cba57c79d47c8d7e7d8ef3`
- `Lean4/shipped-manifest.json`: `bb3a511c95d009530a7e6f469fa5c67e42f4109b7a85f3dbd9108fa1545c0889`
- `SETUP.md`: `a8b5f91f2304e76a6e816195c0d3bebe4ede49d93fc0a6d2f4c797a08e27a06d`
- `formalization.yaml`: `a44d738524d538102090ea6f5eb399e9f5a9892e19e9f26baf313e266f731b80`
- `.github/workflows/palomar.yml`: `470101f2c746aa35791755ceb1ee45f786657c16be1ee08325ba7074ba9b2b53`
- `reports/local-verification-results.json`: `5cae56b2ca608f30389818c44b5eadb339aa22b355fa6595009b47ec05bd31cc`
- `reports/lake-full-build.log`: `a4b9c7e561c8214d83285b3bb67befc15aa58ac116c42aff5407ba77f2f729d8`
- `reports/reconstructed-solution-build.log`: `7d5e5a1c08303028c53bc4d4cd536878cfcea507d83bc6baf713acd718fad184`
- `reports/final-axioms.log`: `63787d76fb48bf609a6c527cc8801858a63881212b103a97e891d210321c19ee`
- `reports/nanoda.log`: `389ba9935851d49579527cec2aa74e29ce76a836e9ae51bb683de32026e3e33a`
- `reports/conron.log`: `8adceb13212202ecbf81c83f3dca49751795991b731e166751e8253356bb4096`
- `reports/comparator-from-export.log`: `bff4bbf71a0b76d9282dc0a1855ec7b7cecca64f0405b2b83892d633496a7c31`
- `reports/export-targets.json`: `1ba3bcb8c9eff1da62430cdf3b209df096d58e1ad71bcf08a82b96b68d2851d1`
- `reports/nanoda-config.json`: `c4b235a05f0170480a1b598e197b43ee3ced60b496d30541f05a6afae8053577`
- `reports/leanchecker.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `reports/leanchecker-paranoid.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `reports/dependency-heads.json`: `0488cb75e9e4b1eb26a2274ed78a3d43a4f1098f3ae4e1ad70d0bfaeed309c90`
- `reports/toolchain-binary-sha256.json`: `8007b737b0da248b81335e78ebfdba21dbfd16ef68af23836fe2d09aaead64a3`
- `reports/lean4lean.log`: `010866f9bbe77556720548ce67d6cbadba79420f8b84eebf8aeb33f23e1e017f`

External exact-toolchain source inspected for control-flow evidence (not project shipment):

- `Lake/CLI/Check.lean`: `55daf430e5adea38453b21798cbdf4cd099f66ec969494022a566a8ae098c00b`
- `Lake/Check/Compare.lean`: `0281630a33b8f08a9f3f40f229cd843c02441a0cd4d8a6d8548dc2bb8ded4c68`
- `Lake/Check/Axioms.lean`: `261fa54494a6a17c23b8588d788ab1080e5c39af2143948f8e140cfa295560d1`
