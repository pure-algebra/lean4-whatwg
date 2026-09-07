# Provenance

Every pin this repository relies on, with its digest, how it was fetched, the
cross-check performed, and its license. `SPEC-MANIFEST.md` owns what each pin
is for; this file owns that the bytes are what they are claimed to be.

Sealed-source digest cross-check protocol: each sealed-file digest is computed by `lake exe vendorseal`
through the required `hash` package (`Hash.Sha256.sha256`, proved against
FIPS 180-4 in lean4-hash) and independently by PowerShell `Get-FileHash
-Algorithm SHA256`; both spellings must agree. At P0 the first computation was
the in-tree `lake exe sha256`, executable evidence until the lane's proof
graph closed; at the swap to the package (step 6 of
`docs/HASH-PACKAGE-PLAN.md`) `generated/vendor-manifest.tsv` regenerated
byte-identically, so the sealed-source digests below are unchanged. The separate
Lake dependency section states its local object-check protocol explicitly.

## Vendored, sealed

| Pin | Fetched | Command | Cross-check |
| --- | --- | --- | --- |
| `whatwg/encoding` @ `67494fceee1b95bbc87b58142fcc14e48310f257` (2025-06-16T07:39:10Z, "Review Draft Publication: June 2025", the latest review draft at pin time), `encoding.bs`, `LICENSE`, `README.md` | 2026-09-07, for URL U3 and the Infra UTF-8 core | `gh api repos/whatwg/encoding/git/trees/67494fce…` (not truncated), then binary reads from `https://raw.githubusercontent.com/whatwg/encoding/67494fce…/<path>`; no checkout or newline conversion | all three files match upstream blob hash (`git hash-object --no-filters`) and byte size: `encoding.bs` blob `ad1af60b262002ec320c4deeae63a2af3b8148f6`, 144,545 bytes, SHA-256 `43cb027a611580ad07b5cd3a96e82ee4303594e6b24b8b7c5b903cd2e50f19ad`; `LICENSE` is the same 16,315-byte CC-BY blob and digest as the other WHATWG pins; `README.md` blob `5eb93055d56a8fc7c12c1ef9a3dd7ef2a853d6b6`, 4,730 bytes, SHA-256 `75e954485f650b41546d73ba8bdeb5a7677b967156f9f9ff82b19cc36541440d`; seal and `Get-FileHash` agree |
| `whatwg/webidl` @ `a652053f1e74e4aaf647528deb174012ed6c909f` (2026-03-16T07:19:44Z, "Review Draft Publication: March 2026"), `index.bs`, `LICENSE`, `README.md` | 2026-09-06, for P8 | `gh api repos/whatwg/webidl/git/trees/a652053f…` (not truncated), then binary reads from `https://raw.githubusercontent.com/whatwg/webidl/a652053f…/<path>`; no checkout or newline conversion | all three files match upstream blob hash (`git hash-object --no-filters`) and byte size: `index.bs` blob `5e28e635ae9106fe18dc8d4c7b14f79b23355995`, 695,845 bytes, SHA-256 `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`; `LICENSE` is the same 16,315-byte CC-BY blob and digest as Infra/HTML/Streams/URL; `README.md` blob `7232827147b3c121eab2451e4a41ba0c3cc5324a`, 2,402 bytes, SHA-256 `78d9b5da7b22ef6f39704a0cc52e96c9c16c17ab6770ee868903eed7b21f0d81`; all rows agree between Lean's vendor seal and independent PowerShell `Get-FileHash -Algorithm SHA256` |
| `tc39/ecma262` @ `0248456c758431e4bb8e5d26333ff1865123c9cd` (tag `es2026`, 2026-03-31T05:40:50Z), `spec.html`, `LICENSE.md`, `README.md` | 2026-09-06, for P8 | the same blob route through `gh api repos/tc39/ecma262/git/trees/0248456c…` and `raw.githubusercontent.com` at the commit | all three files match upstream blob hash and byte size: `spec.html` blob `22dc069f5aeda770c1db2e389cbaa252188f43bf`, 2,978,793 bytes, SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0`; `LICENSE.md` blob `6e6b6a4742069c493c4b66e06dad9e5bd9f05f9a`, 804 bytes, SHA-256 `484d4a9e3e4bab42e5e2f8703c34ed46e861fb62662e1818b4534d1e34584967`; `README.md` blob `a816344bf5bf7dbdf8723a1e0b2ee627d957ba4c`, 1,662 bytes, SHA-256 `68872cf8dcff99d980cccdfeef312e69a1b9cb84378494152f10c66ed8eb7c47`; seal and `Get-FileHash` agree |
| `whatwg/url` @ `55d6699373ba68a16ec182f34222a74ed8bc3dac` (2026-08-18T11:17:15Z, "Review Draft Publication: August 2026"), `url.bs`, `LICENSE`, `README.md` | 2026-09-05, U0 | unauthenticated GitHub API tree at the exact commit, then binary reads from `https://raw.githubusercontent.com/whatwg/url/55d6699373ba68a16ec182f34222a74ed8bc3dac/<path>`; no checkout or newline conversion | all three files match upstream blob hash and byte size, checked by `git hash-object --no-filters`; `url.bs` blob `3fd9afa1ea31fe397f38b901b0d46ac290ad3fc9`, 162,680 bytes, SHA-256 `a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`; `LICENSE` is the same 16,315-byte blob and digest as Infra/HTML/Streams; `README.md` blob `0c05995e577af064e2ba8c13293f10194a6c6d93`, 5,549 bytes, SHA-256 `bc515ffd0eed8dd34f5fb9cf2b0099239fa6844a13db1c3122393bc560820206`; all rows agree between Lean's vendor seal and independent PowerShell `Get-FileHash -Algorithm SHA256` |
| WPT `url/**` @ existing `480fdfcd85d043c23875665f464c35c0043dff52`, 49 files | 2026-09-05, U0 | read root tree at the pin and recursive `url/` tree `63cdded2721ea89e3d28f9bae6ed31ffaeeaf591` through GitHub API; binary reads from `https://raw.githubusercontent.com/web-platform-tests/wpt/480fdfcd85d043c23875665f464c35c0043dff52/url/<path>` | the tree response is not truncated; every file matches upstream blob hash (`git hash-object --no-filters`) and byte size; all 49 Lean-generated manifest digests independently match `Get-FileHash`; existing WPT `LICENSE.md` retained byte-identically; fetched corpus only, no runner or host receipt |
| `whatwg/streams` @ `b9ba9f49d95b4280be0dc2372377a006c3a91c18` (2026-08-18T11:17:34Z, "Review Draft Publication: August 2026") | 2026-09-01 | `git clone --filter=blob:none https://github.com/whatwg/streams` then `git checkout b9ba9f49…`; copied `index.bs`, `LICENSE`, `README.md`, and `reference-implementation/{lib/**, package.json, README.md, LICENSE.md, COPYING.txt, run-web-platform-tests.js, compile-idl.js}` | every one of the 54 files matches the upstream git blob object hash from `git ls-tree -r b9ba9f49…` (checked with `git hash-object --no-filters`); `index.bs` `24360b4f8446e6c80e185c5021fcca9b67a7e0bb62490a00109080ebc04c6440`, 417,076 bytes, agrees between both SHA-256 implementations and with `raw.githubusercontent.com` at the commit; every file's digest is in `generated/vendor-manifest.tsv` |
| `whatwg/infra` @ `3f984adcd24a6d5c53cc26b3e737701808003f3e` (2026-07-17T13:21:29Z, "Review Draft Publication: July 2026"), `infra.bs` and `LICENSE` | 2026-09-02, slice W5 | `gh api repos/whatwg/infra/contents/infra.bs?ref=3f984adc… --jq .content \| base64 -d` (blob `0446ff3db3bb9101275968e6c4442e2aa8ab8ff7`, 104059 bytes) and the same for `LICENSE` (blob `f2dcda46deccefd245749202a88a7837e35c6daa`, 16315 bytes) | `lake exe vendorseal` through `Hash.Sha256.sha256` and, independently, macOS `shasum -a 256`: `infra.bs` `7c38e6e25ef21f536142cfc6d94954c41bc9889cd0b6fd67ab34571215acd8eb`, `LICENSE` `85dc6f5ccb57a6fe8c33d158f9fc8fc7ee5655a5d3db2cdd131c6a3d0f48a864` (byte-identical to the Streams `LICENSE`); both agree |
| `ocsigen/tyxml` @ `d2916535536f2134bad7793a598ba5b7327cae41` (tag `4.6.0`, tagged 2023-09-27T09:48:59Z), 25 files: `lib/**`, `syntax/reflect/**`, `syntax/sigs_reflected.mli`, `LICENSE`, `CHANGES.md`, `README.md`, `tyxml.opam` | 2026-09-03, slice H0 | `gh api repos/ocsigen/tyxml/git/trees/d2916535…?recursive=1`, then each blob through `gh api repos/ocsigen/tyxml/git/blobs/<sha> --jq .content \| base64 -d` | every one of the 25 files matches its upstream git blob object hash (`git hash-object --no-filters`) and size from the tree listing; `lake exe vendorseal` through `Hash.Sha256.sha256` and, independently, macOS `shasum -a 256` agree on all 25 rows; the opam-installed `tyxml.4.6.0` sources on the pinning host are the same bytes |
| `whatwg/html` @ `746f2ede8a56bc01204e0f9cc23da33b37c6fbab` (2026-07-17T13:21:58Z, "Review Draft Publication: July 2026"), `source` and `LICENSE` | 2026-09-03, slice H0 | the same blob route (`source` blob `1d4de3a60e28b9cd27863720b166e3e49376361b`… as listed at the commit, 7,891,297 bytes; `LICENSE` blob `f2dcda46deccefd245749202a88a7837e35c6daa`, 16,315 bytes) | both blob hashes and sizes match; `source` `c985a14d1871fe862de386f5af92b5da84068267c6095ef0379c069ae85f9cde` and `LICENSE` `85dc6f5ccb57a6fe8c33d158f9fc8fc7ee5655a5d3db2cdd131c6a3d0f48a864` (byte-identical to the Streams and Infra `LICENSE`) agree between the seal and `shasum -a 256` |
| `web-platform-tests/wpt` @ `480fdfcd85d043c23875665f464c35c0043dff52` (committer date 2026-09-02T02:49:23Z) | 2026-09-01 | sparse clone: `git sparse-checkout set streams`, `git fetch --depth 1 --filter=blob:none origin 480fdfcd…`, `git checkout FETCH_HEAD`; copied `streams/**` and `LICENSE.md` | every one of the 123 files matches the upstream git blob object hash from `git ls-tree -r 480fdfcd…`; per-file digests in `generated/vendor-manifest.tsv`; `LICENSE.md` `5fac07febb0e2a97fb0d7b0def149ec08b642e1ba4b9c345283ab1cbd2af6570`; `streams/piping/general.any.js` also agrees with `raw.githubusercontent.com` at the commit |
| NIST FIPS 180-4, *Secure Hash Standard (SHS)*, August 2015 (`vendor/nist-fips-180-4/NIST.FIPS.180-4.pdf`) | moved to lean4-hash with the SHA-256 lane (slice W3b of `docs/WHATWG-PACKAGE-PLAN.md`, 2026-09-02); pinned, sealed, and cross-checked there under the same protocol | — | — |
| NIST CAVP `SHA256ShortMsg.rsp`, CAVS 11.0, generated 2011-03-15, 65 vectors (`vendor/nist-cavp-sha256/SHA256ShortMsg.rsp`) | moved to lean4-hash with the SHA-256 lane (slice W3b of `docs/WHATWG-PACKAGE-PLAN.md`, 2026-09-02); pinned, sealed, and cross-checked there under the same protocol | — | — |
| NIST CAVP `SHA224ShortMsg.rsp`, CAVS 11.0, generated 2011-03-15, 65 vectors (`vendor/nist-cavp-sha224/SHA224ShortMsg.rsp`) | moved to lean4-hash with the SHA-256 lane (slice W3b of `docs/WHATWG-PACKAGE-PLAN.md`, 2026-09-02); pinned, sealed, and cross-checked there under the same protocol | — | — |

TyXML pin retired, 2026-09-06. The TyXML row above records a pin that no
longer exists in `vendor/`: the `Whatwg.Html.Schema` modules were transcribed
from it at H2 (2026-09-03; the projection's 931 `type`/`val` rows were
cross-checked against OCaml 4.14.2's own parser, identical lines in the same
order), and on 2026-09-06 the vendor tree, the projection
`generated/tyxml-html-schema.tsv`, the generator and drift gate
`lake exe tyxmlschema`, and the OCaml cross-check scripts were removed. The
schema modules are authored source from that date; the HTML Standard is the
sole authority. TyXML bootstrapped the shape and has no further role.

Vendored licenses: WHATWG Streams, Infra, HTML, URL, Web IDL, and Encoding Standards, CC-BY 4.0 with BSD-3-Clause for
portions incorporated into source code (`vendor/whatwg-streams-b9ba9f49/LICENSE`,
`85dc6f5ccb57a6fe8c33d158f9fc8fc7ee5655a5d3db2cdd131c6a3d0f48a864`); reference
implementation, dual CC0 / MIT (`reference-implementation/LICENSE.md`,
`2d301992ca987e748f1b9d6eb2d591acf074fff828883887228eee3732fc0f79`); WPT,
BSD-3-Clause. TyXML (LGPL-2.1 with the OCaml linking exception, `LICENSE`
`98ffe2221c1f0e316987ea418aada8e9e860b3fb79693ee768034328465fd440`) was
retained until 2026-09-06 as a schema source only, never compiled or linked;
the transcribed schema is attributed in its module headers. ECMA-262 is
under Ecma International TC39's IP policy (`vendor/ecma262-0248456c/LICENSE.md`,
`484d4a9e3e4bab42e5e2f8703c34ed46e861fb62662e1818b4534d1e34584967`): the
natural-language text under Ecma's alternative copyright notice, which permits
reproduction for standards work, and the source code under Ecma's MIT-style
software policy; it is retained as a specification source only. All permit
retention with attribution; the upstream license files are retained in place.

The NIST pins (FIPS 180-4 and the two CAVP response files) moved to
lean4-hash with the SHA-256 lane; they are works of the US Government, not
subject to copyright in the United States, and are retained unmodified there. The repository's own `LICENSE` (MIT since 2026-09-02) does not apply to
anything under `vendor/`.

`.gitattributes` disables end-of-line conversion for the whole repository
(`* -text`), so a checkout on any host reproduces the committed bytes and the
seal holds without a host-specific `core.autocrlf` setting.

**Why the blob-hash check exists.** The first P0 vendoring copied the
whatwg/streams files out of a Windows working tree, where that repository's
own `text` attributes had converted every text file to CRLF on checkout;
`git archive` applied the same conversion. The in-tree SHA-256 and
`Get-FileHash` agreed with each other on those bytes, and the seal passed,
because both were measuring the converted file. Only a comparison against
GitHub's raw content exposed the 8,401-byte difference in `index.bs`. The
vendored files were then rewritten directly from the upstream blob objects
(`git cat-file blob <sha>`), and every file in both trees is now verified
against `git ls-tree` object hashes, which cannot be affected by any
attribute or host setting. Two agreeing digests of the same wrong bytes are
not provenance; the reference point has to be upstream's own identity of the
object.

The reference implementation's `node_modules` and its own test runner
dependencies are not vendored. Running it as a host profile installs its
pinned npm dependencies outside `vendor/` (P8).

## Not vendored, digest only

| Pin | Fetched | Command | Digest | Cross-check | Why not vendored |
| --- | --- | --- | --- | --- | --- |
| EffHOL: Liron Cohen, Ariel Grunfeld, Dominik Kirst, Étienne Miquey, *Syntactic Effectful Realizability in Higher-Order Logic*, arXiv:2506.09458v1, published 2025-06-11T07:02:23Z, LICS 2025 | 2026-09-01 | `Invoke-WebRequest https://arxiv.org/pdf/2506.09458v1`; metadata from `http://export.arxiv.org/api/query?id_list=2506.09458` | `a493e698895878136a71e9ffdaaf9ece786cdd30864f853149cd69cec774ad0c`, 777,345 bytes | both implementations agree | arXiv redistribution terms not verified; the digest identifies the exact bytes any reader can fetch |

FIPS 180-4 was a digest-only row until S1.0. Ruling R-8 vendored it; it is now
sealed, and its row is in "Vendored, sealed" above with the same digest.

## Lake dependency objects (cross-checked 2026-09-05)

These are Lake-managed Git dependencies, outside the `vendor/` seal.
`SPEC-MANIFEST.md` owns their current roles and pins. The configured URLs are
`https://github.com/pure-algebra/lean4-hash`, `lean4-effects`, and
`lean4-typescript` under the same owner. Local clones use matching SSH remotes.
The original fetch dates were not recorded. The reproducible fetch route is
`lake update` with the exact `[[require]]` revisions in `lakefile.toml`; this
audit did not refetch or change them.

| Package | Commit / locally verified tag | Committed tree | License at this commit |
| --- | --- | --- | --- |
| `hash` | `0168306b7068b97758e3f2d4307eeb97aa31a104`; no local tag | `9613a78e01ec449bd2977c492a55efcfdf0e24cd` | Apache-2.0; `LICENSE` blob `d645695673349e3947e8e5ae42332d0ac3164cd7`, 11358 bytes, SHA-256 `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` |
| `effects` | `c28833b3c14431ba2886a0fb66bcc688c86c2589`; `v0.5.0` | `4725df0d6563e8a8b74137d23c2711be8608a5bb` | MIT; `LICENSE` blob `1e7fe3f72d2c0baf370f7375bca9802594a9a6ef`, 1069 bytes, SHA-256 `c51d370d20b9c1b2906d5583a1e9c519eaaf5d2033010eecfc7788e399d8eecf` |
| `typescript` | `fcbc05a40e52f9bbe8a8e3ee0f4a746ebd4e9554`; `v0.2.0` | `0be6d0a2b2a5f5ba50932140ecb745a533d95e4a` | MIT; same committed `LICENSE` blob and digest as the effects row |

For each `.lake/packages/<name>`, `git rev-parse HEAD` and
`git rev-parse HEAD^{tree}` match these rows; `HEAD` agrees with both
`lakefile.toml` and `lake-manifest.json`. `git rev-parse <tag>^{commit}` checks
the two tags. `git ls-tree HEAD LICENSE lean-toolchain lake-manifest.json`
and `git cat-file blob HEAD:LICENSE` identify the committed bytes; the
license SHA-256 values above were computed over those raw object bytes with
the system implementation. All three committed toolchain blobs are
`a8afa7d1b02d96f0671eba854a8dc4b416beb473`, 25 bytes, naming Lean 4.33.1 and
matching this repository's toolchain SHA-256. All three Git statuses are
clean and their package manifests list no transitive packages.

This is a local object/lockfile cross-check, with no network revalidation or
second SHA-256 implementation claimed. Package checkout attributes can
convert text to CRLF even with a clean Git status; therefore these rows
identify committed Git objects and do not claim that package working files
are sealed or byte-identical to those objects.

## Toolchain and hosts

| Pin | Evidence |
| --- | --- |
| `leanprover/lean4:v4.33.1` | `lean-toolchain` SHA-256 `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`, both implementations agree; `elan show` lists the toolchain as installed |
| Node v22.23.2 | `node --version` on the P0 host |
| Bun 1.4.0 | `bun --version` on the P0 host |
| P0 host | Windows 11 (NT 10.0.26200), AMD Ryzen 7 8700F |

## Process precedents (not semantic pins)

| Source | Commit | Used for |
| --- | --- | --- |
| `pure-algebra/lean4-effect4` | `e9075e192bb3065e3900ccabe7c0c2a6df1ddffc` | the router hierarchy, breaker/builder order, counterexample register, assurance threshold, the axiom gate (ported to `WhatwgTest/Audit/AxiomGate.lean`), the coverage-metric discipline |
| `mepuka/foldlab` `formal/fips202` | `8d36195970b83a1439ec705b9a504617554b8062` | the Pass A / Pass B contract shape and the spec-to-implementation refinement decomposition reused by `docs/SHA256-DAG.md`; its `TOOLING-NOTES.md` requirements on gates as checked programs |

## Pending

| Row | Needed by | State |
| --- | --- | --- |
| NIST CAVP `SHA224ShortMsg.rsp` | S1.6 | vendored and sealed at S1.6 from the git object (blob `ab3b099c73048c279c97f88c3a549e7545c3887b`); its row is in "Vendored, sealed" above |
| NIST SHA-256 example values (`abc`, the two-block message) | S1.7 | not yet fetched; until it is, the seven memory-typed literals in `lake exe sha256 --self-test` have no pinned provenance (`docs/SHA256-DAG.md` §3.4) |
| kim-em/lean-crypto-hash prior art, commit `54e6068abd4658fd91203cae1c2316188ffa0e89`, Apache-2.0, toolchain v4.33.0 | S1 | read first-hand 2026-09-01; no code imported; API shapes and the streaming technique are credited in `docs/SHA256-DAG.md` §3.5 |
| foldlab `.staging/fips202-library/SPEC.md` (decision 45, R-1 approved 2026-09-01) | S1 | the staging discipline `docs/SHA256-DAG.md` adapts; at foldlab commit `8d36195970b83a1439ec705b9a504617554b8062` plus the uncommitted working-tree file read 2026-09-01 |
| wpt.fyi run identifiers for Chromium, Gecko, WebKit at the WPT pin | P8 | not recorded |
| reference implementation npm dependency lock at the pin | P8 | not installed |
| `pure-algebra/lean4-nlp` benchmark corpus commit | R0 | not yet read |
