# Provenance

Every pin this repository relies on, with its digest, how it was fetched, the
cross-check performed, and its license. `SPEC-MANIFEST.md` owns what each pin
is for; this file owns that the bytes are what they are claimed to be.

Sealed-source digest cross-check protocol: each sealed-file digest is computed by `lake exe whatwg_vendorseal`
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
| `w3c/svgwg` @ `47e645ef7cb61490e6975ddbcfa1997c9e972cc3` (2026-10-07T04:36:19Z, "Merge pull request #1183 from karlcow/1169-getitem-identity", the head of `main` at pin time; the repository carries no tag), thirteen files: the five definitions files that `master/publish.xml` lists, that file, the chapters `master/struct.html`, `master/paths.html`, `master/shapes.html`, `master/coords.html` and `master/types.html`, `LICENSE.md` and `README.md` | 2026-10-11, slice S1 of `docs/SVG-PACKAGE-PLAN.md` | `gh api repos/w3c/svgwg/git/trees/47e645ef…` for the root and for `master/` (neither truncated) and `gh api repos/w3c/svgwg/contents/specs/animations/master/definitions.xml?ref=47e645ef…`, then binary reads from `https://raw.githubusercontent.com/w3c/svgwg/47e645ef…/<path>`; no checkout or newline conversion | every file matches its upstream blob hash (`git hash-object --no-filters`) and byte size: `master/definitions.xml` blob `1afe3cea45f48f5280b2c497e3b99ae2e6eb0054`, 83,931 bytes, SHA-256 `7db42f32f4c2c3c5d6395737dd20cd91e91a41efccf6b9d545cc5abc7400e34b`; `master/definitions-filters.xml` blob `eb52ccc7bcb8d8a10f31a715fbb2de8e13f88bac`, 20,896 bytes, `f96968584136839df0770a6f09049f780b066f1a4b0821dd6664dc50992c696c`; `master/definitions-masking.xml` blob `a387de584d331e5b1548800c2f3522998a03f772`, 3,090 bytes, `50a0769cbc0855fa91b3323876a3a8005cd59ffcb6521d7c13cdf936a4de3ac8`; `master/definitions-compositing.xml` blob `241e62163f25c9dce595939ecba56ca08a30b288`, 2,303 bytes, `c055f400e90888d9f107da62e470c750ba2dcd1d205bfa52f2a29d15f9ed844e`; `specs/animations/master/definitions.xml` blob `c8874f61a07373714b904bc932f5af5867f4f6de`, 7,488 bytes, `bcdd0fc20a13924d423243d6d2fecc28c265d23851c3f7d0ef762ebc917c3385`; `master/publish.xml` blob `d8837ed1f9b89af3fadbd096586fa5f82aa72d98`, 3,273 bytes, `ef196a8fc4646430801a15e943c212bc9f82371bb061e076c79c419df03301f1`; `master/struct.html` blob `67eb3c7ad8dca5065ee39203089fd1ccfa319d33`, 153,803 bytes, `d7082566754adf7ed741274d11960c55a587ce2d6b217a46c4921f3cc5c37a87`; `master/paths.html` blob `23ccb649af7dfa6b8216cd5c57fa0d310a11aa10`, 52,259 bytes, `cd818a1b7c5f82a1ab1709eb4020170e27ff5f01822f0e3e791663c42e109fbd`; `master/shapes.html` blob `cdcee5c60c1e6ecf867982426f69104fdb5db47e`, 37,360 bytes, `3005c3c951c8f000b651cb1fb4e781d909c245f976faf5542dedfa1ab709a03e`; `master/coords.html` blob `5230813c2cd2bee39f000c34336f299b9edd8f6b`, 149,848 bytes, `c91c5d0a7059db4d32952bbc4cba86a57714f99c31ab16dc244602977c10f5d4`; `master/types.html` blob `cd0abbdc8866cce4d3edd9e6f6ff669d70115a3e`, 140,699 bytes, `5c4fdd0cd9c6587948ccd41e6d51069d22bfaba03dc8d80bb57b306507f830d4`; `LICENSE.md` blob `6b9ee26976b2adc8accdc4a439f63bbd08694ff2`, 152 bytes, `6bb0235e84e19f807f271b54459eb494742a421e1c5c36a1de702c151ecb15f3`; `README.md` blob `debcd5c093ccec4c06fb74ad30bb6193c5dde612`, 999 bytes, `7bd3d0cec0a146d0331b98bf3a1778bd7cb907a99989f07e4a08e60971cd9710`; all thirteen rows agree between Lean's vendor seal and `Get-FileHash` |
| `w3c/csswg-drafts` @ `50337328484f7fcdd9ab6fe9ded6011815b1707e` (2026-10-10T22:53:52Z, "[css-sizing-4] Oversight (#14579)", the head of `main` at pin time), three files: `css-transforms-1/Overview.bs`, the source of CSS Transforms Module Level 1, and the root files `LICENSE.md` and `README.markdown` (the repository has no `README.md`); nothing else of the repository is stored (ruling SV-26) | 2026-10-11, slice S4c of `docs/SVG-PACKAGE-PLAN.md` | `gh api repos/w3c/csswg-drafts/commits/main` for the head, `gh api repos/w3c/csswg-drafts/git/trees/50337328…` for the root and `gh api repos/w3c/csswg-drafts/git/trees/16272a28…` for `css-transforms-1/` (neither truncated), and `gh api repos/w3c/csswg-drafts/contents/<path>?ref=50337328…` for each file's blob hash and size, then `curl.exe -sS -L --fail -o <file> https://raw.githubusercontent.com/w3c/csswg-drafts/50337328…/<path>`; no checkout or newline conversion | every file matches its upstream blob hash (`git hash-object --no-filters`) and byte size: `css-transforms-1/Overview.bs` blob `308749d07130451ef515a67282b6de7fa6d96443`, 73,009 bytes, SHA-256 `efa546b47442be30a773fd60b1a236b206720ea7942d88cfd539ebc6b32c95ee`; `LICENSE.md` blob `0f7c218c64691e29b618b5c1fed5cd9db7651727`, 167 bytes, `232da9c6c2b9f7e19e5d85cc7cf43760d80b7c4174406ac6404fa2c1b51d531b`; `README.markdown` blob `deec6c5f3156b82ca36a53907e4448bcf59627f2`, 771 bytes, `eec1a93fc349f0d61191f49c0cda9e5f30575f5743f3c77209d7cd7613ce912e`; all three rows agree between Lean's vendor seal and `Get-FileHash` |
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

The HTML Standard element projection `generated/html-standard-elements.tsv`
and the generated module `Whatwg/Html/Schema/Standard.lean` are produced by
`lake exe whatwg_htmlstandard --write` from the sealed
`vendor/whatwg-html-746f2ede/source` (SHA-256
`c985a14d1871fe862de386f5af92b5da84068267c6095ef0379c069ae85f9cde`, which
the gate refuses to deviate from): one row per element name of every
`<dl class="element">` block, with the block's line, the SHA-256 of the
bytes between its open tag and its `</dl>` as the span digest, and the
`Categories`, `Contexts`, `Content model` and `Content attributes` entries
as the standard's words with markup removed; likewise
`generated/html-standard-attributes.tsv`, one row per row of the standard's
attribute index (`attributes-1`) and event-handler index
(`ix-event-handlers`) with the row's span digest; and from those rows the
schema modules `Whatwg/Html/Schema/{Tags,Families,Attributes,ContentModel}.lean`
and `Whatwg/Html/Node/Combinators.lean` (`WhatwgGates/HtmlStandardEmit.lean`,
reading the authored `Whatwg/Html/Schema/Readings.lean`, whose readings of
the standard's prose sentences are each pinned to the digest of the block
they read, and reading each `Value` cell as a kind by the cell's leading
words and quoted items). `lake exe
whatwg_htmlstandard` fails on any byte of drift in any output. Cross-check at the
pin: a Python regular-expression pass found the same 179 attribute and 89
handler rows. Cross-check at the pin: a Python
regular-expression pass over the same file found the same 107 blocks and
the same 113 element names (`menu`'s block is spelled `<dl class=element>`).

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

SVG 2 (`vendor/w3c-svgwg-47e645ef/LICENSE.md`,
`6bb0235e84e19f807f271b54459eb494742a421e1c5c36a1de702c151ecb15f3`) is under the W3C
Document License: the file is a pointer of 152 bytes to that licence, and the
licence text is not vendored. Read on 2026-10-11 at
`https://www.w3.org/copyright/document-license-2023/`, the 2023 version permits
copying with a link to the original, the copyright notice and the document's
status. It permits a derived work only in software, in material that accompanies
software and in software documentation, with a notice that names the source by
title and address. The sealed files are retained unmodified. Each projection
and schema module generated from them at slice S2 carries that notice.

CSS Transforms 1 (`vendor/w3c-csswg-drafts-50337328/LICENSE.md`,
`232da9c6c2b9f7e19e5d85cc7cf43760d80b7c4174406ac6404fa2c1b51d531b`): the file is a
pointer of 167 bytes. It says that all documents in the repository are licensed by
contributors under the W3C Software and Document License, and it links
`https://www.w3.org/Consortium/Legal/copyright-software`. That is not the licence the
SVG 2 pointer names, and the licence text is not vendored. Read on 2026-10-11 at that
address, the page is the Software and Document license, 2023 version. It permits
copying, modifying and distributing the work for any purpose and without fee, on three
conditions: the full text of the notice goes where a user of the copy or of the derived
work can view it; any existing disclaimer, notice or terms go with it, or else W3C's
short notice; and a derived work says what it changed, with a statement that it
includes material copied or derived from the W3C document. The sealed files are
retained unmodified. The grammar module derived from the pin at slice S4c carries that
statement.

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

## Lake dependency objects (cross-checked 2026-10-01)

These are Lake-managed Git dependencies, outside the `vendor/` seal.
`SPEC-MANIFEST.md` owns their current roles and pins. The configured URLs are
`https://github.com/pure-algebra/lean4-hash`, `lean4-effects`, and
`lean4-typescript` under the same owner. Local clones use matching SSH remotes.
Ruling R-V3(b) moved the three pins to lean4-effect4's at `0f16828a`; they were
fetched on 2026-10-01 by `lake update effects typescript hash` with the exact
`[[require]]` revisions in `lakefile.toml`. The same day `git ls-remote`
resolved `refs/tags/v0.8.0^{}` of lean4-effects to the effects pin and
`refs/heads/main` of lean4-hash to the hash pin, and found the typescript pin
only as `refs/heads/codex/typed-source-carrier`: lean4-typescript has no
`v0.6.0` tag (its latest tag, `v0.5.0`, is `71bad1252ee8a1b243ed283320ededcb7d0a93c4`),
and `0.6.0` is the `version` its `lakefile.toml` declares at the pin. The
previous pins (hash `0168306`, Apache-2.0; effects `c28833b`, `v0.5.0`;
typescript `fcbc05a`, `v0.2.0`), cross-checked 2026-09-05, are in this file's
history.

Ruling R-S10 added a fourth requirement on 2026-10-11, at the commit
lean4-effect4 pins: `aesop` from
`https://github.com/leanprover-community/aesop` at
`3448c0bcc5ce01b2d1546e483ec3620e32df3d0e`. It brings `batteries` from
`https://github.com/leanprover-community/batteries` at
`4488d40d070b9700d4d5a6aa342f0d40c31b2a2d`, the commit of its tag `v4.33.0`,
as an inherited dependency. Both were fetched that day by `lake update aesop`,
which left the three earlier pins unchanged, and `git rev-parse HEAD` in each
package directory answers the pinned commit. Both are under the Apache License
2.0. Neither is vendored: `lake-manifest.json` holds the two commits.

| Package | Commit / locally verified tag | Committed tree | License at this commit |
| --- | --- | --- | --- |
| `hash` | `c906b15dc3e94ebac0c10056270fbb345a1d2b6e`; no tag (`main`) | `15e4bde04887faf982eeca111f50be08eab86e1d` | MIT; `LICENSE` blob `1e7fe3f72d2c0baf370f7375bca9802594a9a6ef`, 1069 bytes, SHA-256 `c51d370d20b9c1b2906d5583a1e9c519eaaf5d2033010eecfc7788e399d8eecf` |
| `effects` | `a4ee7a14248ee5976039b73039319efa87834986`; `v0.8.0` | `2b705611e5efe66bbd34134b2f6c092b4d9895dd` | MIT; same committed `LICENSE` blob and digest as the hash row |
| `typescript` | `6afc9b841603796c16b266c0b8b92ded37a9445c`; no tag (lakefile version 0.6.0) | `5aa05b3fb81a7a4d56d2b2dcaac5117fde746ecb` | MIT; same committed `LICENSE` blob and digest as the hash row |

For each `.lake/packages/<name>`, `git rev-parse HEAD` and
`git rev-parse HEAD^{tree}` match these rows; `HEAD` agrees with both
`lakefile.toml` and `lake-manifest.json`. `git tag --points-at HEAD` names
`v0.8.0` for effects and no tag for the other two. `git ls-tree HEAD LICENSE
lean-toolchain lake-manifest.json` and `git cat-file blob HEAD:LICENSE`
identify the committed bytes; the license SHA-256 values above were computed
over those raw object bytes with the system implementation. All three
committed toolchain blobs are `a8afa7d1b02d96f0671eba854a8dc4b416beb473`, 25
bytes, naming Lean 4.33.1 and matching this repository's toolchain SHA-256.
All three Git statuses are clean and their package manifests list no
transitive packages (`"packages": []`). The hash pin differs from `0168306` in
`LICENSE` (Apache-2.0 to MIT), `README.md`, `docs/PROVENANCE.md` and the
lakefile's `license` field, and in no Lean source; the vendor seal gate
passed through it and its `--write` mode regenerated
`generated/vendor-manifest.tsv` byte-identically (SHA-256
`56479a5223c6fa9363bb1f2e81a330351f22ffef2899560c34de516d6481ebbb` before and
after), which is the cutover proof.

This is a local object/lockfile cross-check with a same-day network fetch,
with no second SHA-256 implementation claimed. Package checkout attributes can
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
