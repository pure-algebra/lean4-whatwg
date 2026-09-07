# Web IDL promise and exception census contract (P8-C1)

Status: FROZEN / RED, promise census breaker seat, 2026-09-06, based on
`03abfc579883d1c79492b0e4d1e933f71a830e68`.

This packet freezes `WhatwgTest/Audit/WebIdl/CensusContract.lean` before the
Web IDL census exists. Its rulings are R-P1 through R-P7 of `COORDINATION.md`;
its source evidence is `docs/research/2026-09-06-webidl-promise-census-survey.md`,
every number of which was independently recomputed here from the sealed bytes.
The builder may repair elaboration but may not weaken, delete or replace a
frozen row, count, digest or refusal.

Read `test/contracts/census-profile-identity.contract.md` first: it freezes the
byte-identity the same refactor must preserve for Streams and Infra.

## Claim boundary

This is a tooling contract. A census row is a byte span of the pinned source
with a joined disposition. Nothing here grants a Web IDL semantic claim, an
observation mask, a coverage state, a denominator the numerator may quote, a
host observation, or any statement about `Whatwg.WebIdl`. `docs/SPEC-COVERAGE.md`
owns the metric and no numerator exists for this standard yet.

## 1. The pin

| Item | Value |
| --- | --- |
| Source | `vendor/whatwg-webidl-a652053f/index.bs` |
| Upstream | `whatwg/webidl` at `a652053f1e74e4aaf647528deb174012ed6c909f`, Review Draft, March 2026 |
| Size | 695,845 bytes |
| SHA-256 | `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83` |

Recomputed in this packet with `[IO.File]::ReadAllBytes` and .NET
`System.Security.Cryptography.SHA256`; it agrees with `SPEC-MANIFEST.md`,
`docs/PROVENANCE.md` and the survey. The generator refuses any other bytes
(section 6). Offsets below are 0-based byte offsets; ends are exclusive; no
line number is cited anywhere.

## 2. The section scope

`census/webidl/sections.tsv` names exactly these five heading ids. A section's
extent runs from its heading tag to the next line-opening heading of the same
or higher level. Together they hold 54,343 bytes, 7.81 % of the file.

| id | level | start | end | bytes | SHA-256 of `[start, end)` |
| --- | --- | --- | --- | --- | --- |
| `idl-exceptions` | h3 | 193957 | 217551 | 23594 | `b8c34eecb372c4cc76c476b3d1806fdd523c33112fc05c86c11bd6f59676ac0d` |
| `idl-promise` | h4 | 252146 | 252819 | 673 | `c0f7dcec8c01af9f09faaf23c6d9aa8cb4fce16e55f788cc54018c63175369c7` |
| `js-promise` | h4 | 346519 | 364590 | 18071 | `784465713cb51539e5dc012d985c3129b10d90b10d8f213e245dbdff0f81f996` |
| `js-exceptions` | h3 | 663547 | 671837 | 8290 | `0219395d3a2e97187ce2e6dbc62b8b81bc0527ae2b2cf1ae678f3cfb42fefc53` |
| `idl-DOMException` | h3 | 673398 | 677113 | 3715 | `55a0c66acdc2eab5dc8cba0ebb6fc982d029350c0f2bf80ed89bcb284e07e515` |

Their nine descendant headings, which the disposition walk also reaches:

| id | level | start | end | bytes | SHA-256 of `[start, end)` |
| --- | --- | --- | --- | --- | --- |
| `idl-DOMException-error-names` | h4 | 198581 | 211138 | 12557 | `2baf51f7fd3f509a0e1b8ad3a1bb6be1353045df11e67782f9eb32a619771478` |
| `idl-DOMException-derived-interfaces` | h4 | 211138 | 213283 | 2145 | `bea024c7146f0d2044eff5f77b8ec8f5d619e595e9d836ef0127ca0ccfda7c13` |
| `idl-DOMException-derived-predefineds` | h4 | 213283 | 217551 | 4268 | `bcf40e666435f4aeb3bba2546ebcb008c214e6d820bbb1566b9ad534365a1f6f` |
| `js-promise-manipulation` | **h5** | 347497 | 356716 | 9219 | `ae739fc5a23e72c2cbc1fd8fc0545cb186452b8db633a5e1fe514b3414281abb` |
| `js-promise-examples` | **h5** | 356716 | 364590 | 7874 | `691d8bdefbb9363b25cc578e098fbfd7c26fd353cfc951490f147174675030d5` |
| `js-DOMException-specialness` | h4 | 663610 | 664320 | 710 | `923178c810fcff090e9c7d11a8d668aaca92d393d486535500a65ee20efa6357` |
| `js-exception-objects` | h4 | 664320 | 664612 | 292 | `ef1143597f76f45d3127c900bb225642cae5d637376e7c523f791c407a5c87b9` |
| `js-creating-throwing-exceptions` | h4 | 664612 | 669093 | 4481 | `fcb3f587bf2a39d1cdc58ceea453d0a75550e7d6dc304bd72b76f239daa4a19c` |
| `js-handling-exceptions` | h4 | 669093 | 671837 | 2744 | `6a96769d1fa4a7af507679f208a776c5465a2af0e1a73f4a0c29ebdaeae27491` |

Two of the nine are `<h5>`, which is why `headingLevels` is `(2, 5)` for this
standard. The section scope is part of the frozen contract, not a convenience:
widening it brings in 45 more algorithm blocks and roughly 293 more
definitions and makes the span rules of section 4 load-bearing on text nobody
has read.

## 3. The source profile

Under R-P1 the standard is a Bikeshed profile:

| Switch | Value | Why |
| --- | --- | --- |
| `algorithmRows` | `true` | 26 blocks in scope |
| `definitionRows` | `true` | 89 `<dfn>` and 3 heading-borne definitions in scope |
| `idlRows` | `true` | two IDL blocks in scope |
| `slotRows` | `false` | R-P4. All 47 slot rows the scanner would emit anchor at an incidental use site, and 38 of them are JavaScript-binding object-model internals. `[[Promise]]`, `[[Resolve]]`, `[[Reject]]` and `[[PromiseIsHandled]]` become `Whatwg.Ecma262` dependency rows instead. |
| `requirementMarker` | `none` | R-P4. `scanRequirements` is hard-wired to `<div algorithm="ReadableStreamPipeTo">`; with `none` it emits no rows and the six derived-interface bullets come in through `rules.tsv`. |
| `sectionScope` | `true` | the five ids of section 2 |
| `headingLevels` | `(2, 5)` | `js-promise-manipulation` and `js-promise-examples` are `<h5>`; without them the eleven promise operations and the seven worked examples would take the same disposition |
| `idlOpeners` | `#[("<pre class=\"idl\">", "</pre>"), ("<pre class=idl>", "</pre>")]` | the file has **zero** `<xmp class="idl">`; it writes 11 `<pre class="idl">` and 1 `<pre class=idl>` |

`idlOpeners` is one field more than R-P1's list names. It is unavoidable: the
Streams opener does not occur in this source at all, and the two in-scope IDL
blocks use two different spellings of the same class attribute. It is recorded
here as a deliberate, documented extension of R-P1.

Scope filtering is a predicate the scanners consult, not a filter applied to
rows afterwards: the ten out-of-scope `<pre class="idl">` blocks must never be
parsed, because an error raised in one of them would abort a run for reasons
outside this lane.

## 4. Row taxonomy, id scheme and span rules

Kinds are the existing six of `docs/SPEC-COVERAGE.md`; R-P2's seven new kinds
belong to ECMA-262 and are unused here. Row ids keep the existing
`<kind>.<name>` shape and the existing `Gates.Census.kebab` and
`Gates.Census.flattenName` naming ladders.

### 4.1 `op` rows from algorithm blocks — 26 rows

One row per `<div>` in scope whose tag carries an `algorithm` attribute
anywhere, keyed on the attribute and not on the byte prefix `<div algorithm`.
Recomputed at this pin: the file has 156 tags under the prefix rule and 201
under the attribute rule, and 26 in scope under the attribute rule against 25
under the prefix rule; the block the prefix rule drops is
`<div id="js-to-promise" algorithm="convert a JavaScript value to promise">`.
The span is the whole `<div>` element. The name follows the existing ladder:
the opener's `id`, else the block's first `<dfn>` (its `id`, else the first
`lt` alternative, else its text, the last two prefixed by the flattened `for`),
else the opener's `algorithm` attribute.

### 4.2 Definition rows — 13 `op` and 39 `type`, 52 rows

A definition is a `<dfn>` in scope, or a line-opening heading in scope whose
tag carries a bare Bikeshed definition marker. Three headings in scope carry
one and no other heading in Streams or Infra carries any:
`idl-promise` (`interface`), `js-exception-objects` (`dfn`) and
`idl-DOMException` (`interface`).

Kind comes from the Bikeshed dfn type on the tag:

| Bikeshed dfn type | Row |
| --- | --- |
| `const`, `attribute`, `constructor` | no row: the IDL-block statement of section 4.3 already carries it |
| `exception`, `interface`, `dictionary`, `enum`, `typedef` | kind `type` |
| anything else, including a bare `dfn` and a plain `export` | kind `op` |

Recomputed at this pin: 89 `<dfn>` open in scope, 12 of them inside an in-scope
algorithm block (the eleven promise operations and the `QuotaExceededError`
constructor) and 77 standalone. Of the 77: 22 `const`, 5 `attribute` and 1
`constructor` are dropped, 28 in all; 37 are `exception`; and 12 carry no
type-bearing attribute. The three heading-borne definitions split 2 `type`
(both `interface`) and 1 `op` (the bare `dfn`). That is 37 + 2 = 39 `type`
rows and 12 + 1 = 13 definition `op` rows, 52 in all.
The id follows the existing `scanDefinitions` ladder unchanged: the `id`
attribute, else the first `lt` alternative, else the text, the last two
prefixed by the kebab of the first `for` alternative.

**The span ladder, first match wins.** Every step is vacuous on the Infra
source, which is the only standard that uses `definitionRows` today; the
recomputed evidence is in
`test/contracts/census-profile-identity.contract.md`.

1. the innermost enclosing algorithm block;
2. the innermost enclosing `<tr>` … `</tr>` (Infra has 0 `<tr>`);
3. the Bikeshed markdown list-item line containing the definition, when the
   line's first non-space bytes are `*`, `-` or `1.` followed by a space, with
   trailing ASCII whitespace trimmed (0 of Infra's 197 `<dfn>` sit on such a
   line);
4. otherwise the existing rule: the span starts at the later of the last
   `<p>`, `<p `, `<dt>` or `<li>` opener before the definition and the start of
   the definition's own blank-line chunk (0 of Infra's 177 non-block `<dfn>`
   are affected by the clamp), and ends at the next `"\n\n"` or at the file
   size; and when the span ends in a colon after trailing whitespace and an
   optional `</p>`, it extends through
   4a. the Bikeshed markdown list that begins at the first non-whitespace byte
   after the chunk, when one does (of Infra's 23 colon-branch definitions, 21
   are followed immediately by `<ol` and 2 by `<p`, never by a markdown list),
   else
   4b. the matching `</ol>` of the next `<ol` opener, unchanged.

For a heading-borne definition the span is the heading element itself.

Three pairs of co-defined terms share one paragraph span, and that is
intentional rather than a defect: `op.dfn-create-exception` with
`op.dfn-throw`, `op.quota-exceeded-error-quota` with
`op.quota-exceeded-error-requested`, and `op.dom-exception-name` with
`op.dom-exception-message`. No other two rows share a span, the longest row
span is 2,333 bytes, and every one of the 121 rows finds a unique anchor
within 64 bytes.

### 4.3 `idl` rows — 37 rows

One row per statement of the two in-scope IDL blocks,
`<pre class=idl>` at 213511–213861 (SHA-256
`c261d7cb63c4c311acc3ef1d020dc30d041b64599fa9a3454510fca85419b669`) and
`<pre class="idl">` at 673570–675052 (SHA-256
`8c1843c9c476d21a743b43d59dae846a6e877f22dd4413ebe39648dd34d8d494`). The
existing statement machine needs three repairs, each forced by one of the two
blocks:

- a trailing `//…` comment is stripped from each line before the `;`/`{`
  terminator test and before the span end is taken. Without it the
  `DOMException` header line, which ends `interface DOMException { // but see
  below note…`, never terminates and all 30 statements of the block are
  silently counted as skipped.
- the header match accepts the five-word form `interface <Name> : <Base> {`.
  Without it `[Exposed=*, Serializable] interface QuotaExceededError :
  DOMException {` aborts the run with `unrecognised IDL header`.
- a `const` member takes `trailingIdent` of the part before ` = `. Without it
  the 25 legacy constants are named `1` … `25`.

The 37 statements are 30 from `DOMException` (the interface header, the
constructor, three attributes, 25 constants) and 7 from `QuotaExceededError`
(the interface header, the constructor, two attributes) plus
`QuotaExceededErrorOptions` (the dictionary header and two members). The span
of a statement runs from the first non-whitespace byte of its first line to
the last non-whitespace byte of its last line, comment excluded.

### 4.4 `rule` rows — 6 rows

`idl-DOMException-derived-interfaces` states six `must`/`should` constraints as
Bikeshed markdown bullets, with no `<dfn>`, no algorithm block and no IDL. They
enter through `census/webidl/rules.tsv`. Under R-P4 that file gains an optional
third field, the end locator: with two fields the span runs from the unique
start locator to the next blank line, as today; with three, it runs to the
first occurrence of the end locator at or after the start locator, with
trailing ASCII whitespace trimmed. Without the end locator all six bullets sit
in one blank-line paragraph and would receive six nested spans ending at the
same offset.

The disagreement recorded: the survey's §2.3 expected-count table puts these
six under kind `requirement`. They are `rule` rows — its §2.3(f) and §4.2 say
so, and `Gates.Census.scanRules` emits `rule`. Their **disposition** is
`requirement`.

### 4.5 What is not a row

`slot` rows are off (R-P4). Example and note containers are not rows; the
seven `js-promise-examples` algorithm blocks are rows but `evidenceOnly`. The
`<table id="error-names">` at 200422–211136 is layout, not a definition
carrier: each of its 32 name cells and 22 legacy-code cells carries its own
`<dfn>`.

## 5. Expected row counts

| kind | rows |
| --- | --- |
| `idl` | 37 |
| `op` | 39 |
| `requirement` | 0 |
| `rule` | 6 |
| `slot` | 0 |
| `type` | 39 |
| `builtin`, `hook`, `property`, `record`, `field`, `term`, `clause` | 0 |
| **total** | **121** |

Dispositions, following R-P4 and the survey's §4 as instantiated on this row
set:

| Section | kind | disposition | rows |
| --- | --- | --- | --- |
| `idl-exceptions` (lead) | `*` | `owned` | 9 |
| `idl-DOMException-error-names` | `*` | `owned` | 33 |
| `idl-DOMException-derived-interfaces` | `*` | `requirement` | 6 |
| `idl-DOMException-derived-predefineds` | `*` | `hostOnly` | 12 |
| `idl-promise` | `*` | `hostOnly` | 2 |
| `js-promise` (lead) | `*` | `hostOnly` | 1 |
| `js-promise-manipulation` | `*` | `owned` | 11 |
| `js-promise-examples` | `*` | `evidenceOnly` | 8 |
| `js-exception-objects` | `*` | `hostOnly` | 1 |
| `js-creating-throwing-exceptions` | `*` | `owned` | 4 |
| `js-handling-exceptions` | `*` | `evidenceOnly` | 1 |
| `idl-DOMException` | `op` | `owned` | 2 |
| `idl-DOMException` | `idl` | `hostOnly` | 30 |
| `idl-DOMException` | `type` | `hostOnly` | 1 |

| disposition | rows |
| --- | --- |
| `owned` | 59 |
| `hostOnly` | 47 |
| `evidenceOnly` | 9 |
| `requirement` | 6 |
| `foreignBoundary`, `refused`, `targetOnly` | 0 |
| **denominator** | **112** |

Three disagreements with the survey's §4.1 are recorded here rather than
silently repaired. The survey gives `idl-DOMException-error-names` an `idl`
line dispositioned `hostOnly`; under this taxonomy the 25 legacy constants are
`idl` rows of `idl-DOMException`, so that section has no `idl` row and such a
line would fail generation as an entry that matches no row. The survey gives
`js-DOMException-specialness` a `hostOnly` line; that section produces no row
at all, so it gets no line. The survey recommends `owned` for `idl-promise`;
R-P4 rules `hostOnly` and this packet follows the ruling.

## 6. The command line

```text
lake exe census --standard webidl            check
lake exe census --standard webidl --write    regenerate
lake exe census --standard webidl --report   refused: no numerator exists
```

`--report` exits 2 with the existing "no coverage numerator exists" message,
as `--standard infra` does today. `check` regenerates both projections in
memory and compares bytes; it verifies, independently of the scanners, that
every recorded anchor occurs exactly once in the pinned bytes at its recorded
span start and that every recorded span digest recomputes. It refuses, with a
nonzero exit and a `FAIL` line, when:

- `vendor/whatwg-webidl-a652053f/index.bs` is missing, or has any SHA-256 other
  than the pin;
- any authored input under `census/webidl/` is missing;
- any scanner meets a source shape it does not handle. A shape is never
  skipped: no silent statement counter, no dropped block, no default
  disposition. The one exception the existing generator keeps is the reported
  count of IDL statements outside the row vocabulary, which must be **0** for
  this standard;
- a row id is duplicated, a span is empty or reversed or outside the file, an
  anchor is not unique within the admitted ladder, or an anchor or span splits
  a UTF-8 character;
- a row lands outside every section named in `sections.tsv`;
- either projection differs from a fresh regeneration by one byte.

Two CI steps are added, one per new standard (R-P7).

## 7. Authored inputs

All under `census/webidl/`. Every one is validated in both directions: an
entry that reaches no row fails generation, and a row that no entry reaches
fails generation. The generator invents no default.

| File | Fields | Validation |
| --- | --- | --- |
| `sections.tsv` | `<heading id>` | Exactly the five ids of section 2. A listed id that is not a line-opening heading with that exact `id` in the pinned bytes fails; an id whose section governs no row fails; a row outside every listed section fails. Ids are case-exact: `idl-DOMException`, `js-DOMException-specialness`. |
| `dispositions.tsv` | `<section id>` TAB `<kind or `*`>` TAB `<disposition>` | Unchanged format. Duplicate `(section, kind)` fails; unknown kind or disposition fails; empty section id fails; an entry that no row uses fails. |
| `overrides.tsv` | `<row id>` TAB `<disposition>` TAB `<reason>` | Unchanged format. Duplicate row id fails; empty field fails; an override that no row uses fails. |
| `rules.tsv` | `<kebab name>` TAB `<start locator>` [TAB `<end locator>`] | Two or three fields; any other count fails. Empty field fails, including an empty third field. A start locator that does not occur exactly once fails. An end locator with no occurrence at or after the start locator fails; it is never widened to the blank-line rule. |
| `dependencies.tsv` | the URL lane's format (`census/url/dependencies.tsv`) | Every row id named must exist; every dependency identity must resolve to a row of this census, to a row of another census by that census's row id, or to an `ext.` identity declared in `externals.tsv`; a duplicate or self dependency fails. |
| `externals.tsv` | the URL lane's format (`census/url/externals.tsv`) | Every identity is namespaced `ext.`; a duplicate identity fails; an identity no dependency uses fails. |

Under R-P6 the escaping references split four ways: the `Whatwg.Ecma262`
boundary (`[$Call$]`, `[$Construct$]`, `[$CreateBuiltinFunction$]`,
`[$NewPromiseCapability$]`, `[$PerformPromiseThen$]`, `{{%Promise%}}`,
`{{%Promise.prototype.then%}}`, `{{%Error.prototype%}}`, `[=PromiseCapability=]`,
`[=abrupt completions=]`, `[=ECMAScript/error objects=]`, and the internal slots
`[[Promise]]`, `[[Resolve]]`, `[[Reject]]`, `[[PromiseIsHandled]]`) as
dependency rows; Infra terms (`[=list=]`, `[=list/Append=]`,
`[=list/For each=]`, `[=list/size=]`, `[=strings=]`, `[=implementation-defined=]`)
as dependency rows onto `generated/infra-census.tsv` by Infra row id;
out-of-scope Web IDL sections as `hostOnly` dependency rows naming the target
heading id; and HTML, DOM and realm machinery as externals.

## 8. Frozen rows

The complete census. `anchor` is the byte length of the anchor
`Gates.Census.chooseAnchorLength` selects for the span; the anchor itself is
the first that many bytes of the span, so the battery checks the projection's
anchor field against the pinned bytes rather than against a transcription.
Every digest is the SHA-256 of `[start, end)` of the pinned bytes, recomputed
in this packet with .NET SHA-256 and again by the battery with
`Gates.Sha256.hexDigest`.

| kind | id | start | end | anchor | SHA-256 of `[start, end)` |
| --- | --- | --- | --- | --- | --- |
| `idl` | `idl.dom-exception` | 673588 | 673639 | 24 | `4e9332bb7e47cf957a9ff8fcfeb1fdd42d6a8a93b2b9227765d29e6c1f7f2e9e` |
| `idl` | `idl.domexception-abort-err` | 674776 | 674812 | 24 | `180a37fcd9ce24e6d0f515e38b8b3987ceed6d97e26869a3cb2212c1ac75f172` |
| `idl` | `idl.domexception-code` | 673849 | 673888 | 48 | `19315c8e4e4c657557461099d25f86f0a7ec9650d040b40d3b4581ae36d2739d` |
| `idl` | `idl.domexception-constructor` | 673689 | 673769 | 64 | `49d172735ba63a076fc928ac085343af36cdd1a6ac2a52c054de2d816e5aa8eb` |
| `idl` | `idl.domexception-data-clone-err` | 675001 | 675042 | 24 | `740e593d32f8901e25cdc3e6d978bb67272c65de1868a0396cd341c65db93872` |
| `idl` | `idl.domexception-domstring-size-err` | 673935 | 673979 | 24 | `98ccc4904605695d859a7cc591cb2bad479187313056884a0920a41b534f56ea` |
| `idl` | `idl.domexception-hierarchy-request-err` | 673982 | 674029 | 24 | `e2cbabfefeeafbe86b317692ed8687af27c48dd8844c32771a9d1d1d224199db` |
| `idl` | `idl.domexception-index-size-err` | 673892 | 673932 | 24 | `133bbbb3c421027af025736b6212d27076227710f988c9c5d7b0546d1ae9d32b` |
| `idl` | `idl.domexception-inuse-attribute-err` | 674321 | 674367 | 24 | `fb243755c7c3c3fcc11d888843c2256e30af6885596d46d4f2c3e79ccd655c19` |
| `idl` | `idl.domexception-invalid-access-err` | 674554 | 674599 | 32 | `21164016f5e04ec857f2b3b486fb23ef06b86fd86f90e612af1025673857f8d2` |
| `idl` | `idl.domexception-invalid-character-err` | 674079 | 674126 | 32 | `cea85d0cb5514da5e97e857c053cec173ec3aa9e50ebd033617f432700045b5d` |
| `idl` | `idl.domexception-invalid-modification-err` | 674457 | 674508 | 32 | `af7f4f553f8fce7279534ed78e365a89cbf2affecfd1e9ac1ba83b40e7379007` |
| `idl` | `idl.domexception-invalid-node-type-err` | 674950 | 674998 | 32 | `091646b6151b0dd2470323b442186140a17f2d809a388c805f937b5e97fa0686` |
| `idl` | `idl.domexception-invalid-state-err` | 674370 | 674414 | 32 | `cc06444ebabf8d34bf3c917f510cc92646b4e729bf2d8106f8140fb096184b3e` |
| `idl` | `idl.domexception-message` | 673809 | 673846 | 32 | `06bc68820b3b8af473c2c0d0bfe9328441f524ca261be6a85bebadece9f1de9b` |
| `idl` | `idl.domexception-name` | 673772 | 673806 | 48 | `cdf794c2d44a1dfe2a6821c33397454e0bb260c41490873433e4e40246e2d1b7` |
| `idl` | `idl.domexception-namespace-err` | 674511 | 674551 | 24 | `27e146b180ea0d8687b3d7516cd89eae8c844063d069f984b0a495f5ce2e4edc` |
| `idl` | `idl.domexception-network-err` | 674735 | 674773 | 24 | `e5e19c055273f8b6d4c1ba8558477b13d92ea22e8f2f567dce64a66ba9fd89b7` |
| `idl` | `idl.domexception-no-data-allowed-err` | 674129 | 674174 | 32 | `48bc28c5b781e86a43ec6ff8c184eb774a55a49bf73634967ab293c84ef4dbc1` |
| `idl` | `idl.domexception-no-modification-allowed-err` | 674177 | 674230 | 32 | `d6ff442ef60633d8420cb074a11bdc30c49b4adfe1fd1def8786699e276d14c4` |
| `idl` | `idl.domexception-not-found-err` | 674233 | 674272 | 32 | `be946dd8e85954ab10fde83cb01b079bd50dbf48ebc10c4c2c320f34e1e43067` |
| `idl` | `idl.domexception-not-supported-err` | 674275 | 674318 | 32 | `cc6b8d89ddb057b9c1500629748ba16769af4b2e2085738e211295611bd33d3b` |
| `idl` | `idl.domexception-quota-exceeded-err` | 674861 | 674906 | 24 | `b42e6d43c7b2f20d051499fb83849d71a4f1e6af3a6d1497b97490ea2aea5fcc` |
| `idl` | `idl.domexception-security-err` | 674693 | 674732 | 24 | `60d9210cc3fcd70c71edbe17c0a632b3bf7d088e42b5a394b94645bf14d4387d` |
| `idl` | `idl.domexception-syntax-err` | 674417 | 674454 | 24 | `a5c8a5c025e197f311f9c7f19d6b43b4427baba7aeb43ab4a04309e49ebcd0be` |
| `idl` | `idl.domexception-timeout-err` | 674909 | 674947 | 24 | `40d0c8ec21f4420c2e7c30db23f84fb313e811fc2f9660e72a72f8d4d124a2fa` |
| `idl` | `idl.domexception-type-mismatch-err` | 674646 | 674690 | 24 | `b0895a121349c365285cc3d9633d4b9baa561c696701506099f7c349fdd347f1` |
| `idl` | `idl.domexception-url-mismatch-err` | 674815 | 674858 | 24 | `b6cd3a45dbe17c39b6af91cea88620bcc411d566b180e54908047b7c5f1a42fb` |
| `idl` | `idl.domexception-validation-err` | 674602 | 674643 | 24 | `2f83b8cef33249cc3ba05e3e6a58abeb5fe440f63fbbef96686d5b84b4202ef0` |
| `idl` | `idl.domexception-wrong-document-err` | 674032 | 674076 | 24 | `a7ef7c9458a97fcee6e6787218799723e9f808d1fefff01db29411702f90e5e2` |
| `idl` | `idl.quota-exceeded-error` | 213527 | 213598 | 24 | `e27a117ef91d587eb017ada33f4c1a2e200be5272395d9890455355b90fbecd2` |
| `idl` | `idl.quota-exceeded-error-options` | 213777 | 213815 | 24 | `b641b4d494d106b025a3cd95eeb543a1d233588e5b7413645cf9e8af30d9c27d` |
| `idl` | `idl.quotaexceedederror-constructor` | 213601 | 213695 | 64 | `b09449cf5e0157f7876a617e91d67ca96e75c66d8cf6dd662c6c0d478d304ee2` |
| `idl` | `idl.quotaexceedederror-quota` | 213699 | 213732 | 32 | `971545ce535cf3c8a6dc69a5f292f0f49fb1030218fb0d1d7f7d2e61afaa2f2d` |
| `idl` | `idl.quotaexceedederror-requested` | 213735 | 213772 | 32 | `e590defe8544439fb751e5a92b0c8beedba417e7dbc1767163140deafb4c9911` |
| `idl` | `idl.quotaexceedederroroptions-quota` | 213818 | 213831 | 24 | `e5cada2860e8ecd3720a5c003e2607f96b89e8ccd1f4dc19c077c4bac266fef8` |
| `idl` | `idl.quotaexceedederroroptions-requested` | 213834 | 213851 | 24 | `c5a302d1c3172aacff4d8697b72f642c3849d26563eff76ce7ff27c970ffb743` |
| `op` | `op.a-new-promise` | 347604 | 347946 | 48 | `a9c212f9448d6cfdaf262e33f33ed5104392aaec738b6e3ae22b285edc3751b3` |
| `op` | `op.a-promise-rejected-with` | 348633 | 349214 | 64 | `3f6d84e5da374f56e56aebba956939b54dbefb219a67137a37128ecce58f20f8` |
| `op` | `op.a-promise-resolved-with` | 347948 | 348631 | 64 | `a5b86f19962066ef9844df3f2ee2494cb78c74bae6cf6690cc8ee1b6e0b60015` |
| `op` | `op.add-bookmark` | 362329 | 363490 | 24 | `c7999583a7b35262fcd27f7b4139b94ae17fd9ab73bdbed47131d590e3c4614c` |
| `op` | `op.add-delay` | 359201 | 360103 | 24 | `c41832d6488f46c5e6e135f0a2118c1fef90c39180900ffff10d3898fc88e182` |
| `op` | `op.an-exception-was-thrown` | 669437 | 669665 | 24 | `a705b8c63991bc538c2c97e6aa1a5ef66360e8e37f5e9a6bb1dc44544859efa6` |
| `op` | `op.batch-request` | 364131 | 364580 | 24 | `13713a763dcfd6681cbac28d539dcbc0c003751446261d83c3b97f5f48d50482` |
| `op` | `op.delay` | 357180 | 357688 | 24 | `947b495ff64d4df797af63cc0252de4e696f7289b059114ae173f642737b9392` |
| `op` | `op.dfn-create-exception` | 195867 | 196437 | 24 | `f532faf75bb38516470dfa36637d8c495ff494a8188ae96a5e55a3aa8181e041` |
| `op` | `op.dfn-error-names-table` | 198659 | 198938 | 24 | `41f19f926ee8be134bc10020ccd4f95b505991f165245143bb965fc9f44775bd` |
| `op` | `op.dfn-exception` | 193998 | 194431 | 24 | `a727aa273727aa630983e9f4f49a017ca2c9c421bdfacd3bea03a45fe964a980` |
| `op` | `op.dfn-perform-steps-once-promise-is-settled` | 350075 | 352408 | 48 | `dd0e08ae5b8739280837b31e10f2ace6f1a7f9b20034124d7c748d450aaab383` |
| `op` | `op.dfn-promise-type` | 252271 | 252705 | 24 | `517973beeca92afcddbb3ebc38522fd1f95c964706b3e0183dcbaa6e4835bfb5` |
| `op` | `op.dfn-simple-exception` | 194433 | 194721 | 24 | `23597069802c1cb8d6b73ddb94125c7fed97b65815cf8e7bf7b3cdd69e1041d3` |
| `op` | `op.dfn-throw` | 195867 | 196437 | 24 | `f532faf75bb38516470dfa36637d8c495ff494a8188ae96a5e55a3aa8181e041` |
| `op` | `op.dom-exception-message` | 675214 | 675370 | 24 | `5d36b1e822347566aae87eafaa4d0125413f13f8aaab8f2c05c28c163fb71de3` |
| `op` | `op.dom-exception-name` | 675214 | 675370 | 24 | `5d36b1e822347566aae87eafaa4d0125413f13f8aaab8f2c05c28c163fb71de3` |
| `op` | `op.environment-create` | 360876 | 361777 | 32 | `931feca212ae287d25ad348a8da9ff9c314c20cb6a3810963ea83bb0718e11e2` |
| `op` | `op.environment-ready` | 360719 | 360874 | 32 | `b36bfad03aec0c8fddaa59eb6567d025b7a049e88b727b19fa8b86eacf451fa5` |
| `op` | `op.environment-ready-promise` | 360535 | 360717 | 24 | `8f86f770f6d88675276f175fb5522403170a92290f8ee5449574ef36403a35d8` |
| `op` | `op.js-exception-objects` | 664320 | 664406 | 24 | `036d4e370d6f4dc68f7266889421e196ca709b894fc8ae9cfd293ae9eac124e4` |
| `op` | `op.js-to-promise` | 346692 | 347209 | 24 | `c42584ffe744b7ecb64aee1920b52123a79024aa81ad1ed268f34351cc87158b` |
| `op` | `op.mark-a-promise-as-handled` | 356060 | 356713 | 48 | `644263e9155cf45d31167e53346f9d0e2431aedde301b440dbc92d9021b618bc` |
| `op` | `op.quota-exceeded-error-deserialization-steps` | 216862 | 217258 | 48 | `b595923cd7a3d7ea789812018fe48c8ba464eb3109215a72a4adbf632a691a7a` |
| `op` | `op.quota-exceeded-error-quota` | 214367 | 214571 | 24 | `99018d0b0b70c2b17fc53c8caa1f7d47ee092af97989b516aab48f2aed681b3d` |
| `op` | `op.quota-exceeded-error-requested` | 214367 | 214571 | 24 | `99018d0b0b70c2b17fc53c8caa1f7d47ee092af97989b516aab48f2aed681b3d` |
| `op` | `op.quota-exceeded-error-serialization-steps` | 216470 | 216860 | 48 | `1bdcd05ecca0b4517b231b35aadfec823e7a0c3dc24d53945b5e4b370761edbe` |
| `op` | `op.quotaexceedederror-quota-exceeded-error-message-options` | 214573 | 215831 | 32 | `058bb10014d24c4dcfb77050f02193ce07f8ef6dbba643d103df8c5977b83ffc` |
| `op` | `op.reject` | 349785 | 350073 | 48 | `c2edaaba6c2c29a161365819f857be96eabcf9ee573580a4687e8eec72a900ea` |
| `op` | `op.resolve` | 349216 | 349783 | 48 | `071c11c45c5c1da04b86837e7911385b64880eaf3a013ff769676110af545cc3` |
| `op` | `op.throw-an-exception` | 667326 | 667543 | 24 | `eef218df5d89e680179c4fd287dc583ed2f32c627bb99c514f7e7b7c0e5b54b7` |
| `op` | `op.to-create-a-dom-exception` | 665488 | 666331 | 48 | `9c9e8e3900f31454289e363c04d9cb3d534bc9723d7e4864788e2558acf1b54f` |
| `op` | `op.to-create-a-dom-exception-derived-interface` | 666333 | 667324 | 48 | `ff0eedd3a45de5b085e69a570d46272ca1b9d60d1ca4b471f7561708bfc2f710` |
| `op` | `op.to-create-a-simple-exception` | 664734 | 665486 | 32 | `a685c4154d0f603eb41dfcc0b4cafcb2ffcfc201d1519963d63a1008d36351de` |
| `op` | `op.upon-fulfillment` | 352410 | 352816 | 64 | `81ccd0a141715f38ae30f05c97a994c4ea3fef748c6301da8f3b8e4c6c785b9d` |
| `op` | `op.upon-rejection` | 352818 | 353237 | 64 | `f1e47b988febfd3652dac64ddb390db465d96a07f5b2d939cd8c62413221e7e9` |
| `op` | `op.validated-delay` | 358205 | 358816 | 24 | `520648ac6758cb1bfe8aaf7b54d209872c5e428255c266f01a32940cdc503b3d` |
| `op` | `op.wait-for-all` | 353239 | 354879 | 48 | `518fae182417ff76e800ed67df039a512d35b6af29ee11251b684172e703d930` |
| `op` | `op.waiting-for-all-promise` | 354881 | 356058 | 24 | `e8e29da9e357ce2532fe7acb9b978139f217f5dbc83db043cc2f7ffeacb605b3` |
| `rule` | `rule.domexception-derived-attributes` | 212319 | 212507 | 24 | `b6f0959816c25a86e3190fa116bce101193b052dc473bfa9f5d6ef859101aedc` |
| `rule` | `rule.domexception-derived-constructor-message` | 211922 | 212161 | 48 | `8c76ad3f87e6e38bf899921555982b993526392959c49443fe804978f81d5496` |
| `rule` | `rule.domexception-derived-constructor-name` | 211775 | 211921 | 24 | `725cee27de08373b9d2f6a91a8e50ed462e030e2924bf2d858d7539fa006be16` |
| `rule` | `rule.domexception-derived-constructor-options` | 212162 | 212318 | 48 | `b22c520f07b64ef41cc104c1506b06f289461dc1abcf6b1f636f55780a610000` |
| `rule` | `rule.domexception-derived-identifier` | 211607 | 211774 | 24 | `f624781f6a7b62a5daa3deb6805a683e9fdd76d9d033ce6867726b8e0ee24564` |
| `rule` | `rule.domexception-derived-serializable` | 212508 | 212653 | 24 | `f29b16284e3c090804206588df17445b408eb0e821feb9b190b84acf4fcbbc84` |
| `type` | `type.aborterror` | 206394 | 206680 | 32 | `18920890af5a1bb435cd9d7215ef532f9c599e4400f56e012cf25da6b84ced66` |
| `type` | `type.constrainterror` | 209105 | 209369 | 32 | `2bbb3bd78064f6f703f29e3439dc75f4c25d15a9584a888621b890cc69c0ae7f` |
| `type` | `type.datacloneerror` | 208109 | 208416 | 48 | `f4989a2f14bed893723de1a9c1bcd2f037d933bf07a5811d7ae37beae18fe49b` |
| `type` | `type.dataerror` | 209378 | 209560 | 48 | `1250a40d36b944ce09519ab3baab26b848091322ec10d322f89ce6e62c25cbc9` |
| `type` | `type.encodingerror` | 208425 | 208646 | 32 | `09f5bb975f55e29abebae3e9d7d9ba514d815a0b707a0ee158e1252ceef52a47` |
| `type` | `type.eval-error` | 194542 | 194576 | 24 | `fe52f6d4a2d0a88af703f2350adddf91c27a6ee76cd229324b54724bed0c93d8` |
| `type` | `type.hierarchyrequesterror` | 200957 | 201323 | 32 | `47148ba23577331f23085583db568390eb676e1e5da0eb0dbf217cf232ab2403` |
| `type` | `type.idl-dom-exception` | 673398 | 673477 | 24 | `0d75c2304dcc564dd7e4199120d80adc2f23dc2b033b78ac174ec19dae5d82d6` |
| `type` | `type.idl-promise` | 252146 | 252269 | 24 | `fa4cada5568a7371132cec82e9632293dd79e663dbc121e0c6deb0639316e334` |
| `type` | `type.indexsizeerror` | 200596 | 200948 | 64 | `a78fab8f0aa76c8e861b409bfaedfecdfb45a4902dc41e9b0ea9dc7240a3b07c` |
| `type` | `type.inuseattributeerror` | 203047 | 203401 | 48 | `cdcb8259df8f08935d5de9972c8581d982824ce0b4f24c4e21366eb1eb587ad8` |
| `type` | `type.invalidaccesserror` | 204794 | 205410 | 64 | `36eb12e30a0a5172ff2e20ae8938f1857701721c16b3f5e6888c423dcbb5326a` |
| `type` | `type.invalidcharactererror` | 201683 | 202027 | 48 | `d6ee3a99130a2233697485719c8be7fee4206a6476e98643b7b93a496f0cbc48` |
| `type` | `type.invalidmodificationerror` | 204062 | 204423 | 48 | `39d4d1ebf79d34688ba197b09eba06ea7ce31202d870bcf887e333f6676fb800` |
| `type` | `type.invalidnodetypeerror` | 207705 | 208100 | 48 | `4f6c50936ec7d13da070d3b5d22443da1c1a12911d3c0b455ec06901be69f01c` |
| `type` | `type.invalidstateerror` | 203410 | 203734 | 48 | `37f9c581b7ef85e806642ab4359c5d2a8c178c985012e556c6899dd73a182110` |
| `type` | `type.namespaceerror` | 204432 | 204785 | 48 | `059c76bc893cbf7b23d449727a898649eadccfe1f68852c71a48c42a7b9bbec7` |
| `type` | `type.networkerror` | 206092 | 206385 | 48 | `5fd5052507c74a89ef7ada1bff51a85643377976b2b1c1a42cb5faf331170402` |
| `type` | `type.nomodificationallowederror` | 202036 | 202394 | 48 | `7caa02a5efd0af1a87df073e2efcda61958725d1c05581bde74dfb7d0c370783` |
| `type` | `type.notallowederror` | 210618 | 210913 | 48 | `f3382081f3f1551544d0eacad475a64b1c46eebd22c2eefbe7207f298022aa97` |
| `type` | `type.notfounderror` | 202403 | 202709 | 48 | `4c8d7c60abde59dba7d92a596a89935c0f34e6995706afdc7805354c9d1bed41` |
| `type` | `type.notreadableerror` | 208655 | 208853 | 48 | `cb8c86f88a824b41d9caffa5e0f4159a77b97757c710acd34fc0b2f7049ff2de` |
| `type` | `type.notsupportederror` | 202718 | 203038 | 48 | `7ef8b3a7417ef440e6cbb241c0a612d10fbad37ca6e276cdec84665a6fdba4eb` |
| `type` | `type.operationerror` | 210391 | 210609 | 48 | `63019aafdb8dd9cecc174c10c15e970a68e941b977868c4b4a851c9c4c037cca` |
| `type` | `type.optouterror` | 210922 | 211114 | 48 | `79525ead90cfbfd0d548f12b2d1abd9ddb13c0c6b9c053ba1a87e43f8d2b3eb5` |
| `type` | `type.range-error` | 194577 | 194612 | 24 | `d15db5c544b96a84193b54197019d13371c736db365c85dc348ad49e3a2b7311` |
| `type` | `type.readonlyerror` | 209871 | 210112 | 32 | `91d02708973dcf9c44bf5e4a8704880161e48e6705b0b57c2e2a8ff475b12a47` |
| `type` | `type.reference-error` | 194613 | 194652 | 24 | `25210a48ac8e4d513cb59d2f82798138187e0b03b2b89fc5091fa0e252ce5dc1` |
| `type` | `type.securityerror` | 205785 | 206083 | 48 | `59c3f7350f0655d8ae23f30ad8e7c00f16f241aa12fa2cc7dac8aa21c202305c` |
| `type` | `type.syntaxerror` | 203743 | 204053 | 48 | `a53db98ed19f851882b83ed576f99404c39648335b82da1e835a366753532e40` |
| `type` | `type.timeouterror` | 207404 | 207696 | 48 | `24af6447be4228aa7f4ab63f6d49380fdc1ca73399af82882cb91e0926e9ee6e` |
| `type` | `type.transactioninactiveerror` | 209569 | 209862 | 48 | `3e7b1fcf5ac3c2dfd5eb3d90b5ea49f9c9166db31fb9fec6219c24ea6ce0291d` |
| `type` | `type.type-error` | 194653 | 194687 | 24 | `d81310aea9f58cfc2aad57a69a92a8d6752ea011377684ff9859969ed5832c7f` |
| `type` | `type.typemismatcherror` | 205419 | 205776 | 64 | `0c1751de3cb145f9d78e5d1fffa55270a3a18456e32336b8db05f8aab7bc3999` |
| `type` | `type.unknownerror` | 208862 | 209096 | 32 | `b18781b2f65d78ec81babe2c219ebb8f4e965034333e33bf909f5665689eb2ab` |
| `type` | `type.uri-error` | 194688 | 194721 | 24 | `f7bf226ec77f3615c85f432c11ad4d0ae345c50a0dae119baa662f8a4a6ce0bf` |
| `type` | `type.urlmismatcherror` | 206689 | 207022 | 64 | `53910d07cfa4481ecde98f9aa78594b271e216a61c58e27a8a7ae7c9d127c3f5` |
| `type` | `type.versionerror` | 210121 | 210382 | 32 | `3457c1af6ec4f7e1eb224c85b8e3067cfe3469706bf9e5c5d014962e5ba0ef47` |
| `type` | `type.wrongdocumenterror` | 201332 | 201674 | 32 | `d590c3a636b3e789e16529a3e72f35e5a883eb2dca6b29260e93b513f01e503c` |

## 9. Acceptance

1. Every name the battery ascribes exists with that exact signature, and every
   `#guard` in it passes.
2. `generated/webidl-census.tsv` has the frozen header line, 121 rows, the
   per-kind counts of section 5, and every row of section 8 byte-exactly in
   kind, id, start, end, anchor and digest.
3. The file is strictly increasing in `kind.name ++ "|" ++ id`, so no row id
   repeats.
4. `WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean` records `rowTotal 121`,
   `denominator 112` and the disposition counts of section 5.
5. `lake exe census --standard webidl` prints `PASS`, and `--write` in a clean
   tree leaves no diff.
6. `test/contracts/census-profile-identity.contract.md` still passes: the
   Streams and Infra projections are byte-identical.
7. `lake build` and the repository gates pass, and the axiom receipt of the
   whole tree is inside the R-11 ceiling.

## 10. Fence and verification

Frozen breaker files:

- `test/contracts/webidl-census.contract.md`
- `WhatwgTest/Audit/WebIdl/CensusContract.lean`
- `test/counterexamples/webidl/CENSUS.md`

Red-phase registration: `test/fixtures/trust-gate/known-red.txt`, entry
`WhatwgTest.Audit.WebIdl.CensusContract`, removed by the builder the moment the
battery is green. The breaker edits no implementation, no vendored bytes, no
generated projection, no authored census input and no central counterexample
register.

Builder fence: `Gates/Census.lean`, `census/webidl/**`,
`generated/webidl-census.tsv`, `WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean`,
the CI step, and the `SPEC-MANIFEST.md` / `docs/SPEC-COVERAGE.md` rows the plan
seat owns.

Narrow command:

```text
lake build WhatwgTest.Audit.WebIdl.CensusContract
```

## 11. Freeze receipt

Observed in the breaker's worktree at the base commit, on Lean 4.33.1,
Windows x64. `lake --wfail build Whatwg Gates` completes 163 jobs with exit
code 0.

`lake build WhatwgTest` reports exactly three failing targets, which is exactly
the declared red set:
`WhatwgTest.Audit.CensusProfileIdentity`,
`WhatwgTest.Audit.WebIdl.CensusContract`,
`WhatwgTest.Audit.Ecma262.CensusContract`.
`lake build WhatwgTest.Audit.WebIdl.CensusContract` fails on its own.

Lean's `maxErrors` is 100 and is read once per file, so the complete diagnostic
list was collected with `lake env lean -DmaxErrors=5000` on the same file:
**76 errors, 0 warnings**. Every one is one of these, and no other error class
appears:

| Count | Diagnostic | Where |
| --- | --- | --- |
| 41 | `Unknown identifier` for `Gates.Census.Bikeshed`, its eight field projections and `.mk`, `Gates.Census.Profile`, `Gates.Census.Profile.bikeshed`, `Gates.Census.Profile.ecmarkup`, `Gates.Census.webidl` and each of its twelve field reads | sections 1 and 2 |
| 5 | `Unknown constant` for `Gates.Census.Standard.profile`, `…sectionsRelativePath`, `…dependenciesRelativePath`, `…externalsRelativePath`, `Gates.Census.RuleInput.endLocator` | sections 1 and 2 |
| 1 | `Type mismatch` on `@Gates.Census.RuleInput.mk`: the constructor takes two fields today | the `rules.tsv` ascription |
| 2 | `Invalid field 'endLocator': The environment does not contain 'Gates.Census.RuleInput.endLocator'` | the two `parseRules` probes |
| 5 | `Application type mismatch` | the five `⟨name, locator, endLocator⟩` literals |
| 1 | `Invalid dotted identifier notation: The expected type of '.bikeshed' could not be determined` | the profile `#guard` |
| 1 | `Expression … did not evaluate to 'true'` | `(Gates.Census.Standard.ofKey? "webidl").isSome` |
| 19 | `cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors` | each `#guard` whose subject is one of the above |
| 1 | `webidl census contract: no standard is registered under the key webidl; ruling R-P1 requires ` + `` `lake exe census --standard webidl` `` | the projection gate, which refuses before touching a file |

The last line is the packet's own refusal, not a Lean error class: the gate
runs, finds no `webidl` standard, and stops. The frozen row table, the header
literal, the counts and the whole gate body elaborate cleanly today; their
logic was exercised end to end against `generated/spec-algorithm-census.tsv`
with a throwaway probe module before this packet was frozen, and that probe was
removed.

The `Gates/` tree and the semantic/test tree share one axiom ceiling under
ruling R-11, so this battery's elaboration-time command needs no entry in
`WhatwgTest/Audit/AxiomGate.lean`'s `auditImplementationModules`.
