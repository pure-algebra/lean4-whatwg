# Web IDL census Q2 addendum (P8-C1a)

Status: FROZEN / RED, Q2 census breaker seat, 2026-09-07, based on
`e819a9f` (`main`, the Q1 landing plus ratification R-P17).

This packet is an **addendum** to `test/contracts/webidl-census.contract.md`,
not a replacement. The base packet stays byte-identical to its frozen form;
this file layers the Q2 amendments on top of it, in the way the P5a lifecycle
and exact addenda were layered on `test/contracts/writable-default.contract.md`
(`docs/WRITABLE-DAG.md` records that precedent). Where the two disagree, the
disagreement is listed in section 1 with its date and reason and this file
wins; everything the base packet states and this file does not name is
unchanged and still binding.

Its authorities are the review debts D3, D4 and D5 of `COORDINATION.md` and
the five acceptance conditions of the "Q2 — dispositions, dependency and
external rows, coverage blocks" section of `docs/PROMISE-PACKAGE-PLAN.md`,
together with rulings R-P4, R-P6, R-P10, R-P16 and R-P17.

The battery this packet freezes is
`WhatwgTest/Audit/WebIdl/CensusQ2Contract.lean`. The builder may repair
elaboration but may not weaken, delete or replace a frozen row, count, digest,
locator, signature or refusal.

## Claim boundary

This is a tooling contract, exactly as the base packet is. A census row is a
byte span of the pinned source with a joined disposition. Nothing here grants
a Web IDL semantic claim, an observation mask, a coverage state above
`absent`, a host observation, or any statement about `Whatwg.WebIdl`. The two
coverage blocks section 6 freezes are **all-`absent`** blocks: they state that
nothing is proved, and quoting either as coverage is a defect.

Offsets are 0-based byte offsets into
`vendor/whatwg-webidl-a652053f/index.bs` (695,845 bytes, SHA-256
`3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`); ends are
exclusive; no line number is cited anywhere. Every span digest below was
recomputed in this packet from the sealed bytes with `[IO.File]::ReadAllBytes`
and .NET `System.Security.Cryptography.SHA256`, and the span rule of
`Gates.Census.scanRules` and the ladder of `Gates.Census.chooseAnchorLength`
were re-implemented independently and validated against three already-frozen
rows before any new number was taken (section 9).

## 1. Q2 amendment

Three amendments, each dated, each with the frozen base statement it
supersedes. No other statement of `test/contracts/webidl-census.contract.md`
changes.

### 1.1 (2026-09-07, debt D3) DOMException's serialization and deserialization steps become two authored `rule` rows

**Reason.** The independent Q1 review found that `DOMException`'s
[=serialization steps=] and [=deserialization steps=], between bytes 675370
and 677113 of the pinned source inside `idl-DOMException`, produce no census
row. They are normative steps: the text says these objects are serializable
objects and then states, in order, what each step sets. They are invisible to
every scanner because they are written as plain `<ol>` lists in running prose —
no `<div>` carries an `algorithm` attribute over them, no `<dfn>` opens inside
them, and they are not IDL. The same two operations of the *derived*
interface `QuotaExceededError` are rows
(`op.quota-exceeded-error-serialization-steps` at 216470–216860 and
`op.quota-exceeded-error-deserialization-steps` at 216862–217258) only because
that section writes them inside `<div algorithm="…">`. A census in which the
derived interface's steps are rows and the base interface's steps are not is
wrong about the source, and the error is silent: the run reports `PASS`.

Ruling R-P4 already gives `rules.tsv` the optional end locator for exactly
this class of prose. The base packet's section 4.4 says `rule` rows "enter
through `census/webidl/rules.tsv`"; this amendment adds two entries to that
file and takes the recorded-exclusion alternative off the table.

**Superseded.** The base packet's section 4.5 ("What is not a row") is read as
silent about these two step lists rather than as excluding them; its section 5
expected-row and disposition tables, and its section 8 frozen row table, are
superseded by sections 3 and 4 below.

### 1.2 (2026-09-07, debt D4) `op.an-exception-was-thrown` moves from `evidenceOnly` to `hostOnly`

**The coordinator's decision to record.** The reviewer's argument is adopted:
an exported normative `<dfn>` sitting under a sentence that requires
propagation is a host obligation, not an example. `op.an-exception-was-thrown`
is the whole of section `js-handling-exceptions` (669093–671837); its row spans
669437–669665 and its digest is
`a705b8c63991bc538c2c97e6aa1a5ef66360e8e37f5e9a6bb1dc44544859efa6`. Labelling
it `evidenceOnly` puts it outside the denominator, where no witness is ever
owed and no host-profile refusal is ever recorded against it. `hostOnly` keeps
it in the denominator as a row this repository may never make `green`, which
`docs/SPEC-COVERAGE.md` calls the honest record.

**How it is authored.** By changing the disposition of the section's one line
in `census/webidl/dispositions.tsv` from `evidenceOnly` to `hostOnly`, **not**
by an entry in `census/webidl/overrides.tsv`. `Gates.Census.finishBuild`
credits an overridden row to the override alone, so an override here would
leave the section's own line matching no row and generation would fail with
`census/webidl/dispositions.tsv: js-handling-exceptions * matches no row`.
The section holds exactly this one row, so the two readings coincide on the
row set and only the authored form is admissible.

**Superseded.** The base packet's section 5 disposition tables (the
`js-handling-exceptions` line and the `evidenceOnly` and `hostOnly` totals) and
its section 9 acceptance conditions 2 and 4, by sections 3 and 4 below. The
base packet's section 8 row table is unchanged: it records no disposition
column.

### 1.3 (2026-09-07, debt D5) `convert an IDL promise to a JavaScript value` becomes the authored `rule` row `rule.promise-to-js`

**Reason.** The reviewer found that the census carries a row for one direction
of the promise conversion pair and not for the other.
`op.js-to-promise` (346692–347209) exists because the JavaScript-to-IDL
direction is written as `<div id="js-to-promise" algorithm="convert a
JavaScript value to promise">`. The reverse direction is a bare
`<p id="promise-to-js">` paragraph at 347211, in the same `js-promise` lead
section. A census that carries one direction and not the other silently
asserts that only one direction is specified.

**The decision this packet takes with the source, as Q2 asks.** It is an
**authored `rule` row**, not a definition-keyed `op` row the existing scanners
can produce. The evidence, recomputed here from the sealed bytes:

- `scanOps` keys on a `<div>` whose tag carries an `algorithm` attribute
  (base packet section 4.1). The element at 347211 is a `<p>`; the file holds
  exactly one occurrence of `<p id="promise-to-js">` and zero `<div>` tags in
  `[347209, 347497)`. No `op` row is reachable.
- `scanDefinitions` keys on a `<dfn>` in scope or a line-opening heading
  carrying a bare Bikeshed definition marker (base packet section 4.2). The
  paragraph contains no `<dfn>`: `[=converted to a JavaScript value|converting=]`
  and `[=promise type=]` are autolinks *into* definitions, the first of which
  is defined outside `census/webidl/sections.tsv`. No definition row is
  reachable, and reaching it would require widening the frozen section scope,
  which is a contract change the base packet's section 2 forbids as a
  convenience.
- `scanRules` with R-P4's end locator produces exactly the wanted span with
  two authored strings and no generator change. It is the mechanism the base
  packet already admits for "a cross-cutting rule the text states in prose"
  (`docs/SPEC-COVERAGE.md`).

Its kind is therefore `rule` and its id is `rule.promise-to-js`, mirroring the
element's own `id` exactly as `op.js-to-promise` mirrors `js-to-promise`. Its
disposition mirrors `op.js-to-promise`'s: `hostOnly`, from the unchanged
`js-promise * hostOnly` line, because the innermost heading containing byte
347211 is `js-promise` — `js-promise-manipulation` opens at 347497, after it.

**Superseded.** The base packet's sections 5 and 8, by sections 3 and 4 below.
The base packet's section 4.5 is again read as silent rather than exclusive.

## 2. The three new authored `rules.tsv` entries

Appended to `census/webidl/rules.tsv`, in this order, each three
tab-separated fields under R-P4. Every start locator was checked against the
whole pinned file and occurs **exactly once**; `Gates.Census.scanRules`
refuses any other count. Every end locator occurs at or after its start
locator, so none is widened to the blank-line rule.

| name | start locator | end locator |
| --- | --- | --- |
| `domexception-serialization-steps` | `Their [=serialization steps=], given <var>value</var>` | `Their [=deserialization steps=], given <var>value</var>` |
| `domexception-deserialization-steps` | `Their [=deserialization steps=], given <var>value</var>` | `<h3 id="Function" callback` |
| `promise-to-js` | `<p id="promise-to-js">` | `<h5 id="js-promise-manipulation"` |

Three facts that make these the locators and not others:

1. The shorter locator `Their [=serialization steps=], given` occurs **twice**
   in the pinned file, at 216531 and 676192, because `QuotaExceededError`
   states the same sentence. The `<var>value</var>` tail separates them: the
   `QuotaExceededError` block writes the Bikeshed variable form `|value|`.
   A two-occurrence locator is refused by `scanRules`, so the shorter string
   is not merely worse, it does not generate.
2. The serialization row's end locator is the deserialization row's start
   locator. That is deliberate: it is the only string between the two `<ol>`
   lists, and it puts the boundary exactly at the blank line after
   `</ol>`, so the two spans are disjoint and neither nests in the other.
   Ending it on `</ol>` instead would truncate the span before the closing
   tag, because `scanRules` ends the span *at* the first byte of the end
   locator.
3. The deserialization row runs to the next heading, `<h3 id="Function"
   callback`, at 677113, which is also where the `idl-DOMException` section
   ends. `trimSpanEnd` then removes the two newline bytes, so the span ends at
   677111, just past `</ol>`.

## 3. The three new rows

`anchor` is the byte length `Gates.Census.chooseAnchorLength` selects for the
span; the anchor itself is the first that many bytes of the span. Every digest
is the SHA-256 of `[start, end)` of the pinned bytes.

| kind | id | start | end | anchor | SHA-256 of `[start, end)` |
| --- | --- | --- | --- | --- | --- |
| `rule` | `rule.domexception-deserialization-steps` | 676693 | 677111 | 48 | `56b4661e16e17c24d633c37423077ef96810a7d737f5e97ed657aebb08e35555` |
| `rule` | `rule.domexception-serialization-steps` | 676192 | 676691 | 48 | `1c9753a8ed03b7e0a7e5b238408cbc3347746d0a341277a910386969dadeb218` |
| `rule` | `rule.promise-to-js` | 347211 | 347495 | 24 | `ef392964ee06eff2e3fd5682ecbb9704d004d704ec7de1032f8d40d9d535a111` |

Their anchor texts, which the battery reads back from the pinned bytes rather
than from this table:

| id | anchor |
| --- | --- |
| `rule.domexception-deserialization-steps` | `Their [=deserialization steps=], given <var>valu` |
| `rule.domexception-serialization-steps` | `Their [=serialization steps=], given <var>value<` |
| `rule.promise-to-js` | `<p id="promise-to-js">` followed by a newline and one space |

Why 48 and not 24 for the two step rows: the 24-byte prefixes
`Their [=serialization st` and `Their [=deserialization ` both recur in the
`QuotaExceededError` section, and so do the 32-byte prefixes; 48 bytes reaches
the `<var>` that separates the two spellings. This is the real ladder's answer,
not a transcription: the battery of section 7 asserts all three lengths with
`Gates.Census.chooseAnchorLength` itself over the pinned bytes.

Placement in the projection, which is strictly increasing in
`kind.name ++ "|" ++ id` under Lean's ordinal `String` order. The `rule` block
grows from six rows to nine, and the three new ids interleave with the six
frozen ones as follows; no existing row moves relative to any other:

```text
rule.domexception-derived-attributes
rule.domexception-derived-constructor-message
rule.domexception-derived-constructor-name
rule.domexception-derived-constructor-options
rule.domexception-derived-identifier
rule.domexception-derived-serializable
rule.domexception-deserialization-steps      <- new
rule.domexception-serialization-steps        <- new
rule.promise-to-js                           <- new
```

`derived` precedes `deserialization` because `r` precedes `s` at the
fifteenth byte, and `deserialization` precedes `serialization` because `d`
precedes `s` at the fourteenth. The whole `rule` block still precedes the
`type` block.

## 4. The new frozen totals

Superseding section 5 of the base packet.

| kind | rows (Q1) | rows (Q2) |
| --- | ---: | ---: |
| `idl` | 37 | 37 |
| `op` | 39 | 39 |
| `requirement` | 0 | 0 |
| `rule` | 6 | **9** |
| `slot` | 0 | 0 |
| `type` | 39 | 39 |
| `builtin`, `hook`, `property`, `record`, `field`, `term`, `clause` | 0 | 0 |
| **total** | 121 | **124** |

Section-and-kind dispositions, with the two changes marked:

| Section | kind | disposition | rows |
| --- | --- | --- | --- |
| `idl-exceptions` (lead) | `*` | `owned` | 9 |
| `idl-DOMException-error-names` | `*` | `owned` | 33 |
| `idl-DOMException-derived-interfaces` | `*` | `requirement` | 6 |
| `idl-DOMException-derived-predefineds` | `*` | `hostOnly` | 12 |
| `idl-promise` | `*` | `hostOnly` | 2 |
| `js-promise` (lead) | `*` | `hostOnly` | **2** (was 1; `rule.promise-to-js` joins `op.js-to-promise`) |
| `js-promise-manipulation` | `*` | `owned` | 11 |
| `js-promise-examples` | `*` | `evidenceOnly` | 8 |
| `js-exception-objects` | `*` | `hostOnly` | 1 |
| `js-creating-throwing-exceptions` | `*` | `owned` | 4 |
| `js-handling-exceptions` | `*` | **`hostOnly`** (was `evidenceOnly`; amendment 1.2) | 1 |
| `idl-DOMException` | `op` | `owned` | 2 |
| `idl-DOMException` | `idl` | `hostOnly` | 30 |
| `idl-DOMException` | `type` | `hostOnly` | 1 |
| `idl-DOMException` | **`rule`** | **`owned`** (new line; amendment 1.1) | **2** |

The new `idl-DOMException rule owned` line reads the manifest's
`idl-DOMException` cell — "`idl` rows `hostOnly`; the associated `name` and
`message` and the constructor and getter steps `owned`" — consistently with
debt D1's repair of that cell: what the section states as *steps of the
interface* is owned, and what it states as *IDL surface* or as the *interface
type* is the host's. The serialization and deserialization steps are steps of
the interface over the same associated `name` and `message` the two `op` rows
already carry, so they take the same side of that line. They are not `idl`
rows and they are not the interface type.

| disposition | rows (Q1) | rows (Q2) |
| --- | ---: | ---: |
| `owned` | 59 | **61** |
| `hostOnly` | 47 | **49** |
| `evidenceOnly` | 9 | **8** |
| `requirement` | 6 | 6 |
| `foreignBoundary`, `refused`, `targetOnly` | 0 | 0 |
| **denominator** | 112 | **116** |
| **excluded** | 9 | **8** |

Arithmetic, stated so a reader can check it without regenerating: `owned`
gains the two `idl-DOMException` `rule` rows; `hostOnly` gains
`rule.promise-to-js` and `op.an-exception-was-thrown`; `evidenceOnly` loses
`op.an-exception-was-thrown`. 61 + 49 + 8 + 6 = 124, and 124 − 8 = 116.

The exact `lake exe census --standard webidl` summary line, both lines, exit 0:

```text
census: 124 rows (idl 37, op 39, requirement 0, rule 9, slot 0, type 39, builtin 0, hook 0, property 0, record 0, field 0, term 0, clause 0); dispositions (owned 61, requirement 6, foreignBoundary 0, hostOnly 49, refused 0, evidenceOnly 8, targetOnly 0); denominator 116, excluded 8; 0 IDL statement(s) outside the row vocabulary
PASS census (webidl): input digest is the pin, every anchor occurs exactly once at its span start, every span digest recomputes, every row has exactly one disposition, both projections are byte-identical to a fresh regeneration, and the coverage emit agrees with that regeneration row for row
```

The PASS line's tail changes from Q1's "; no numerator exists for this
standard yet, so no emit was checked" because section 6 gives this standard a
numerator. The frozen census header line becomes

```text
#census format=1 generator=Gates.Census input=vendor/whatwg-webidl-a652053f/index.bs input-sha256=3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83 rows=124 regenerate=lake exe census --standard webidl --write
```

and `WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean` records `rowTotal 124`
and `denominator 116` with the disposition counts above.

## 5. Dependency and external rows for the three new rows

Q2 acceptance 2 requires exactly one dependency list per row, so the three new
rows need three new lines in `census/webidl/dependencies.tsv`. They are frozen
here, derived from the `[=…=]`, `{{…}}` and `\[[…]]` references inside each
row's own byte span and from nothing else, in the file's existing sorted
form:

```text
rule.domexception-deserialization-steps	ext.html.deserialization-steps,ext.html.serialized-record,op.dom-exception-message,op.dom-exception-name
rule.domexception-serialization-steps	ext.html.serialization-steps,ext.html.serialized-record,op.dom-exception-message,op.dom-exception-name
rule.promise-to-js	ext.ecma262.slot-promise,ext.webidl.js-type-mapping,op.dfn-promise-type
```

Three readings this fixes, each with the precedent it follows:

- `[=serialization steps=]` and `[=deserialization steps=]` are HTML's
  structured-serialization hooks, already declared as
  `ext.html.serialization-steps` and `ext.html.deserialization-steps` and
  already used by the `QuotaExceededError` rows.
- `\[[Name]]` and `\[[Message]]` are fields of HTML's serialized record, the
  same reading `op.quota-exceeded-error-serialization-steps` gives `\[[Quota]]`
  through `ext.html.serialized-record`.
- `{{DOMException}}` and `[=serializable objects=]` are **not** dependencies of
  either step row: both occur in the sentence at 676136, which is outside both
  spans. `rule.domexception-derived-serializable` already carries
  `ext.html.serializable-objects` for the requirement that states it.
- `[=converted to a JavaScript value|converting=]` resolves into the
  out-of-scope type-mapping section, which is
  `ext.webidl.js-type-mapping` — the identity `op.js-to-promise` already uses
  for the mirror-image autolink. `[=promise type=]` resolves inside this
  census to `op.dfn-promise-type`, and `\[[Promise]]` to
  `ext.ecma262.slot-promise`.

No identity is added to `census/webidl/externals.tsv`: all five names above
are already declared there and already used, so the file's row set and its
"every declared identity is used" invariant are unchanged. Under R-P11 this
addendum decides no new escape group; the three ECMA-262 escapes R-P17
ratified as absent stay absent, because no row of
`js-DOMException-specialness` exists after these amendments either.

## 6. The numerator and the report (Q2 acceptance 4)

### 6.1 The two numerator modules

| Module | Path | Freeze |
| --- | --- | --- |
| `WhatwgTest.Audit.WebIdl.SpecCoverage` | `WhatwgTest/Audit/WebIdl/SpecCoverage.lean` | `def emit : Array CoverageRow` under `open Gates.Census`, the same type the Streams emit has (`Gates.Census.CoverageRow`); every row carries a census row id, state `absent` and no witness |
| `WhatwgTest.Audit.Ecma262.SpecCoverage` | `WhatwgTest/Audit/Ecma262/SpecCoverage.lean` | the same, for `ecma262`; frozen by `test/contracts/ecma262-census-q2.contract.md` |

The type is the existing one, not a new one:

```lean
Gates.Census.CoverageRow            -- id, disposition, state, witnesses
Gates.Census.CoverageState.absent
WhatwgTest.Audit.WebIdl.SpecCoverage.emit : Array Gates.Census.CoverageRow
```

At Q2 the emit is the generated all-absent scaffold, so the module is thin and
the freeze is that it stays honest: `emit` is `SpecCoverageRows.rows`, and the
module carries `expectedRowTotal := 124` and `expectedDenominator := 116`
beside it so that a census change that invalidates the freeze is repaired in
the same edit, exactly as `WhatwgTest/Audit/SpecCoverage.lean` does for
Streams. Nothing in either module may set a state above `absent` or attach a
witness at Q2; `Gates.Census.verifyEmit` already refuses a witness on an
`absent` row and a non-`absent` state on an excluded row, and Q3 is the slice
that adds the first witness.

### 6.2 The `Gates.Census.cli` signature change

The minimal change, and the one this packet ascribes, is **one map from
standard key to emit** rather than one `Option` field per standard: the number
of standards is already four and R-P6 leaves the door open for more, an
association list adds no case analysis at any call site, and the alternative
would put a per-standard argument into a signature that `bin/Census.lean` is
the only caller of.

```lean
Gates.Census.cli :
  List (String × Array Gates.Census.CoverageRow) → List String → IO UInt32
```

Its body changes in exactly one line: today's

```lean
let emit? := if std.key == streams.key then some emit else none
```

becomes a lookup in the map, `(emits.find? (fun pair => pair.1 == std.key)).map (·.2)`.
Everything downstream — `check`, `report`, `verifyEmit`, `write`, `usage` and
the three-mode dispatch — keeps its current signature and its current
behaviour. In particular:

- `Gates.Census.check : System.FilePath → Standard → Option (Array CoverageRow) → IO UInt32`
  is unchanged, and a standard that the map does not name is still checked with
  `none`;
- `Gates.Census.report : System.FilePath → Standard → Array CoverageRow → IO UInt32`
  is unchanged;
- `Gates.Census.verifyEmit : Built → Array CoverageRow → Array String` is
  unchanged, and it is what makes the block trustworthy: it re-derives ids,
  order and dispositions from a fresh regeneration before a number is printed.

`bin/Census.lean` becomes the three-entry map and gains two imports:

```text
import WhatwgTest.Audit.WebIdl.SpecCoverage
import WhatwgTest.Audit.Ecma262.SpecCoverage
("webidl", WhatwgTest.Audit.WebIdl.SpecCoverage.emit)
("ecma262", WhatwgTest.Audit.Ecma262.SpecCoverage.emit)
```

The cost is the one `Gates/AGENTS.md` already records for Streams, now three
times over: building the census executable, and so every mode of it, needs
these modules to elaborate. `--write` still does not read an emit, so a census
the numerators have not caught up with is still regenerable.

### 6.3 The refusal that must remain

`infra` gets no entry in the map, so

```text
lake exe census --standard infra --report
```

still exits 2 with

```text
census: no coverage numerator exists for infra, so there is no report yet
```

and `lake exe census --standard infra` still prints the PASS line ending
"; no numerator exists for this standard yet, so no emit was checked". A
change that makes every standard reportable by inventing an empty emit for
`infra` is a defect: the refusal is the record that Infra has no numerator.

### 6.4 The exact expected block text

In the format of `docs/SPEC-COVERAGE.md` — three lines, broken after
`owned-with-green <O>/<D>;` and after `<E> excluded`, third line
`partial:` with nothing after it because no row is `partial`. These replace
the two placeholder blocks under "Blocks not yet emitted", which state that
every field is a placeholder and no number has been computed.

```text
WHATWG Web IDL (a652053f) coverage: denominator 116; owned-with-green 0/116;
green 0, partial 0, absent 116; census 124 rows, 8 excluded
partial:
```

```text
ECMAScript ES2026 (0248456c) coverage: denominator 75; owned-with-green 0/75;
green 0, partial 0, absent 75; census 77 rows, 2 excluded
partial:
```

Both are all-`absent`. `owned-with-green 0/116` and `green 0` are the whole
content of the Web IDL claim: 116 rows are owed a witness and none has one.
The labels are `Gates.Census.webidl.label` and `Gates.Census.ecma262.label`
and are not authored here.

## 7. Acceptance

Q2's five acceptance conditions, restated for this standard as checkable
assertions, with the battery clause that checks each. Conditions already
checked by a Q1 battery are named rather than duplicated.

1. **Every row resolves to exactly one disposition with no generator default,
   and every `dispositions.tsv`, `overrides.tsv`, `rules.tsv` and
   `sections.tsv` entry reaches at least one row, in both directions.** This
   is enforced by `Gates.Census.finishBuild`, which fails generation on an
   unresolved row and on an authored entry that outlived its rows, and it is
   observable in the projection: the battery checks the row total 124, the
   per-kind counts of section 4, and the per-disposition counts of section 4
   against `WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean`, which are
   reachable only if every entry resolved. The battery additionally asserts
   the exact three `rules.tsv` entries of section 2 by locating each start
   locator in the pinned bytes and checking it occurs exactly once, which is
   the one direction the projection alone does not show.
2. **Exactly one dependency list per row; every external identity is used; no
   dependency names an unresolvable target.** The battery re-checks all three,
   independently of `Gates.Census.checkDependencies`, over
   `census/webidl/dependencies.tsv`, `census/webidl/externals.tsv`,
   `generated/webidl-census.tsv` and `generated/infra-census.tsv`: one line per
   census row and one census row per line; every declared `ext.` identity named
   by at least one line; every named target an in-census row id, an Infra row
   id, or a declared external. The three new lines of section 5 are asserted
   byte-exactly.
3. **The disposition totals agree with the `SPEC-MANIFEST.md` Web IDL table.**
   Section 4 is that agreement, as amended by 1.1, 1.2 and 1.3; the two
   manifest repairs debt D1 owes (the `idl-DOMException` cell and the
   `js-handling-exceptions` disposition) are the coordinator's, and a
   disagreement is repaired there or in the authored input, never by
   relabelling a row to make a total come out.
4. **Both coverage blocks emit all-`absent` from the Lean emit.** The battery
   asserts the `Gates.Census.cli` signature of 6.2 by ascription, the two
   numerator modules and the two `bin/Census.lean` map entries of 6.2 by their
   frozen source text, and the exact Web IDL block of 6.4 as a substring of
   `docs/SPEC-COVERAGE.md`.
5. **The two anchor-ladder rows are checked against the real
   `Gates.Census.chooseAnchorLength`.** *Already checked; not duplicated.*
   `WhatwgTest/Audit/Ecma262/EcmarkupScanner.lean` carries
   `anchorLengthProbes`, which runs the real ladder over
   `field.jobcallback-records.HostDefined` at 629941 (256 bytes) and
   `field.promisecapability-records.Promise` at 2688749 (64 bytes) — the two
   rows the plan names as `field.job-callback-record.host-defined` and
   `field.promise-capability-record.promise` under the survey's id scheme, at
   the same two spans — together with the lane's shortest anchor
   `term.%Promise%`. This battery adds the same treatment for the three rows
   this addendum introduces rather than restating those three.

Two conditions carried over from the base packet, unchanged: the projection is
strictly increasing in `kind.name ++ "|" ++ id`, and
`test/contracts/census-profile-identity.contract.md` still passes. That last
one is untouched by this addendum: it freezes only the Streams and Infra
projections and rows modules, and no byte of any of the four moves here.

## 8. Fence and verification

Frozen breaker files:

- `test/contracts/webidl-census-q2.contract.md`
- `WhatwgTest/Audit/WebIdl/CensusQ2Contract.lean`
- the `WEBIDL-CEN-CE-013` … `WEBIDL-CEN-CE-016` sections of
  `test/counterexamples/webidl/CENSUS.md`
- the amended frozen totals of `WhatwgTest/Audit/WebIdl/CensusContract.lean`,
  each amended line carrying the addendum and the date in a comment

Red-phase registration: `test/fixtures/trust-gate/known-red.txt`, entries
`WhatwgTest.Audit.WebIdl.CensusQ2Contract` and
`WhatwgTest.Audit.WebIdl.CensusContract`, both removed by the builder the
moment the two batteries are green. The second is declared because this
addendum supersedes totals the Q1 battery froze, so that battery is red for
the duration of the Q2 red phase and not because anything it checks is wrong.

The breaker edits no implementation, no vendored bytes, no generated
projection, no authored census input, no `docs/`, no `SPEC-MANIFEST.md` and no
central counterexample register.

Builder fence: `Gates/Census.lean` (the `cli` signature only),
`bin/Census.lean`, `census/webidl/rules.tsv`,
`census/webidl/dispositions.tsv`, `census/webidl/dependencies.tsv`,
`generated/webidl-census.tsv`,
`WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean`,
`WhatwgTest/Audit/WebIdl/SpecCoverage.lean`, and the
`docs/SPEC-COVERAGE.md` and `SPEC-MANIFEST.md` rows the plan seat and the
coordinator own.

Narrow command:

```text
lake build WhatwgTest.Audit.WebIdl.CensusQ2Contract
```

## 9. Freeze receipt

Observed in the breaker's worktree at base `e819a9f`, on Lean 4.33.1, Windows
x64.

**Method for every number in sections 2, 3 and 4.** `Gates.Census.scanRules`'
span rule (unique start locator; end at the first occurrence of the end
locator at or after it; `trimSpanEnd` over ASCII space, tab, CR and LF) and
`Gates.Census.chooseAnchorLength`'s ladder
(`baseWanted = min(bs.size − start, 24)`, UTF-8 forward alignment, then
24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048, 3072,
4096 and finally the rest of the file, first length that separates the span
start from every rival occurrence) were re-implemented in PowerShell over
`[IO.File]::ReadAllBytes` and validated before use against three already-frozen
rows: `rule.domexception-derived-identifier` (211607–211774, digest
`f624781f…`), `op.js-to-promise` (346692–347209, digest `c42584ff…`, anchor
24) and the `op.js-to-promise` anchor length. All three reproduced exactly.
Only then were the three new spans, digests and anchor lengths taken.

`lake --wfail build Whatwg Gates` completes 164 jobs with exit code 0; the
production tree is untouched by this packet.

`lake build WhatwgTest` fails on exactly the declared red set and on nothing
else — four targets out of 215, reported as

```text
✖ [210/215] Building WhatwgTest.Audit.WebIdl.CensusContract
✖ [211/215] Building WhatwgTest.Audit.WebIdl.CensusQ2Contract
✖ [212/215] Building WhatwgTest.Audit.Ecma262.CensusQ2Contract
✖ [213/215] Building WhatwgTest.Audit.Ecma262.CensusContract
```

Lean's `maxErrors` is 100 and is read once per file, so the complete
diagnostic list for this battery was collected with
`lake env lean -DmaxErrors=5000` on the absolute path of
`WhatwgTest/Audit/WebIdl/CensusQ2Contract.lean`: **2 errors, 0 warnings**.
Both are expected and no other error class appears:

| Count | Diagnostic | Where |
| --- | --- | --- |
| 1 | `Type mismatch`: `Gates.Census.cli` has type `Array Gates.Census.CoverageRow → List String → IO UInt32` but is expected to have type `List (String × Array Gates.Census.CoverageRow) → List String → IO UInt32` | the ascription in section 1 of the battery |
| 1 | `webidl census Q2 contract: generated/webidl-census.tsv carries 121 rows; the addendum freezes 124` | the projection gate, which stops at the first frozen fact the tree contradicts |

The six ascriptions before that one are green and print their types, which is
the freeze that `check`, `report` and `verifyEmit` keep their current
signatures across the change.

The gate is deliberately fail-fast, and the row total is its first clause
rather than the header line, because the row total is the fact every later
assertion is conditional on: a tree at Q1 reports one clear sentence rather
than a cascade.

**How the later clauses were exercised, since the tree cannot satisfy them
yet.** A copy of this battery was retargeted at the Q1 tree — `expectedRowTotal
121`, `expectedDenominator 112`, `rule` 6, the Q1 disposition counts, `newRows`
pointed at the two already-frozen rows `rule.domexception-derived-identifier`
(211607–211774, anchor 24) and `op.js-to-promise` (346692–347209, anchor 24),
`newRuleInputs` at the existing `domexception-derived-identifier` entry,
`newDependencyLines` at its existing dependency line, the numerator and entry
point at `WhatwgTest/Audit/SpecCoverage.lean` and `bin/Census.lean` as they
stand, and the coverage block at the Q1 placeholder text. It ran to `logInfo`
in 4.9 s with only the `cli` ascription still red, printing

```text
webidl census Q2 contract: 121 rows, denominator 112, 2 new rule rows verified against vendor/whatwg-webidl-a652053f/index.bs (SHA-256 3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83) with the real anchor ladder, 121 dependency lines and 46 externals used in both directions, and the all-absent coverage block emitted
```

so every clause of the gate — the projection parse, the strict sort, the kind
counts, the digest recomputation, the real `Gates.Census.chooseAnchorLength`
call, the `rules.tsv` locator-uniqueness scan, the rows-module totals and named
entries, the whole two-directional dependency and externals join over 121 rows
and 46 identities, the numerator and entry-point fragments and the coverage
block substring — is exercised end to end against real data. That copy was
deleted before this packet was frozen and no byte of the tree it read was
changed.

The amended `WhatwgTest/Audit/WebIdl/CensusContract.lean` reports, with the
same command, **1 error, 0 warnings**: `webidl census contract: the header
line of generated/webidl-census.tsv is not the frozen one` — that gate checks
the header before the row count, so it names the `rows=124` field rather than
the count. Its five amended lines (`expectedRowTotal`, `expectedDenominator`,
`expectedHeader`, the `rule` entry of `expectedKindCounts`, and the `owned`,
`hostOnly` and `evidenceOnly` entries of `expectedDispositionCounts`) each
carry a comment naming this addendum and the date; no other line of that file
changed, and no frozen row, span, digest, anchor, locator or refusal moved.

Every repository gate still passes at this freeze, unchanged by the packet:

| Command | Result |
| --- | --- |
| `lake exe vendorseal` | `PASS vendor seal: manifest and vendor/ agree in both directions; every path is valid on Windows` |
| `lake exe citations` | `PASS internal citations: 323 files scanned; no line-numbered citation into a protected authored document` |
| `lake exe census` | `PASS census (streams): …, and the coverage emit agrees with that regeneration row for row` |
| `lake exe census --report` | the Streams block unchanged: denominator 410, owned-with-green 12/410, green 12, partial 6, absent 392, 450 rows, 40 excluded |
| `lake exe census --standard infra` | `PASS census (infra): …; no numerator exists for this standard yet, so no emit was checked` |
| `lake exe census --standard webidl` | `PASS census (webidl): …`, still the 121-row Q1 summary: the authored inputs are the builder's and this packet does not touch them |
| `lake exe census --standard ecma262` | `PASS census (ecma262): …`, still the Q1 summary, for the same reason |

The `Gates/` tree and the semantic and test trees share one axiom ceiling
under ruling R-11, so this battery's elaboration-time command needs no entry
in `WhatwgTest/Audit/AxiomGate.lean`'s `auditImplementationModules`. This
battery declares no theorem, so it carries no axiom receipt of its own.
