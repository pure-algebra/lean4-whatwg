# ECMA-262 promise and job census contract (P8-C2)

Status: FROZEN / RED, promise census breaker seat, 2026-09-06, based on
`03abfc579883d1c79492b0e4d1e933f71a830e68`.

This packet freezes `WhatwgTest/Audit/Ecma262/CensusContract.lean` before the
ECMA-262 census and the `Gates/Ecmarkup.lean` scanner exist. Its rulings are
R-P1 through R-P7 of `COORDINATION.md`; its source evidence is
`docs/research/2026-09-06-ecma262-promise-census-survey.md`, every number of
which was independently recomputed here from the sealed bytes. The builder may
repair elaboration but may not weaken, delete or replace a frozen row, count,
digest or refusal.

Read `test/contracts/census-profile-identity.contract.md` first, and
`test/contracts/webidl-census.contract.md` second: R-P7 lands the profile
refactor with the Web IDL standard, and this lane sits on top of it.

## Claim boundary

This is a tooling contract. A census row is a byte span of the pinned source
with a joined disposition. Nothing here grants an ECMAScript semantic claim, an
observation mask, a coverage state, a denominator the numerator may quote, a
host observation, or any statement about `Whatwg.Ecma262`. In particular this
packet does not decide DB-03: it records that
`requirement.hostenqueuepromisejob.3` is the row the FIFO ordering claim will
hang on, and stops there.

## 1. The pin

| Item | Value |
| --- | --- |
| Source | `vendor/ecma262-0248456c/spec.html` |
| Upstream | `tc39/ecma262` at `0248456c758431e4bb8e5d26333ff1865123c9cd`, tag `es2026`, 2026-03-31 |
| Size | 2,978,793 bytes |
| SHA-256 | `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0` |

Recomputed here with `[IO.File]::ReadAllBytes` and .NET
`System.Security.Cryptography.SHA256`; it agrees with `SPEC-MANIFEST.md`,
`docs/PROVENANCE.md` and the survey. Offsets are 0-based byte offsets; ends are
exclusive; no line number is cited anywhere.

## 2. The clause scope

`census/ecma262/sections.tsv` names exactly two root clause ids. Each must
occur exactly once as an `<emu-clause id=…>` in the pinned bytes, and every row
must lie inside one of the two windows.

| id | start | end | bytes | SHA-256 of `[start, end)` |
| --- | --- | --- | --- | --- |
| `sec-jobs` | 624525 | 636548 | 12023 | `871310fa2bcc46a2c06c2b0cc2e590632270246801336d7188185f0b4b3573bf` |
| `sec-promise-objects` | 2686444 | 2746707 | 60263 | `21deb38546b2e5e928888349f91a40a16074a8cfa7f91469a0aec56c5bc7e9e0` |

Together: 49 sectioning elements, 72,286 bytes, 2.43 % of the file.
`sec-host-promise-rejection-tracker` is not a third root; it sits inside
`sec-promise-abstract-operations`. The scope is part of the frozen contract:
`Gates.Census.occurrences` caps at 4096 hits, and file-wide `<p>`, `<li>` and
`<td>` scans would exceed that cap silently.

## 3. The ecmarkup subset, and what the scanner must refuse

Recomputed over the two windows at this pin:

| Fact | Value |
| --- | --- |
| sectioning elements | 49 `<emu-clause>`, balanced, 0 `<emu-annex>`, 0 `<emu-intro>` |
| `type` attribute | 34 occurrences, exactly three distinct values: `abstract operation`, `built-in function`, `host-defined abstract operation`; 15 clauses untyped |
| `aoid` attribute | 1, on `sec-ifabruptrejectpromise` |
| `<h1>` | 49 |
| `<dl class="header">` | 21, of which 10 carry exactly one `<dt>description</dt>` and 11 are empty; no other `<dt>` occurs |
| `<emu-alg>` | 32, every one the bare tag `<emu-alg>`, no attribute |
| step lines | 390, every one matching `^ *1\. `; 0 violations, 0 odd relative indents, 0 level jumps greater than one; absolute indents 8 (3), 10 (131), 12 (100), 14 (87), 16 (53), 18 (16) |
| `<emu-table>` | 4, each with one `<thead>` of three `<th>`; 13 body `<tr>`, each of three `<td>` |
| `<dfn>` | 9 |
| `<emu-note>` | 20; `<emu-xref>` 8 |
| character references | 0: the byte `&` does not occur in scope at all |
| tabs, CR | 0 and 0 |
| non-ASCII bytes | 188, four code points: U+00AB, U+00BB, U+201C, U+201D |

Ruling R-P1 gives this standard `Gates.Census.Profile.ecmarkup`, served by a
new `Gates/Ecmarkup.lean`. It is a pure scanner over a byte window: it reads no
file, decides no disposition, and **refuses rather than skipping**. Every
rejection is `Except.error` whose message contains the decimal byte offset of
the refused construct — the opening tag for a clause, a table row or an
algorithm block, and the first byte of the line for a step. That is the one
place in this repository where diagnostic text is part of the contract, and it
matches the existing `Gates.Census` message style (`census: unterminated <dfn
at byte {d}`).

The refusals, all of them vacuous at this pin and therefore permanent
regressions:

| Shape | Refused |
| --- | --- |
| an `<emu-clause>` with a `type` value outside the three observed | yes |
| an `<emu-clause>` with no `id`, or with no `<h1>` | yes |
| an unclosed sectioning element, a close whose element name does not match the open on top, or a stack underflow | yes |
| an `<emu-alg>` carrying any attribute (`example`, `replaces-step`, `type`) | yes |
| a non-blank line inside an `<emu-alg>` that does not match `^ *1\. ` | yes |
| a step indent that is not a multiple of two relative to the block minimum | yes |
| a step indent that jumps more than one level | yes |
| an unterminated `<emu-alg>` | yes |
| a `&` inside a scanned window | yes; never decoded |
| a `<dl class="header">` whose `<dt>` is not `description` | yes |
| an `<emu-table>` whose `<thead>` has other than three `<th>` | yes |
| a body `<tr>` with other than three `<td>`, or unterminated | yes |
| a `<dfn>` with neither an `id` nor text | yes |

## 4. The scanner surface

```lean
Gates.Ecmarkup.Clause      -- id, kindAttr, aoid, title, depth, b, e
Gates.Ecmarkup.Step        -- level, b, e
Gates.Ecmarkup.TableRow    -- cells : Array (Nat × Nat), b, e
Gates.Ecmarkup.scanClauses    : ByteArray → Nat → Nat → Except String (Array Clause)
Gates.Ecmarkup.scanSteps      : ByteArray → Nat → Nat → Except String (Array Step)
Gates.Ecmarkup.scanTableRows  : ByteArray → Nat → Nat → Except String (Array TableRow)
Gates.Ecmarkup.escapeId       : String → String
Gates.Ecmarkup.unescapeId     : String → Option String
```

Intended meanings. `Clause.id` is the `id` attribute; `Clause.kindAttr` is the
`type` attribute, empty where the tag carries none; `Clause.aoid` is the `aoid`
attribute, empty where absent; `Clause.title` is the `<h1>` inner text with
runs of whitespace collapsed to one space; `Clause.depth` is 0 for a clause
with no clause ancestor inside the scanned window and one more than its
parent's otherwise; `b` and `e` are the half-open byte interval of the whole
element, `e` just past the closing tag. `Step.level` is the nesting level
relative to the block's own minimum indent, 0 for a top-level step, so an
absolute column is never read as an ordinal; the literal `1.` is never read as
a number. `TableRow.cells` holds the three `<td>` content intervals in order.
The two `Nat` arguments of each scanner are the window `[b, e)`; the scanners
are fuel-bounded structural recursion with fuel taken from a size the data
carries, exactly as `Gates.Census` is, and use no `partial` and no
well-founded recursion.

### 4.1 The R-P3 escaping

`escapeId` writes every character of the safe alphabet `A-Z a-z 0-9 . % -`
through unchanged — so `.`, `%` and case survive, which is what R-P3 requires —
and writes every other character `c` as `~`, the lower-case hexadecimal of
`c.toNat` with no leading zero, `~`. Because `~` is outside the safe alphabet
the encoding is prefix-free, so `escapeId` is injective and `unescapeId`
inverts it exactly, returning `none` on any string outside the image.

Worked values, all frozen as probes:

| input | `escapeId` |
| --- | --- |
| `promise.resolve` | `promise.resolve` |
| `promise-resolve` | `promise-resolve` |
| `promise.withResolvers` | `promise.withResolvers` |
| `get-promise-%symbol.species%` | `get-promise-%symbol.species%` |
| `promise.prototype-%symbol.tostringtag%` | `promise.prototype-%symbol.tostringtag%` |
| `Promise prototype object` | `Promise~20~prototype~20~object` |
| `a_b` | `a~5f~b` |
| `a~b` | `a~7e~b` |

**The named collision test.** `Gates.Census.kebab "sec-promise.resolve"` and
`Gates.Census.kebab "sec-promise-resolve"` are the same string,
`sec-promise-resolve`: `kebab` maps every non-alphanumeric byte to one
separator, so the `.` of `Promise.resolve` and the `-` of `PromiseResolve`
become the same character. The battery asserts that equality — it is the defect
R-P3 names and it is checkable against the generator as it stands — and then
asserts that `escapeId "promise.resolve"` and `escapeId "promise-resolve"`
differ. On the frozen row set the two clauses become `builtin.promise.resolve`
and `op.promise-resolve`, distinct on the kind prefix as well.

## 5. Row taxonomy and id scheme

R-P2 extends `Gates.Census.Kind` with `builtin`, `hook`, `property`, `record`,
`field`, `term` and `clause`, appended after the existing six so that no
Streams or Infra sort key moves. `Kind.all` is

```text
idl, op, requirement, rule, slot, type, builtin, hook, property, record, field, term, clause
```

### 5.1 Primary rows — one per clause, 49 rows

The 49 clause spans are the rows' spans; the id is
`<kind>.<escapeId(clause id with a leading "sec-" removed)>`. Kind is decided
by the tag and the `<h1>`, in this order:

| Condition | Kind |
| --- | --- |
| `type="abstract operation"` | `op` |
| `type="host-defined abstract operation"` | `hook` |
| `type="built-in function"` | `builtin` |
| untyped, `aoid` present | `op` |
| untyped, no `aoid`, title ends with `" Records"` | `record` |
| untyped, no `aoid`, the first whitespace-separated token of the title contains a `.` | `property` |
| otherwise | `clause` |

At this pin that is 16 `op`, 6 `hook`, 13 `builtin`, 3 `record`, 3 `property`
and 8 `clause`. The rule is exhaustive and deterministic: the three `record`
titles are `JobCallback Records`, `PromiseCapability Records` and
`PromiseReaction Records`, and the three `property` titles are
`Promise.prototype`, `Promise.prototype.constructor` and
`Promise.prototype [ %Symbol.toStringTag% ]`.

Clause rows nest, as Streams rows already do: `clause.promise-objects` contains
every other row of its subtree. The generator does not subtract child spans.

### 5.2 `field` and `slot` rows — 13 rows

One row per body `<tr>` of an `<emu-table>` in scope; the span is the `<tr>`
element. A `<tr>` inside a `record` clause is a `field` row with id
`field.<owner clause id minus "sec-">.<slot name>`; a `<tr>` inside any other
clause is a `slot` row with id `slot.<slot name>`. The slot name is the
`[[Name]]` of the first `<td>` with the brackets removed, case preserved. That
gives 8 `field` rows over the three record tables and 5 `slot` rows over
`table-internal-slots-of-promise-instances`.

### 5.3 `requirement` rows — 9 rows

A requirement list is a `<ul>` whose immediately preceding `<p>` has
whitespace-normalised text containing `must conform to the`. At this pin
exactly four of the eleven in-scope `<ul>` match, in `sec-jobs` (4 bullets),
`sec-hostmakejobcallback` (1), `sec-hostcalljobcallback` (1) and
`sec-hostenqueuepromisejob` (3), for nine top-level `<li>`. The seven `<ul>`
that do not match are the two `sec-jobs` definitional condition lists, the
`sec-host-promise-rejection-tracker` note list, the promise-state list, and the
three object-description lists. The span is the `<li>` element; the id is
`requirement.<owner clause id minus "sec-">.<1-based index in its list>`.

R-P3 makes the positional index explicit: none of the nine carries an `id`,
unlike the Streams piping bullets. The index is guarded by the span digest, so
an upstream reorder is a visible failure rather than a silent relabel.

### 5.4 `term` rows — 6 rows

One row per `<dfn>` in scope that is not the first `<dfn>` of a `record`
clause; that exclusion is what keeps the three record names from being counted
twice. The span is the `<dfn>` element; the id is
`term.<escapeId(the dfn id, else its whitespace-normalised text)>`. Only three
of the nine in-scope `<dfn>` carry an `id`, which is why an `<dfn id=…>`-keyed
scheme like Infra's is not usable here.

## 6. Expected row counts

| kind | rows |
| --- | --- |
| `builtin` | 13 |
| `clause` | 8 |
| `field` | 8 |
| `hook` | 6 |
| `op` | 16 |
| `property` | 3 |
| `record` | 3 |
| `requirement` | 9 |
| `slot` | 5 |
| `term` | 6 |
| `idl`, `rule`, `type` | 0 |
| **total** | **77** |

Dispositions are R-P5's: the survey's proposal stands, with
`HostEnqueuePromiseJob` and its ordering bullet `requirement`, realized by the
FIFO queue in `Whatwg.Ecma262.Jobs` under DB-03.

| disposition | rows | primary | sub-rows |
| --- | --- | --- | --- |
| `owned` | 44 | 31 | 13 |
| `foreignBoundary` | 13 | 6 | 7 |
| `hostOnly` | 10 | 7 | 3 |
| `requirement` | 7 | 2 | 5 |
| `evidenceOnly` | 3 | 3 | 0 |
| `refused`, `targetOnly` | 0 | 0 | 0 |
| **denominator** | **74** | | |

The three `evidenceOnly` rows are `clause.promise-objects`,
`clause.promise-abstract-operations` and `clause.promise-jobs`. The two
`requirement` primary rows are `clause.jobs` and `hook.hostenqueuepromisejob`;
the five `requirement` sub-rows are `requirement.jobs.1` … `.4` and
`requirement.hostenqueuepromisejob.3`. R-P5 also records that the five promise
instance slots are `owned` here while the Streams census keeps the same named
slots `foreignBoundary`: the two censuses describe two libraries, and the
Streams rows become references into `Whatwg.Ecma262` when P8 opens.

## 7. The command line

```text
lake exe census --standard ecma262            check
lake exe census --standard ecma262 --write    regenerate
lake exe census --standard ecma262 --report   refused: no numerator exists
```

`check` regenerates both projections in memory and compares bytes; it verifies,
independently of the scanners, that every recorded anchor occurs exactly once
in the pinned bytes at its recorded span start and that every recorded span
digest recomputes. It refuses, with a nonzero exit and a `FAIL` line, when:

- `vendor/ecma262-0248456c/spec.html` is missing, or has any SHA-256 other than
  the pin;
- any authored input under `census/ecma262/` is missing;
- either root clause id of `sections.tsv` does not occur exactly once;
- any scanner meets an unhandled source shape (section 3). A shape is never
  skipped and no row is dropped;
- an `occurrences` scan reaches its 4096 cap: a cap hit is an error, never a
  truncation;
- a row id is duplicated, a span is empty or reversed or outside its window, an
  anchor is not unique within the admitted ladder, or an anchor or span splits
  a UTF-8 character;
- either projection differs from a fresh regeneration by one byte.

Two CI steps are added, one per new standard (R-P7).

## 8. Authored inputs

All under `census/ecma262/`, validated in both directions exactly as the Web
IDL packet states: an entry that reaches no row fails generation, and a row
that no entry reaches fails generation.

| File | Fields | Validation |
| --- | --- | --- |
| `sections.tsv` | `<clause id>` | Exactly `sec-jobs` and `sec-promise-objects`. An id that is not an `<emu-clause id=…>` occurring exactly once fails; a listed root that governs no row fails; a row outside every window fails. |
| `dispositions.tsv` | `<clause id>` TAB `<kind or `*`>` TAB `<disposition>` | Unchanged format. The section key is a clause id, resolved by the innermost enclosing clause of the row's span. Duplicate `(clause, kind)` fails; unknown kind or disposition fails; an entry no row uses fails. |
| `overrides.tsv` | `<row id>` TAB `<disposition>` TAB `<reason>` | Unchanged format. Duplicate row id fails; empty field fails; an override no row uses fails. |
| `rules.tsv` | `<kebab name>` TAB `<start locator>` [TAB `<end locator>`] | Present and entry-free at this pin: this standard emits 0 `rule` rows. The optional third field is R-P4's. |
| `dependencies.tsv` | the URL lane's format | Every row id named must exist; every dependency identity must resolve to a row of this census or to an `ext.` identity in `externals.tsv`; a duplicate or self dependency fails. |
| `externals.tsv` | the URL lane's format | Every identity namespaced `ext.`; a duplicate fails; an identity no dependency uses fails. |

Under R-P6 the escaping references split two ways. A named **ES2026 core
boundary** takes Completion Records (`sec-completion-record-specification-type`,
`sec-normalcompletion`, `sec-throwcompletion`, `sec-completion-ao`, and the `?`
and `!` shorthands — 53 and 9 occurrences in scope), Abstract Closures
(`sec-abstract-closure`, `sec-createbuiltinfunction`, `sec-setfunctionname`,
`sec-setfunctionlength`; 13 closures are created in scope and 11 are wrapped),
and the object-model operations (`Call`, `Construct`, `Get`, `Invoke`,
`IsCallable`, `IsConstructor`, `CreateDataPropertyOrThrow`,
`DefinePropertyOrThrow`, `OrdinaryObjectCreate`,
`OrdinaryCreateFromConstructor`, `SameValue`, `SpeciesConstructor`,
`GetFunctionRealm`, `CreateArrayFromList`) together with the iterator protocol
the four combinators consume. **Externals** take agents, realms and execution
contexts (`sec-execution-contexts`, `sec-code-realms`, `sec-agents`,
`sec-getactivescriptormodule`, Script and Module Records), the well-known
intrinsics and symbols, and the error objects (`TypeError`, `AggregateError`).
`HostEnqueueFinalizationRegistryCleanupJob` and `EnqueueResolveInAgentJob` are
dependency rows marked out of lane, so a later reader can see they were found
and deliberately excluded.

## 9. Frozen rows

The complete census, all 77 rows. `anchor` is the byte length of the anchor
`Gates.Census.chooseAnchorLength` selects for the span; the anchor itself is
the first that many bytes of the span, so the battery checks the projection's
anchor field against the pinned bytes rather than against a transcription.
Every digest is the SHA-256 of `[start, end)` of the pinned bytes, recomputed
here with .NET SHA-256 and again by the battery with `Gates.Sha256.hexDigest`.

Anchor-length distribution over the 77 rows: 24 bytes for 20 rows, 32 for 29,
48 for 26, 64 for 1 (`field.promisecapability-records.Promise`) and 256 for 1
(`field.jobcallback-records.HostDefined`). No row falls through to the whole
remainder of the file. Two disagreements with the survey's §3.1 table are
recorded in section 11.

| kind | id | start | end | anchor | SHA-256 of `[start, end)` |
| --- | --- | --- | --- | --- | --- |
| `builtin` | `builtin.get-promise-%symbol.species%` | 2735737 | 2736537 | 32 | `b019e293eb4a7b2349f33ab6e48abc9c20427063aa3f0acdbc3e233dac58a20a` |
| `builtin` | `builtin.promise-executor` | 2708413 | 2711495 | 32 | `765932794c01fd8b82164d88f54a765a96ed390f011de69396470e48f2575ea5` |
| `builtin` | `builtin.promise.all` | 2711835 | 2717026 | 32 | `86c966b7f88d69f50dda8100c3b3e1bc1af352fdc6d0e47a3fc7687fb9e65a90` |
| `builtin` | `builtin.promise.allsettled` | 2717034 | 2723460 | 32 | `083105d5a28c05d0f92325aef4b388e12d420abfc379d2c93551522b1d52e108` |
| `builtin` | `builtin.promise.any` | 2723468 | 2728545 | 32 | `10016318f59b61ad2f3e3e153be3dcc23881ce3a0c5611f9cd9fb6cf3dda4ed4` |
| `builtin` | `builtin.promise.prototype.catch` | 2737067 | 2737453 | 48 | `5fa520b7bc4b9fdb9599ae193385ee21dbb2188ee37f036a02d34903f6174f25` |
| `builtin` | `builtin.promise.prototype.finally` | 2737669 | 2740006 | 48 | `8900f09e03c588c6f990f5a511d98a0e8b90b65bd067a6d7d276b657deddbed6` |
| `builtin` | `builtin.promise.prototype.then` | 2740014 | 2743689 | 48 | `97a409281b34879a52da89b63be07cc15a9dfd70443035debcb4b38636dbd588` |
| `builtin` | `builtin.promise.race` | 2728871 | 2731537 | 32 | `68eabc5289e154aa5cf28ea5f159eb83daff9f1cff470c012f4f5882b5b61865` |
| `builtin` | `builtin.promise.reject` | 2731545 | 2732230 | 32 | `7b918a7dc1f44d633f07ded2e87864b7d841d669d50b5631e4c96475d8bf3ba5` |
| `builtin` | `builtin.promise.resolve` | 2732238 | 2733852 | 32 | `e38d9843379c55dc41c53b77e053048e86c125c752a9e999ed2a1ff1ef77cc7c` |
| `builtin` | `builtin.promise.try` | 2733860 | 2734885 | 32 | `498e54e44b5ef0d5b7faaa243a5b4f9c8505d90f820c9c3a01b33858f18b6535` |
| `builtin` | `builtin.promise.withResolvers` | 2734893 | 2735729 | 32 | `35bfc8591d8a2046a0d07a2943e44c5891f7a5a22bb93fd99148a419ddc99a45` |
| `clause` | `clause.jobs` | 624525 | 636548 | 24 | `871310fa2bcc46a2c06c2b0cc2e590632270246801336d7188185f0b4b3573bf` |
| `clause` | `clause.promise-abstract-operations` | 2687651 | 2702809 | 32 | `fa30b3b37aa9cfd702de3d7a9b8d1408ec959bd95381ef7dd7653f5c2675436f` |
| `clause` | `clause.promise-constructor` | 2707565 | 2711513 | 32 | `b7bb9e4831d34a8a4e091ccd90506e9cce8ad25ef7a1b66cccec25149c5fa1d1` |
| `clause` | `clause.promise-jobs` | 2702815 | 2707559 | 32 | `9ee19fb76c828986e3aff598ace336dfbacab6a69c51bcedc46c007ba1f1b7cb` |
| `clause` | `clause.promise-objects` | 2686444 | 2746707 | 32 | `21deb38546b2e5e928888349f91a40a16074a8cfa7f91469a0aec56c5bc7e9e0` |
| `clause` | `clause.properties-of-promise-instances` | 2744135 | 2746691 | 48 | `f3c8e70543376d039c9138e95afd153a99dd914f87398ba9208d8b76bd00aa0d` |
| `clause` | `clause.properties-of-the-promise-constructor` | 2711519 | 2736555 | 48 | `31a227af9032fdbb0e501b8419acf570bbee74959df62259fc4d57c4f6655b1a` |
| `clause` | `clause.properties-of-the-promise-prototype-object` | 2736561 | 2744129 | 48 | `f1599e711c81aceabca5ef33d796867271015536b12200fc2e04b12a14c212d4` |
| `field` | `field.jobcallback-records.Callback` | 629684 | 629930 | 48 | `0aa3d4ac28a7163324040babf2ffc96e492bf530e71b7c29e1222596bb86ab57` |
| `field` | `field.jobcallback-records.HostDefined` | 629941 | 630193 | 256 | `9edf19e8961f9d0341683b05f33c634d920df9b2f48412b1d1c623cda62a4446` |
| `field` | `field.promisecapability-records.Promise` | 2688749 | 2688997 | 64 | `59942a56a0e02b4fcc325226c71897937d87e435526b06ec2166a0e8c882cf64` |
| `field` | `field.promisecapability-records.Reject` | 2689296 | 2689567 | 48 | `0d38dbfc1eeaa69490e9efc8b8e68e16603c20f82f9cd20f4793fb65d70b9371` |
| `field` | `field.promisecapability-records.Resolve` | 2689010 | 2689283 | 48 | `c1b547ccba62ad0a5b2b5222643a00a19ee63336b5d9821ba27cb3501542f57c` |
| `field` | `field.promisereaction-records.Capability` | 2691475 | 2691802 | 48 | `67b47fd1bc6773cb099432f10db3b5b427d445cd1a10077db3ec90ec381d6a77` |
| `field` | `field.promisereaction-records.Handler` | 2692151 | 2692611 | 48 | `79e2058b8d3cfcbff3ace42ff8e52406429d38ea5252ebb18bd4b0fa56fa25ca` |
| `field` | `field.promisereaction-records.Type` | 2691815 | 2692138 | 48 | `9d8bbc74e5fa8aca1901755de043e11705ab76ee6dbaa10339cfc408f71fa8d2` |
| `hook` | `hook.host-promise-rejection-tracker` | 2701220 | 2702791 | 32 | `8b44c32c206fff92fefb2dbf3208efb4b53226fb18bd8cd42dfe1f72182fde07` |
| `hook` | `hook.hostcalljobcallback` | 631447 | 632699 | 32 | `8c71cf59d88d1e5d189be02e8a179a59d57dd35c0978b0419fcc02ea34d34267` |
| `hook` | `hook.hostenqueuegenericjob` | 632705 | 633441 | 32 | `3c4716a0db0dc18a9eb400f975a12026aa81cfdae6924d2b51e79348fd621b51` |
| `hook` | `hook.hostenqueuepromisejob` | 633447 | 635836 | 32 | `2dd7ba925b7ef8424773a60bdef524789cf044e2a97d7f1796fa74acec613b93` |
| `hook` | `hook.hostenqueuetimeoutjob` | 635842 | 636532 | 32 | `ee98ff2feb4f02946c4508ed8d47e5c1df82714138d1644cee02b912d6345870` |
| `hook` | `hook.hostmakejobcallback` | 630253 | 631441 | 32 | `f8ccca3399819ba3253b0dbec63f9663ed4fc3737ae74cc708e00e1235c46e4a` |
| `op` | `op.createresolvingfunctions` | 2692679 | 2695411 | 32 | `8227712c5eaa66d17942e1b7c13a8d6f7c29f24a03a591df81ce9868a90c8944` |
| `op` | `op.fulfillpromise` | 2695419 | 2696230 | 24 | `f0efa1ffede8b5b861cdb87a36f340ddbab87b2cdcd83abd7172d68e41a1c67e` |
| `op` | `op.getpromiseresolve` | 2713285 | 2713877 | 32 | `e3d4435301645c214ed0df54ef70ba2b71216c1c447f36c2e274c183125bf85b` |
| `op` | `op.ifabruptrejectpromise` | 2689617 | 2690417 | 32 | `7453862884877f7d2186444ab91e950c928cb0a711074025577311073a810ba9` |
| `op` | `op.ispromise` | 2698778 | 2699315 | 32 | `4762e66357e6408fde8f751a3008cda25dd492e99c5061b291f99c8514a121cf` |
| `op` | `op.newpromisecapability` | 2696238 | 2698770 | 32 | `9d0157b63bd72c38fb0951e4d0030b46997508ca43b46c5402eb901bb4f5c1d9` |
| `op` | `op.newpromisereactionjob` | 2702885 | 2705591 | 48 | `3225cb2f3907ae48b448c01a862587e80cd5e8b795b8ad5d610df68b5f291a7b` |
| `op` | `op.newpromiseresolvethenablejob` | 2705599 | 2707541 | 48 | `cde161e71ffde5bfde25825afa6b4e7c879c31d8056ab6c26f2d27c461f92e13` |
| `op` | `op.performpromiseall` | 2713887 | 2717006 | 48 | `a1c1fd99668df4f6b18316ccf4cfee9cd40d7137fb93e50da05c8abd5be5bfca` |
| `op` | `op.performpromiseallsettled` | 2718509 | 2723440 | 48 | `a9a3a64032ae6ac8500aa76e05a2ebd5751d2d0ef53fe9f4f23d714392ad9caa` |
| `op` | `op.performpromiseany` | 2724939 | 2728525 | 48 | `820398cb01553fc0bfe57e34aa9e430372e3639acee832fa85abb916ff98483d` |
| `op` | `op.performpromiserace` | 2730549 | 2731517 | 48 | `1061c0d5656d6fe17c945f326aac79e2938ef121d2d454f722e93a7b4edde680` |
| `op` | `op.performpromisethen` | 2740635 | 2743669 | 48 | `ff69ee65628ebe06e4fe2717feb6013c3d3089b3fa2b034fd90c085c3fa7e2ce` |
| `op` | `op.promise-resolve` | 2732914 | 2733832 | 32 | `9bfa14eade2e7991ee59dcdfdba99458d54bf48a8640dc0727e85df00ce649e6` |
| `op` | `op.rejectpromise` | 2699323 | 2700252 | 24 | `1006df0c95f76cd0a9edadadb8f68bf85446b0e8778485cfd8b913fb169fc056` |
| `op` | `op.triggerpromisereactions` | 2700260 | 2701212 | 24 | `ba03acae7a5640e794655f0fcb6e085859ce91eb4a8f899472ff01dc122c1839` |
| `property` | `property.promise.prototype` | 2728553 | 2728863 | 48 | `bdce2e364c2e0104a38b05bea65aa79f5c7262473ed8c83fafb37a756eaac56c` |
| `property` | `property.promise.prototype-%symbol.tostringtag%` | 2743697 | 2744111 | 32 | `dbe55bc57a9ab199033ca8ad2742c44d565f74431e43aa49e1c2b03ff8300eb3` |
| `property` | `property.promise.prototype.constructor` | 2737461 | 2737661 | 48 | `8176eb3689ce275615a724264dbf4b369621a8fe40f3db39e1bb2f81bf495a07` |
| `record` | `record.jobcallback-records` | 628436 | 630247 | 24 | `0fdda86da2a80f733a34298da2bec97f7a3c3da2cb173e0270813d63a9e85a1d` |
| `record` | `record.promisecapability-records` | 2687751 | 2690437 | 32 | `08c37430874eb8f162eb3e84825cfecf3aae49700ec1a28e9728864e79fe83ab` |
| `record` | `record.promisereaction-records` | 2690445 | 2692671 | 32 | `d66fc8081d7a889ffbdd77b8a4828c5ad87095a72fa04b257f808dbea8816743` |
| `requirement` | `requirement.hostcalljobcallback.1` | 631993 | 632098 | 24 | `1e479d75efd60b7e7342f9d2113a4237de99cfba08a1a29c1dc25a9a268bce96` |
| `requirement` | `requirement.hostenqueuepromisejob.1` | 634193 | 634410 | 24 | `7a33838fa1b5acbfb44c7f685abffc7c489667fdb590f30a80f8273c5a2f2e89` |
| `requirement` | `requirement.hostenqueuepromisejob.2` | 634419 | 634730 | 24 | `4041960ebfe66a4dc729e9f67acf868e6dc7049835b24a08552ffc3d4da696d6` |
| `requirement` | `requirement.hostenqueuepromisejob.3` | 634739 | 634841 | 24 | `6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65` |
| `requirement` | `requirement.hostmakejobcallback.1` | 630615 | 630699 | 24 | `398f9ac14e8275f65bf58957f19f8f0cceda1440f931d2b7293e78dd002aed01` |
| `requirement` | `requirement.jobs.1` | 625769 | 626250 | 24 | `c1afc33fed819c64bf74bbdfda723687b449fc135daaa0bb9dd9b73d0f5954e2` |
| `requirement` | `requirement.jobs.2` | 626257 | 626350 | 24 | `dec0ab05daf30a7def2efe98018bbdf58750e2f762313b2b50d8184b00720ec5` |
| `requirement` | `requirement.jobs.3` | 626357 | 626479 | 24 | `3cee57a0e02ed9d66b34bdaa1398995eebf32ac008eb9d493e15647bb9235378` |
| `requirement` | `requirement.jobs.4` | 626486 | 626589 | 24 | `22934fdf600a46d75443c562c8de0fdd4f441e8f67c4816d25ac4ec03aca194b` |
| `slot` | `slot.PromiseFulfillReactions` | 2745630 | 2745966 | 48 | `f13205764479117eddbc24d537a2981738b8e758dd5bd4f0d2042ce382fba3e0` |
| `slot` | `slot.PromiseIsHandled` | 2746322 | 2746637 | 48 | `c5e0730a73986eb475cb399584433d21e4aadecc069e3b2d61517937d39ed652` |
| `slot` | `slot.PromiseRejectReactions` | 2745977 | 2746311 | 48 | `d4c90d6b411a4b0359bfc0e9e75c1f9c25be373fb12d3a5bdbea60339a020f81` |
| `slot` | `slot.PromiseResult` | 2745263 | 2745619 | 48 | `c0c3b1b3c19902cdec5971211ec6f5cce01d5a5696f5728c480c61013cbb9a2f` |
| `slot` | `slot.PromiseState` | 2744957 | 2745252 | 48 | `b752fb3cead6b7d3063935ef7a5867b1af9f1f298b688dbe9d015540012f33fb` |
| `term` | `term.%Promise.prototype%` | 2736764 | 2736794 | 24 | `302fe81fc6fd80019abc332c6a47ba9dedd0e029fa784d49a7a328142294695e` |
| `term` | `term.%Promise%` | 2707710 | 2707730 | 24 | `bab66ccb5d0f0e98396dd6d48bb696c5f831210ac5edba920d191654b5003425` |
| `term` | `term.job` | 624685 | 624724 | 24 | `9be48048e1c5bbdd279753b6e574c4c1c10fe0b30daf54b1bbf468ee353a9fa5` |
| `term` | `term.job-activescriptormodule` | 627006 | 627070 | 24 | `189a5af3e9e04656c8e4196392fefc25a9cc1990eaf2792b0eb79fb2b5539ade` |
| `term` | `term.job-preparedtoevaluatecode` | 627505 | 627584 | 24 | `516906e43a51acff6bea69b650808674600154eadcaebbdfb147e455c32f01ec` |
| `term` | `term.Promise~20~prototype~20~object` | 2736697 | 2736732 | 24 | `362a4b141200ade425ce88a78c944ae6cd994fc2cfb7f1ab754a83d1c3a4b5cf` |

## 10. Acceptance

1. Every name the battery ascribes exists with that exact signature, and every
   `#guard` in it passes, including the 22 scanner probes of section 3 (7
   acceptances and 15 refusals) and the 14 escaping probes of section 4.1.
2. `generated/ecma262-census.tsv` has the frozen header line, 77 rows, the
   per-kind counts of section 6, and every row of section 9 byte-exactly in
   kind, id, start, end, anchor and digest.
3. The file is strictly increasing in `kind.name ++ "|" ++ id`, so no row id
   repeats.
4. `WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean` records `rowTotal 77`,
   `denominator 74` and the disposition counts of section 6.
5. `lake exe census --standard ecma262` prints `PASS`, and `--write` in a clean
   tree leaves no diff.
6. `test/contracts/census-profile-identity.contract.md` and
   `test/contracts/webidl-census.contract.md` still pass.
7. `lake build` and the repository gates pass, and the axiom receipt of the
   whole tree is inside the R-11 ceiling.

## 11. Where this packet disagrees with the survey

| Fact | Survey | This packet | Why |
| --- | --- | --- | --- |
| anchor length of `field.jobcallback-record.host-defined` | 252, the whole `<tr>` span | **256** | The survey's PowerShell re-implementation clamps a ladder rung to the span length; `Gates.Census.chooseAnchorLength` does not, and rung 256 separates the row. The survey asked for exactly this check. |
| the shortest anchor | 20 bytes, for `term.promise-intrinsic` | **24** | Same clamp. `chooseAnchorLength` takes `baseWanted = min(bs.size - start, 24)`, and `bs.size - start` is the rest of the file, never the span; on a 20-byte span the anchor is still 24 bytes. |
| anchor histogram | 20→1, 24→19, 32→26, 48→29, 64→1, 252→1 | **24→20, 32→29, 48→26, 64→1, 256→1** | The same clamp shifts one row out of each of the first three buckets. |
| row ids | derived from the `<h1>` operation name (`op.perform-promise-then`) | derived from the clause id (`op.performpromisethen`) | R-P3 rules that ids derive from clause ids with `.`, `%` and case preserved. This is a ruling difference, not a measurement difference. |
| `sec-promise-objects` state vocabulary | open decision 6 | `evidenceOnly` | R-P5 adopts the survey's proposal, which is `evidenceOnly`. |

Everything else the survey measured over these two windows reproduces exactly:
the 49 clause spans and digests, the 4 table spans, the 13 body-row spans and
digests, the 9 requirement-bullet spans and digests, the 9 `<dfn>` spans and
digests, 32 `<emu-alg>` blocks with 390 step lines and 0 violations, 1 `aoid`,
34 `type` attributes with three distinct values, 21 `<dl class="header">` with
10 `<dt>description</dt>`, 0 `&`, 0 tabs, 0 CR and 188 non-ASCII bytes.

## 12. Fence and verification

Frozen breaker files:

- `test/contracts/ecma262-census.contract.md`
- `WhatwgTest/Audit/Ecma262/CensusContract.lean`
- `test/counterexamples/ecma262/CENSUS.md`

Red-phase registration: `test/fixtures/trust-gate/known-red.txt`, entry
`WhatwgTest.Audit.Ecma262.CensusContract`, removed by the builder the moment
the battery is green. The breaker edits no implementation, no vendored bytes,
no generated projection, no authored census input and no central counterexample
register.

Builder fence: `Gates/Ecmarkup.lean`, `Gates/Census.lean`, `census/ecma262/**`,
`generated/ecma262-census.tsv`,
`WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean`, the CI step, and the
`SPEC-MANIFEST.md` / `docs/SPEC-COVERAGE.md` rows the plan seat owns. R-P7 lets
the scanner be developed in parallel as a pure scanner with its own battery;
the `ecma262` standard lands on top of it after the Web IDL builder lands the
profile refactor.

Narrow command:

```text
lake build WhatwgTest.Audit.Ecma262.CensusContract
```

## 13. Freeze receipt

Observed in the breaker's worktree at the base commit, on Lean 4.33.1,
Windows x64. `lake --wfail build Whatwg Gates` completes 163 jobs with exit
code 0.

`lake build WhatwgTest` reports exactly three failing targets, which is exactly
the declared red set:
`WhatwgTest.Audit.CensusProfileIdentity`,
`WhatwgTest.Audit.WebIdl.CensusContract`,
`WhatwgTest.Audit.Ecma262.CensusContract`.
`lake build WhatwgTest.Audit.Ecma262.CensusContract` fails on its own.

Lean's `maxErrors` is 100 and is read once per file, so the complete diagnostic
list was collected with `lake env lean -DmaxErrors=5000` on the same file:
**164 errors and 22 warnings**. Every one is one of these, and no other error
class appears:

| Count | Diagnostic | Where |
| --- | --- | --- |
| 76 | `Unknown identifier` for `Gates.Census.ecma262` and each of its twelve field reads, `Gates.Census.Profile`, `Gates.Census.Profile.ecmarkup`, `Gates.Ecmarkup.Clause`, `…Step`, `…TableRow`, their thirteen field projections, `…scanClauses`, `…scanSteps`, `…scanTableRows`, `…escapeId`, `…unescapeId` | sections 2 and 4 |
| 21 | `Unknown constant` for the seven `Gates.Census.Kind` constructors, their seven `.name` reads, and the seven inside the `ofString?` `#guard`s | section 1 |
| 4 | `Expression … did not evaluate to 'true'` for `Kind.all.length == 13`, for the `Kind.all` spelling list, for `(Standard.ofKey? "ecma262").isSome` and for `standards.length == 4` | the four `#guard`s whose subjects exist but whose values are not yet the frozen ones |
| 1 | `Invalid dotted identifier notation: The expected type of '.ecmarkup' could not be determined` | the profile `#guard` |
| 61 | `cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors`, or because one of the private fixture helpers `clauses`, `steps`, `tableRows` does | every escaping and refusal probe, and every field `#guard` |
| 1 | `ecma262 census contract: no standard is registered under the key ecma262; ruling R-P1 requires ` + `` `lake exe census --standard ecma262` `` | the projection gate, which refuses before touching a file |
| 22 (warnings) | `declaration uses 'sorry'` | the auxiliary declarations of the same `#guard`s; under the package's `warningAsError = true` these are errors in a `lake build` and the same class |

The last line is the packet's own refusal, not a Lean error class. The one
`#guard` in the battery that passes today is the R-P3 collision statement
`Gates.Census.kebab "sec-promise.resolve" == Gates.Census.kebab
"sec-promise-resolve"`, which records the defect the escaping repairs.

The frozen row table, the header literal, the counts and the whole gate body
elaborate cleanly today; the gate's logic was exercised end to end against
`generated/spec-algorithm-census.tsv` with a throwaway probe module before this
packet was frozen, and that probe was removed.

The `Gates/` tree and the semantic/test tree share one axiom ceiling under
ruling R-11, so this battery's elaboration-time command needs no entry in
`WhatwgTest/Audit/AxiomGate.lean`'s `auditImplementationModules`.
