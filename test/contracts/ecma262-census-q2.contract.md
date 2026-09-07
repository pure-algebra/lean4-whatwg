# ECMA-262 census Q2 addendum (P8-C2a)

Status: FROZEN / RED, Q2 census breaker seat, 2026-09-07, based on
`e819a9f` (`main`, the Q1 landing plus ratification R-P17).

This packet is an **addendum** to `test/contracts/ecma262-census.contract.md`,
not a replacement, on the pattern the P5a lifecycle and exact addenda
established over `test/contracts/writable-default.contract.md`. The base
packet stays byte-identical to its frozen form. Where the two disagree, the
disagreement is listed in section 1 with its date and reason and this file
wins; everything the base packet states and this file does not name is
unchanged and still binding.

Read `test/contracts/webidl-census-q2.contract.md` first: it freezes the
`Gates.Census.cli` signature change and the report obligations that both
standards share, and this packet does not restate them.

Its authority is review debt D4 of `COORDINATION.md` and the five acceptance
conditions of the "Q2 — dispositions, dependency and external rows, coverage
blocks" section of `docs/PROMISE-PACKAGE-PLAN.md`, together with rulings
R-P5, R-P6, R-P11 and R-P13.

The battery this packet freezes is
`WhatwgTest/Audit/Ecma262/CensusQ2Contract.lean`. The builder may repair
elaboration but may not weaken, delete or replace a frozen count, disposition,
signature or refusal.

## Claim boundary

This is a tooling contract, exactly as the base packet is. Nothing here grants
an ECMAScript semantic claim, an observation mask, a coverage state above
`absent`, a host observation, or any statement about `Whatwg.Ecma262`. In
particular amendment 1.1 does **not** decide DB-03, does not assert that
`Whatwg.Ecma262.Promise.State` exists, and does not give
`clause.promise-objects` a witness: it moves one row into the denominator, so
that the row can be *owed* a witness. Owed is not held.

The block of section 4 is all-`absent`; quoting it as coverage is a defect.

Offsets are 0-based byte offsets into `vendor/ecma262-0248456c/spec.html`
(2,978,793 bytes, SHA-256
`ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0`); ends are
exclusive; no line number is cited anywhere.

## 1. Q2 amendment

One amendment. No other statement of
`test/contracts/ecma262-census.contract.md` changes; in particular the 77
rows, their spans, anchors and digests, the per-kind counts, the 22 scanner
probes and the 14 escaping probes are untouched, and this addendum adds no
row.

### 1.1 (2026-09-07, debt D4) `clause.promise-objects` moves from `evidenceOnly` to `owned`

**The coordinator's decision to record.** The reviewer's argument is adopted.
`clause.promise-objects` is the row for the clause at 2686444–2746707, digest
`21deb38546b2e5e928888349f91a40a16074a8cfa7f91469a0aec56c5bc7e9e0`. Its own
prose — the part of the clause that is not one of its child clauses — is the
promise state vocabulary: *fulfilled*, *rejected*, *pending*, and the
*settled* / *resolved* / *unresolved* distinctions. That vocabulary is exactly
what `Whatwg.Ecma262.Promise.State` realizes under ruling R-P13, which fixes
the type as two-parameter over value and reason with `Readable.PromiseState`
becoming an `abbrev` of it. A clause whose content a declaration realizes is
not evidence for something else; it is a row the model answers to, and
`docs/SPEC-COVERAGE.md` puts such a row in the denominator so it can be owed a
witness. Under `evidenceOnly` it is outside the denominator, where no witness
is ever owed — which would have left the one clause `State` answers to
permanently unaccountable and understated the lane's denominator by one.

**Its two siblings stay `evidenceOnly`, and that is the point of the
amendment.** `clause.promise-abstract-operations` (2687651–2702809) and
`clause.promise-jobs` (2702815–2707559) are bare headings: their own prose is
a section title and nothing else, and every operation under them is already
its own `op` row with its own disposition. Ruling R-P5's blanket
`evidenceOnly` for "the settled/resolved vocabulary and two headings" read all
three the same way; this amendment separates the one clause that carries text
a declaration realizes from the two that carry none. A future re-reading that
promotes either sibling has to say what its own prose is.

**How it is authored.** By changing the disposition on the one line
`sec-promise-objects	clause	evidenceOnly` of `census/ecma262/dispositions.tsv`
to `owned`, **not** by an entry in `census/ecma262/overrides.tsv`.
`Gates.Census.finishBuild` credits an overridden row to the override alone, so
an override would leave that line matching no row and generation would fail
with `census/ecma262/dispositions.tsv: sec-promise-objects clause matches no
row`. The `(clause id, kind)` key `sec-promise-objects` × `clause` reaches
exactly one row — `clause.promise-objects` itself, because
`Gates.Census.clauseAncestry` resolves every other `clause` row at its own
innermost enclosing clause — so the two readings coincide on the row set and
only the authored form is admissible. The two sibling lines are untouched, and
`census/ecma262/overrides.tsv` keeps exactly its three Q1 entries.

**Superseded.** Section 6 of the base packet, in the `owned` and
`evidenceOnly` rows of its disposition table, in its denominator, and in the
sentence "The three `evidenceOnly` rows are `clause.promise-objects`,
`clause.promise-abstract-operations` and `clause.promise-jobs`", which now
names two rows and not three. The base packet's section 10 acceptance
condition 4 is superseded by section 2 below. Nothing else moves.

## 2. The new frozen totals

Superseding section 6 of the base packet. The row total, the per-kind counts
and every span, anchor and digest of the base packet's section 9 are
unchanged: 77 rows as `builtin` 13, `clause` 8, `field` 8, `hook` 6, `op` 16,
`property` 3, `record` 3, `requirement` 9, `slot` 5, `term` 6, with `idl`,
`rule` and `type` zero.

| disposition | rows (Q1) | rows (Q2) | primary | sub-rows |
| --- | ---: | ---: | ---: | ---: |
| `owned` | 44 | **45** | **32** | 13 |
| `foreignBoundary` | 13 | 13 | 6 | 7 |
| `hostOnly` | 10 | 10 | 7 | 3 |
| `requirement` | 7 | 7 | 2 | 5 |
| `evidenceOnly` | 3 | **2** | **2** | 0 |
| `refused`, `targetOnly` | 0 | 0 | 0 | 0 |
| **denominator** | 74 | **75** | | |
| **excluded** | 3 | **2** | | |

45 + 13 + 10 + 7 + 2 = 77, and 77 − 2 = 75. The 49 primary rows split
32/6/7/2/2 and the 28 sub-rows 13/7/3/5/0, both unchanged apart from the one
row that moved between the first and the last primary column.

R-P5's other record stands unchanged: the five promise instance slots are
`owned` here while the Streams census keeps the same named slots
`foreignBoundary`, because the two censuses describe two libraries.

The exact `lake exe census --standard ecma262` output, both lines, exit 0:

```text
census: 77 rows (idl 0, op 16, requirement 9, rule 0, slot 5, type 0, builtin 13, hook 6, property 3, record 3, field 8, term 6, clause 8); dispositions (owned 45, requirement 7, foreignBoundary 13, hostOnly 10, refused 0, evidenceOnly 2, targetOnly 0); denominator 75, excluded 2; 0 IDL statement(s) outside the row vocabulary
PASS census (ecma262): input digest is the pin, every anchor occurs exactly once at its span start, every span digest recomputes, every row has exactly one disposition, both projections are byte-identical to a fresh regeneration, and the coverage emit agrees with that regeneration row for row
```

The PASS line's tail changes from Q1's "; no numerator exists for this
standard yet, so no emit was checked" because section 3 gives this standard a
numerator. The frozen census header line does **not** change: the row count
stays 77.

```text
#census format=1 generator=Gates.Census input=vendor/ecma262-0248456c/spec.html input-sha256=ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0 rows=77 regenerate=lake exe census --standard ecma262 --write
```

`WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean` keeps `rowTotal 77`, records
`denominator 75`, and its entry for the moved row reads

```text
  ⟨"clause.promise-objects", .owned, .absent, []⟩,
```

while its two siblings keep

```text
  ⟨"clause.promise-abstract-operations", .evidenceOnly, .absent, []⟩,
  ⟨"clause.promise-jobs", .evidenceOnly, .absent, []⟩,
```

## 3. The numerator and the report (Q2 acceptance 4)

The `Gates.Census.cli` signature change, the map from standard key to emit,
the `bin/Census.lean` shape and the refusal that must remain for
`--standard infra --report` are frozen in section 6 of
`test/contracts/webidl-census-q2.contract.md` and are not restated here. This
packet freezes the `ecma262` half:

| Item | Freeze |
| --- | --- |
| Module | `WhatwgTest.Audit.Ecma262.SpecCoverage`, at `WhatwgTest/Audit/Ecma262/SpecCoverage.lean` |
| Emit | `def emit : Array CoverageRow` under `open Gates.Census`, that is `Array Gates.Census.CoverageRow`, the exact type the Streams emit has |
| Content at Q2 | `emit` is `SpecCoverageRows.rows`: one entry per census row, carrying the census row id and the joined disposition, state `absent`, witness list empty |
| Totals beside it | `expectedRowTotal := 77` and `expectedDenominator := 75`, so that a census change that invalidates the freeze is repaired in the same edit |
| Map entry | `("ecma262", WhatwgTest.Audit.Ecma262.SpecCoverage.emit)` in `bin/Census.lean`, with `import WhatwgTest.Audit.Ecma262.SpecCoverage` |

Nothing in the module may set a state above `absent` or attach a witness at
Q2. Q3 is the slice that lands the first witness; until then
`Gates.Census.verifyEmit` refuses a witness on an `absent` row, and every one
of the 77 rows is `absent`.

The report is printed from the emit and never from
`SpecCoverageRows.lean` directly, because `Gates.Census.verifyEmit` re-derives
ids, order and dispositions from a fresh regeneration before `report` prints a
number. That is what makes the block of section 4 a checked fact rather than a
transcription, and it is why `check` for this standard now also runs the emit
comparison.

## 4. The exact expected block text

In the format of `docs/SPEC-COVERAGE.md` — three lines, broken after
`owned-with-green <O>/<D>;` and after `<E> excluded`, third line `partial:`
with nothing after it. This replaces the ECMA-262 placeholder block under
"Blocks not yet emitted".

```text
ECMAScript ES2026 (0248456c) coverage: denominator 75; owned-with-green 0/75;
green 0, partial 0, absent 75; census 77 rows, 2 excluded
partial:
```

The label is `Gates.Census.ecma262.label` and is not authored here. The block
is all-`absent`: `owned-with-green 0/75` and `green 0` are the whole content
of the claim. 75 rows are owed a witness and none has one.

## 5. Acceptance

Q2's five acceptance conditions, restated for this standard as checkable
assertions, with the battery clause that checks each. Conditions already
checked by a Q1 battery are named rather than duplicated.

1. **Every row resolves to exactly one disposition with no generator default,
   and every authored entry reaches at least one row, in both directions.**
   Enforced by `Gates.Census.finishBuild` and observable in the projection.
   The battery checks the row total 77, the per-kind counts, the amended
   per-disposition counts of section 2 and the three named `clause` entries
   above against `WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean`, which are
   reachable only if all 52 `dispositions.tsv` entries, all 3 `overrides.tsv`
   entries and both `sections.tsv` roots resolved. It additionally asserts
   that `census/ecma262/overrides.tsv` still carries exactly its three Q1
   entries and does **not** carry one for `clause.promise-objects`, which is
   amendment 1.1's authored form.
2. **Exactly one dependency list per row; every external identity is used; no
   dependency names an unresolvable target.** The battery re-checks all three
   independently of `Gates.Census.checkDependencies`, over
   `census/ecma262/dependencies.tsv`, `census/ecma262/externals.tsv` and
   `generated/ecma262-census.tsv`: one line per census row and one census row
   per line; every declared `ext.` identity named by at least one line; every
   named target an in-census row id or a declared external. This standard has
   an empty `crossCensusPaths`, so a target that is neither is a failure with
   no third case. No dependency line and no external identity changes under
   this addendum: it adds no row.
3. **The disposition totals agree with the `SPEC-MANIFEST.md` ECMA-262
   table.** Section 2 is that agreement, as amended by 1.1. The manifest's
   `sec-promise-objects, sec-promise-abstract-operations, sec-promise-jobs`
   row and its "ruled totals" paragraph are the coordinator's to repair under
   debt D1; a disagreement is repaired there or in the authored input, never
   by relabelling a row to make a total come out.
4. **Both coverage blocks emit all-`absent` from the Lean emit.** The battery
   asserts the `Gates.Census.cli` signature by ascription, the numerator
   module and the `bin/Census.lean` map entry of section 3 by their frozen
   source text, and the exact block of section 4 as a substring of
   `docs/SPEC-COVERAGE.md`.
5. **The two anchor-ladder rows are checked against the real
   `Gates.Census.chooseAnchorLength`.** *Already checked; not duplicated.*
   `WhatwgTest/Audit/Ecma262/EcmarkupScanner.lean` carries
   `anchorLengthProbes`, which runs the real ladder over
   `field.jobcallback-records.HostDefined` at span start 629941 and asserts
   256, and over `field.promisecapability-records.Promise` at 2688749 and
   asserts 64. Those are the two rows the plan names as
   `field.job-callback-record.host-defined` (span 629941..630193) and
   `field.promise-capability-record.promise` (span 2688749..2688997) under the
   survey's id scheme: same spans, the ids the census landed. The same probe
   list carries the lane's shortest anchor, `term.%Promise%` at 2707710 with
   24 bytes and not the survey's 20. This battery asserts that those three
   probes are still present with those three lengths and does not re-run them.

Two conditions carried over from the base packet, unchanged: the projection is
strictly increasing in `kind.name ++ "|" ++ id`, and
`test/contracts/census-profile-identity.contract.md` and
`test/contracts/webidl-census.contract.md` still pass, the latter as amended
by `test/contracts/webidl-census-q2.contract.md`.

## 6. Fence and verification

Frozen breaker files:

- `test/contracts/ecma262-census-q2.contract.md`
- `WhatwgTest/Audit/Ecma262/CensusQ2Contract.lean`
- the `ECMA-CEN-CE-015` … `ECMA-CEN-CE-017` sections of
  `test/counterexamples/ecma262/CENSUS.md`
- the amended frozen totals of `WhatwgTest/Audit/Ecma262/CensusContract.lean`,
  each amended line carrying the addendum and the date in a comment

Red-phase registration: `test/fixtures/trust-gate/known-red.txt`, entries
`WhatwgTest.Audit.Ecma262.CensusQ2Contract` and
`WhatwgTest.Audit.Ecma262.CensusContract`, both removed by the builder the
moment the two batteries are green. The second is declared because this
addendum supersedes totals the Q1 battery froze.

The breaker edits no implementation, no vendored bytes, no generated
projection, no authored census input, no `docs/`, no `SPEC-MANIFEST.md` and no
central counterexample register.

Builder fence: `Gates/Census.lean` (the `cli` signature only),
`bin/Census.lean`, `census/ecma262/dispositions.tsv`,
`WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean`,
`WhatwgTest/Audit/Ecma262/SpecCoverage.lean`, and the `docs/SPEC-COVERAGE.md`
and `SPEC-MANIFEST.md` rows the plan seat and the coordinator own.

Narrow command:

```text
lake build WhatwgTest.Audit.Ecma262.CensusQ2Contract
```

## 7. Freeze receipt

Observed in the breaker's worktree at base `e819a9f`, on Lean 4.33.1, Windows
x64.

This addendum recomputes no span and no digest: it moves one row between two
dispositions and adds no row, so every byte-level fact it relies on is the
base packet's, which the Q1 landing verified row by row against the sealed
bytes. The one span it cites, `clause.promise-objects` at 2686444–2746707 with
digest `21deb38546b2e5e928888349f91a40a16074a8cfa7f91469a0aec56c5bc7e9e0`, was
re-read from `vendor/ecma262-0248456c/spec.html` here and agrees.

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
`WhatwgTest/Audit/Ecma262/CensusQ2Contract.lean`: **2 errors, 0 warnings**.
Both are expected and no other error class appears:

| Count | Diagnostic | Where |
| --- | --- | --- |
| 1 | `Type mismatch`: `Gates.Census.cli` has type `Array Gates.Census.CoverageRow → List String → IO UInt32` but is expected to have type `List (String × Array Gates.Census.CoverageRow) → List String → IO UInt32` | the ascription in section 1 of the battery |
| 1 | `ecma262 census Q2 contract: WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean does not record denominator 75` | the projection gate, which stops at the first amended fact the tree contradicts |

The three ascriptions before that one are green and print their types. The
gate reaches the denominator clause because nothing before it moves under this
addendum: the row total is still 77, the header is unchanged, the sort holds
and the per-kind counts are the Q1 counts.

**How the later clauses were exercised, since the tree cannot satisfy them
yet.** A copy of this battery was retargeted at the Q1 tree — `expectedDenominator
74`, the Q1 disposition counts, `clause.promise-objects` expected
`.evidenceOnly`, the numerator and entry point pointed at
`WhatwgTest/Audit/SpecCoverage.lean` and `bin/Census.lean` as they stand, and
the coverage block at the Q1 placeholder text. It ran to `logInfo` with only
the `cli` ascription still red, printing

```text
ecma262 census Q2 contract: 77 rows, denominator 74, clause.promise-objects re-dispositioned owned against vendor/ecma262-0248456c/spec.html (SHA-256 ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0), 3 overrides unchanged, 77 dependency lines and 41 externals used in both directions, and the all-absent coverage block emitted
```

so every clause of the gate — the projection parse, the strict sort, the kind
counts, the moved row's span and recomputed digest, the rows-module totals and
named entries, the overrides file in both its directions, the whole
two-directional dependency and externals join over 77 rows and 41 identities,
the `anchorLengthProbes` fragments in the Q1 scanner battery, the numerator and
entry-point fragments and the coverage block substring — is exercised end to
end against real data. That copy was deleted before this packet was frozen and
no byte of the tree it read was changed.

The amended `WhatwgTest/Audit/Ecma262/CensusContract.lean` reports, with the
same command, **1 error, 0 warnings**: `ecma262 census contract:
WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean does not record denominator
75`. Its amended lines (`expectedDenominator`, and the `owned` and
`evidenceOnly` entries of `expectedDispositionCounts`) each carry a comment
naming this addendum and the date; no other line of that file changed, and no
frozen row, span, digest, anchor, probe or refusal moved.

Every repository gate still passes at this freeze, unchanged by the packet:
`lake exe vendorseal`, `lake exe citations` (323 files scanned), `lake exe
census` and `--report` (the Streams block unchanged at denominator 410,
green 12, partial 6, absent 392), and `lake exe census --standard` for `infra`,
`webidl` and `ecma262`, the last two still printing their Q1 summaries because
the authored inputs are the builder's and this packet does not touch them.

The `Gates/` tree and the semantic and test trees share one axiom ceiling
under ruling R-11, so this battery's elaboration-time command needs no entry
in `WhatwgTest/Audit/AxiomGate.lean`'s `auditImplementationModules`. This
battery declares no theorem, so it carries no axiom receipt of its own.
