# ECMA-262 census attack shapes

Seeded by the promise census breaker seat, 2026-09-06, alongside
`test/contracts/ecma262-census.contract.md` and its frozen battery
`WhatwgTest/Audit/Ecma262/CensusContract.lean`.

Every attack below is already encoded in that battery: as a `#guard` over a
literal ecmarkup fixture where the attacked behaviour is pure, and as a clause
of the projection gate where it is a property of the generated file. None has a
stable ID yet. The coordinator assigns the `ECMA-CEN-CE-nnn` ids and adds the
rows to `test/counterexamples/REGISTER.md` at landing; the placeholders below
are the order in which they should be assigned. This file adds no row to that
register.

The area token is `ECMA` under the scheme in
`test/counterexamples/README.md`. Witnesses stay in the battery rather than
moving to a `Counterexamples/` module, because each attacks the census
generator rather than a semantic declaration.

The scanner's refusals are checked with an offset-bearing predicate: a probe
passes only when the result is `Except.error` **and** the message contains the
decimal byte offset of the refused construct. That is the one place in this
repository where diagnostic text is part of the contract, and the contract says
so.

## ECMA-CEN-CE-001 — `kebab` collides `Promise.resolve` with `PromiseResolve`

Attacked: `Gates.Census.kebab` as a source of ECMA-262 row ids. It maps every
non-alphanumeric byte to one separator, so the clause ids
`sec-promise.resolve` (27.2.4.7, a built-in function) and `sec-promise-resolve`
(27.2.4.7.1, an abstract operation) both become `sec-promise-resolve`. The
generator would either emit a duplicate row id or silently lose one row.

Encoded as two `#guard`s: the equality of the two `kebab` results, which passes
against the generator as it stands and is the defect itself; and the inequality
of `Gates.Ecmarkup.escapeId "promise.resolve"` and
`escapeId "promise-resolve"`. Forced repair: R-P3's injective escaping, which
preserves `.`, `%` and case. On the frozen row set the two clauses become
`builtin.promise.resolve` and `op.promise-resolve`.

## ECMA-CEN-CE-002 — an id scheme that is not injective loses rows silently

Attacked: any escaping that is not prefix-free. `escapeId` writes a character
outside the safe alphabet as `~`, its lower-case hexadecimal, `~`; `unescapeId`
must invert it exactly and return `none` on anything outside the image.

Encoded as the escaping probes, including `Promise prototype object` →
`Promise~20~prototype~20~object`, `a~b` → `a~7e~b`, the round trip through
`unescapeId`, and the two rejections `unescapeId "a~zz~b" == none` and
`unescapeId "a~20b" == none`.

## ECMA-CEN-CE-003 — an unknown clause `type` is classified as structural

Attacked: `Gates.Ecmarkup.scanClauses`. Exactly three `type` values occur in
scope, and the kind ladder turns an untyped clause into `record`, `property` or
`clause`. A fourth value appearing at a re-pin would be classified as
structural and its operation would vanish from the `op`/`hook`/`builtin`
counts.

Encoded as four acceptance probes over the three observed values and the
untyped case, and one refusal probe: a clause with
`type="grammar production"` is refused at byte 0.

## ECMA-CEN-CE-004 — an unbalanced sectioning element is skipped

Attacked: `Gates.Ecmarkup.scanClauses`' stack machine. An unclosed
`<emu-clause>`, a `</emu-annex>` closing an `<emu-clause>`, and a stack
underflow must each be refused rather than absorbed, because each of the three
silently changes the clause forest and therefore the 49 primary rows.

Encoded as three refusal probes; the first two name byte 0.

## ECMA-CEN-CE-005 — a clause with no `id` or no `<h1>` produces a nameless row

Attacked: `Gates.Ecmarkup.scanClauses`. The row id is the clause id and the
kind ladder reads the `<h1>`, so a clause missing either has no derivable
identity. Both are refused at the opening tag's offset.

## ECMA-CEN-CE-006 — `<emu-alg>` bodies are read as prose

Attacked: any reuse of the Streams line scanners. An `<emu-alg>` body is not
HTML: it is markdown-ish `1. ` lines whose only nesting signal is two spaces
per level, relative to the block's own minimum, and whose literal `1.` is never
an ordinal. All 390 in-scope step lines match, with 0 odd relative indents and
0 level jumps greater than one, so the three refusals are free and permanent.

Encoded as two acceptance probes and three refusal probes: a non-matching line
refused at byte 10, an odd relative indent refused at byte 18, and a level jump
of two refused at byte 18. Both offsets are the first byte of the offending
line.

## ECMA-CEN-CE-007 — an `<emu-alg>` attribute changes what the block means

Attacked: `Gates.Ecmarkup.scanSteps`. All 32 in-scope blocks open with the bare
tag. `example` and `replaces-step` change whether the block is normative and
where its steps belong, so a block carrying any attribute is refused at byte 0
rather than scanned as if it were bare. An unterminated `<emu-alg>` is refused
too.

## ECMA-CEN-CE-008 — a character reference is decoded instead of refused

Attacked: `Gates.Ecmarkup`'s entity-free assumption. The byte `&` occurs zero
times in the two windows, but entities do occur elsewhere in the file, so a
re-pin that moves one into scope must be a visible failure and never a silent
half-decoded excerpt.

Encoded as a refusal probe over an `<emu-alg>` step containing `&amp;`.

## ECMA-CEN-CE-009 — a record table with the wrong shape yields partial rows

Attacked: `Gates.Ecmarkup.scanTableRows`. Every in-scope `<emu-table>` has one
`<thead>` of three `<th>` and body rows of three `<td>`; the first cell is the
`[[Name]]` the row id is taken from and the second is the type phrase. A
two-cell header, a two-cell body row and an unterminated body row must each be
refused, because each would emit a `field` or `slot` row with a missing or
misaligned name.

Encoded as one acceptance probe and three refusal probes.

## ECMA-CEN-CE-010 — a header list with a `dt` other than `description`

Attacked: the structured-header reader. Ten in-scope `<dl class="header">`
carry exactly one `<dt>description</dt>` and eleven are empty; no `For:` and no
`Effects:` `<dt>` occurs. A parser must not require them and must not ignore
one if the pin moves, because `For:` changes which object an operation belongs
to. Refused at the `<dt>` offset.

## ECMA-CEN-CE-011 — the requirement bullets are positional and unlabelled

Attacked: the requirement-row id scheme. None of the nine normative `<li>`
carries an `id`, unlike the Streams piping bullets, so the id is the owner
clause plus a 1-based index and is stable only while the list is. An upstream
reorder relabels rows silently.

Encoded as the nine frozen `requirement.*` rows with their exact spans and
span digests: a reorder changes a digest and fails the packet rather than
passing under a shifted label. The selection rule is itself frozen — a `<ul>`
is a requirement list exactly when its immediately preceding `<p>` contains
`must conform to the` — which admits four of the eleven in-scope `<ul>` and
nine bullets, and excludes the two `sec-jobs` condition lists, the
`sec-host-promise-rejection-tracker` note list, the promise-state list and the
three object-description lists.

## ECMA-CEN-CE-012 — the record name is counted twice

Attacked: the `term` row rule. Nine `<dfn>` occur in scope and three of them
name a record that already has a `record` row, so a naive rule emits 80 rows
instead of 77 and gives `JobCallback Record` two anchors.

Encoded as the frozen `term` count of 6 and the frozen `record` count of 3.

## ECMA-CEN-CE-013 — a 4096-hit cap truncates a file-wide scan

Attacked: `Gates.Census.occurrences`, which stops at its cap without reporting
it. The pinned file is 2,978,793 bytes and the rows live in 2.43 % of it;
`<emu-clause>` occurs 2,189 times and `<emu-alg>` 2,239, both under the cap, but
`<p>`, `<li>` and `<td>` are not. A file-wide scan would silently lose rows.

Encoded as the two-root scope of `sections.tsv`, the acceptance condition that
each root occurs exactly once, and the acceptance condition that a cap hit is
an error.

## ECMA-CEN-CE-014 — the anchor ladder falls through to the rest of the file

Attacked: `Gates.Census.chooseAnchorLength`, whose last resort is
`bs.size - start` — the whole remainder of a 2.9 MB file, not the span. One
in-scope row comes close: `field.jobcallback-records.HostDefined` at 629941 is
separated by no ladder rung below 256, because its `<tr>` opens with the same
indented shape dozens of other record tables use. It resolves at 256, and no
row falls through.

Encoded as the frozen anchor length 256 for that row, the frozen 64 for
`field.promisecapability-records.Promise`, and the contract's statement that no
row falls through to the remainder. This is also where this packet disagrees
with the survey, which reported 252 by clamping a rung to the span length.

## ECMA-CEN-CE-015 — a blanket section label hides the one clause a declaration realizes

Seeded 2026-09-07 by the Q2 census breaker seat, alongside
`test/contracts/ecma262-census-q2.contract.md` and its frozen battery
`WhatwgTest/Audit/Ecma262/CensusQ2Contract.lean`. Review debt D4.

Attacked: the disposition join over the three structural `clause` rows of the
promise subtree. `clause.promise-abstract-operations` (2687651–2702809) and
`clause.promise-jobs` (2702815–2707559) really are bare headings: their own
prose is a section title, and every operation beneath them is already its own
row. `clause.promise-objects` (2686444–2746707) is not. Its own prose is the
promise state vocabulary — fulfilled, rejected, pending, and the settled,
resolved and unresolved distinctions — which is exactly what
`Whatwg.Ecma262.Promise.State` realizes under ruling R-P13. Labelling all
three `evidenceOnly` because two of them are headings puts the one clause the
state type answers to outside the denominator, where no witness is ever owed;
the census still lists it, so the record looks complete while understating the
lane by one row.

Encoded as: the frozen entry
`⟨"clause.promise-objects", .owned, .absent, []⟩` in
`WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean`, the two frozen sibling
entries that stay `.evidenceOnly`, and the frozen totals `owned` 45,
`evidenceOnly` 2, denominator 75. Forced repair: change the disposition of
that one `dispositions.tsv` line and leave the two siblings alone. Recorded
alternative, rejected because it does not generate: an entry in
`census/ecma262/overrides.tsv` would leave `sec-promise-objects clause`
matching no row, and `Gates.Census.finishBuild` fails on an authored entry
that outlived its rows — which is why the battery also asserts that the
overrides file still carries exactly its three Q1 entries and none for this
row.

Owed is not held. This attack moves a row into the denominator so that it
*can* be owed a witness; it grants no coverage state, and the block of the
addendum is all-`absent`.

## ECMA-CEN-CE-016 — a standard with a denominator and no report

Seeded 2026-09-07, Q2 acceptance 4.

Attacked: the reporting path. Since the Q1 landing this standard has a
checked, drift-gated census with a denominator and an all-absent generated row
list, and `lake exe census --standard ecma262 --report` refuses. A denominator
with no sanctioned way to state it is the condition under which a reader
substitutes a row count for coverage, which is the one thing
`docs/SPEC-COVERAGE.md` forbids: "Take exact row counts from the census, never
from this document."

Encoded as: the numerator module `WhatwgTest/Audit/Ecma262/SpecCoverage.lean`
with `def emit : Array CoverageRow`, its `("ecma262", …)` entry in
`bin/Census.lean`'s standard-key-to-emit map, and the exact three-line
all-`absent` block

```text
ECMAScript ES2026 (0248456c) coverage: denominator 75; owned-with-green 0/75;
green 0, partial 0, absent 75; census 77 rows, 2 excluded
partial:
```

which the battery asserts is present in `docs/SPEC-COVERAGE.md` in place of
the Q1 placeholder. `owned-with-green 0/75` and `green 0` are the whole
content of the claim.

## ECMA-CEN-CE-017 — the emit and the census drift apart

Seeded 2026-09-07, Q2 acceptance 4.

Attacked: the direction of trust between the two projections. The generated
`SpecCoverageRows.lean` is Lean data, so it is tempting to print the coverage
block straight from it and let `lake exe census` catch the drift. That is one
gate too late: `--report` is the command a person quotes, and a
`SpecCoverageRows.lean` edited by hand between a regeneration and a report
prints a denominator nothing recomputed. The same hole opens if the emit is
supplied for `--report` but not for the plain check, because then only the
mode nobody runs in CI compares them.

Encoded as: `Gates.Census.verifyEmit` re-deriving ids, order and dispositions
from a fresh regeneration before `report` prints, and the frozen PASS line of
`lake exe census --standard ecma262`, whose tail becomes ", and the coverage
emit agrees with that regeneration row for row" — so the plain check runs the
comparison too. The complementary frozen refusal is
`lake exe census --standard infra --report`, still exit 2: a standard with no
numerator keeps no report rather than acquiring an unchecked one.

## Scope

These are finite tooling probes over a pinned source. They contribute no
ECMAScript semantic theorem, no coverage state, no denominator the numerator
may quote, no host observation and no axiom receipt; in particular none of them
decides DB-03, and `ECMA-CEN-CE-015` decides no promise semantics: it moves one
row into the denominator and stops there. The narrow commands are

```text
lake build WhatwgTest.Audit.Ecma262.CensusContract
lake build WhatwgTest.Audit.Ecma262.CensusQ2Contract
```

and the coordinator owns the full build, the actual axiom receipt and the
repository gates.
