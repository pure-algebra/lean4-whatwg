# Declaration snapshot contract (review lane W, slice W6, the snapshot)

Status: FROZEN / RED, W6 breaker seat, 2026-10-01, on branch
`review/w6-snapshot-breaker`, stacked on the head of
`review/w6-freeze-breaker` (ruling R-W9), whose packet
`test/contracts/freeze-registry.contract.md` this one reads entries from.

Authority: ruling R-W5 of `COORDINATION.md` (binding: the executable
`whatwg_declsnapshot` over the built `.olean` files through the shared loader
of R-W7, writing `generated/declarations/<library>.tsv`, authored records as
`test/records/<packet>.tsv`, anchors as census row ids only, and
`recordedPrefixes` empty at its landing), with R-W7(a), R-W8 and R-W9; the
routing rules of `docs/AGENT-ROUTING.md` ("Public declaration records",
"Existing-type annotation") and `generated/AGENTS.md`. Evidence: sections
2.7, 6.3 and appendix B of
`docs/research/2026-10-01-w6-freeze-registry-design.md`. It closes debt D47's
first half (the snapshot exists and joins); the first prefixes join later.

This packet freezes behaviour. The executable falsifier is the battery
`WhatwgTest/Audit/DeclSnapshotContract.lean`, which exercises the pure core;
the Lean battery is the authority on names, spellings and messages.

## 1. Files and fences

Breaker-owned and frozen by this packet: this file,
`WhatwgTest/Audit/DeclSnapshotContract.lean`, and its block in
`test/fixtures/trust-gate/known-red.txt`.

Builder 2 (R-W8 wave 2b, "the snapshot executable"), after builder 1 of the
freeze command and after the loader `WhatwgGates/Trust/Load.lean` (wave 2a),
implements in this fence and edits none of the files above:

- `WhatwgGates/DeclSnapshot.lean`, new: module `WhatwgGates.DeclSnapshot`,
  namespace `Gates.DeclSnapshot`;
- `whatwgbin/DeclSnapshot.lean`, new, a bare wrapper
  `def main (args : List String) : IO UInt32 := Gates.DeclSnapshot.cli args`;
- in `lakefile.toml`, one `[[lean_exe]]` with `name = "whatwg_declsnapshot"`
  and `root = "whatwgbin.DeclSnapshot"`, and the name in `defaultTargets`;
- one import line in `WhatwgGates.lean` (the module-closure gate requires
  every source to be reachable from the test root, which imports
  `WhatwgGates`);
- the root import `import WhatwgTest.Audit.DeclSnapshotContract` in
  `WhatwgTest.lean` (R-W9);
- the seven files `generated/declarations/*.tsv`, written only by
  `lake exe whatwg_declsnapshot --write`;
- the removal of this packet's `known-red.txt` entry when the battery is
  green.

The CI step that runs `lake exe whatwg_declsnapshot` after `lake build`, and
the rows of the routers that name it, are R-W8 wave 3's ("CI and routing")
unless the coordinator gives them to builder 2. `test/records/` does not
exist at this freeze; the first packet that records declarations creates it
(R-W5: this lane's closing slice, for `Whatwg.Streams.Kernel` and
`Whatwg.Ecma262.Agent`).

## 2. Terms

- *Production module*: a module whose name has `Whatwg` as a prefix under
  `Lean.Name.isPrefixOf` (whole components).
- *Test module*: a module with prefix `WhatwgTest`.
- *Public constant*: a constant whose name is not `Lean.Name.isInternal`
  (private names, `_proof_N`, `_sparseCasesOn_N` and macro-scoped names are
  internal).
- *Authored*: `Lean.findDeclarationRanges?` returns a value for the constant;
  otherwise the constant is *generated* (equation lemmas, `match_N`,
  `casesOn`, `noConfusion` and the like). Measured at the base: 5,678 of
  8,784 public production constants are authored.
- *Entry*: a constant `<m>.frozen.<d>` of a test module `m`, as
  `#whatwg_freeze` adds it (freeze contract, section 6).
- *Record*: a row of `test/records/<packet>.tsv` (section 9); its *id* is
  `<packet>:<name as written>`.
- *Family record*: a record whose name ends `.*`; `P.*` covers exactly the
  names that begin `P.` (strictly below `P`, never `P` itself). Every other
  record is *exact*.
- *Covering record* of a name: its exact record, otherwise the family record
  with the longest prefix that covers it (`coveringRecord?`).
- *Recorded*: a name `n` lies under a recorded prefix `p` when `n == p` or
  `n` begins `p.`, comparing the `Name.toString` texts (`isRecorded`).

## 3. The executable

`lake exe whatwg_declsnapshot [--check | --write]`, entry point
`Gates.DeclSnapshot.cli : List String → IO UInt32`.

- No argument or `--check`: compute the projection and compare it byte for
  byte with the committed files; write nothing.
- `--write`: compute the projection and, when no input refusal and no join
  failure of rules 1 to 8 is found, write every file of it and delete every
  other `*.tsv` under `generated/declarations/`; with a refusal or failure,
  write nothing. It never writes an `AGENTS.md`.
- Any other argument list: a usage line on stderr, exit code 2.
- Exit 0 after a line beginning `PASS declaration snapshot:` that states the
  counts of declarations, libraries, entries and records and the recorded
  prefixes (or `none`); exit 1 after one line beginning
  `FAIL declaration snapshot:` followed by every refusal and failure, one per
  line, never truncated.
- The repository root is found by `Gates.Common.findProjectRoot` from the
  working directory, as every gate does; no environment variable is read.
- The tooling tree never imports `Whatwg` or `WhatwgTest` at compile time:
  `WhatwgGates.DeclSnapshot` imports Lean, `WhatwgGates.Common`,
  `WhatwgGates.Sha256` and `WhatwgGates.Trust.Load` only. Everything it knows
  about the freeze command is the constant names of section 7.
- No `partial`, no `unsafe`; recursion is structural or on fuel; the module
  declares no syntax, macro or elaborator and is not a metaprogramming
  module (`WhatwgGates/AGENTS.md`).

## 4. Loading (the shared loader)

The environment comes from the shared loader `WhatwgGates/Trust/Load.lean`,
which another breaker freezes (R-W7(a); branch `review/w10-load-breaker`).
This packet depends on its behaviour, not its names:

- it imports the built `.olean` files with `loadExts := false`, so no
  audited initializer, parser or elaborator runs in the snapshot's process;
- it refuses, with a failure the snapshot reports and exit code 1, a module
  whose `.olean` is missing or stale against its Lake trace;
- the snapshot asks it for this module set: every module whose source file
  exists under `Whatwg/` or `WhatwgTest/`, plus the umbrella `Whatwg`, minus
  the modules declared in `test/fixtures/trust-gate/known-red.txt`. Not the
  closure of `WhatwgTest.lean`: a battery the root does not import still
  contributes its entries, which is the repair of `FREEZE-CE-004`.

Measured in scratch with `Lean.importModules` directly (the loader does not
exist yet): 207 modules load in 2.6 s, and `Lean.findDeclarationRanges?` and
`Lean.collectAxioms` both work with `loadExts := false`. If the frozen loader
cannot load an arbitrary module set, or cannot load modules the root does not
import, that is reported to the coordinator, not worked around here by a
second loader.

## 5. The walk

For every loaded production module `m`, for every public constant `c` of
`m`'s own constants (`env.header.moduleData[i].constNames`), one `Decl`:
name `c`, module `m`, kind `kindOf` of its `ConstantInfo` (`axiom`,
`definition`, `theorem`, `opaque`, `quotient`, `inductive`, `constructor`,
`recursor`), authored as section 2 defines, the number of its universe
parameters, `typeDigest` of its type (section 8), and its
`Lean.collectAxioms` set sorted by `Lean.Name.lt`.

A production module that `libraryOf` maps to no library is an input refusal:
`declaration snapshot: input: module <m> belongs to no library of
Gates.DeclSnapshot.libraries`.

For every loaded test module `m` and every constant `k` of `m`'s own
constants with `entryDeclaration? m k = some d`, the entry is
`decodeEntry m (value of k)`. An entry that does not decode, or whose decoded
declaration is not `d`, is an input refusal (`declaration snapshot: input:
entry <k>: <reason>`). Entries are read by constant name only: no environment
extension and no `#whatwg_freeze` code is consulted.

Measured in scratch over the base plus this lane's freeze battery: 8,784
public production constants (3,317 theorems, 4,236 definitions, 143
inductive types, 944 constructors, 144 recursors), the ten entries of
`WhatwgTest.Audit.FreezeContract` decoded with no refusal, and the walk in
62 s interpreted. The design measured 26 s compiled, 23 of them in
`collectAxioms`.

## 6. The projection

One file per library of `libraries`, in that order:
`generated/declarations/<library>.tsv` for `Whatwg` (the umbrella module
only), `WhatwgInfra`, `WhatwgEcma262`, `WhatwgWebIdl`, `WhatwgUrl`,
`WhatwgHtml` and `WhatwgStreams`. Every file is written, with zero rows when
its library declares nothing.

Each file is LF-terminated lines:

1. the header
   `#declarations format=1 generator=Gates.DeclSnapshot library=<library> rows=<n> regenerate=lake exe whatwg_declsnapshot --write`;
2. the column line, `#` then the fourteen column names of `columns` joined by
   tab; then
3. one row per declaration of the library, sorted by the `name` field, then
   by the `module` field, each in ascending `String` order.

A name is not a key; (name, module) is. Lean realizes a generated constant
such as an equation lemma in each module that needs it, so one name can be a
constant of several modules, and each yields its own row. A row belongs to
the library of its module, which for such a constant can differ from the
library its name suggests. Measured at the base: 8,784 rows carry 8,647
distinct names; 69 names are constants of two or more modules (206 rows, all
generated, such as `Whatwg.Ecma262.Jobs.Queue.dequeue.eq_1` in both
`Whatwg.Streams.Readable.Laws` and `Whatwg.Streams.Writable.Laws`), and 17
rows sit in a library other than their name's.

The columns, in order (`renderRow`):

| Column | Value |
| --- | --- |
| `name` | `Name.toString` of the declaration |
| `module` | its module |
| `kind` | `kindOf` |
| `origin` | `authored` or `generated` |
| `universes` | the count of universe parameters, decimal |
| `type-sha256` | `typeDigest` of the type |
| `axioms` | the axiom set, `Name.lt` order, joined by `,`; `-` when empty |
| `frozen-by` | the recording modules of its entries, `Name.lt` order, joined by `,`; `-` when none |
| `mask` | `M1`, `M2` or `none:<reason>`, from the first of its entries in `frozen-by` order that has a mask clause; `-` when none has |
| `anchor` | the same rule over the entries' `anchor` clauses |
| `graph` | the same rule over the entries' `graph` clauses |
| `counterexamples` | the union of its entries' ids, sorted in `String` order, joined by `,`; `-` when empty |
| `record` | the id of its covering record; `-` when none |
| `route` | that record's `route`; `-` when none |

Every field value passes through `escapeField` (`\` to `\\`, tab to `\t`, LF
to `\n`, CR to `\r`, `,` to `\,`), each list element separately; `-` marks
absence and is never escaped. The files carry no absolute path and no
timestamp. Measured in scratch: 1,570,133 bytes over the seven files, and two
runs wrote byte-identical files.

## 7. Entries and their decoding

An entry's value is `WhatwgTest.Audit.Freeze.Entry.mk` applied to exactly six
arguments, in the forms `Lean.toExpr` produces at the pinned toolchain
(freeze contract, section 6). `decodeEntry recording value` reads:

- a name as `Lean.Name.anonymous`, `Lean.Name.mkStr1` to `Lean.Name.mkStr8`
  applied to that many string literals, `Lean.Name.str p s` or
  `Lean.Name.num p n` (`decodeName`; `n` a raw literal or `OfNat.ofNat` of
  one);
- an option as `Option.none α` or `Option.some α x`, a list as `List.nil α`
  or `List.cons α x xs`, a string as a string literal;
- a mask as `WhatwgTest.Audit.Freeze.ObservationMask.chunksAndOutcome`
  (`M1`), `….settlementOrder` (`M2`), or `….notApplicable` applied to a
  string literal (`none:<reason>`).

Any other shape is refused with a reason; the whole value of another shape
with `the value is not WhatwgTest.Audit.Freeze.Entry.mk applied to six
fields`. `EntryData` mirrors `Entry` on the tooling side, which cannot import
`WhatwgTest`; the mask is carried as its column spelling.

## 8. The type text and its digest

`typeDigest e` is `Gates.Sha256.hexDigestOfString (typeText e)`, SHA-256 of
the UTF-8 bytes of a canonical text, through the proved `hash` package.
`Expr.hash` is never used: it keeps 32 bits. `typeText` is total and
structural:

| Expression | Text |
| --- | --- |
| bound variable `i` | `#i` |
| free variable, metavariable | `fvar`, `mvar` (neither occurs in a declared type) |
| sort `l` | `(S <level>)` |
| constant `c` at levels `ls` | `(C <c> [<levels joined by a space>])` |
| application | `(A <function> <argument>)` |
| `fun`, `∀` | `(L <name> <binder> <type> <body>)`, `(P …)` |
| `let` | `(E <name> <h or l> <type> <value> <body>)`, `h` when `nonDep` |
| natural literal | `(N <decimal>)` |
| string literal | `(T <UTF-8 byte length> <the string>)` |
| metadata | the text of the inner term |
| projection | `(J <structure> <index> <term>)` |

Binder codes are `d` default, `i` implicit, `s` strict implicit, `c`
instance implicit. Levels: `0`, `(s <l>)`, `(max <a> <b>)`, `(imax <a> <b>)`,
`(p <name>)`, `?`. Names are `Name.toString`. Unlike the freeze judgment,
the digest keeps binder names, binder annotations and the `let`/`have` flag,
so the snapshot records changes a freeze accepts (freeze contract, section
13). The battery pins one digest against an independent .NET SHA-256.

## 9. Authored records

`test/records/<packet>.tsv`, breaker-owned, frozen with its packet, LF only
(a CR byte anywhere refuses the file). Lines that are empty or begin `#` are
ignored; every other line is one record of exactly ten tab-separated,
non-empty fields:

| Field | Value |
| --- | --- |
| `name` | a full declaration name, or a family `<prefix>.*`; no other `*` |
| `owner` | the owning seat or packet |
| `role` | one of `roles`: `canonical`, `view`, `adapter`, `separate-calculus`, `derived`, `helper`, `foreign-boundary`, `target-only` |
| `related` | `-` exactly when the role is `canonical`; otherwise the full name of the related public declaration |
| `anchor` | `-`, or a census row id (section 10) |
| `anchor-sha256` | `-` exactly when the anchor is `-`; otherwise the row's span digest, 64 lowercase hexadecimal digits |
| `disposition` | `-` exactly when the anchor is `-`; otherwise one of `owned`, `requirement`, `foreignBoundary`, `hostOnly`, `refused`, `evidenceOnly`, `targetOnly` (`SPEC-MANIFEST.md`) |
| `contract` | `test/contracts/<name>.contract.md` |
| `battery` | the module of the packet's battery, under `WhatwgTest` |
| `route` | the assurance route: a proof-graph id, or a leaf-receipt id marked `standalone` or linked to its parent edge |

A record precedes the declaration it names, so it is text, not a Lean
reference. `parseRecords packet text` refuses, with the battery's frozen
messages: a wrong field count, an empty field, a malformed name, an unknown
role, a related owner inconsistent with the role, an anchor without its
digest or the reverse, a malformed digest, an unknown disposition, a
disposition inconsistent with the anchor, a contract or battery of the wrong
shape, a name recorded twice in one file, and a CR byte. Across files,
`duplicateRecords` refuses one name recorded by two records.

## 10. Census anchors

Anchors are census row ids only (R-W5), never packet-local labels. The census
rows are those of every `generated/*-census.tsv` (today five files, 1,109
rows), read by `parseCensus`, which accepts the two projection formats of
the tree: a `#census ` header with `|`-separated rows (id in field 2, span
digest in field 6) and a `#url-census ` header with tab-separated rows and
`#` comment lines (id in field 2, `span-sha256` in field 5); any other header
is refused. `duplicateCensusIds` refuses an id that occurs twice across the
files; none does at the base.

## 11. The nine join failures

Each is a pure function of the `JoinInput` (rules 1 to 8) or of two file
lists (rule 9), returning one message per failure; `joinFailures` is rules 1
to 8 concatenated in order. The messages are frozen by the battery; `<id>` is
a record id, `<n>` a declaration name, `<e>` an entry constant.

| Rule | Function | Fails when | Message |
| --- | --- | --- | --- |
| 1 | `unrecordedTypes` | an authored `inductive` under a recorded prefix has no exact record | `declaration snapshot: rule 1: exported type <n> of <module> under a recorded prefix has no exact record` |
| 2 | `uncoveredDeclarations` | a public declaration under a recorded prefix, authored or generated, has no covering record | `declaration snapshot: rule 2: exported declaration <n> of <module> under a recorded prefix has no covering record` |
| 3 | `danglingRecords` | a record whose name (or family prefix) is under a recorded prefix covers no declaration, and its battery is not in `known-red.txt` | `declaration snapshot: rule 3: record <id> names no declaration, and its battery <module> is not declared red` |
| 4 | `sharedAnchors` | two or more records carry one census row id | `declaration snapshot: rule 4: census row <row> is claimed by <k> records: <ids, sorted>` |
| 5 | `orphanRelations` | a non-canonical record's related name has no exact record | `declaration snapshot: rule 5: record <id> relates to <related>, which has no exact record` |
| 6 | `unknownAnchors` | a record anchor is no census row id; a record's digest differs from the row's; an entry anchor is no census row id | `declaration snapshot: rule 6: record <id> anchors <row>, which is no census row id`; `… record <id> anchors <row> at <digest>; the census span digest is <digest>`; `… entry <e> anchors <row>, which is no census row id` |
| 7 | `unrecordedEntries` | an entry's declaration is under a recorded prefix and has no exact record | `declaration snapshot: rule 7: entry <e> freezes <n>, which has no exact record` |
| 8 | `disagreeingEntries` | two entries for one declaration carry different mask, anchor or graph clauses (an entry without the clause disagrees with nothing) | `declaration snapshot: rule 8: the entries for <n> in <modules, Name.lt order> disagree on the <mask, anchor or graph>` |
| 9 | `byteDrift` | a projection file is missing, differs, or a committed `generated/declarations/*.tsv` is not one the generator writes | `declaration snapshot: rule 9: <path> is missing; run lake exe whatwg_declsnapshot --write`; `… <path> differs from a fresh regeneration; run …`; `… <path> is not a projection this generator writes` |

Rules 1, 2, 3 and 7 bind only under `recordedPrefixes`; rules 4, 5, 6 and 8
bind every record and every entry, the entries of battery fixtures (names
outside `Whatwg`) included; rule 9 binds every file.

## 12. `recordedPrefixes` and how a prefix joins

`Gates.DeclSnapshot.recordedPrefixes : List String` is `[]` at the landing
(R-W5), so rules 1, 2, 3 and 7 bind nothing and the others bind everything.
A prefix joins by a later breaker packet that, in one change: adds the prefix
to the list; adds `test/records/<packet>.tsv` with an exact record for every
authored `inductive` under it and a covering record for every public
declaration under it; and regenerates the projection. The prefix names a
namespace under `Whatwg` that covers at least one declaration. A prefix leaves
the list only by a ruling. The first to join are `Whatwg.Streams.Kernel` and
`Whatwg.Ecma262.Agent`, in this lane's closing slice (R-W5); each graph's
identity edge closes when its prefix joins. As with R-V1's strict prefixes,
the list is data in the generator, not an authored document.

## 13. Public declaration record

All in `WhatwgGates.DeclSnapshot`, namespace `Gates.DeclSnapshot`, owner this
packet for the statement and builder 2 for the implementation; tooling under
R-11's ceiling, no specification anchor, disposition not applicable;
assurance route: this contract and its battery, as for the census (R-W5).
Signatures as the battery ascribes them.

| Declaration | Signature | Role |
| --- | --- | --- |
| `Decl`, `Decl.mk` | `Lean.Name → Lean.Name → String → Bool → Nat → String → List Lean.Name → Decl` (name, module, kind, authored, universes, typeDigest, axioms) | canonical: one walked declaration |
| `EntryData`, `EntryData.mk` | `Lean.Name → Lean.Name → Option (List Lean.Name) → Option String → Option String → Option String → List String → EntryData` (recording, declaration, axioms, mask, anchor, graph, counterexamples) | adapter of `WhatwgTest.Audit.Freeze.Entry` on the tooling side |
| `Record`, `Record.mk` | eleven `String` fields: packet, name, owner, role, related, anchor, anchorDigest, disposition, contract, battery, route | canonical: one authored record |
| `CensusRow`, `CensusRow.mk` | `String → String → CensusRow` (id, digest) | helper |
| `JoinInput`, `JoinInput.mk` | `List String → Array Decl → Array EntryData → Array Record → Array CensusRow → List String → JoinInput` (recordedPrefixes, decls, entries, records, census, knownRed) | helper: everything the join reads |
| `Row`, `Row.mk` | fourteen fields in column order; `universes : Nat`, the four list columns `List String`, the rest `String` | canonical: one projection row |
| `formatVersion`, `regenerateCommand`, `outputDirectory`, `recordsDirectory` | `String`: `"1"`, `"lake exe whatwg_declsnapshot --write"`, `"generated/declarations"`, `"test/records"` | helper |
| `recordedPrefixes` | `List String`, `[]` | canonical |
| `libraries` | `List (String × Lean.Name)` | canonical: the seven libraries |
| `roles`, `dispositions`, `columns` | `List String` | helper vocabularies |
| `libraryOf` | `Lean.Name → Option String` | helper |
| `escapeField` | `String → String` | helper |
| `levelText`, `typeText`, `typeDigest` | `Lean.Level → String`, `Lean.Expr → String`, `Lean.Expr → String` | canonical: the type digest |
| `kindOf` | `Lean.ConstantInfo → String` | helper |
| `isRecorded` | `List String → String → Bool` | helper |
| `entryDeclaration?` | `Lean.Name → Lean.Name → Option Lean.Name` | helper: the freeze naming rule, inverted |
| `decodeName`, `decodeEntry` | `Lean.Expr → Except String Lean.Name`, `Lean.Name → Lean.Expr → Except String EntryData` | canonical: entry decoding |
| `parseRecords`, `parseCensus` | `String → String → Except String (Array Record)`, `String → Except String (Array CensusRow)` | canonical: the authored inputs |
| `duplicateRecords`, `duplicateCensusIds` | `Array Record → Array String`, `Array CensusRow → Array String` | input refusals |
| `coveringRecord?` | `Array Record → String → Option Record` | helper |
| `rows`, `renderRow`, `renderFile`, `projection` | `JoinInput → Array Row`, `Row → String`, `String → Array Row → String`, `JoinInput → List (String × String)` | canonical: the projection |
| `unrecordedTypes`, `uncoveredDeclarations`, `danglingRecords`, `sharedAnchors`, `orphanRelations`, `unknownAnchors`, `unrecordedEntries`, `disagreeingEntries` | `JoinInput → Array String` | canonical: join rules 1 to 8 |
| `byteDrift` | `List (String × String) → List (String × String) → Array String` | canonical: join rule 9 |
| `joinFailures` | `JoinInput → Array String` | helper: rules 1 to 8 in order |
| `cli` | `List String → IO UInt32` | canonical: the only function that does IO |

`Decl`, `EntryData`, `Record`, `CensusRow` and `Row` derive `BEq` and
`Inhabited` at least (the battery compares and defaults them). Any other
declaration the module needs is `private` or an instance.

## 14. Claim scope

- A PASS means: the loaded environment's public production declarations,
  their type digests, axiom sets and entries render to the committed bytes,
  and the records, entries and census rows join under rules 1 to 8. It
  does not mean a declaration is correct, covered, or proved; the snapshot
  reads no proof and judges no statement (the freeze command does that).
- Records under no recorded prefix are parsed and checked by rules 4, 5 and
  6 only; a declaration under no recorded prefix needs no record.
- Graph ids and counterexample ids are carried, not joined: graphs are W7's,
  counterexample ids slice W6b's (debts D45 and D50).
- Docstrings, attributes, declaration ranges' positions and value bodies are
  not in the projection; a body change that keeps the type and the axiom set
  leaves the projection unchanged.
- The type digest is of the declared type at the pinned toolchain: a
  toolchain change that alters elaboration may change digests with no
  source change, and the drift check reports it.
- The snapshot trusts the loader's staleness verdict; it does not re-derive
  Lake traces.
- Entries are read only from modules the loader loads; the modules declared
  red are not loaded, so their entries are absent until they are green.

## 15. Validation status (R-W9)

| Item | Status |
| --- | --- |
| every `#guard` of the battery (sections 1 to 6, the nine rules and both accepted controls) | run in scratch: a scratch `WhatwgGates/DeclSnapshot.lean` implementing this contract's pure core made the battery elaborate with exit 0 |
| the battery's power | run in scratch: nine mutants of that core (rule 3 ignoring `known-red.txt`, rule 8 treating an absent clause as a value, no comma escaping, binder codes dropped, rule 1 satisfied by a family, rule 2 exempting generated declarations, a family covering its own prefix, rule 6 skipping entries, names read only as `Name.mkStr`) each fail at least one `#guard` |
| the walk, loading, entry decoding and the projection over the real tree | run in scratch with `Lean.importModules` in place of the loader: 207 modules, 8,784 declarations, the ten entries of the freeze battery decoded, 1,109 census rows parsed, no join failure with `recordedPrefixes` empty, 1,570,133 bytes, and two runs byte-identical |
| the loader's behaviour (section 4) | unprobed: the loader is another packet's |
| `cli`'s modes, exit codes, PASS and FAIL lines, deletion of stale files | unprobed: the battery ascribes `cli` only |
| the compiled run time | probed by the design (26 s); not re-measured |

## 16. Deviations from the design and the ruling

- D1. The design's columns are kept, with `origin` spelled `authored` or
  `generated`, `universes` a count, and `record` and `route` from the
  covering record. The design's "two entries that disagree" is read as two
  entries that both carry the clause with different values.
- D2. Records gain a `battery` column, which rule 3's known-red exception
  needs, and the anchor and disposition columns are tied (`-` together).
- D3. Rule 6 also checks entry anchors, and every census projection is read,
  including the URL census's own format; an id in two censuses is an input
  refusal, so an anchor never names an ambiguous row.
- D4. The loaded module set is every source module, not the root's closure,
  so that an unimported battery's entries are seen (`FREEZE-CE-004`).
- D5. Two input refusals beyond the nine rules are pure and frozen:
  `duplicateRecords` and `duplicateCensusIds`.
- D6. Rows are keyed by (name, module), not by name: the scratch walk found
  generated constants realized in several modules (section 6), which the
  design's appendix B, sorting whole lines, did not separate. Rules 1 and 2
  name the module in their messages for the same reason.

## 17. Red state at the freeze

Narrow command:

```text
lake build WhatwgTest.Audit.DeclSnapshotContract
```

At the freeze it fails because `WhatwgGates.DeclSnapshot` does not exist, and
for no other reason:

```text
✖ [2/3] Running WhatwgGates.DeclSnapshot
error: no such file or directory (error code: 4294963238)
  file: …\WhatwgGates\DeclSnapshot.lean
✖ [3/3] Running WhatwgTest.Audit.DeclSnapshotContract
error: WhatwgTest\Audit\DeclSnapshotContract.lean: bad import 'WhatwgGates.DeclSnapshot'
Some required targets logged failures:
- WhatwgGates.DeclSnapshot
- WhatwgTest.Audit.DeclSnapshotContract
```

Lake lists the missing module as a failing target of its own, which the trust
self-test can neither ignore nor excise (freeze contract, section 14).

The default `lake build` on this branch fails on exactly the two batteries of
the two stacked packets and the two modules they import, and on nothing else.
In that run Lake replayed the root `WhatwgTest` ("checked 222 source files
and 16723 declarations"), so its module-closure gate never saw the two
batteries the root does not import: `FREEZE-CE-004`, observed again. Section
15's scratch implementation, and the freeze prototype used to build entries
for the scratch walk, were removed before the commit with their build
products.
