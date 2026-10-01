# W6 design: the freeze registry, 2026-10-01

Status: design record of review lane W, slice W6 (row 6 of
`docs/research/2026-09-30-implementation-review.md`). It recommends; it makes
no Model Claim, closes no graph edge and changes no frozen surface. The
coordinator rules on it (R-W2 onward). Every prototype named below was built
in the seat's worktree or scratch directory and removed before the final
commit; the command's source is appendix A, the snapshot walk appendix B.

| Subject | Pin |
| --- | --- |
| this repository | `97a871522ce18f792449f51300c9d93288abb398` (R-W0, R-W1) |
| lean4-effect4 | `efcf1ae2` (read-only) |
| toolchain | `leanprover/lean4:v4.33.1`, Lake 5.0.0 |

Evidence labels follow the review: `[C]` measured here, with the command;
`[S]` read in source; `[H]` hypothesis not tried.

## 1. Recommendation

One command, `#whatwg_freeze`, in one new listed metaprogramming module,
`WhatwgTest/Audit/Freeze.lean`. A battery keeps today's ascription text byte
for byte; the command word changes and the receipt is appended:

```lean
#whatwg_freeze (@Whatwg.Streams.Writable.sizes_eq :
  Whatwg.Streams.Writable.sizes = Whatwg.Streams.Data.DyadicSize.sizes) axioms [propext]
```

The command elaborates the statement alone and refuses a leftover
metavariable: a hole pins nothing. It compares the result with the declared
type by `sameStatement`, which is `Expr.eqv` plus two allowances, the
`let`/`have` flag and auxiliary `match` definitions compared by their bodies;
nothing else is unfolded. It compares the exact `Lean.collectAxioms` set with the
listed one, a clause required for theorems. Optional clauses carry the mask
(`M1`, `M2`, `none "reason"`), a census row id, a graph edge and
counterexample ids. On success it prints nothing and adds one kernel-checked
declaration `<module>.frozen.<n> : Entry`; a persistent environment extension
is out, because `initialize` declares an `opaque` the gate refuses.

The declaration snapshot (D47) is an executable, `whatwg_declsnapshot`, that
imports the built `.olean` files, walks every constant under `Whatwg`, joins
the registry and authored records (`test/records/<packet>.tsv`), and writes
`generated/declarations/<library>.tsv`; check mode compares bytes. It runs in
26 s compiled, and an executable run is never a cached replay (D49).

Conversion: option (i), every battery, by a Lean conversion pass, one commit
per owner group, after a breaker addendum amends the 12 ascriptions the
strict check refuses (4 holes; 8 written in another, definitionally equal
form). 2,260 of 2,272 pass unchanged in a prototype run. The 957 production
`#print axioms` lines are retired; the build log falls from 9,957 lines to
about 110.

Order: breaker packet (contract, red battery, trust-gate addendum, the 12
amendments); builder 1 (command, list entry); builder 2 (snapshot,
`recordedPrefixes` empty); builder 3 (conversion); reviewer; landing. W6
lands before W7, whose evidence points at `<module>.frozen.<n>`.

## 2. Evidence

### 2.1 The receipt forms at the base

Counted over line starts with `Get-ChildItem -Recurse -Filter *.lean
WhatwgTest | Select-String`, then re-counted by elaboration (2.2). `[C]`

| Form | Lines | Files | What it pins today |
| --- | ---: | ---: | --- |
| `#check (@n : T)` | 2,278 text, 2,272 commands | 46 | `T` unifies with the type of `n` at default transparency |
| `#check (e : T)` without `@` (`inferInstance`, `rfl`, constructors) | 50 | 11 | an instance or a definitional equation exists |
| `#print axioms n` | 1,031 | 19 | that `n` resolves; nothing else |
| `example` | 105 | 6 | its own proof (Html probes, queue examples) |
| `#guard_msgs` | 13 | 2 | exact messages (`Html/Breakers.lean`, the gate) |
| `#guard` | 414 | 13 | a `Bool` evaluated by compiled code |
| `#check_failure` | 11 | 2 | an elaboration failure |

The review's 2,278 ascriptions are still 2,278 lines; six of them sit inside
docstrings that quote superseded ascriptions, so 2,272 are commands. The
review's 1,034 receipts are 1,031 at this base. 957 of the 1,031 name a
`Whatwg.*` declaration (12 `*AxiomReport.lean` files), and every one of
those 957 names also has a `#check (@n : T)` ascription; the other 74 name
counterexample witnesses in 7 files. No battery declares a `variable`, two
declare a `universe`, and `autoImplicit = false` holds package-wide. `[C]`

### 2.2 What each ascription elaborates to

A probe command `#w6probe (@n : T)` (an uncommitted module) replaced
`#check` in copies of the 46 files, each elaborated with `lake env lean`; for
every ascription it elaborated `T` alone with `Term.elabType` and
`synthesizeSyntheticMVarsNoPostponing` and classified the result against the
declared type of `n`. `[C]`

| Class | Count | Meaning |
| --- | ---: | --- |
| `Expr.equal` | 1,007 | identical, binder names included |
| `Expr.eqv` only | 1,128 | differs in binder names or binder annotations |
| reducible `isDefEq` only | 45 | needs reducible unfolding |
| default `isDefEq` only | 88 | needs default unfolding |
| a hole after standalone elaboration | 4 | passes today only by unification |
| total | 2,272 | 2,102 distinct declarations, 164 frozen in two or more modules, none twice in one module |

By kind: 1,065 theorems, 692 definitions, 377 constructors, 138 inductive
types. By axiom set: 1,247 none, 529 `[propext]`, 464 `[propext,
Quot.sound]`, 32 with `Classical.choice` (29 of them definitions). `[C]`

The four holes are in `WhatwgTest/Audit/SpecCoverage.lean`:
`Whatwg.Streams.Data.byteLengthSize_number`, `byteLengthSize_undefined`,
`Queue.empty_entries` and `Queue.empty_totalSize`. Each binds a type (`ε` or
`α`) the body never mentions, so the implicit argument of
`ByteLengthAnswer.number` or `Queue.empty` is a metavariable that `#check`
fills from the declaration; a production change from `ByteLengthAnswer Size
ε` to `ByteLengthAnswer Size Unit` would still pass that battery `[H]`.
The same experiment shows `#check (@n : _)` and `#check (@n : ∀ {ε :
Type}, SinkAnswer ε = _)` passing for any `n` of that shape. No ascription
writes `_` as a hole (the 242 standalone underscores in `WhatwgTest` at
the base are match arms, binders and gate code); every theorem ascription
uses `@`, so none freezes a specialisation through an inserted implicit
argument; and the 224 with universe parameters name the declaration's own.
`[C]`

A first-difference walk over the 137 ascriptions outside `Expr.eqv` found
three causes. `[C]`

- 125 are elaboration artefacts. A `match` in the battery gets its own
  auxiliary matcher (`_private.….match_N`, itself built on
  `_sparseCasesOn_N`) where the declaration has `<decl>.match_1`; and Lean
  turns a statement's non-dependent `let` into `have`, which `Expr.eqv`
  separates by the `nonDep` flag.
- 7, in `WhatwgTest/Infra/Utf8Laws.lean`, write `(encodeScalar s).length`,
  which elaborates to `Whatwg.Infra.ByteSequence.length`; the declaration
  states `List.length`.
- 1, in `WhatwgTest/Audit/WebIdl/CensusContract.lean`, writes `String` for a
  parameter declared `optParam String Gates.Census.rulesRelativePath`.

### 2.3 The prototype command over every battery

The command of appendix A, with the axiom lists taken from the probe, was
substituted into copies of the 46 files (command word replaced, ` axioms
[..]` appended after the closing parenthesis, ascription text untouched) and
each copy elaborated, once with an earlier revision and again with the
revision of appendix A. `[C]`

- 2,260 entries pass. The 12 of 2.2 fail with the command's diagnostic and
  nothing else fails.
- Timing, three runs each, `lake env lean <file>`, seconds:

| Battery (entries) | `#check` | freeze, `import Lean` | freeze, narrow imports |
| --- | --- | --- | --- |
| `Streams/Writable/DefaultLaws.lean` (108) | 1.15, 1.14, 1.17 | 2.22, 2.25, 2.29 | 1.33, 1.36, 1.38 |
| `Streams/Writable/DefaultContract.lean` (162) | 0.79, 0.81, 0.82 | 1.92, 1.94, 1.99 | not run |
| `Streams/Readable/DefaultContract.lean` (204) | 0.97, 0.97, 1.02 | 2.29, 2.31, 2.39 | 1.27, 1.29, 1.29 |

  The difference is the import. An empty file importing `Whatwg.Streams`
  takes 0.81 to 0.85 s; adding `Lean.Elab.Command` makes it 1.01 to 1.07 s,
  adding `Lean` 1.92 to 1.93 s; `DefaultLaws` with the freeze module imported
  but still on `#check` takes 2.34 to 2.36 s. Per entry the freeze command
  costs less than `#check`, which pretty-prints. The landed module imports
  `Lean.Elab.Command`, `Lean.Util.CollectAxioms` and
  `Lean.Meta.Match.MatcherInfo`, never `Lean`.
- Output: `DefaultLaws` prints 1,663 lines (137,714 characters) under
  `#check` and nothing under the freeze command.
- Unit cases (scratch file): a theorem without its `axioms` clause is
  refused; a definition without one is accepted with `axioms := none`; every
  optional clause records as written; a statement with a `match` and an
  `axioms` list that omits `propext` is refused with the actual set named.

### 2.4 Build log

`lake build 2>&1` at the base replays 9,957 lines (959,789 characters).
Attributed by message header: 8,802 lines are `#check` output, 1,046
`#print axioms` output, 109 everything else. With `DefaultLaws` converted the
log is 8,294 lines. `[C]`

### 2.5 The gate with the prototype listed

Appendix A was added as `WhatwgTest/Audit/Freeze.lean` with one entry in
`metaprogrammingModules`, one import in `WhatwgTest.lean`, and
`WhatwgTest/Streams/Writable/DefaultLaws.lean` converted in place (108
entries, not listed). `lake build`: 387 jobs, exit 0, "checked 223 source
files and 16920 declarations; Classical.choice is reached by 84 of 12766
declarations in Whatwg, 128 of 2557 in WhatwgTest". WhatwgTest grew by 197
declarations: 108 entries and 89 of the module, six of which reach
`Classical.choice` under R-11. No entry reaches any axiom (`#print axioms` on
an entry). `[C]`

- Without the list entry the same build fails with 27 findings: "registers a
  token", "registers a parser", "registers an elaborator … elabFreeze", and
  "contains an authored `syntax` metaprogramming keyword". `[C]`
- Token-table hygiene reports nothing. The module registers twelve tokens;
  the only non-base one is `#whatwg_freeze`, inert under T1 to T3. The clause
  keywords are `&"…"` non-reserved symbols and add no token. `[C]`
- The converted battery is accepted unlisted: it registers nothing and adds
  declarations through a listed module's command. `[C]`
- `lake exe whatwg_trustselftest` with the prototype listed and the battery
  converted: "every planted declaration was rejected for its stated reason,
  every control was accepted, and every narrow run exited 0", exit 0: 603 s
  on an earlier revision, 571 s on the revision of appendix A. `[C]`
- A revision that held the registry in a `SimplePersistentEnvExtension`
  registered by `initialize registry : … ← …` failed the environment pass:
  "declaration WhatwgTest.Audit.Freeze.registry is an `opaque` with no
  authored body". A `partial def` comparison failed the modifier pass; the
  landed one recurses on a fuel argument. `[C]`

### 2.6 Lake does not rerun the gate for a new unimported source (D49)

With two prototype modules present and not imported by `WhatwgTest.lean`,
`lake build` reported "Replayed WhatwgTest" and success: the root's trace did
not change, so the module closure check, which refuses a source the root
does not import, never ran. `[C]`

### 2.7 The declaration snapshot as an executable

A program (appendix B) imports `WhatwgTest` with `importModules`, walks every
constant of every module under `Whatwg`, and for each public one computes a
SHA-256 of a canonical text of its type (`Gates.Sha256.hexDigest`), its
axioms (`collectAxioms`), its declaration range and its docstring. `[C]`

| Build | Wall | Import | Walk |
| --- | --- | --- | --- |
| interpreted, `lake env lean --run` | 69.3 s | 2.2 s | 64.9 s |
| compiled, `lake exe`, two runs | 26.0 s, 25.5 s | 1.2 s, 1.3 s | 24.3 s, 23.7 s |
| compiled, no axiom column | 2.2 s | 1.2 s | 0.6 s |
| compiled, no axiom or digest column | 1.7 s | 1.2 s | 0.1 s |

The two compiled runs wrote byte-identical files (1,415,440 bytes). The
axiom column is 23 of the 26 s: each `collectAxioms` call builds a fresh
cache, and its per-module table does not make the exported path cheap here
`[H]`. `leanchecker` over the three libraries takes 79 s (R-V6). The walk
found 8,784 public constants under `Whatwg` (2,003 private, 2,128 internal):
1,201 theorems, 3,276 definitions, 136 inductive types, 928 constructors and
137 recursors with their own declaration range, and 2,116 theorems, 960
definitions, 16 constructors, 7 recursors and 7 inductive types without one
(equation lemmas and other generated declarations).
`[C]`

Of the 1,201 public theorems with a range, 982 have an ascription today:
Ecma262 107 of 107, WebIdl 45 of 45, Url 95 of 95, Streams 601 of 618, Infra
134 of 137, Html 0 of 199. Of 3,276 such definitions 566 have one, of 136
inductive types 121, of 928 constructors 362. `[C]`

### 2.8 Masks and lean4-effect4

- 347 of the 1,201 public theorem docstrings contain `M1` or `M2` (295 `M1`,
  130 `M2`, substring counts through `findDocString?` in the snapshot
  program); 263 use the form "Mask M1" or "Mask M2", as in
  `Whatwg/Streams/Semantics/Mask.lean`. Source lines spelling `M1` or `M2`:
  397 in 22 files of `Whatwg`, 174 in 18 files of `WhatwgTest`. `[C]`
- `Effects.Trace.Mask` (`effects` v0.8.0) is a structure of Booleans that
  filters events; its `m1` keeps operations, answers, failures and the
  outcome, its `m2` everything. DB-04's M1 is the chunk sequence plus the
  terminal outcome, M2 the full settlement order. `[S]`
- lean4-effect4 at `efcf1ae2`: `checked_theorem% n`
  (`tools/ProofGraph/Proof.lean`) still builds its `ProofRef` from `t.type`,
  the declaration's current type, and `ProofRef.validate` compares that type
  with itself; at elaboration it checks only that the name is a theorem
  within `propext` and `Quot.sound`, and the quoted proposition is re-quoted
  on every rebuild. It validates a reference and freezes no statement, as the
  review said. `Ledger.check` compares evidence with an authored goal by
  default-transparency `isDefEq`. The census instrument
  (`Test/Audit/TraversalCensus.lean`) prints, and asserts only its fixture
  controls with `#guard_msgs`. `docs/GENERATED.md` records that effect4
  retired its file writer: its commands build checked declarations during
  elaboration (`….checked`, `#obligation_proved`) and Lake tracks them. Its
  gate refuses a synthesised `opaque` as this one does, and its one
  `initialize` is the `IO Unit` form. `[S]`

## 3. Public declaration record

All in `WhatwgTest/Audit/Freeze.lean`, namespace `WhatwgTest.Audit.Freeze`.
Signatures as `#check` printed them from a scratch file importing the
prototype. Every declaration is tooling under R-11; none is a semantic
object of a standard, so none has a specification anchor.

| Declaration | Signature | Role | Route |
| --- | --- | --- | --- |
| `ObservationMask` | `Type`; constructors `m1`, `m2`, `notApplicable : String → ObservationMask` | canonical claim tag for DB-04's masks; separate from `Effects.Trace.Mask` and from the projections of `Whatwg.Streams.Semantics.Mask` | leaf receipt, standalone |
| `Entry` | `Entry.mk : Lean.Name → Option (List Lean.Name) → Option ObservationMask → Option String → Option String → List String → Entry` | canonical registry record (declaration, axioms, mask, anchor, graph, counterexamples) | leaf receipt, standalone |
| `entryName` | `Lean.Name → Lean.Name → Lean.Name` | the naming rule `recording ++ frozen ++ declaration` | helper of `Entry` |
| `sameStatement` | `Nat → Lean.Expr → Lean.Expr → Lean.MetaM Bool` | the statement-identity judgment | graph |
| `statementFuel` | `Nat` | its depth bound, 100,000 | helper |
| `elabFreeze` | `Lean.Elab.Command.CommandElab` | the command; admission and refusal | graph |
| `freezeCommand` | syntax kind | the command's parser | helper of `elabFreeze` |

An entry stores neither a type hash nor a printed type. The battery text is
the authored statement and the command has just compared it with the
declared type; the snapshot then pins the declared type by a SHA-256 of a
canonical text (appendix B). `Expr.hash` is not a pin: `Expr.Data.hash` keeps
32 bits (`c.toUInt32.toUInt64` in `Lean/Expr.lean`) `[S]`. A pretty-printed
type hides implicit arguments and instances, so it serves the diff reader
only, and the snapshot does not need it.

`Entry` uses `List`, not `Array`, so the snapshot executable can decode an
entry with `Lean.Meta.reduceEval`, whose instances cover `Name`, `String`,
`Option` and `List` and not `Array` (`Lean/Meta/ReduceEval.lean`). `[S]`
`ObservationMask` needs one `ReduceEval` instance, or the executable matches
its three constructor names. The judgment and the command own admission and
refusal, so `docs/AGENT-ROUTING.md` puts them on a graph route: one graph,
`FREEZE-PG-REGISTRY`, owned by the breaker packet, whose laws edge is the
refusal battery of 6.1.

## 4. Effect on frozen surfaces

| Owner group | Files with ascriptions | Ascriptions | Receipt files | Receipts | Text amendments |
| --- | ---: | ---: | ---: | ---: | ---: |
| P3 queue breaker | 1 | 171 | 1 | 99 | 0 |
| P4 readable breaker | 1 | 204 | 2 | 111 | 0 |
| P5 writable breaker | 4 | 273 | 5 | 129 | 0 |
| P6 transform breaker | 2 | 230 | 2 | 132 | 0 |
| P7 piping breaker | 3 | 144 | 2 | 62 | 0 |
| Q4 configuration-ordering | 3 | 264 | 1 | 93 | 0 |
| promise lane (Ecma262, WebIdl, bridges) | 12 | 455 | 2 | 182 | 0 |
| Infra | 5 | 220 | 3 | 128 | 7 |
| URL lane | 8 | 174 | 1 | 95 | 0 |
| audit and census | 7 | 137 | 0 | 0 | 5 |
| total | 46 | 2,272 | 19 | 1,031 | 12 |

The first five owners are named in the claims table of `COORDINATION.md`;
the other groups are released claims whose files stay breaker-owned under
`WhatwgTest/AGENTS.md`. Receipt counts include the 74 witness receipts (P4
17, P5 18, P6 14, P7 16, Infra 9). Under option (i) every ascription changes
its command word and, for the 1,065 theorems, gains an `axioms` clause;
2,260 keep their statement text byte for byte; 12 change it and need the
breaker addendum: the 4 holes of `SpecCoverage.lean` gain their implicit
argument, the 7 of `Utf8Laws.lean` write `List.length`, the one of
`WebIdl/CensusContract.lean` writes its `optParam`. Each battery gains one
`import` line; appendix C gives every count per file. The 12 production
`*AxiomReport.lean` files (957 lines) are retired by the ruling; the 7
witness files keep their 74 receipts until the counterexample slice (6.5).

Sentences that count the metaprogramming list: in
`test/contracts/trust-gate-hardening.contract.md`, section V2c.2 ("So the
list holds exactly those ten modules", "At the freeze the list holds the ten
modules above"), section V2c.7 ("The ten listed modules"), and the
acceptance text ("The ten listed modules are the live witnesses"); outside
it, `PLAN.md`, `WhatwgTest/AGENTS.md` ("the eight modules … and the two
constructive-contract batteries") and the docstring of
`metaprogrammingModules`. The trust self-test checks no count (`Select-String
metaprogramming WhatwgGates/TrustSelfTest.lean`). `[C]` The breaker addendum
amends the contract's sentences; the coordinator repairs `PLAN.md` and the
router; builder 1 edits the docstring.

## 5. Effect on the trust gate

- The list entry, below the anchor comment of `metaprogrammingModules`:

```lean
  ⟨`WhatwgTest.Audit.Freeze, "declares the registry command #whatwg_freeze with syntax and command_elab"⟩ ::
```

- Strict ceiling: unchanged. The module is under `WhatwgTest` and R-11; the
  entries reach no axiom (2.5).
- Token rules: one non-base token, `#whatwg_freeze`, inert (2.5). The clause
  keywords stay non-reserved; a reserved `mask` or `axioms` would turn every
  identifier of that spelling in every audited source into a keyword.
- Environment pass: the module registers a parser, its tokens and one
  elaborator, and no initializer. A battery that uses the command registers
  nothing and adds `Entry` declarations, which the environment and axiom
  passes audit like any other.
- Self-test rows the addendum adds: an acceptance row (a new unlisted module
  that only uses `#whatwg_freeze` is accepted) and a refusal row (an unlisted
  module that registers a second elaborator for `freezeCommand` is refused by
  rule 1). The command's own refusals are battery rows (6.1).
- D55 does not widen: `addDecl` keeps the kernel check, and `leanchecker`
  replays every entry.

## 6. Slices

### 6.1 Breaker packet

- Contract `test/contracts/freeze-registry.contract.md`: the grammar,
  `sameStatement` and its two allowances, the refusal diagnostics verbatim,
  the entry naming rule, the record TSV format and the join failures of 6.3,
  and the conversion check of 6.4.
- Red battery `WhatwgTest/Audit/FreezeContract.lean`, declared in
  `test/fixtures/trust-gate/known-red.txt`. Acceptance controls: an
  `Expr.equal` statement, renamed binders, an implicit made explicit, a
  `let`, a `match`, a definition without `axioms`. Refusal controls under
  `#guard_msgs` with the frozen diagnostic: an expression hole, a universe
  hole, a definitionally equal statement naming another function, an omitted
  `optParam`, a theorem without `axioms`, an axiom not listed, an axiom
  listed and not reached, a second entry in one module.
- Counterexample seeds for `test/counterexamples/REGISTER.md`: the hole
  vacuity (2.2), the function swap (2.2), the unpinned receipt (a `#print
  axioms` line accepts any axiom set), and the cached replay (2.6).
- Trust-gate addendum V2d: the list entry, the count sentences of section 4,
  the two self-test rows of section 5.
- The 12 text amendments, once per owning battery.

### 6.2 Builder 1: the command

Fence: `WhatwgTest/Audit/Freeze.lean` (new), one line of
`metaprogrammingModules` and its docstring in
`WhatwgTest/Audit/AxiomGate.lean`, one import in `WhatwgTest.lean`. Narrow
imports (2.3). Turns `FreezeContract.lean` green and removes its known-red
line.

### 6.3 Builder 2: the snapshot executable

Fence: `WhatwgGates/DeclSnapshot.lean` (new, `Gates.DeclSnapshot.cli`),
`whatwgbin/DeclSnapshot.lean`, one `[[lean_exe]]` in `lakefile.toml`,
`generated/declarations/*.tsv`, the CI step after `lake build`. The tooling
tree does not import `WhatwgTest`; it reads the entries from the imported
environment by constant name.

Columns: name, module, kind, origin (own declaration range or generated),
universe count, type SHA-256 of a canonical text (binder names included: the
snapshot pins the public surface, the battery the statement), axioms,
recording modules, mask, anchor, graph edge, counterexamples, record id,
route. One file per standard library; about 1.4 MB in all today.

Authored records: `test/records/<packet>.tsv`, breaker-owned and frozen with
the packet, one row per stable name or per namespace family, with owner,
role (`canonical`, `view`, `adapter`, `separate-calculus`, `derived`,
`helper`, `foreign-boundary`, `target-only`), related owner, census row id
and span digest, disposition, contract and route. A record precedes the
declaration it names, so it cannot be a Lean reference.

Join failures:

1. an exported type with its own range, under a recorded prefix, with no
   exact record;
2. an exported declaration under a recorded prefix that no record covers,
   exactly or by family;
3. a record naming no declaration, unless its battery is known-red;
4. two records claiming one census row;
5. a non-canonical record whose related owner has no record;
6. a record or entry anchor that is not a census row id of
   `generated/*-census.tsv`, or whose digest differs;
7. an entry under a recorded prefix whose declaration has no record;
8. two entries for one declaration that disagree on mask, anchor or graph;
9. regenerated bytes that differ from the committed files.

`recordedPrefixes` is data in the generator and starts empty, so rules 1, 2,
3 and 7 bind nothing at landing and the others bind everything; a prefix
joins when its records exist, as R-V1's strict prefixes did, and each graph's
identity edge closes when its prefix joins. The executable refuses to run
when a source under the audited trees is newer than its `.olean`, so a
forgotten `lake build` cannot yield a stale verdict `[H]`.

### 6.4 Builder 3: the conversion

A Lean conversion pass, run once and not landed: it elaborates each battery
with the frontend, finds every `#check (@n : T)` command by its syntax range
(never by regular expression: six such lines are inside docstrings),
replaces the command word, and appends `axioms [..]` for theorems from
`collectAxioms`. One commit per owner group of section 4. The receipt that no
statement changed: (1) for every converted command the bytes from `(@` to
the matching `)` are identical before and after, except the 12 named
amendments; (2) the multiset of (recording module, declaration) pairs of the
2,272 old ascriptions equals that of the new entries, read by the snapshot
executable; (3) the R-V6 fingerprint of every constant under `Whatwg` is
unchanged.

### 6.5 Counterexample join (D45, D50): out of this slice

The `counterexamples` clause and join failure 6 carry the ids. Checking them
against `test/counterexamples/REGISTER.md`, freezing the 74 witness
receipts, and making the witness modules import production are a follow-up,
W6b. It needs a machine-readable register, a breaker-owned document change
of its own, where the 51 missing ids of D45 are added.

### 6.6 Reviewer

Checks: every refusal control is refused for its frozen reason and nothing
else in the tree is; the conversion receipt of 6.4; no statement text change
outside the 12 named; the gate's summary line and the self-test; the
snapshot regenerates byte-identically twice on a clean tree; `leanchecker`
replays the entries.

### 6.7 Dependencies, and what to borrow

- W7 needs the entry naming rule and `Entry`, so a ledger evidence item can
  read "frozen by `<module>.frozen.<n>`"; the `graph` clause becomes a typed
  reference once W7 names graphs in Lean. W6 builder 1 lands first; W7 needs
  nothing else from W6.
- W10: the snapshot executable is the first gate that runs over built
  `.olean` files. Its walk should be one function W10's gate package can
  absorb.
- W8 and W9: `ObservationMask` is a claim tag. Masks as projections stay in
  `Whatwg.Streams.Semantics.Mask` and its successors; a relation to
  `Effects.Trace.Mask` is a W9 theorem, not a rename.
- From lean4-effect4, borrow: generated declarations during elaboration in
  place of an extension or a file writer (`docs/GENERATED.md`), which
  appendix A does; `#guard_msgs`-asserted red controls for an instrument
  (`TraversalCensus.lean`), which 6.1 does; `Obligation (statement : Prop)`
  for W7's wanted goals. Leave: `checked_theorem%`, default-transparency
  `isDefEq` as the identity check, the hard-coded ceiling and the Batteries
  import of `tools/ProofGraph`.

## 7. Decisions for the coordinator

1. Where the registry lives. (a) Declarations `<module>.frozen.<n> : Entry`,
   kernel-checked; no gate change beyond the list entry; 2,272 more
   declarations in the gate's count. (b) A persistent environment extension;
   needs an addendum admitting an `initialize`-declared `opaque` in a listed
   module. (c) No stored registry; the snapshot reads battery sources.
   Recommend (a).
2. The identity judgment. (a) `sameStatement`: 12 amendments. (b)
   `Expr.eqv` alone: 137 refusals in 15 files, and no battery text can name
   the declaration's own auxiliary matcher, so a statement with a `match`
   cannot be frozen at all. (c) Reducible `isDefEq`: 92 refusals (the 88 that
   need default unfolding, most of them `match` statements, and the 4 holes),
   and it accepts unfoldings of reducible definitions. (d) Default
   `isDefEq`: today's check without holes; accepts the function swap.
   Recommend (a).
3. Receipts on non-theorems. (a) Required for theorems, optional otherwise:
   1,065 converted clauses. (b) Required for every entry: 2,272 clauses, and
   a body change of a definition becomes a battery change. Recommend (a).
4. Conversion. (i) Every battery: 46 files, 10 owner groups, 12 text
   amendments, about +0.2 s import per battery, build log 9,957 to about 110
   lines. (ii) Registry beside `#check`: a fourth copy of every statement, or
   a reference check that freezes nothing; holes stay; elaboration roughly
   doubles per battery. (iii) New packets only: a debt of 2,272 ascriptions
   and 957 receipts; holes stay. Recommend (i).
5. The 12 amendments. (a) The battery adopts the declared form, by breaker
   addendum per owner. (b) Production adopts the battery's form: a statement
   change. (c) Keep those 12 as `#check` with a debt. Recommend (a).
6. The 957 production receipts. (a) Retire the 12 report files when the
   conversion lands. (b) Keep them. Recommend (a): they pin nothing, and the
   entries pin the exact set.
7. The snapshot route. (a) An executable over `.olean`, 26 s. (b) An
   elaboration-time command that writes a file Lake does not track (D49).
   Recommend (a).
8. Authored records. (a) TSV per packet under `test/records/`. (b) Lean data
   modules. (c) Parse the graph documents' tables. Recommend (a).
9. Join rollout. (a) `recordedPrefixes`, empty at landing. (b) All at once,
   which fails today on every exported type. Recommend (a).
10. Masks. (a) `ObservationMask` with `m1`, `m2`, `notApplicable`, optional
    in converted entries and required for new packets by a prefix list in
    the snapshot. (b) Descriptive constructor names. Recommend (a).
11. Counterexample join. (a) Out of this slice, as W6b. (b) In. Recommend
    (a).
12. Anchors. (a) Census row ids only, joined to `generated/*-census.tsv`.
    (b) Packet-local labels (`-- SIZE`; 160 of 2,169 column-0 ascriptions
    carry one). Recommend (a).

## 8. Not checked

- The conversion pass itself; the measurement substituted text in copies,
  which suffices for counts and not for landing.
- Why `collectAxioms` costs 2.6 ms per declaration in the executable `[H]`.
- The stale-`.olean` refusal of 6.3 `[H]`.
- `sameStatement` on a universe-polymorphic statement whose battery names
  its universes differently; none exists in the tree.
- `leanchecker` over the entry declarations, and the gate's time with all
  2,272 entries (108 were measured, 2.5).
- The 50 ascriptions without `@` (`inferInstance`, `rfl`, constructors),
  which stay `#check` and keep printing.
- Batteries outside this repository.

## Appendix A: the prototype command

`WhatwgTest/Audit/Freeze.lean` as it elaborated and passed the gate, removed
from the worktree before this commit.

```lean
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Meta.Match.MatcherInfo

/-!
# The freeze registry (W6 design prototype; not for landing as written)

`#whatwg_freeze (@n : T) axioms [a, …] …` pins three facts about the constant
`n` and records them as one ordinary, kernel-checked declaration of type
`Entry`, named `<recording module>.frozen.<n>`:

1. its statement: `T` is elaborated alone, with no expected type, must leave no
   metavariable, and must be the declared type of `n` under `sameStatement`;
2. its exact axiom set: `Lean.collectAxioms n`, compared as a set with the
   listed names; the clause is required when `n` is a theorem and optional
   otherwise; and
3. its data: an observation mask, a census row or specification anchor, a
   graph edge and counterexample identifiers, each optional.

It prints nothing on success. A failure is an error at the clause it concerns.

The registry is held in declarations rather than in a persistent environment
extension because `initialize x : T ← e` declares `x` as an `opaque` whose
value Lean synthesises, which the trust gate's environment pass refuses in
every audited tree (ruling R-V2).
-/

open Lean Elab Command Term Meta

namespace WhatwgTest.Audit.Freeze

/-- The observation mask a frozen declaration claims (design basis DB-04 and
the root router's representation rules). Not `Effects.Trace.Mask`, whose `m1`
and `m2` keep different observations. -/
inductive ObservationMask where
  /-- M1: the chunk sequence plus the terminal outcome. -/
  | m1
  /-- M2: the full settlement order. -/
  | m2
  /-- The declaration states no observation; the reason says why. -/
  | notApplicable (reason : String)
  deriving Inhabited, BEq, Repr

/-- One registry entry. The statement is not stored: the battery text is the
authored copy and the environment holds the declared type. -/
structure Entry where
  declaration : Name
  /-- The exact axiom set, when the entry pins one; every theorem's entry does. -/
  axioms : Option (List Name)
  mask : Option ObservationMask := Option.none
  anchor : Option String := Option.none
  graph : Option String := Option.none
  counterexamples : List String := []
  deriving Inhabited, Repr

instance : ToExpr ObservationMask where
  toExpr
    | .m1 => mkConst ``ObservationMask.m1
    | .m2 => mkConst ``ObservationMask.m2
    | .notApplicable reason => mkApp (mkConst ``ObservationMask.notApplicable) (toExpr reason)
  toTypeExpr := mkConst ``ObservationMask

/-- The entry as a closed term of type `Entry`. -/
def Entry.toExpr (entry : Entry) : Expr :=
  mkAppN (mkConst ``Entry.mk)
    #[Lean.toExpr entry.declaration, Lean.toExpr entry.axioms, Lean.toExpr entry.mask,
      Lean.toExpr entry.anchor, Lean.toExpr entry.graph, Lean.toExpr entry.counterexamples]

/-- The name of the entry that module `recording` holds for `declaration`. -/
def entryName (recording declaration : Name) : Name :=
  (recording ++ `frozen) ++ declaration

/-- The command. Clause keywords are non-reserved, so the only token the module
adds to the table is `#whatwg_freeze`. -/
syntax (name := freezeCommand) "#whatwg_freeze " "(" "@" ident " : " term ")"
  (&"axioms" "[" ident,* "]")?
  (&"mask" (&"M1" <|> &"M2" <|> (&"none" str)))?
  (&"anchor" str)?
  (&"graph" str)?
  (&"counterexamples" "[" str,* "]")? : command

/-- The axiom names as a sorted array with no duplicates. -/
private def normalise (names : Array Name) : Array Name :=
  (names.qsort Name.quickLt).toList.eraseDups.toArray

/-- Statement identity: alpha-equivalence (binder names and annotations
ignored, as `Expr.eqv` does), with two allowances for what the declaration
elaborator does and a standalone elaboration does not: a `let` and a `have`
with the same type, value and body agree (Lean turns a statement's
non-dependent `let` into `have`), and two auxiliary definitions (a matcher, or
a constant with an internal name such as `_sparseCasesOn_1`) agree when their
own types and values agree under this relation at the same universe levels (a
`match` elaborated in the battery gets its own auxiliary names). Nothing else
is unfolded. `fuel` bounds the depth of the comparison; running out refuses. -/
def sameStatement : Nat → Expr → Expr → MetaM Bool
  | 0, _, _ => return false
  | fuel + 1, a, b => do
    if a == b then return true
    match a, b with
    | .app f x, .app g y => return (← sameStatement fuel f g) && (← sameStatement fuel x y)
    | .forallE _ t₁ b₁ _, .forallE _ t₂ b₂ _ =>
        return (← sameStatement fuel t₁ t₂) && (← sameStatement fuel b₁ b₂)
    | .lam _ t₁ b₁ _, .lam _ t₂ b₂ _ =>
        return (← sameStatement fuel t₁ t₂) && (← sameStatement fuel b₁ b₂)
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ =>
        return (← sameStatement fuel t₁ t₂) && (← sameStatement fuel v₁ v₂) &&
          (← sameStatement fuel b₁ b₂)
    | .mdata _ x, _ => sameStatement fuel x b
    | _, .mdata _ y => sameStatement fuel a y
    | .proj s₁ i₁ x, .proj s₂ i₂ y =>
        return s₁ == s₂ && i₁ == i₂ && (← sameStatement fuel x y)
    | .const n₁ ls₁, .const n₂ ls₂ =>
        if ls₁ != ls₂ then return false
        let auxiliary (n : Name) : MetaM Bool := return (← isMatcher n) || n.isInternal
        unless (← auxiliary n₁) && (← auxiliary n₂) do return false
        let some c₁ := (← getEnv).find? n₁ | return false
        let some c₂ := (← getEnv).find? n₂ | return false
        let some v₁ := c₁.value? | return false
        let some v₂ := c₂.value? | return false
        return (← sameStatement fuel (c₁.instantiateTypeLevelParams ls₁)
            (c₂.instantiateTypeLevelParams ls₂)) &&
          (← sameStatement fuel (v₁.instantiateLevelParams c₁.levelParams ls₁)
            (v₂.instantiateLevelParams c₂.levelParams ls₂))
    | _, _ => return false

/-- The comparison depth: far above any statement in the tree. -/
def statementFuel : Nat := 100000

@[command_elab freezeCommand]
def elabFreeze : CommandElab := fun stx => do
  let id : Syntax := stx[3]
  let typeStx : Syntax := stx[5]
  let axiomsStx := stx[7]
  let maskStx := stx[8]
  let anchorStx := stx[9]
  let graphStx := stx[10]
  let ceStx := stx[11]
  let declaration ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let name := entryName (← getMainModule) declaration
  if (← getEnv).contains name then
    throwErrorAt id "freeze: {declaration} is already frozen in this module"
  let info ← getConstInfo declaration
  -- 1. The statement, elaborated alone; auxiliary matchers it creates are
  -- discarded with the environment.
  withoutModifyingEnv <| liftTermElabM <| Term.withoutErrToSorry do
    let type ← Term.elabType typeStx
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    if type.hasMVar then
      throwErrorAt typeStx "freeze: the statement of {declaration} has a hole; write every argument"
    unless ← sameStatement statementFuel type info.type do
      throwErrorAt typeStx "freeze: the statement of {declaration} is not the declared one{indentExpr info.type}"
  -- 2. The exact axiom set: required for a theorem, optional otherwise.
  let actual := normalise (← liftCoreM <| collectAxioms declaration)
  let pinned : Option (List Name) ← if axiomsStx.isNone then
      if info matches .thmInfo _ then
        throwErrorAt id "freeze: {declaration} is a theorem; its axioms clause is required"
      pure Option.none
    else
      let listed ← axiomsStx[2].getSepArgs.mapM fun axiomId =>
        liftCoreM <| realizeGlobalConstNoOverloadWithInfo axiomId
      let listed := normalise listed
      unless actual == listed do
        let extra := actual.filter (!listed.contains ·)
        let stale := listed.filter (!actual.contains ·)
        throwErrorAt axiomsStx "freeze: the axioms of {declaration} are {actual}; not listed {extra}, listed but not reached {stale}"
      pure (some listed.toList)
  -- 3. The data, recorded as one declaration.
  let mask : Option ObservationMask :=
    if maskStx.isNone then Option.none
    else
      let choice := maskStx[1]
      -- `&"M1"` inside `<|>` parses to a node of kind `token.M1`
      if choice.isOfKind `token.M1 then some .m1
      else if choice.isOfKind `token.M2 then some .m2
      else some (.notApplicable (choice[1].isStrLit?.getD ""))
  let anchor := if anchorStx.isNone then Option.none else anchorStx[1].isStrLit?
  let graph := if graphStx.isNone then Option.none else graphStx[1].isStrLit?
  let counterexamples : Array String :=
    if ceStx.isNone then #[] else ceStx[2].getSepArgs.filterMap (·.isStrLit?)
  let entry : Entry :=
    { declaration, axioms := pinned, mask, anchor, graph,
      counterexamples := counterexamples.toList }
  liftCoreM <| addDecl <| .defnDecl
    { name, levelParams := [], type := mkConst ``Entry, value := entry.toExpr,
      hints := .opaque, safety := .safe }

end WhatwgTest.Audit.Freeze
```

## Appendix B: the snapshot walk

The core of the measured program of 2.7, built as a temporary `[[lean_exe]]`
over `whatwgbin/`; the docstring and origin counters are omitted. It is not
gate code: a landed version decodes entries, joins records and prints
PASS or FAIL.

```lean
import Lean
import WhatwgGates.Sha256

open Lean

def levelText : Level → String
  | .zero => "0"
  | .succ l => s!"(s {levelText l})"
  | .max a b => s!"(max {levelText a} {levelText b})"
  | .imax a b => s!"(imax {levelText a} {levelText b})"
  | .param n => s!"(p {n})"
  | .mvar _ => "?"

/-- Canonical text of a type: tags, names, levels, literals, binder names and
annotations; `mdata` dropped. -/
def exprText : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar _ => "fvar"
  | .mvar _ => "mvar"
  | .sort l => s!"(S {levelText l})"
  | .const n ls => s!"(C {n} {ls.map levelText})"
  | .app f a => s!"(A {exprText f} {exprText a})"
  | .lam n t b bi => s!"(L {n} {repr bi} {exprText t} {exprText b})"
  | .forallE n t b bi => s!"(P {n} {repr bi} {exprText t} {exprText b})"
  | .letE n t v b nd => s!"(E {n} {nd} {exprText t} {exprText v} {exprText b})"
  | .lit (.natVal v) => s!"(N {v})"
  | .lit (.strVal s) => s!"(T {repr s})"
  | .mdata _ e => exprText e
  | .proj s i e => s!"(J {s} {i} {exprText e})"

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `WhatwgTest }] {} (trustLevel := 1024)
  let ctx : Core.Context := { fileName := "<snapshot>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  -- the registry: every constant `<module>.frozen.<declaration>` of a WhatwgTest module
  let mut frozenBy : Std.HashMap Name (Array Name) := {}
  for idx in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[idx]!
    unless (`WhatwgTest).isPrefixOf m do continue
    for c in env.header.moduleData[idx]!.constNames do
      if (m ++ `frozen).isPrefixOf c then
        let declaration := c.replacePrefix (m ++ `frozen) .anonymous
        frozenBy := frozenBy.insert declaration ((frozenBy.getD declaration #[]).push m)
  let mut rows : Array String := #[]
  for idx in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[idx]!
    unless (`Whatwg).isPrefixOf m do continue
    for c in env.header.moduleData[idx]!.constNames do
      let some info := env.find? c | continue
      if isPrivateName c || c.isInternal then continue
      let digest := Gates.Sha256.hexDigest (exprText info.type).toUTF8
      let (axioms, _) ← (collectAxioms c : CoreM (Array Name)).toIO ctx state
      let axiomText := ",".intercalate ((axioms.qsort Name.quickLt).toList.map toString)
      let frozen := ";".intercalate ((frozenBy.getD c #[]).toList.map toString)
      rows := rows.push s!"{c}\t{m}\t{info.levelParams.length}\t{digest}\t{axiomText}\t{frozen}"
  IO.FS.writeFile (args.headD "declarations.tsv")
    ("\n".intercalate (rows.qsort (· < ·)).toList ++ "\n")
  return 0
```

## Appendix C: receipt forms per file

Paths are relative to `WhatwgTest/`. Ascriptions are `#check (@n : T)`
commands (2.2); theorems are those of them whose `#whatwg_freeze` needs an`
axioms` clause; receipts are `#print axioms` lines; amendments are the`
entries the prototype refused (2.3). `[C]`

| File | Ascriptions | Theorems | Receipts | Amendments |
| --- | ---: | ---: | ---: | ---: |
| `Audit/CensusProfileIdentity.lean` | 4 | 0 | 0 | 0 |
| `Audit/Ecma262/CensusContract.lean` | 22 | 0 | 0 | 0 |
| `Audit/Ecma262/CensusQ2Contract.lean` | 4 | 0 | 0 | 0 |
| `Audit/Ecma262/EcmarkupScanner.lean` | 23 | 0 | 0 | 0 |
| `Audit/SpecCoverage.lean` | 55 | 55 | 0 | 4 |
| `Audit/WebIdl/CensusContract.lean` | 23 | 0 | 0 | 1 |
| `Audit/WebIdl/CensusQ2Contract.lean` | 6 | 0 | 0 | 0 |
| `Ecma262/JobsCompleteContract.lean` | 14 | 11 | 0 | 0 |
| `Ecma262/JobsContract.lean` | 24 | 0 | 0 | 0 |
| `Ecma262/JobsLaws.lean` | 20 | 20 | 0 | 0 |
| `Ecma262/PromiseAxiomReport.lean` | 0 | 0 | 125 | 0 |
| `Ecma262/PromiseContract.lean` | 75 | 0 | 0 | 0 |
| `Ecma262/PromiseFidelityAxiomReport.lean` | 0 | 0 | 57 | 0 |
| `Ecma262/PromiseFidelityContract.lean` | 10 | 0 | 0 | 0 |
| `Ecma262/PromiseFidelityLaws.lean` | 33 | 33 | 0 | 0 |
| `Ecma262/PromiseLaws.lean` | 44 | 44 | 0 | 0 |
| `Infra/Counterexamples/CommaSplit.lean` | 3 | 3 | 3 | 0 |
| `Infra/IntegerConstructiveContract.lean` | 9 | 9 | 0 | 0 |
| `Infra/ScalarConstructiveContract.lean` | 9 | 6 | 0 | 0 |
| `Infra/Utf8AxiomReport.lean` | 0 | 0 | 119 | 0 |
| `Infra/Utf8Contract.lean` | 80 | 0 | 0 | 0 |
| `Infra/Utf8Laws.lean` | 119 | 119 | 0 | 7 |
| `Streams/Counterexamples/Infra/Split.lean` | 0 | 0 | 6 | 0 |
| `Streams/Counterexamples/Piping/Shutdown.lean` | 0 | 0 | 16 | 0 |
| `Streams/Counterexamples/Readable/Default.lean` | 0 | 0 | 17 | 0 |
| `Streams/Counterexamples/Transform/Backpressure.lean` | 0 | 0 | 14 | 0 |
| `Streams/Counterexamples/Writable/Default.lean` | 0 | 0 | 16 | 0 |
| `Streams/Counterexamples/Writable/InFlightPrecedence.lean` | 0 | 0 | 2 | 0 |
| `Streams/Data/QueueAxiomReport.lean` | 0 | 0 | 99 | 0 |
| `Streams/Data/QueueContract.lean` | 171 | 105 | 0 | 0 |
| `Streams/Piping/ShutdownAxiomReport.lean` | 0 | 0 | 46 | 0 |
| `Streams/Piping/ShutdownContract.lean` | 98 | 0 | 0 | 0 |
| `Streams/Piping/ShutdownLaws.lean` | 44 | 44 | 0 | 0 |
| `Streams/Piping/ShutdownRuns.lean` | 2 | 2 | 0 | 0 |
| `Streams/PromiseBridge.lean` | 84 | 42 | 0 | 0 |
| `Streams/PromiseBridgeQ4.lean` | 38 | 26 | 0 | 0 |
| `Streams/Readable/DefaultAxiomReport.lean` | 0 | 0 | 94 | 0 |
| `Streams/Readable/DefaultContract.lean` | 204 | 94 | 0 | 0 |
| `Streams/Semantics/OrderingAxiomReport.lean` | 0 | 0 | 93 | 0 |
| `Streams/Semantics/OrderingContract.lean` | 109 | 1 | 0 | 0 |
| `Streams/Semantics/OrderingLaws.lean` | 69 | 69 | 0 | 0 |
| `Streams/Semantics/OrderingSource.lean` | 86 | 13 | 0 | 0 |
| `Streams/Transform/BackpressureAxiomReport.lean` | 0 | 0 | 118 | 0 |
| `Streams/Transform/BackpressureContract.lean` | 112 | 0 | 0 | 0 |
| `Streams/Transform/BackpressureLaws.lean` | 118 | 118 | 0 | 0 |
| `Streams/Writable/DefaultAxiomReport.lean` | 0 | 0 | 108 | 0 |
| `Streams/Writable/DefaultContract.lean` | 162 | 0 | 0 | 0 |
| `Streams/Writable/DefaultLaws.lean` | 108 | 108 | 0 | 0 |
| `Streams/Writable/InFlightExactAxiomReport.lean` | 0 | 0 | 1 | 0 |
| `Streams/Writable/InFlightExactContract.lean` | 1 | 1 | 0 | 0 |
| `Streams/Writable/LifecycleAxiomReport.lean` | 0 | 0 | 2 | 0 |
| `Streams/Writable/LifecycleContract.lean` | 2 | 2 | 0 | 0 |
| `Url/CensusContract.lean` | 1 | 0 | 0 | 0 |
| `Url/CensusInputContract.lean` | 11 | 0 | 0 | 0 |
| `Url/Counterexamples/Census.lean` | 1 | 0 | 0 | 0 |
| `Url/Counterexamples/CensusInput.lean` | 2 | 0 | 0 | 0 |
| `Url/Counterexamples/Inventory.lean` | 1 | 0 | 0 | 0 |
| `Url/InventoryContract.lean` | 3 | 0 | 0 | 0 |
| `Url/PercentEncodingAxiomReport.lean` | 0 | 0 | 95 | 0 |
| `Url/PercentEncodingContract.lean` | 60 | 0 | 0 | 0 |
| `Url/PercentEncodingLaws.lean` | 95 | 95 | 0 | 0 |
| `WebIdl/ExceptionsContract.lean` | 63 | 15 | 0 | 0 |
| `WebIdl/PromiseContract.lean` | 33 | 17 | 0 | 0 |
| `WebIdl/PromiseFidelityContract.lean` | 17 | 13 | 0 | 0 |
