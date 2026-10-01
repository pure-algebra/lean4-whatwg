# Freeze registry contract (review lane W, slice W6, the command)

Status: FROZEN / RED, W6 breaker seat, 2026-10-01, on branch
`review/w6-freeze-breaker`, based on `b0d35e2` (the commit that lands ruling
R-W9).

Authority: ruling R-W5 of `COORDINATION.md` (binding), with R-W1, R-W7(a)
and (b), R-W8 and R-W9. Evidence and prototype: the design record
`docs/research/2026-10-01-w6-freeze-registry-design.md` (its appendix A is the
prototype command). Where the design and R-W5 differ, R-W5 is followed;
section 12 lists every place this packet departs from either.

This packet freezes behaviour, not code. The subject is the command
`#whatwg_freeze`, declared by the new module `WhatwgTest/Audit/Freeze.lean`.
The executable falsifier is the battery `WhatwgTest/Audit/FreezeContract.lean`.
The Lean battery is the authority on names, propositions and diagnostics; the
Lean in this file is a reading aid. The declaration snapshot of R-W5 is the
second, stacked packet, `test/contracts/declaration-snapshot.contract.md`, on
branch `review/w6-snapshot-breaker`.

## 1. Files and fences

Breaker-owned and frozen by this packet:

- this file;
- `WhatwgTest/Audit/FreezeContract.lean`;
- the twelve text amendments of section 9, one dated comment each, in
  `WhatwgTest/Audit/SpecCoverage.lean`, `WhatwgTest/Infra/Utf8Laws.lean` and
  `WhatwgTest/Audit/WebIdl/CensusContract.lean`;
- the rows `FREEZE-CE-001` to `FREEZE-CE-004` of
  `test/counterexamples/REGISTER.md` (section 11); and
- the block for `WhatwgTest.Audit.FreezeContract` in
  `test/fixtures/trust-gate/known-red.txt`.

Builder 1 (R-W8 wave 2a, "the freeze command") implements in this fence and
edits none of the files above:

- `WhatwgTest/Audit/Freeze.lean`, new;
- the one import line `import WhatwgTest.Audit.Freeze` and the one import line
  `import WhatwgTest.Audit.FreezeContract` in `WhatwgTest.lean` (R-W9: the
  builder that turns a battery green adds its root import);
- the `metaprogrammingModules` entry for `WhatwgTest.Audit.Freeze`, exactly as
  trust-gate addendum V2d freezes it, in whichever module holds that list when
  builder 1 lands (R-W7(a) moves the list to `WhatwgGates/TrustConfig.lean`),
  with the docstring sentence that counts the list; and
- the removal of this packet's `known-red.txt` entry, the moment the battery
  is green.

The list entry, the sentences of `test/contracts/trust-gate-hardening.contract.md`
that count the listed modules and the two self-test rows of the design's
section 5 belong to addendum V2d, which another breaker seat freezes (R-W7(b)).
This packet does not restate them. A row of this packet that cannot be
satisfied as frozen is reported to the coordinator, not repaired by the
builder.

## 2. Terms

- *Ascription*: the text `(@n : T)` of a command, `n` an identifier and `T` a
  term.
- *Declared type*: `ConstantInfo.type` of the constant `n` resolves to.
- *Standalone elaboration*: `T` elaborated as a type with no expected type
  (`Lean.Elab.Term.elabType`), then
  `Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing` (default instances
  included), then `instantiateMVars`, all inside
  `Lean.Elab.Term.withoutErrToSorry`, so an elaboration error in `T` is an
  error of the command and never a `sorry`.
- *Recording module*: the main module of the command, `getMainModule`, which
  is the module name under `lake build` and under
  `lake env lean <path>` alike (measured: `lake env lean
  WhatwgTest/Audit/FreezeContract.lean` reports
  `WhatwgTest.Audit.FreezeContract`).
- *Entry*: the constant the command adds (section 6).
- *Auxiliary constant*: a constant `c` for which `Lean.Meta.isMatcher c`
  holds or whose name satisfies `Lean.Name.isInternal` (a component beginning
  with `_`, such as `_sparseCasesOn_1` or `_private`).
- A diagnostic template writes `<d>` for the resolved full name of `n`,
  printed as a `Lean.Name` interpolated into a message (no `«»` shortening,
  no namespace stripping: the battery's messages print
  `WhatwgTest.Audit.FreezeContract.Fixture.exact`), and `<list>` for a name
  list rendered as plain text (section 7).

## 3. Grammar

```text
#whatwg_freeze (@n : T)
  [axioms [a, …]]
  [mask M1 | mask M2 | mask none "reason"]
  [anchor "row-id"]
  [graph "edge"]
  [counterexamples ["id", …]]
```

The clauses are optional, appear at most once each, and appear in this order.
The reference syntax, as it elaborates in the prototype:

```lean
syntax (name := freezeCommand) "#whatwg_freeze " "(" "@" ident " : " term ")"
  (&"axioms" "[" ident,* "]")?
  (&"mask" ident (str)?)?
  (&"anchor" str)?
  (&"graph" str)?
  (&"counterexamples" "[" str,* "]")? : command
```

- The syntax kind is `WhatwgTest.Audit.Freeze.freezeCommand`, a
  `Lean.ParserDescr`; its one elaborator is
  `WhatwgTest.Audit.Freeze.elabFreeze`, registered by `@[command_elab]` in
  the same module.
- The command adds exactly one token to the final token table,
  `#whatwg_freeze`. The clause words `axioms`, `mask`, `anchor`, `graph` and
  `counterexamples` are non-reserved symbols (`&"…"`) and add no token; a
  reserved `mask` or `axioms` would turn every identifier of that spelling in
  every audited source into a keyword. `M1`, `M2` and `none` are read as
  identifiers. Every other token of the grammar is a base token.
- The `mask` clause parses one identifier and an optional string, and the
  elaborator decides (section 7, F7 and F8), so that a malformed mask clause
  is an elaboration error a `#guard_msgs` can pin, not a parse error.
- `axioms []` and `counterexamples []` are well formed.
- A clause out of order, repeated, or misspelt is a parse error. A parse error
  cannot be pinned by `#guard_msgs` and is not frozen here beyond the fact
  that it is an error.

## 4. Public declaration record

All in the module `WhatwgTest.Audit.Freeze`, namespace
`WhatwgTest.Audit.Freeze`. Owner: this packet (the W6 breaker) for the
statement, builder 1 for the implementation. Every declaration is tooling
under R-11's ceiling; none models a named algorithm, slot, IDL member or
requirement of a pinned specification, so none has a specification anchor or
a span digest, and the `SPEC-MANIFEST.md` disposition is not applicable.
Assurance route, by R-W5's change two: this contract and its battery, as for
the census and the trust gate; no proof graph `FREEZE-PG-REGISTRY` is opened.

| Declaration | Exact signature | Role | Relationship |
| --- | --- | --- | --- |
| `ObservationMask` | `Type` | the observation mask a frozen declaration claims | `canonical`; intentionally separate from `Effects.Trace.Mask` (a filter of trace events; a relation is a W9 theorem, not a rename) and from the projections of `Whatwg.Streams.Semantics.Mask` |
| `ObservationMask.chunksAndOutcome` | `ObservationMask` | DB-04's M1: the chunk sequence plus the terminal outcome | constructor of `ObservationMask` |
| `ObservationMask.settlementOrder` | `ObservationMask` | DB-04's M2: the full settlement order | constructor of `ObservationMask` |
| `ObservationMask.notApplicable` | `String → ObservationMask` | the declaration states no observation; the argument (`reason`) says why | constructor of `ObservationMask` |
| `Entry` | `Type` | one registry record | `canonical` |
| `Entry.mk` | `Lean.Name → Option (List Lean.Name) → Option ObservationMask → Option String → Option String → List String → Entry` | its constructor; fields in this order | constructor of `Entry` |
| `Entry.declaration` | `Entry → Lean.Name` | the frozen declaration's resolved full name | projection of `Entry` |
| `Entry.axioms` | `Entry → Option (List Lean.Name)` | the pinned axiom set; `none` when no clause was written | projection of `Entry` |
| `Entry.mask` | `Entry → Option ObservationMask` | the `mask` clause | projection of `Entry` |
| `Entry.anchor` | `Entry → Option String` | the `anchor` clause | projection of `Entry` |
| `Entry.graph` | `Entry → Option String` | the `graph` clause | projection of `Entry` |
| `Entry.counterexamples` | `Entry → List String` | the `counterexamples` clause; `[]` when absent | projection of `Entry` |
| `entryName` | `Lean.Name → Lean.Name → Lean.Name` | the naming rule: `entryName recording declaration = (recording ++ `frozen) ++ declaration` | `helper` of `Entry` |
| `sameStatement` | `Nat → Lean.Expr → Lean.Expr → Lean.MetaM Bool` | the statement-identity judgment of section 5, the first argument its fuel | `canonical` |
| `statementFuel` | `Nat` | the fuel the command passes, `100000` | `helper` of `sameStatement` |
| `elabFreeze` | `Lean.Elab.Command.CommandElab` | the command: admission and refusal | `canonical` |
| `freezeCommand` | `Lean.ParserDescr` | the command's syntax kind | `helper` of `elabFreeze` |

`Entry` uses `List`, not `Array`, for its two list fields. Fields `mask`,
`anchor` and `graph` may carry the structure default `none` and
`counterexamples` the default `[]`; `Entry.mk` takes no `optParam`. Beyond
these names, the module declares only instances (`deriving` clauses and a
`Lean.ToExpr` instance are the builder's choice) and the declarations Lean
generates for the names above (recursors, `casesOn`, `noConfusion`, structure
default auxiliaries and the like); every other declaration it needs is
`private`. No declaration of the module, or of this repository, is named
`m1` or `m2` (R-W5); the battery refuses the two obvious spellings.

The battery ascribes every row with `#check (@n : T)`, not with the command
under test: the command does not attest its own surface, and the conversion of
section 10 leaves this battery's ascriptions as they are.

## 5. The judgment `sameStatement`

`sameStatement fuel a b`, in `MetaM`, defined by structural recursion on the
fuel and never `partial`:

1. fuel `0`: `false`, so a comparison that runs out refuses;
2. otherwise, if `a == b` (`Lean.Expr.eqv`: binder names and binder
   annotations ignored), `true`;
3. otherwise, by the shapes of `a` and `b`, recursing with fuel one less:
   - application and application: the functions and the arguments;
   - `∀` and `∀`, `fun` and `fun`: the binder types and the bodies (names and
     annotations ignored, as `Expr.eqv` ignores them);
   - `let` and `let`: the types, the values and the bodies, **ignoring the
     `nonDep` flag** (allowance 1: Lean records a statement's non-dependent
     `let` as `have` when it elaborates a declaration's signature, and a
     standalone elaboration does not);
   - projection and projection: the same structure name, the same index, and
     the projected terms;
   - metadata and metadata: the same entries (keys and values, in order),
     then the inner terms; metadata on one side only, or different entries,
     is `false`, exactly as `Expr.eqv` treats metadata (section 12, D4);
   - constant and constant with equal universe level lists, **both
     auxiliary**: their declared types and their values, each instantiated at
     its level list (allowance 2: a `match` elaborated in a battery gets its
     own auxiliary matcher, built on its own `_sparseCasesOn_N`, where the
     declaration has `<declaration>.match_N`); a constant with no value is
     not the same as another;
   - any other pair: `false`.

Nothing else is unfolded: no constant other than an auxiliary one is replaced
by its value, and no beta, eta, zeta, iota, projection or instance reduction
is performed. Universe levels compare structurally, so a universe parameter is
compared by its name: an ascription must name the declaration's own universe
parameters (refusal R3). `statementFuel = 100000`, far above the depth of any
statement in the tree.

The command compares the standalone elaboration of `T` (left) with the
declared type (right) by `sameStatement statementFuel`.

## 6. The entry

On success the command adds exactly one declaration and prints nothing:

- name: `entryName (← getMainModule) d`, that is
  `<recording module>.frozen.<d>`; the entry of `Fixture.exact` frozen in
  `WhatwgTest.Audit.FreezeContract` is
  `WhatwgTest.Audit.FreezeContract.frozen.WhatwgTest.Audit.FreezeContract.Fixture.exact`;
- kind: a safe definition with no universe parameters, of type the constant
  `WhatwgTest.Audit.Freeze.Entry`, added by `Lean.addDecl`, so the kernel
  checks it (no `skipKernelTC`, no `Environment.addDeclWithoutChecking`); its
  reducibility hints are the builder's;
- value: the closed term `Entry.mk d a m an g ce`, each argument the
  `Lean.toExpr` form of its field at the pinned toolchain (`Name`, `Option`,
  `List`, `String`), the mask as `Option.none` or `Option.some` of one of the
  three constructor constants (`notApplicable` applied to a string literal).
  Packet 2 decodes entries in exactly this form;
- fields: `declaration` is `d`; `axioms` is `none` when the clause is absent
  and otherwise `some` of the actual axiom set (which equals the listed set),
  sorted by `Lean.Name.lt` without duplicates; `mask`, `anchor`, `graph` and
  `counterexamples` are the clauses as written, `none` or `[]` when absent,
  counterexample ids in the order written.

The registry is the set of these declarations. No persistent environment
extension is used: `initialize x : T ← e` declares `x` as an `opaque` whose
value Lean synthesises, which the trust gate's environment pass refuses in
every audited tree. The command does not compile the entry; the battery reads
entries back by `rfl`, never by evaluation. Auxiliary declarations the
standalone elaboration creates (a battery `match`'s matcher) are discarded
with `withoutModifyingEnv`; only the entry remains.

A declaration may be frozen once per recording module and in any number of
modules (at the base, 164 declarations are ascribed in two or more modules and
none twice in one). Because `WhatwgTest` may import `Whatwg` and not the
reverse, and `Whatwg/` gains no metaprogramming module (R-W1(d)), entries live
only in modules under `WhatwgTest`.

## 7. Order of checks and the refusal diagnostics

The command runs, and stops at the first refusal:

1. resolve `n` (Lean's own error for an unknown or ambiguous name; not frozen);
2. F1, the entry name is already a constant;
3. elaborate `T` alone (Lean's own error for an ill-typed `T`; not frozen);
4. F2, an expression metavariable remains; F3, a universe metavariable
   remains;
5. F4, `sameStatement statementFuel` refuses;
6. F5, `n` is a theorem (`ConstantInfo.thmInfo`) and no `axioms` clause is
   written; F6, the clause is written and its set differs from the actual set
   (each listed name is resolved as a global constant first);
7. F7 and F8, the `mask` clause; and
8. the entry is added.

Each diagnostic is an error, reported at the syntax it concerns (positions are
informative and not frozen). Verbatim, as `#guard_msgs` compares them:

| Id | Condition | Diagnostic |
| --- | --- | --- |
| F1 | a second entry for `<d>` in this module | `freeze: <d> is already frozen in this module` |
| F2 | expression hole | `freeze: the statement of <d> has an expression hole; write every argument` |
| F3 | universe hole | `freeze: the statement of <d> has a universe hole; write every universe level` |
| F4 | not the declared statement | `freeze: the statement of <d> is not the declared one` followed by the declared type printed by `Lean.indentExpr` (a line break, then the type indented by two spaces, as the battery shows) |
| F5 | a theorem without `axioms` | `freeze: <d> is a theorem; its axioms clause is required` |
| F6 | listed set differs from the actual set | `freeze: the axioms of <d> are <actual>; not listed <extra>, listed but not reached <stale>` |
| F7 | malformed mask: a word other than `M1`, `M2`, `none`; `M1` or `M2` with a string; `none` without one | `freeze: the mask clause of <d> is not mask M1, mask M2 or mask none "reason"` |
| F8 | `mask none` with a reason that is empty after trimming ASCII whitespace | `freeze: the mask clause of <d> gives an empty reason` |

In F6, `<actual>` is the `Lean.collectAxioms` set of `<d>`, `<extra>` the
actual names not listed and `<stale>` the listed names not reached. Each is
sorted by `Lean.Name.lt` with duplicates removed and rendered as plain text,
`[` then the names joined by `, ` then `]`, each name by `Name.toString`, so
the empty list is `[]` and a long list never breaks across lines (the
`MessageData` rendering of a `List Name` does, which is why it is not used).

The F3 condition is a universe metavariable with no expression metavariable;
a statement with both reports F2.

## 8. The battery

`WhatwgTest/Audit/FreezeContract.lean` imports only `WhatwgTest.Audit.Freeze`
and declares its fixtures in `WhatwgTest.Audit.FreezeContract.Fixture`. It
uses no `macro`, `syntax`, `elab`, `run_cmd` or `#eval`, so it is not a
metaprogramming module; it registers nothing and adds entries through the
listed module's command (design section 2.5 measured this shape accepted
unlisted).

Section 1 ascribes the record of section 4 and pins `entryName` on two names
and `statementFuel` by `#guard`, and refuses `ObservationMask.m1` and
`ObservationMask.m2` as unknown constants.

Acceptance controls, each wrapped in a bare `#guard_msgs` (it prints nothing)
and read back by an `example … := rfl` against the whole `Entry`:

| Id | Control | Ascription differs from the declared type by |
| --- | --- | --- |
| A1 | `Fixture.exact` | nothing (`Expr.equal`) |
| A2 | `Fixture.renamed` | a binder name |
| A3 | `Fixture.implicitMadeExplicit` | an implicit binder written explicit |
| A4 | `Fixture.withLet` | the `let`/`have` flag (allowance 1) |
| A5 | `Fixture.withMatch` | its own auxiliary matcher (allowance 2) |
| A6 | `Fixture.plainDefinition` | nothing; a definition, no `axioms` clause, entry `axioms = none` |
| A7 | `Fixture.listedDefinition` | nothing; a definition with `axioms []`, entry `axioms = some []` |
| A8 | `Fixture.excludedMiddle` | nothing; every optional clause, axioms written `[Quot.sound, Classical.choice, propext]` and recorded `[propext, Classical.choice, Quot.sound]`; `mask M1`; a census row id as anchor; a graph; two counterexample ids out of numeric order, recorded as written |
| A9 | `Fixture.settlementFixture` | `mask M2` |
| A10 | `Fixture.equationalFixture` | `mask none "…"`, reason recorded as written |

Refusal controls, each under `#guard_msgs` with its frozen diagnostic:

| Id | Control | Diagnostic |
| --- | --- | --- |
| R1 | expression hole: `Except.ok n` with its error type never written | F2 |
| R2 | universe hole: `PUnit` with its level never written | F3 |
| R3 | the universe parameter `u` written as `v` | F4 |
| R4 | a definitionally equal statement naming another function (`myLength` for `List.length`) | F4 |
| R5 | an omitted `optParam` (`Nat → Nat → Nat` for `Nat → optParam Nat 3 → Nat`) | F4 |
| R6 | a battery `match` with other patterns over the same arguments: the matchers' bodies differ | F4 |
| R7 | a theorem without `axioms` | F5 |
| R8 | an axiom reached and not listed (`propext`) | F6 |
| R9 | an axiom listed and not reached (`propext`) | F6 |
| R10 | a second entry for one declaration in one module | F1 |
| R11 | an unknown mask word (`M3`) | F7 |
| R12 | `mask M1` with a reason | F7 |
| R13 | `mask none` without a reason | F7 |
| R14 | `mask none " "` | F8 |
| R15 | metadata on one side only: the declaration annotates a lambda binder, the ascription does not, and its postponed `match` gains a `save_info` annotation | F4 |

A5 needs care. Lean's matcher cache is module-local and keyed on the
matcher's value and on the option `bootstrap.genMatcherCode`, so a battery
that declares a statement and then freezes it would reuse the declaration's
matcher and never exercise allowance 2, while a battery that imports the
declaration (every real one) always builds its own. The fixture of A5 is
therefore declared under `set_option bootstrap.genMatcherCode false`, which
gives its matcher another cache key; the command itself runs with default
options. R6 needs no such option, since its patterns differ.

Section 5 of the battery pins, under `#guard_msgs`, the `#check` output that
makes `FREEZE-CE-001` and `FREEZE-CE-002` counterexamples to today's form.

What each control validates was run, not argued: section 13 records the
prototype run. Laws about `sameStatement` beyond these controls are not
claimed.

## 9. The twelve text amendments

R-W5 names them; each adopts the declared form, keeps the ascription's
declaration name and its place, stays green under `#check`, and carries a
dated comment `-- R-W5, 2026-10-01` on the line above it saying what changed
and why. Nothing else in the three files changes.

| File | Declaration | Before | After |
| --- | --- | --- | --- |
| `WhatwgTest/Audit/SpecCoverage.lean` | `Whatwg.Streams.Data.byteLengthSize_number` | `ByteLengthAnswer.number n` | `(ByteLengthAnswer.number n : ByteLengthAnswer Size ε)` |
| same | `Whatwg.Streams.Data.byteLengthSize_undefined` | `ByteLengthAnswer.undefined` | `(ByteLengthAnswer.undefined : ByteLengthAnswer Size ε)` |
| same | `Whatwg.Streams.Data.Queue.empty_entries` | `Queue.empty sizes` | `(Queue.empty sizes : Queue α Size)` |
| same | `Whatwg.Streams.Data.Queue.empty_totalSize` | `Queue.empty sizes` | `(Queue.empty sizes : Queue α Size)` |
| `WhatwgTest/Infra/Utf8Laws.lean` | `Whatwg.Infra.Utf8.encoderTail_length` | `(encoderTail v n).length` | `List.length (encoderTail v n)` |
| same | `Whatwg.Infra.Utf8.encodeScalar_length_one` | `(encodeScalar s).length` | `List.length (encodeScalar s)` |
| same | `Whatwg.Infra.Utf8.encodeScalar_length_two` | the same | the same |
| same | `Whatwg.Infra.Utf8.encodeScalar_length_three` | the same | the same |
| same | `Whatwg.Infra.Utf8.encodeScalar_length_four` | the same | the same |
| same | `Whatwg.Infra.Utf8.encodeScalar_length_mem` | the same | the same |
| same | `Whatwg.Infra.Utf8.decodeWithoutBom_truncated_one` | the same, in its length hypothesis | the same |
| `WhatwgTest/Audit/WebIdl/CensusContract.lean` | `Gates.Census.parseRules` | `String → String → …` | `String → optParam String Gates.Census.rulesRelativePath → …` |

(Names in the Before and After columns are shortened here; the files write
them in full.)

The four holes: each declaration binds a type (`ε` or `α`) that its
statement mentions only as an implicit argument of a constructor or of
`Queue.empty`, and the ascription never wrote it, so `#check` filled it by
unification and a production change of that argument (to `Unit`, say) would
still pass (`FREEZE-CE-001`). The seven: `encodeScalar` and `encoderTail`
return `Whatwg.Infra.ByteSequence`, so `.length` elaborates to
`Whatwg.Infra.ByteSequence.length` where the declarations state `List.length`
(`FREEZE-CE-002`). The one: the declaration's second parameter is
`optParam String Gates.Census.rulesRelativePath`.

`WhatwgTest/Audit/SpecCoverage.lean`'s own gate reads the ascription names
from line starts `#check (@`; each amended ascription keeps that line start
and its name, so the gate's order check is unchanged.

## 10. The conversion (R-W8 wave 3, builder 3)

R-W5 names the change R-W1(b) asks for; this section fixes its rule and its
receipt, so that the conversion builder implements and the reviewer
re-derives.

Rule:

- Every `#check (@n : T)` **command** of the 46 battery files the design
  counts (appendix C), and of the batteries that are green at the
  conversion's base (the Q5 and W8a packets' included), becomes
  `#whatwg_freeze (@n : T)`. Commands are found by their syntax range from
  the frontend, never by a regular expression over text: six lines that read
  `#check (@` sit inside docstrings and are not commands. The bytes from `(@`
  to the matching `)` are not edited.
- A theorem's command gains ` axioms [..]` after the closing parenthesis,
  listing its `Lean.collectAxioms` set sorted by `Lean.Name.lt`. A
  non-theorem's command gains no clause (decision 3(a) of the design).
- Each converted battery gains `import WhatwgTest.Audit.Freeze`.
- Not converted: the 50 ascriptions without `@` (`inferInstance`, `rfl`,
  constructors), which stay `#check`; the 74 witness receipts (`#print axioms`
  in the 7 counterexample files), which stay until the counterexample slice
  W6b; and this packet's battery `WhatwgTest/Audit/FreezeContract.lean`.
- Retired: the 12 production `*AxiomReport.lean` modules (957
  `#print axioms` lines), with their imports in `WhatwgTest.lean`; each named
  declaration then carries its exact set in its entry. Frozen contracts and
  historical receipts that name a retired module are left as written.
- `WhatwgTest/Audit/SpecCoverage.lean`'s gate reads ascription names from the
  line start `#check (@` (its private `ascriptionNames`); after the
  conversion that reader must read `#whatwg_freeze (@` or the gate refuses
  every row. This is the one non-ascription edit the conversion needs inside a
  breaker-owned battery, and it is named here so that R-W5's ruling covers it.
- One commit per owner group of the design's section 4.

Receipt, three checks, each reproduced by the reviewer:

1. for every converted command, the bytes from `(@` to the matching `)` are
   identical before and after, except the twelve of section 9, which are
   identical to their amended text at this packet's head;
2. the multiset of (recording module, declaration) pairs of the old
   `#check (@n : T)` commands equals that of the new entries, the new side
   read by `whatwg_declsnapshot` (packet 2) and the old side by the
   conversion pass at its base; and
3. the R-V6 fingerprint (name, kind, universe parameters, type hash, and
   value hash for non-theorems) of every constant under `Whatwg` is unchanged
   between the conversion's base and its head.

The design measured, by substituting text into copies, that 2,260 of 2,272
commands pass and the twelve of section 9 are the only refusals; this packet
re-measured it (section 13). The conversion pass itself was not run.

## 11. Counterexample rows

Appended to `test/counterexamples/REGISTER.md` as one block, section "Freeze
registry witnesses". Each attacks a receipt form of the base, not a semantic
statement; the register takes them because each can change a cutover decision
(the conversion).

| Id | Attacked claim | Witness |
| --- | --- | --- |
| `FREEZE-CE-001` | hole vacuity: `#check (@n : T)` pins `T` | battery section 5 (one ascription text accepted for `Fixture.exceptPhantom` and `Fixture.exceptUnit`, two statements) with R1 and R2; at the base, the four ascriptions of section 9 in `SpecCoverage.lean` |
| `FREEZE-CE-002` | function swap: an accepted ascription names the functions the declaration names | battery section 5 (`myLength` for `List.length`) with R4 and R5; at the base, the seven of `Utf8Laws.lean` and the one of `WebIdl/CensusContract.lean` |
| `FREEZE-CE-003` | unpinned receipt: a `#print axioms n` line pins `n`'s axioms | R8 and R9; at the base, every line of the 12 `*AxiomReport.lean` modules elaborates whatever set its declaration reaches |
| `FREEZE-CE-004` | cached replay: a green `lake build` means the root's gate checked every audited module | no Lean witness: the attack is a property of Lake's trace, measured in the design's section 2.6 (two modules present and not imported by `WhatwgTest.lean`; `lake build` printed "Replayed WhatwgTest" and passed). The repair is packet 2's executable, which loads every built module on every run |

## 12. Deviations from the design and the ruling

- D1 (R-W5 over the design). `ObservationMask`'s constructors are
  `chunksAndOutcome`, `settlementOrder` and `notApplicable`, not `m1`, `m2`
  and `notApplicable`; the clause is still spelled `mask M1`, `mask M2` and
  `mask none "reason"`. No proof graph is opened (the design's
  `FREEZE-PG-REGISTRY` and its "graph" routes in section 3).
- D2 (grammar). The `mask` clause parses an identifier and an optional string
  rather than `&"M1" <|> &"M2" <|> (&"none" str)`, so a malformed clause is an
  elaboration error (F7) that `#guard_msgs` pins, as the brief's "unknown mask
  word" control requires. F8 (blank reason) is new, on the model of the trust
  gate's blank-reason refusals.
- D3 (diagnostics). Holes are split into F2 and F3. Name lists render as
  plain text sorted by `Lean.Name.lt`, not as an `Array` sorted by
  `Name.quickLt` (a hash order); the `MessageData` rendering broke a
  three-name list across lines. The recorded axiom list uses the same order,
  so two modules that freeze one declaration record one list.
- D4 (metadata). The prototype drops `Expr.mdata` on either side, a third
  allowance. R-W5 says `Expr.eqv` with the two allowances, and `Expr.eqv`
  compares metadata (measured: `Expr.eqv (.mdata {} e) e` is `false`, and two
  metadata nodes are `eqv` only with equal entries). This packet follows the
  ruling: metadata is compared, never dropped. Measured over the 2,272
  ascriptions of the base (section 15): 5 carry metadata, a `save_info`
  annotation, on both sides with equal entries, and none needs metadata
  dropped. R15 pins the refusal of one-sided metadata, which a builder that
  drops metadata would accept. A later ascription that meets it adopts the
  declared form, as the twelve of section 9 do.
- D5 (universe names). The design left "a battery that names its universes
  differently" unchecked. Under `Expr.eqv` it is another statement; R3 pins
  that.
- D6 (battery shape). Acceptance controls are additionally wrapped in a bare
  `#guard_msgs`, which pins "prints nothing", and read back by `rfl`; the
  battery adds A7 to A10 and R3, R6, R11 to R15 beyond the brief's list.

## 13. Claim scope: what a freeze does not pin

- A definition's body. The statement is the type; a body change that keeps
  the type passes. With an `axioms` clause, the body's axiom set is pinned
  and nothing else of it.
- A theorem's proof, beyond its axiom set.
- Binder names and binder annotations of the declared type: an implicit
  argument made explicit in production passes the freeze (A3 is that
  direction). The declaration snapshot of packet 2 digests the type with
  both, so it records such a change.
- The `let`/`have` flag, and the identity of auxiliary constants whose types
  and values agree under section 5.
- Docstrings, attributes (`simp`, `reducible`, `instance`), declaration
  ranges, the module that declares `n`, and whether `n` is public.
- Whether the `anchor` is a census row id, the `graph` an edge, or the
  counterexample ids rows of the register: the command records them as
  written. Packet 2 joins anchors; graphs are W7's and counterexample ids
  W6b's.
- Anything in a battery that stays `#check` (section 10), and the 74 witness
  receipts.
- A module that is never built. An entry is checked when its module
  elaborates; `lake build` elaborates every module under `WhatwgTest/` (the
  library's glob is `WhatwgTest.*`), and Lake re-elaborates a battery when
  any module it imports changes, so a production statement change re-runs its
  freezes. A replayed root gate is `FREEZE-CE-004`.
- Universe-polymorphic equality up to renaming: none is granted (R3).
- A pass of this battery means: against the implementation under test, the
  fifteen frozen refusals are refused with their diagnostics and the ten
  acceptances are accepted silently with the stated entries. It is a finite
  set of controls, not a proof about `sameStatement`.

## 14. Red state at the freeze

Narrow command:

```text
lake build WhatwgTest.Audit.FreezeContract
```

At the freeze it fails because `WhatwgTest.Audit.Freeze` does not exist;
section 15 records the exact output. The default `lake build` fails on this
module and on nothing else; `WhatwgTest.lean` does not import it (R-W9), so
the root gate's closure check does not see it until builder 1 adds the
imports, and Lake replays the root (that is `FREEZE-CE-004` at work, and the
reason builder 1 runs the root build after adding the imports).

## 15. Freeze run

Recorded in the commits that follow this one on the same branch.
