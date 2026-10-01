# Implementation review, 2026-09-30

Status: research record. It states findings and a recommended order of work.
It makes no Model Claim, closes no graph edge, and changes no disposition.
The rulings that act on it are in `COORDINATION.md` (R-V1 to R-V5, R-U5).

## Scope and pins

The review covers four questions the operator asked on 2026-09-30:

1. whether the proof graphs are accurate and how to clean them up;
2. whether the Lean representation and proofs are clean;
3. whether the tooling uses what Lean 4.33.1 core, Std and Lake offer;
4. whether the public surface is usable by lean4-effect4.

| Subject | Pin |
| --- | --- |
| this repository | `main` at `baa8656d3a4c929ac1b8a5a7d162305dc355ff23` |
| lean4-effect4 | `refactor/phase1-phase3` at `0f16828aba1d6d811701286b204c79218f73fb3b` |
| toolchain, both | `leanprover/lean4:v4.33.1`, Lake 5.0.0 |
| `effects` | here `c28833b` (v0.5.0); effect4 `a4ee7a1` (v0.8.0) |
| `typescript` | here `fcbc05a` (v0.2.0); effect4 `6afc9b8` (v0.6.0) |
| `hash` | here `0168306`; effect4 `c906b15` |

## Method and evidence classes

Five read-only seats read the tree in parallel: proof graphs, the Streams
calculi, the libraries beneath Streams, the gates and metaprogramming, and
the fit with lean4-effect4. No seat ran `lake` or edited a file. The
coordinator ran the build, the timings, the axiom census and the gate probe,
and re-read the source behind each seat's main claims.

Each finding below carries one of three labels.

- `[C]`: measured or read by the coordinator at the pins above.
- `[S]`: read by a seat with a file and line; not re-read by the coordinator.
- `[H]`: a hypothesis that needs a build or an experiment to confirm.

## Measurements

### Build

`lake build` at the pin replays 396 jobs and exits 0. The axiom gate reports
216 modules and 16,233 declarations, 1,477 of them in the `Gates` tree. `[C]`

### Elaboration time per file

Elaboration cost is low, so no proof needs restructuring for build time.
Each file was elaborated alone with

```text
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dprofiler=true <file>
```

| File | Wall time | Dominant profiler category |
| --- | ---: | --- |
| `WhatwgTest/Audit/Ecma262/EcmarkupScanner.lean` | 28.1 s | interpretation 25.4 s |
| `Whatwg/Streams/Piping/Laws.lean` | 11.9 s | `simp` 12.5 s cumulative, `grind` 1.1 s |
| `Whatwg/Streams/Piping/Runs.lean` | 11.4 s | `simp` 6.3 s |
| `WhatwgTest.lean`, the gate | 8.5 s | interpretation 6.4 s |
| `Whatwg/Html/Content/Transparent.lean` | 7.8 s | type checking 6.9 s |
| `WhatwgTest/Audit/WebIdl/CensusQ2Contract.lean` | 7.3 s | interpretation 4.8 s |
| `Whatwg/Infra/Text/Utf8.lean` | 5.5 s | tactic execution |
| `Whatwg/Streams/Writable/Laws.lean` | 5.5 s | `simp` 6.2 s |

A four-at-a-time pass over the 120 files of 100 lines or more summed to
about 260 s once four `lake env` cold-start outliers are removed. `[C]`

The slowest file in the tree is a test battery that runs the ecmarkup scanner
over the 2.9 MB ES2026 source in the interpreter at elaboration time.

### Reach of `Classical.choice`

lean4-effect4 accepts `propext` and `Quot.sound` only, so the count of
declarations that reach `Classical.choice` decides what it can cite. The
census in appendix B walks every constant whose module is under `Whatwg` and
calls `Lean.collectAxioms` on it. `[C]`

| Module | Declarations | Reach choice | Authored theorems reaching choice |
| --- | ---: | ---: | ---: |
| `Whatwg.Ecma262.Jobs` | 169 | 0 | 0 |
| `Whatwg.Ecma262.Promise` | 493 | 4 | 4 |
| `Whatwg.WebIdl.Promise` | 104 | 2 | 2 |
| `Whatwg.WebIdl.Exceptions` | 222 | 0 | 0 |
| `Whatwg.Infra.Text.Utf8` | 1,095 | 65 | 17 |
| `Whatwg.Infra.Namespaces`, `Text.Scalar`, `Text.String` | 58 | 8 | 0 |
| `Whatwg.Html.Print.Escape`, `Print.Render` | 311 | 76 | 26 |
| `Whatwg.Streams.Piping.Laws`, `Piping.Runs` | 727 | 80 | 3 |
| `Whatwg.Streams.Semantics.*` | 1,309 | 30 | 5 |
| `Whatwg.Streams.Transform.Laws`, `Transform.Runs` | 426 | 6 | 6 |
| `Whatwg.Streams.Readable.Laws` | 163 | 4 | 2 |
| `Whatwg.Streams.Writable.Laws`, `Writable.Lifecycle` | 336 | 3 | 3 |
| every other module under `Whatwg` | 7,393 | 0 | 0 |
| total | 12,806 | 278 | 68 |

The census also counts 25 Lean-generated equation lemmas in `Html.Print`
that reach choice through `String`. Appendix A lists the 68 authored names.

Two facts follow. `Whatwg.Ecma262.Jobs` is already choice-free in every
declaration. The promise libraries need six proofs repaired, which does not
match the "34 declarations" in lean4-effect4's design issue DI-30.

### A `native_decide` inside an `example` is not rejected

```lean
example : (List.range 2000).length = 2000 := by native_decide
```

elaborates with exit code 0 under `-DwarningAsError=true`. `[C]` An `example`
is elaborated without modifying the environment, so the auxiliary axiom never
becomes a constant the axiom gate can find, and Lean emits no warning. The
source-token pass in `WhatwgTest/Audit/AxiomGate.lean` refuses only `unsafe`
and `partial`. The tree holds 146 `example` commands and none uses
`native_decide` today, so the hole is open but unused.

### A narrow run of the gate fails

`lake env lean WhatwgTest.lean` from the repository root fails with "source
file has no parent directory", because the relative file name has no parent
component. `[C]` The same run with `.\WhatwgTest.lean` passes. lean4-effect4's
gate makes the path absolute first.

## Proof graphs

The theorem names and battery counts in the graph documents match the tree.
A seat resolved about 60 sampled names across all graphs and re-counted
every battery; the one miscount is the 85 against 86 ascriptions already
recorded as debt D40. `[S]` The defects are in the status around the
statements.

### Edge status is not stated in one place

`docs/PROMISE-DAG.md` holds seven successive ten-edge tables and
`docs/CONFIGURATION-DAG.md` four. About 40 % of the ten graph documents'
2,794 lines is landing, amendment and review history. `[S]` A reader has to
replay the appendices to learn the current state of an edge.

### Rulings change edge state without touching the graphs

The landing commit for R-P27 and R-U4 edited the coordination record, the
plan and the register, and no graph document. `[S]` Four contradictions
result.

- R-U4 and the plan say the URL `encoding` obligation closes.
  `docs/URL-PERCENT-ENCODING-DAG.md` says it stays open, and the module
  docstring of `Whatwg/Url/Boundary.lean` still says no UTF-8 core has
  landed. `[C]`
- `docs/INFRA-UTF8-DAG.md` has no landing section; its laws and trust edges
  still read as at the freeze. `[S]`
- `docs/CONFIGURATION-DAG.md` holds its trust edge open on an independent
  review that R-P27 records as done. `[S]`
- `docs/DATA-DAG.md`'s only edge table is the freeze-time one; the landing
  prose below it closes the edges. `[S]`

### The generated declaration snapshot does not exist

`docs/AGENT-ROUTING.md` requires a generated declaration snapshot that joins
every exported type to one authored row, and the resume protocol in
`AGENTS.md` reads a per-declaration assurance row. Neither projection
exists: `generated/` holds the census files and the vendor manifest only,
and `Whatwg/Streams/Meta/{Introspection,Emit}.lean` and
`Whatwg/Streams/Audit/{Receipts,Closure}.lean` are empty stubs. `[C]` Ten
graphs hold their identity edge open on this one missing generator. `[S]`

### Axiom receipts pin nothing

`WhatwgTest` contains 1,034 `#print axioms` lines and no `#guard_msgs`
outside `WhatwgTest/Html/Breakers.lean`. `[C]` A receipt line therefore
asserts only that the name resolves. Every receipt breakdown the documents
quote is build output copied by hand. The stricter targets, R-U3's for Infra
and the URL lane's, are enforced by nothing: the gate's two ceilings are the
same list since R-11. `[C]`

The repository already has the stronger pattern in two places:
`WhatwgTest/Audit/SpecCoverage.lean` freezes exact receipts for its 55
coverage witnesses, and the two `*ConstructiveContract.lean` files under
`WhatwgTest/Infra` check a stricter ceiling with `collectAxioms`. `[S]`

### Statements are maintained three times

A theorem's statement is written in production and again in a battery as
`#check (@name : statement)`; its name is listed a third time in an axiom
report. `WhatwgTest` holds 2,278 such ascription lines against 1,492
`theorem` declarations in `Whatwg`. `[C]` Each ascription also prints an
`info` message, so a build log carries more than two thousand lines of
replayed output.

### Counterexample closure is mostly prose

The witness modules for the Data, Readable, UTF-8 and percent-encoding
registers import `Init` or `Std` and no production module, so "the
implementation rejects the attack" is an argument in the register, not a
Lean link. `[S]` Fifty-one attack identifiers, the `INFRA-UTF8-CE`,
`ECMA-CEN-CE` and `WEBIDL-CEN-CE` families, are absent from
`test/counterexamples/REGISTER.md`. `[S]`

### Other status drift

- `README.md` says "no semantic declaration exists yet" and names two Lake
  dependencies; there are three. `[C]`
- `docs/ARCHITECTURE.md` and `SPEC-MANIFEST.md` call Ecma262, WebIdl and Url
  declaration-free. `[C]`
- Forty-seven modules carry the docstring "This breadth stub intentionally
  declares no semantic object"; eight of them now declare semantic objects.
  `[C]`
- `lake exe trustselftest` is not a CI step, and graph trust edges cite it.
  `[C]`
- `Whatwg/Html` (200 public theorems) and Infra text outside UTF-8 sit under
  no graph and no leaf record. `[S]`

### Recommended shape

Edge status becomes a Lean ledger: goals, the kind of evidence for each
(proved, wanted, attested by ruling, checked by a named gate, not
applicable), and the dependencies between graphs. The markdown table is
rendered from it, and landing history moves to a receipts log beside each
graph. lean4-effect4's `tools/ProofGraph` has the right structure, but its
ceiling is hard-coded to `propext` and `Quot.sound`, it imports Batteries,
and its `checked_theorem%` quotes a theorem's current type, which validates
a reference and does not freeze a statement. The idea ports; the code does
not.

## Lean representation and proofs

### Streams

The five calculi repeat the same structure. `[S]`

| Duplicate | Sites |
| --- | --- |
| `Step`, `Steps` or `Reaches`, and the nil, cons and append lemmas | `Readable/Step.lean`, `Writable/Step.lean`, `Transform/Step.lean`, `Piping/Step.lean`, `Semantics/Step.lean` |
| job queue, its view and its dequeue bridge | Readable, Writable, Transform, `Semantics.Config` |
| promise table | Readable `readPromises`, Writable `promises` with `handled`, `Ecma262.Promise.Table` |
| `exceptDecidableEq`, `Size`, `sizes` | `Readable/State.lean:20`, `Writable/Stream.lean:28` `[C]` |
| hand-rolled `find?` over `map` induction | five sites where core `List.find?_map` applies |

A generic labelled-transition kernel with per-calculus `abbrev`s would
remove the first row without changing a frozen statement.

Every identifier is a bare `Nat`. Readable's `Event.sizeCalled` takes
`(call algorithm)` and Writable's takes `(algorithm call)`, so the two `Nat`
arguments are in opposite order. `[S]`

Several invariants are stated and not carried. `[S]`

- `Queue.WF` and `SizesAdmissible` are proved per queue operation and never
  lifted to the Readable or Writable machines.
- Registration-id `Nodup` is a hypothesis of two bridge theorems with no
  preservation theorem.
- `CellsWellFormed` is named as discharging a conjunct in
  `Whatwg/Streams/Semantics/Configuration.lean:206` and is declared nowhere.
  `[C]`

`Whatwg/Streams/Semantics` lifts `Writable.tick` and `Writable.decide` only.
Transform, Piping and Semantics are three independent schedulers over the
same Writable step, and `Readable.Steps` cannot run its own pull reactions.
The module docstring of `Semantics/Runs.lean` names a big-step face and a
fixed-fuel runner; neither is declared. `[S]`

Proof style is where the fragility lives. `[S]`

- 217 `simp_all`, 271 anonymous `intros`, 96 `first | rfl | (simp_all … <;> rfl)`.
- Four `attribute [local simp]` lists of 24 to 85 names.
- `Piping/Runs.lean`'s local list names none of `freshReadCell`,
  `settleReadCell`, `settleReadCells`; it depends on the three global
  `@[simp]` attributes of debt D43. Adding the three names to the local
  lists is the likely repair. `[H]`
- Four functions are named `decide` and shadow `Decidable.decide`.

The Streams reach of `Classical.choice` has three sources. `[S]` for the
sites, `[C]` for the affected names.

- `by_cases` on a proposition with no `Decidable` instance:
  `Readable/Laws.lean:1021`, `Writable/Laws.lean:1552`, and three sites in
  `Semantics/Configuration.lean`.
- Six `grind` calls in `Piping/Laws.lean`.
- Composed-run theorems that inherit from the above.

### Ecma262 and WebIdl

`Whatwg.WebIdl.Promise.resolve` and `reject` are `Table.settle`
(`Whatwg/WebIdl/Promise.lean:59`). `[C]` Their signatures carry neither the
reaction store nor the job queue, so a `react` followed by a `resolve`
enqueues no job. Only `fulfillPromise` and `rejectPromise` in
`Whatwg/Ecma262/Promise.lean` trigger reactions. No recorded debt names
this.

The operations thread `Table`, `Reactions` and `Queue` as three separate
arguments and return 4- and 5-tuples read through `.2.2.1`. `[C]` There is
no single agent record and no step function over it, and three counters
(`Table.next`, `Reactions.next`, the function seed) advance independently.
`[S]`

`Promise.Table` has no well-formedness predicate; `Table.mk` is public, so
duplicate identifiers are constructible, which is why `Table.fresh_get`
carries a freshness hypothesis. `[S]`

Both `Whatwg/Ecma262/Jobs.lean` and `Promise.lean` import `Whatwg.Infra` and
use no symbol from it. `[C]` A consumer importing the job queue therefore
elaborates fifteen Infra modules including `Utf8.lean`.

Many theorems in these modules restate a definition by `rfl`
(`Queue.enqueue_eq`, `step_checkpoint`, `FifoRequirement_iff`). `[C]` They
are accurate and carry no automation value, since none is a `simp` lemma.

### Infra text

The UTF-8 choice debt (D42) has one dominant mechanism. `[S]` The `omega`
frontend turns a hypothesis of the form `¬(P ∧ Q)`, `P → Q` or `P ↔ Q` into
a disjunction through `Classical.propDecidable`, and proves a conjunctive
goal by contradiction. The percent-encoding builder knew this and split its
goals (`Whatwg/Url/PercentEncoding.lean:153`); the UTF-8 packet did not.
Splitting conjunctions before `omega` and replacing negated-conjunction
`by_cases` is proof-only work at 20 to 25 sites.

`Utf8.lean` is long because `run_scalar_one` to `run_scalar_four` simulate
the queue machine one byte at a time, about 460 lines, and re-prove what the
generic step lemmas later in the file provide. `[S]` Bit arithmetic is
already confined to six bridges.

No theorem relates `encodeScalar` to core's `String.utf8EncodeChar`,
although both use the same division form. `[S]` lean4-effect4 has its own
choice-free codec over the core function, so that bridge is what would let
the two agree.

The codec is a specification model: `IoQueue.push` is linear, so decoding is
quadratic. `[S]`

### URL

`Whatwg/Url/Boundary.lean` declares `Utf8Encoding` as a record of an input
and any byte sequence. `[C]` `Whatwg.Infra.Utf8.u3Profile_encoderTape` and
`u3Profile_decodeOrFail` prove the two facts the boundary assumes, as facts
about Infra's own functions. No declaration constructs a `Utf8Encoding` from
the Infra encoder, so the URL operations still accept an arbitrary `bytes`
field. Five private lemmas in `PercentEncoding.lean` re-prove public Infra
lemmas. `[S]`

### HTML

The HTML tables are hand-authored since the TyXML generator was retired.
`[S]`

- `Tag.elementIndex?` is a table of positions with no theorem that
  `t.element? = some e → e.tag = t`.
- `Attr.markupName` is not checked against `attributeCtors`.
- `Element.mk` is public, so a typed element can be built from unchecked
  raw children.

## Tooling and metaprogramming

### The trust gate

| Channel | Refused today | Evidence |
| --- | --- | --- |
| `sorryAx`, `ofReduceBool`, `trustCompiler`, native auxiliary axioms on a constant | yes | `AxiomGate.lean` `[C]` |
| `unsafe`, `partial` | yes | token pass and environment pass `[C]` |
| `native_decide`, `bv_decide`, `decide +native` inside an `example` | no | probe above `[C]` |
| `@[implemented_by]`, `@[extern]` | no | lean4-effect4's gate refuses both `[C]` |
| an `opaque` with no body, a declared `axiom` | no | lean4-effect4's gate refuses both `[C]` |
| declarations under `bin/` | not audited | `auditedSources` omits `bin/` `[S]` |
| `set_option debug.skipKernelTC` | no | only a kernel replay (`leanchecker`) catches it `[S]` |

`Lean.collectAxioms` on an imported declaration is a binary search into a
per-module table computed when the `.olean` is written
(`Lean/Util/CollectAxioms.lean` at v4.33.1). `[C]` The gate's
per-declaration loop is therefore cheap, and the measured 6.4 s is mostly
`environment.constants.toList` and the tokenizer.

Four copies of this gate exist: here, lean4-effect4, lean4-effects and
lean4-hash. They have drifted, and lean4-effect4's is the most complete.

### Gates read files Lake does not track

`WhatwgTest/Audit/SpecCoverage.lean`, `CensusProfileIdentity.lean` and the
census contract batteries read TSV files, generated files, a document and
other modules' source text at elaboration time. `[S]` A Lake module trace
covers imports, the source and the options, so on a cached build these gates
replay an earlier verdict. `[[input_file]]` targets with `needs`, or a
runtime lint executable, close this.

### Scanners

`Gates/Census.lean` caps occurrence scans (4,096 headings, 8,192 definitions)
and continues silently past a cap. `Gates/Ecmarkup.lean` states the opposite
rule, that a cap hit is an error. `[S]` Every current pin is below the caps,
so erroring caps would change no generated byte. The three scanner stacks
re-spell their byte primitives and have two different `stripTags`.

### Packaging

- `docs/AGENT-ROUTING.md` rules that a package's tooling tree and executable
  roots carry the package prefix. This package's own `Gates.*`, `bin.Census`
  and the bare roots `VendorSeal`, `Citations`, `UrlInventory`, `UrlCensus`
  and `TrustSelfTest` do not. `[C]` lean4-hash follows the rule as
  `HashGates`, `hashbin.*` and `hash_*`.
- `bin/Census.lean` imports the three coverage numerators, so the default
  build compiles and links all of `Whatwg.Streams` to native code. `[C]`
- `effects` and `typescript` are required and imported by nothing. `[C]`

### What to adopt and what to leave

| Capability | Verdict | Reason |
| --- | --- | --- |
| a `freeze` command writing to a persistent environment extension | adopt | pins receipts, yields the declaration snapshot, makes mask and anchor checkable data |
| `leanchecker` in CI | adopt | the only check that catches an unchecked declaration |
| `lintDriver`, `testDriver`, `weakLeanArgs = ["-M…"]` | adopt | present in Lake 5.0.0, unused here |
| `fun_cases`, `fun_induction` | adopt in proofs | inversion lemmas for `tick` and `decide` replace split cascades |
| `register_simp_attr` | adopt | one named run set replaces four local lists |
| `grind` in `Whatwg/` | leave out | it reaches `Classical.choice` |
| the module system | defer | no dependency has a module file, and a module exports theorems as axioms |
| `Std.Do` and `mvcgen` for `Logic/Wlp` | leave out | it presumes a bind law the design basis rejects for fixed fuel |
| `Std.Internal.Parsec` | leave out | its combinators are `partial` |
| lowering P11 from LCNF | leave out | the semantic owner is first-order combinator data |

## Fit with lean4-effect4

### Trust

lean4-effect4's gate audits only `Effect4.*` and `Test.*` modules and
follows axioms transitively (`Test/Audit/AxiomGate.lean:325`, `:464` at its
pin). `[C]` Importing this package costs nothing at that gate. A
lean4-effect4 declaration fails only when it cites a provider constant that
reaches `Classical.choice`. The definitions in `Whatwg.Ecma262` and
`Whatwg.WebIdl` contain no proof terms, so they are citable today; the six
theorems of appendix A are what DI-30's refusal applies to.

### Demand

lean4-effect4 built an unproved ECMAScript promise host
(`OCaml5/Runtime/Promise.lean`) and archived it in its commit `ab9f464b`.
`[S]` `Whatwg.Ecma262` is the proved counterpart. Its `DeferredStore`
relates to `Promise.Table` by a projection under M1. Its stream kernel is
three external rows, open, pull and close, with answer `Option (List α)`
(`src/Effect4/Program/Stream.lean`). `[C]` It has no Channel calculus, so
P12's "Effect Channel embedding" has no target, and it retired the Flow
route that `docs/REIFICATION-STRATEGY.md` section 5 lowers through. `[S]`

### Shared substrate

`docs/REIFICATION-STRATEGY.md` RS-3 says each stateful standard is an
`Effects.Signature` with one canonical `Handler`. Nothing under `Whatwg/`
imports `Effects`. `[C]` The calculi are bespoke step functions, so
lean4-effect4 cannot sum a provider signature with its own.

`Effects.Trace.Mask.m1` keeps operations, answers and the outcome, and `m2`
keeps every event (`Effects/Trace.lean` at v0.8.0). `[C]` Design basis DB-04
uses the same two names for chunk sequence plus terminal outcome, and full
settlement order. The names agree and the meanings differ.

At v0.8.0 `Effects.Morphism` and `Effects.Transport` moved under
`Effects.Experimental`, with no contract. `[S]` A bridge built on signature
morphisms would rest on that.

### API shape

- No agent record: a consumer threads three stores by hand. `[C]`
- `Reaction` derives `Repr` only and `Reactions` derives nothing, so neither
  embeds in a record that derives `DecidableEq`. `[S]`
- Every type outside `Streams.Data` is fixed at `Type`. `[S]`
- 334 `private` declarations under `Whatwg/` hide reusable helpers. `[S]`
- The laws are importable without the test library: 1,492 theorems live
  under `Whatwg/`. `[C]`

## Recommended order

| # | Change | Cost | Touches a frozen statement |
| --- | --- | --- | --- |
| 1 | Repair the six promise proofs; enforce a `propext`, `Quot.sound` ceiling per module prefix in the gate | small | no |
| 2 | Harden the gate: `extern`, `implemented_by`, bodyless `opaque`, declared axioms, trust tokens in any command, `bin/`, the path bug; `trustselftest` and `leanchecker` in CI | small | no |
| 3 | Drop the unused Infra import; align the three pins; prefix the tooling tree and executable roots | small | no; four generated-file identity pins change by their import line |
| 4 | Repair the contradicting status lines; one current-state edge table per graph; history to a receipts log | small | no |
| 5 | D43; constructive `by_cases`; remove `grind` from production; the `omega` discipline in `Utf8.lean` | small to medium | no |
| 6 | A `freeze` registry: pinned receipts, the declaration snapshot, masks as data | medium | converts breaker-owned files; needs a ruling |
| 7 | A Lean graph ledger with the markdown as its projection | medium | needs a ruling |
| 8 | A generic transition kernel; one promise table and one job queue | medium | mostly no |
| 9 | `Ecma262.Agent` with one step function; `resolve` triggers reactions; an `Effects.Signature` face | medium to large | new packet |
| 10 | Retarget P11 and P12; one shared gate package across the four repositories | plan level | cross-repository |

Rows 1 to 5 are opened as slices V1 to V5 by rulings R-V1 to R-V5.

## What this review did not check

- No WPT run and no host observation.
- No statement was compared against the specification text; fidelity
  findings above come from recorded debts and from reading definitions.
- The `[S]` findings were not re-read by the coordinator, and the `[H]`
  finding on D43 was not tried.
- lean4-effect4 was read at one commit on a working branch.

## Appendix A: authored theorems reaching `Classical.choice`

Names are relative to `Whatwg`.

Ecma262 and WebIdl (6):
`Ecma262.Promise.Table.fresh_get`, `Ecma262.Promise.Table.settle_handled`,
`Ecma262.Promise.Table.markHandled_idem`,
`Ecma262.Promise.ResolvingFunctions.callResolveSelf_self`,
`WebIdl.Promise.waitForAll_success`, `WebIdl.Promise.waitForAllTraced_success`.

Streams (19):
`Streams.Readable.readTable_settleReadCell`,
`Streams.Readable.readTable_settleReadCells`,
`Streams.Writable.settle_bridge`,
`Streams.Writable.lifecycle_abort_rejection`,
`Streams.Writable.lifecycle_write_close`,
`Streams.Transform.freshInternal_new`,
`Streams.Transform.settle_table_bridge`,
`Streams.Transform.settle_waiting_once`,
`Streams.Transform.coupled_error_during_transform`,
`Streams.Transform.coupled_positive_readable_capacity`,
`Streams.Transform.coupled_write_read_enqueue`,
`Streams.Piping.forwardShutdown_realizes`,
`Streams.Piping.lifecycle_two_writes_abort_rejection`,
`Streams.Piping.lifecycle_write_rejection_retains_source`,
`Streams.Semantics.Ordering.notifySettled_queued_serial`,
`Streams.Semantics.Ordering.notifySettled_reactions_bridge`,
`Streams.Semantics.Ordering.successfulControl_sink_at_most_one`,
`Streams.Semantics.Ordering.Source.erases_prefix_selected_order`,
`Streams.Semantics.Ordering.Source.erasure_preserves_selected_order`.

Infra UTF-8 (17), all under `Infra.Utf8`:
`decodeWithoutBomOrFail_encode`, `decodeWithoutBomOrFail_eq_some_imp`,
`decodeWithoutBomString_encode`, `decodeWithoutBom_all_isScalarValue`,
`decodeWithoutBom_encode`, `decodeWithoutBom_encodeScalars`,
`decodeWithoutBom_truncated_one`, `decode_all_isScalarValue`,
`decoderHandler_error_none`, `decoderHandler_items_isScalarValue`,
`encodeScalar_head_range`, `encodeScalar_tail_continuation`,
`encode_decodeWithoutBom`, `encode_startsWith_bom_iff`,
`encoderTail_continuation`, `isWellFormed_iff`, `processQueue_fuel_stable`.

HTML printing (26), under `Html.Print` unless qualified:
`escapeString_injective`, `toList_escapeAndAtString`, `toList_escapeString`,
`Html.Child.render_eq`, `Html.Element.render_eq`, `afterPrefix_close_ne`,
`decodeAttrs_render`, `decodeNode?_render`, `decodeNode?_renderChars`,
`decode_render`, `nameOk_facts`, `nameOk_markupName`, `nameOk_of_markupName`,
`renderAttr_value_no_quote`, `renderAttrs_head_not_name`,
`renderCharsList_not_injective`, `renderChars_injective_of_wf`,
`renderChars_markup_head`, `renderChars_ne_nil`, `renderChars_not_injective`,
`renderChars_text_no_control`, `renderChars_text_no_delim`,
`render_injective_of_wf`, `toList_render`, `toList_renderDoc`,
`toList_renderList`.

The HTML names reach choice through core's `String` API, which the research
record of 2026-09-01 measured as reaching `Classical.choice` almost
everywhere. They are out of scope for slices V1 and V5.

## Appendix B: the census script

Run from the repository root as `lake env lean <path>/ChoiceCensus.lean`
after `lake build`. It was run from a session scratch directory and is not
part of the tree; slice V2 moves its report into the gate.

```lean
import Lean
import Whatwg

open Lean

def choiceCensus : CoreM Unit := do
  let env ← getEnv
  let mut tally : Std.HashMap Name (Nat × Nat × Nat × Nat) := {}
  let mut choiceTheorems : Array (Name × Name) := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[idx.toNat]? | continue
    unless (`Whatwg).isPrefixOf moduleName do continue
    let axioms ← collectAxioms name
    let reaches := axioms.contains ``Classical.choice
    let isThm := match info with | .thmInfo _ => true | _ => false
    let userFacing := isThm && !name.isInternal && (privateToUserName? name).isNone
    let (d, dc, t, tc) := tally.getD moduleName (0, 0, 0, 0)
    tally := tally.insert moduleName
      (d + 1, dc + (if reaches then 1 else 0),
       t + (if userFacing then 1 else 0), tc + (if userFacing && reaches then 1 else 0))
    if userFacing && reaches then choiceTheorems := choiceTheorems.push (moduleName, name)
  for (moduleName, (d, dc, t, tc)) in tally.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"{moduleName}\t{d}\t{dc}\t{t}\t{tc}"
  for (moduleName, name) in choiceTheorems do
    IO.println s!"{moduleName}\t{name}"

#eval choiceCensus
```

`userFacing` admits Lean-generated equation lemmas (`f.eq_1`, `f.eq_def`),
which is why the script's theorem total is 93 and the authored total is 68.
