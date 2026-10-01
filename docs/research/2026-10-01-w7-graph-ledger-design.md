# W7 design: a Lean graph ledger with the markdown as its projection

Status: design record of the W7 seat of review lane W (ruling R-W0). It
states a recommended design, the measurements behind it and the decisions it
leaves to the coordinator. It makes no Model Claim, closes no graph edge,
changes no disposition and edits no graph document. Base commit `97a8715`.
Evidence labels follow `docs/research/2026-09-30-implementation-review.md`:
`[C]` measured by this seat with the command given, `[S]` read in source,
`[H]` a hypothesis not tried. The prototype it measures was built in the
seat's worktree and is not committed; its source is appendix A.

## 1. Recommendation

Edge status moves out of the eleven hand-written "Current state" tables into
plain Lean data, and each table becomes a generated projection that a gate
compares byte for byte. Nothing declares a command, an elaborator or a
metaprogram, so no module joins `metaprogrammingModules`.

- Model. `WhatwgGates/Ledger/Model.lean` imports only `Init`. A graph has
  exactly ten edge fields, so an entry that omits or repeats an edge does
  not elaborate. A cell is `requiredOpen`, `requiredClosed` or
  `notApplicable` and carries grounds (theorems, declarations, receipt and
  ascription counts, modules, a gate, a ruling, a receipts-log heading,
  register rows, another graph's closed edge), open items (a name, a debt,
  register rows, a wanted theorem, another graph's open edge), recorded
  debts and a prose note.
- Data. One module per graph under `WhatwgTest/Ledger/`, importing only the
  model, with single-backtick names. `WhatwgTest.Ledger.ledger_wellFormed`,
  proved by `decide +kernel`, states that no cell is closed with an open item
  or no ground, open with nothing named, or not applicable without a reason,
  and that cross-graph citations and dependencies resolve and are acyclic.
- Reference pass. `lake exe whatwg_ledger` imports the built environment
  from `.olean` files at run time, as `leanchecker` does, and resolves every
  theorem, declaration, module, count, ruling, debt, register row, heading
  and gate the ledger names. It links 8 objects, none of `Whatwg`, and reads
  files at run time, so debt D49 does not reach it.
- Projection. `generated/graphs/<GRAPH-ID>.md`, written by
  `lake exe whatwg_ledger --write`. Each graph document keeps a "Current
  state" paragraph and a link; its table moves verbatim to the receipts log.
- Rulings. A ruling that changes an edge writes `GRAPH-ID/edge=status` as a
  code span. The gate fails when the latest token disagrees with the ledger
  or the cell does not cite the ruling, and when a ruling names a graph by
  identifier or document path that the ledger neither cites nor acknowledges.

Order: a breaker freezes `test/contracts/graph-ledger.contract.md` and its
battery; builder slice A lands the model, the executable, the three
prototyped graphs and the one leaf record; slice B seeds the other eight
graphs and moves the tables; the coordinator applies routers and CI; slice D
adds module routing and the uncovered-tree records. W6 is not a
prerequisite: evidence names constants, and W6's registry later tightens the
theorem check by the same key.

## Answers to the brief

| Question | Answer | Evidence |
| --- | --- | --- |
| (a) data model | the types of section 3; invariants and their checkers below | 2.4, 2.6, 2.7 |
| (b) reference checking | single-backtick names; existence and kind checked by the executable over `.olean` files | 2.5, 2.8 |
| (c) placement and cost | data in `WhatwgTest/Ledger/`, code in `WhatwgGates/Ledger/`; the executable links no `Whatwg` object; import graph below | 2.5 |
| (d) projection | `generated/graphs/<GRAPH-ID>.md`; `lake exe whatwg_ledger --write` regenerates, `lake exe whatwg_ledger` compares; files read at run time, so D49 does not apply | 2.6, 2.14 |
| (e) two graphs | `DATA-PG-QUEUE`, `PROMISE-PG-FIRST` and `CONFIGURATION-PG-ORDERING` encoded, rendered and compared | 2.10, 2.11 |
| (f) rulings | edge tokens and the mention check, in the executable | 2.7, 2.9 |
| (g) lean4-effect4 | the join, `wanted` and the cycle check port; the commands, the search and the ceiling do not (table below) | 2.13 |
| (h) W6, W10 | names, not registry entries; W7 first; the executable is W10's shape | section 6 |
| (i) uncovered trees | `unrouted` entries citing a new debt; the routing decision is not this slice | 2.12, decision 7 |

| Invariant | Checked by | Fails in |
| --- | --- | --- |
| ten edges, each once | the fields of `Edges` | elaboration |
| closed: a ground, no open item, no row cited other than `CLOSED` | `ledger_wellFormed`, kernel | `lake build` |
| open: at least one item; not applicable: a reason and nothing else | the same | `lake build` |
| graph and leaf identifiers distinct; dependencies known, not reflexive, acyclic | the same | `lake build` |
| a cross-graph ground cites a closed edge, a cross-graph item an open one | the same | `lake build` |
| a theorem ground names a theorem; declaration and module grounds exist | the executable | `lake exe whatwg_ledger` |
| a receipt or ascription count equals the commands in the module source | the executable | the same |
| a ruling is a `COORDINATION.md` bullet or a row of the document's rulings table; a debt occurs as `(Dnn)` | the executable | the same |
| register rows exist with the cited status; a receipts-log heading exists; a gate's executable is declared | the executable | the same |
| a wanted theorem does not exist yet | the executable | the same |
| the latest edge token of each edge agrees and is cited; a ruling naming a graph is cited or acknowledged | the executable | the same |
| each projection is byte-identical to a fresh rendering | the executable | the same |
| a leaf's document names it, and its declarations exist | the executable | the same |
| a theorem lies within its module's ceiling | the axiom gate, over every declaration; not re-checked | `lake build` |

The prototype's import graph; the only module that imports `Lean` is
`Check`, and nothing imports a production module:

```text
whatwgbin.Ledger
  WhatwgGates.Ledger.Check     imports Lean, WhatwgGates.Common, Model, Render
  WhatwgTest.Ledger            imports the three graph modules
    WhatwgTest.Ledger.DataQueue, .PromiseFirst, .ConfigurationOrdering
                               import WhatwgGates.Ledger.Model only
WhatwgGates.Ledger.Render      imports WhatwgGates.Ledger.Model
WhatwgGates.Ledger.Model       imports Init only
WhatwgGates.lean               one line per Ledger module
WhatwgTest.lean                one line: WhatwgTest.Ledger
at run time only               importModules [WhatwgTest] from .olean files
```

| lean4-effect4 at `efcf1ae2` | Verdict | Here |
| --- | --- | --- |
| the goal and evidence join, validated before counting | port | every ground resolves by name; counts are additional |
| `Evidence.wanted` with a `ProofWanted` placeholder | port the idea | `Item.wanted`, a name refused once it exists; no placeholder declaration, no Batteries |
| Kahn's cycle check on goal dependencies | port | `Ledger.dependenciesAcyclic` over graph dependencies |
| the per-scope open-obligation ceiling | leave | edge status replaces counting |
| `checked_theorem%`, `#obligation_proved`, `#typed_state_obligations`, `addWanted` | leave | commands and `addDecl` (R-V10); a quoted current type freezes nothing (W6) |
| `Search.lean` | leave | it publishes theorems found by tactic search through `addDecl` |
| the hard-coded `[propext, Quot.sound]` | leave | ceilings stay in the axiom gate, by module prefix |
| the `GENERATED by …; do not edit` header | port | the projection header, which also names the command |
| on-demand drift check of the architecture map | leave | the ledger gate is in the gate table and CI |
| `tools/` outside the trust gate | leave | the ledger code is audited under `WhatwgGates` |

## 2. Evidence

### 2.1 Baseline

After warming the cache from the main checkout, `lake build` at `97a8715`
finishes 386 jobs, and the gate reports 222 source files and 16,723
declarations. `[C]`

### 2.2 The prototype under the unchanged trust gate

The prototype adds seven modules and one entry point (appendix A), one
import line to each of `WhatwgGates.lean` and `WhatwgTest.lean`, and one
`[[lean_exe]]` with `needs = ["WhatwgTest"]` to `lakefile.toml`. With it,
`lake build` finishes 396 jobs and exits 0 in 45.7 s from a warm cache. The
gate reports 230 source files and 17,501 declarations, the five strict
prefixes unchanged, no strict exception, no source-token exemption, and the
same ten metaprogramming modules. `Classical.choice` is reached by 122
declarations of `WhatwgTest`, as before, and by 222 of 2,368 in
`WhatwgGates`, from 176 of 1,597; the new reach is in derived instances and
the `Lean` API calls of `WhatwgGates.Ledger.Check`, which R-11 admits there.
`lake exe whatwg_citations` and `lake exe whatwg_vendorseal` pass with the
prototype and its three projections present. `[C]`

### 2.3 Kernel evaluation of the invariants

A probe module (`lake env lean`) shows that `decide` evaluates `String`
equality, `String.isEmpty`, `List.map`, `List.all` and `Name` membership in
the kernel with no axiom, and gets stuck on `String.startsWith` and
`String.trimAscii`. The invariant function is therefore written with
equality, emptiness and list operations only. Plain `decide` on the ledger
stops at the elaborator's recursion limit; `decide +kernel` checks it, and
`WhatwgTest.Ledger` elaborates in 1.5 s. `#print axioms` on
`WhatwgTest.Ledger.ledger_wellFormed` prints `[propext]`. The same check over
twelve graphs (the three entries four times under renamed identifiers) costs
0.9 s beyond the import. `[C]`

### 2.4 Structural plants

Each plant below is a theorem `(…).wellFormed = false := by decide +kernel`
in a scratch module, and each elaborates, so the kernel refuses the planted
ledger; two controls are `= true` and also elaborate. `[C]`

| Plant | Refused |
| --- | --- |
| closed cell with a remaining item | yes |
| closed cell with no ground | yes |
| open cell with nothing named | yes |
| not-applicable cell with no reason | yes |
| two graphs with one identifier | yes |
| dependency on an unknown graph | yes |
| closed cell citing another graph's open edge | yes |
| closed cell on register rows cited `SEEDED` | yes |
| graph depending on itself | yes |
| two graphs depending on each other | yes |
| leaf whose parent graph is unknown | yes |
| leaf sharing a graph's identifier | yes |
| control: one well-formed graph; two graphs, one depending on the other | accepted |

An entry with the `coverage` field omitted fails to elaborate with "Fields
missing: `coverage`", and one with `identity` twice with "field `identity`
has already been specified". A cross-graph defect planted in the real ledger
fails `lake build` at `ledger_wellFormed` with the kernel's "application type
mismatch" and no name: the build-time theorem is a tripwire, and the
executable's findings are the diagnosis. `[C]`

### 2.5 The executable's cost

The link response files show the cost the review asked about.
`.lake/build/bin/whatwg_ledger.exe.rsp` lists 8 object files, none under
`ir/Whatwg/`; `whatwg_census.exe.rsp` lists 119, of which 75 are under
`ir/Whatwg/`. Both executables are about 109 MB because both link `Lean`;
`whatwg_citations.exe`, which does not, is 4.1 MB. Building the ledger
executable from a warm cache takes about 5 s. A run through `lake env` on the
binary takes 1.7 s against 0.28 s for `lake env` alone, which bounds the
import of the whole `WhatwgTest` environment and every check at about 1.4 s.
`lake exe whatwg_ledger` takes 5.0 s, most of it Lake replaying the
`WhatwgTest` library for `needs`, and prints 9,957 lines, because the replay
reprints that library's stored information messages; `lake -q exe
whatwg_ledger` takes 1.8 s and prints only the PASS line. `[C]`

### 2.6 The reference pass on three graphs and one leaf

The prototype encodes `DATA-PG-QUEUE`, `PROMISE-PG-FIRST`,
`CONFIGURATION-PG-ORDERING` and the standalone leaf `INFRA-LF-INTEGER`
(`docs/INFRA-INTEGER-CONSTRUCTIVE.md`). `lake exe whatwg_ledger --write`
followed by `lake exe whatwg_ledger` prints

```text
PASS whatwg_ledger: 3 graphs, 30 edges; every reference resolves against the built environment and the authored files, and every projection is byte-identical to a fresh rendering
```

Every receipt count the eleven current tables attach to an axiom-report
module recomputes as the count of `#print axioms` commands in that module:
99 (`Data/QueueAxiomReport`), 125 and 57 (the two promise reports), 119
(`Infra/Utf8AxiomReport`), 46 (`Piping/ShutdownAxiomReport`), 94
(`Readable/DefaultAxiomReport`), 93 (`Semantics/OrderingAxiomReport`), 118
(`Transform/BackpressureAxiomReport`), 108, 1 and 2 (the three writable
reports, 111 together) and 95 (`Url/PercentEncodingAxiomReport`). The
ascription counts stated for `WhatwgTest/Infra/Utf8Contract.lean` (80),
`Utf8Laws.lean` (119) and `WhatwgTest/Url/PercentEncodingLaws.lean` (95)
recompute as the count of `#check (@` commands. `[C]`

### 2.7 Reference plants

With two bullets appended to the worktree's `COORDINATION.md` and six
defects planted in the `DATA-PG-QUEUE` entry, the executable exits 1 and
reports each, by graph and edge, in this form: `[C]`

```text
FAIL whatwg_ledger: 14 finding(s)
  ruling R-W99 records DATA-PG-QUEUE/laws=required-open; the ledger says required-closed
  ruling R-W99 records DATA-PG-QUEUE/laws; that cell does not cite it
  ruling R-W99 records PROMISE-PG-FIRST/trust; that cell does not cite it
  DATA-PG-QUEUE construction: WhatwgTest.Streams.Data.QueueAxiomReport holds 99 receipts, not 98
  DATA-PG-QUEUE construction: ruling P3-R9 is not recorded
  DATA-PG-QUEUE semantics: Whatwg.Streams.Data.dequeueValue_conz names no constant
  DATA-PG-QUEUE semantics: Whatwg.Streams.Data.Queue is not a theorem
  DATA-PG-QUEUE laws: ruling P3-R9 is not recorded
  DATA-PG-QUEUE counterexamples: register row WS-DATA-CE-011 does not exist
  DATA-PG-QUEUE counterexamples: debt D99 is not recorded
  DATA-PG-QUEUE: ruling R-W98 names this graph and the ledger neither cites nor acknowledges it
  DATA-PG-QUEUE: ruling R-W99 names this graph and the ledger neither cites nor acknowledges it
  PROMISE-PG-FIRST: ruling R-W99 names this graph and the ledger neither cites nor acknowledges it
  generated/graphs/DATA-PG-QUEUE.md differs from a fresh rendering
```

`R-W98` names only `docs/DATA-DAG.md`, so the document-path half of the
mention check caught it. The `CONFIGURATION-PG-ORDERING` entry carries two
`wanted` items, `CellsWellFormed` and `run_erases_to_reference`, that name
no constant today, and would be reported the day either exists. Both files
were restored, and `git diff` on `COORDINATION.md` is empty. `[C]`

### 2.8 Name literals

Two probe modules, run with `lake env lean`:

```lean
import WhatwgGates.Ledger.Model
def a : Lean.Name := `Whatwg.Streams.Data.dequeueValue_cons
def b : Lean.Name := ``Whatwg.Streams.Data.dequeueValue_cons
```

`a` elaborates and `b` fails with "Unknown constant". With
`import Whatwg.Streams.Data.Queue` instead, the double-backtick literal
resolves, and so does one naming `Whatwg.Streams.Data.Queue`, a structure. A
double-backtick literal therefore checks existence only, and only in a
module that imports the declaring module. `[C]`

### 2.9 Rulings that name graphs

Of the ruling bullets of `COORDINATION.md` (lines starting `- R-`), two name
a graph by identifier (R-V6 `INFRA-PG-UTF8`; R-V8 `CONFIGURATION-PG-ORDERING`
and `INFRA-PG-UTF8`), and five name one by identifier or document path
(R-P20, R-U1, R-U5, R-V6, R-V8: seven graph mentions). R-P24, R-P27, R-U2
and R-U4, which changed edges the current tables cite, name no graph by
either. R-V8 names "the PROMISE, WRITABLE, TRANSFORM, PIPING and
CONFIGURATION graphs" by short name only. A lexical check over today's
rulings therefore catches little; the token convention is for rulings from
here on, and the seeding cites the past ones. `[C]`

### 2.10 Rendered tables against the hand-written ones

The thirty encoded cells keep the status of the hand-written cells. A token
comparison (every code span, ruling, debt, counterexample identifier, number
and quoted heading of each hand-written cell, looked up in the rendered cell)
leaves these differences, and nothing else: `[C]`

| Hand-written content | In the ledger | Proposal |
| --- | --- | --- |
| "This table describes commit `325d5d5`…" preambles | absent | none: a projection is the state at the commit that holds it |
| source paths such as `Whatwg/Streams/Data/Queue.lean` | module names, checked | none |
| `test/counterexamples/REGISTER.md` | implied by the rows ground, checked | none |
| `lake exe whatwg_census --report` | `lake exe whatwg_census --standard streams --report` | none |
| `lake exe trustselftest` (PROMISE, CONFIGURATION trust rows), a name R-V3(c) removed | `lake exe whatwg_trustselftest`, typed | none; the typed `Gate` cannot name a removed executable |
| `WS-PROM-CE-037` | inside the range 036 to 038, checked row by row | none |
| "182 named receipts" | two receipt grounds, 125 and 57 | none |
| the lists of theorems that reached `Classical.choice` at `325d5d5` and were repaired by lane V (PROMISE, CONFIGURATION trust rows), "`R-11`", the D43 `@[simp]` history | dropped from the note | history stays in the receipts log (decision 6) |
| D46's explanation in PROMISE semantics | the debt identifier, checked | the debt text lives in `COORDINATION.md` |
| the section name "Required residual embeddings" in CONFIGURATION representation | dropped | carry it in the item text at seeding |

What the model cannot carry as checked data, and carries as the note: counts
with no module behind them ("the 29 Q3 bridging lemmas", "86 `Source`
names", "the twelfth row"); claims about another document's rows ("every row
of section 3 names its census row id and span digest"); review judgments
("independent review matched the two source spans"); inventory and contract
item identifiers (`E-22`, `G-08`, `CFG-START`); and which ruling overrides
which sentence ("R-P20 wins"). Three of these become checkable later: the
identity claims through W6's declaration snapshot, ascription counts through
the `ascriptions` ground already in the model, and named lemma counts by
listing the names at seeding.

### 2.11 The eleven graphs

Counted over the "Current state" tables at `97a8715` by regular expressions
over each ground cell. The evidence columns count distinct references per
graph. `[C]`

| Graph | Open | Closed | N/A | Rulings | Debts | CE ids | Paths | Gates | Landing refs | Named items | Lean names | Counts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `DATA-PG-QUEUE` | 0 | 8 | 2 | 2 | 1 | 2 | 11 | 1 | 6 | 0 | 13 | 2 |
| `READABLE-PG-DEFAULT` | 6 | 3 | 1 | 2 | 2 | 2 | 5 | 0 | 7 | 1 | 4 | 3 |
| `WRITABLE-PG-DEFAULT` | 6 | 3 | 1 | 3 | 1 | 2 | 3 | 0 | 9 | 0 | 5 | 3 |
| `TRANSFORM-PG-BACKPRESSURE` | 6 | 3 | 1 | 3 | 1 | 2 | 3 | 0 | 9 | 0 | 6 | 3 |
| `PIPING-PG-FORWARD-SHUTDOWN` | 6 | 3 | 1 | 3 | 1 | 2 | 3 | 0 | 9 | 0 | 5 | 3 |
| `PROMISE-PG-FIRST` | 5 | 4 | 1 | 5 | 3 | 6 | 8 | 1 | 12 | 5 | 26 | 2 |
| `CONFIGURATION-PG-ORDERING` | 8 | 1 | 1 | 6 | 8 | 1 | 0 | 1 | 6 | 12 | 14 | 2 |
| `INFRA-PG-UTF8` | 6 | 3 | 1 | 5 | 5 | 2 | 7 | 0 | 0 | 0 | 11 | 4 |
| `INFRA-PG-SCALAR` | 2 | 7 | 1 | 0 | 1 | 1 | 4 | 1 | 1 | 0 | 7 | 0 |
| `URL-PG-CENSUS` | 8 | 0 | 2 | 0 | 1 | 3 | 3 | 2 | 0 | 0 | 1 | 0 |
| `URL-PG-PERCENT` | 5 | 4 | 1 | 5 | 9 | 1 | 7 | 0 | 4 | 0 | 15 | 2 |
| total | 58 | 39 | 13 | 34 | 33 | 24 | 54 | 6 | 63 | 18 | 107 | 24 |

Every ground cell of the eleven tables falls into the evidence kinds of the
model. The one reference the reference pass cannot check is the
`INFRA-UTF8-CE` rows, which live only in a packet register with its own
format (debt D45); they are carried as a named item. The three prototyped
entries took 86, 101 and 89 lines; the remaining eight hold about half of
the Lean names, so seeding them is about 700 lines of data, and the
executable names every misspelt or misplaced reference on the first run.

### 2.12 Uncovered trees

`Whatwg/Html` holds 200 authored `theorem` commands; 13 of its modules
declare public constants (776 public theorem constants, Lean-generated
included). Outside `INFRA-PG-UTF8`, `INFRA-PG-SCALAR` and the leaf
`INFRA-LF-INTEGER`, twelve Infra modules declare public constants
(`Namespaces`, `Bytes.Byte`, `Bytes.Sequence`, `Primitive.Singleton` and
`Text.{Case,Codec,CodePoint,Order,Scan,String,Substring,Whitespace}`) with
7 authored theorems. `INFRA-LF-INTEGER` is the tree's only leaf-receipt
record. 69 modules under `Whatwg/` declare a top-level `theorem`, `def`,
`abbrev`, `structure`, `inductive`, `instance`, `class` or `opaque`. `[C]`

### 2.13 lean4-effect4 at `efcf1ae2`

`git diff --stat 0f16828a efcf1ae2 -- tools/ProofGraph` is empty, and
`0f16828a` is an ancestor of `efcf1ae2`. `[C]` The review's three objections
stand, read in source: `ProofRef.validate`, `validateWanted` and
`addTheorem` each hard-code `[propext, Quot.sound]`; `Ledger.lean` imports
`Batteries.Util.ProofWanted`; and `checked_theorem%` quotes `t.type` of the
constant as it elaborates, so a dependent module re-elaborated after a
statement change re-quotes the new statement. `[S]`

How the repository uses it, from a read-only survey seat `[S]`: the ledger
runs at elaboration through custom commands in
`src/Effect4/Laws/Auto/Obligations.lean` (`#proof_wanted`,
`#obligation_proved`, `#typed_state_obligations … ceiling N`,
`#obligation_audit`), about seventy `#typed_state_obligations` sites, almost
all with ceiling 0. Goals are theorems whose type ends in `Obligation p`;
evidence is found by the naming convention `<goal>.checked` or
`<goal>.wanted`; `Goal.dependencies` is empty in every production goal. The
only evidence kinds are `proved` and `wanted`; there is no gate, ruling or
not-applicable evidence and no cross-graph data. `tools/` is outside
lean4-effect4's trust gate, whose audited trees are `Effect4` and `Test`.
`docs/GENERATED.md` gives every generated file one producer, a one-line
`GENERATED by <producer>; do not edit` header and a `git diff --exit-code`
drift check; no markdown is rendered from ledger data, and the generated
architecture map (`docs/core/architecture-map.html`, by
`tools/Tools/Architecture.lean` under `lake env lean --run`) is checked only
on demand and not in CI.

### 2.14 A cached build replays the module-closure verdict

With the prototype's modules present but not yet imported by either root,
`lake build whatwg_ledger` replayed `WhatwgTest` from the cache and passed.
After a change to `WhatwgTest.lean` forced the root to elaborate, the gate
refused with "Whatwg module-closure gate: …\WhatwgTest\Ledger.lean is not
reachable from the WhatwgTest audit root" for each unimported module. So
adding an unimported source to an audited tree leaves a cached build green;
this is debt D49 for the gate's own pass 1. A build that elaborates the
root catches it; whether CI's build does depends on its cache, which this
seat did not check. `[C]`

## 3. Public declaration record

Assurance route. The ledger is tooling: it owns no specification anchor, no
stream judgment and no denotation, so `docs/AGENT-ROUTING.md` routes none of
it to a proof graph. The data types are passive finite alphabets and value
records, routed to local receipts (exact signatures, constructor census).
The checking functions are assured the way the census and the trust gate
are: a breaker contract whose battery ascribes the signatures and plants one
falsifier per refusal (section 6). The relationship of every row is
`canonical` unless stated; nothing here duplicates an existing declaration
(no `Gates.*` or `Whatwg.*` constant models edges or evidence today).

Module `WhatwgGates.Ledger.Model` (imports only `Init`), namespace
`Gates.Ledger`; signatures as `#check` printed them in the prototype:

| Declaration | Signature | Role |
| --- | --- | --- |
| `Edge` | `Type` (ten constructors, `DecidableEq`, `Repr`) | the ten edges |
| `Edge.all` | `List Gates.Ledger.Edge` | table order |
| `Edge.label` | `Gates.Ledger.Edge → String` | spelling in the documents |
| `Gate` | `Type` (`build`, `vendorseal`, `citations`, `trustselftest`, `leanchecker`, `census`, `censusReport`, `urlinventory`, `urlcensus`) | a gate an edge relies on |
| `Gate.command` | `Gates.Ledger.Gate → String` | exact command |
| `Gate.executable?` | `Gates.Ledger.Gate → Option String` | the executable `lakefile.toml` must declare |
| `RowStatus` | `Type` (`closed`, `seeded`) | register status |
| `RowStatus.text` | `Gates.Ledger.RowStatus → String` | register spelling |
| `RowRange` | `Type` (`family`, `first`, `last`) | a run of counterexample rows |
| `RowRange.ids` | `Gates.Ledger.RowRange → List String` | its identifiers |
| `threeDigits` | `Nat → String` | row-number spelling |
| `Ground` | `Type` (`theorems`, `declarations`, `receipts`, `ascriptions`, `modules`, `gate`, `ruling`, `receipt`, `rows`, `edge`) | evidence that discharges |
| `Ground.discharges` | `Gates.Ledger.Ground → Bool` | may stand in a closed cell |
| `Item` | `Type` (`named`, `debt`, `rows`, `wanted`, `edge`) | what holds an edge open |
| `Status` | `Type` (`requiredOpen`, `requiredClosed`, `notApplicable`) | edge status |
| `Status.text` | `Gates.Ledger.Status → String` | document spelling |
| `Cell` | `Type` (`status`, `grounds`, `remaining`, `debts`, `note`) | one edge's state |
| `Edges` | `Type` (ten `Cell` fields) | exactly ten edges |
| `Edges.get` | `Gates.Ledger.Edges → Gates.Ledger.Edge → Gates.Ledger.Cell` | lookup |
| `Graph` | `Type` (`id`, `document`, `fence`, `dependsOn`, `acknowledged`, `edges`) | one graph |
| `Graph.receiptsLog` | `Gates.Ledger.Graph → String` | `docs/receipts/<id>.md` |
| `Graph.projection` | `Gates.Ledger.Graph → String` | `generated/graphs/<id>.md` |
| `Leaf` | `Type` (`id`, `document`, `declarations`, `parent`, `receipts`) | a leaf-receipt record |
| `Unrouted` | `Type` (`modulePrefix`, `recordedBy`) | a module prefix under no route |
| `Ledger` | `Type` (`graphs`, `leaves`, `unrouted`) | the whole ledger |
| `distinct` | `{α : Type} → [DecidableEq α] → List α → Bool` | helper |
| `Cell.problem?` | `Gates.Ledger.Cell → Option String` | per-cell invariant |
| `Ledger.statusOf?` | `Gates.Ledger.Ledger → String → Gates.Ledger.Edge → Option Gates.Ledger.Status` | cross-graph lookup |
| `Cell.crossReferences` | `Gates.Ledger.Cell → List (String × Gates.Ledger.Edge × Gates.Ledger.Status)` | cross-graph citations |
| `Ledger.dependenciesAcyclic` | `Gates.Ledger.Ledger → Bool` | Kahn's algorithm with fuel |
| `Ledger.findings` | `Gates.Ledger.Ledger → List String` | every structural finding, named |
| `Ledger.wellFormed` | `Gates.Ledger.Ledger → Bool` | no finding |

Module `WhatwgGates.Ledger.Render` (imports the model):

| Declaration | Signature | Role |
| --- | --- | --- |
| `formatVersion` | `Nat` | projection format |
| `code` | `String → String` | backticks |
| `joinAnd` | `List String → String` | English list |
| `Ground.render` | `Gates.Ledger.Ground → String` | one ground |
| `Item.render` | `Gates.Ledger.Item → String` | one item |
| `Cell.render` | `Gates.Ledger.Cell → String` | the ground cell |
| `Graph.render` | `Gates.Ledger.Graph → String → String` | the projection file |

Module `WhatwgGates.Ledger.Check` (imports `Lean`, `WhatwgGates.Common`,
the model and the renderer):

| Declaration | Signature | Role |
| --- | --- | --- |
| `World` | `Type` | what the pass reads |
| `loadEnvironment` | `List Lean.Name → IO Lean.Environment` | `.olean` import |
| `readLines` | `System.FilePath → IO (List String)` | helper |
| `sourceOf` | `System.FilePath → Lean.Name → System.FilePath` | module source |
| `receiptCount` | `List String → Nat` | `#print axioms` count |
| `ascriptionCount` | `List String → Nat` | `#check (@` count |
| `rulingPresent` | `Gates.Ledger.World → List String → String → Bool` | ruling lookup |
| `debtPresent` | `Gates.Ledger.World → String → Bool` | debt lookup |
| `rowStatus?` | `Gates.Ledger.World → String → Option String` | register lookup |
| `rowFindings` | `Gates.Ledger.World → Gates.Ledger.RowRange → Gates.Ledger.RowStatus → List String` | rows check |
| `moduleExists` | `Gates.Ledger.World → Lean.Name → Bool` | module check |
| `groundFindings` | `Gates.Ledger.World → List String → List String → Gates.Ledger.Ground → IO (List String)` | ground check |
| `itemFindings` | `Gates.Ledger.World → Gates.Ledger.Item → List String` | item check |
| `rulingId?` | `String → Option String` | ruling bullet |
| `rulingMentions` | `List String → List Gates.Ledger.Graph → List (String × String)` | mention scan |
| `EdgeToken` | `Type` | `GRAPH-ID/edge=status` |
| `codeSpans` | `String → List String` | helper |
| `parseStatus?` | `String → Option Gates.Ledger.Status` | helper |
| `edgeTokens` | `List String → List Gates.Ledger.EdgeToken` | token scan |
| `latestTokens` | `List Gates.Ledger.EdgeToken → List Gates.Ledger.EdgeToken` | latest ruling wins |
| `tokenFindings` | `Gates.Ledger.Ledger → List Gates.Ledger.EdgeToken → List String` | token check |
| `Graph.citedRulings` | `Gates.Ledger.Graph → List String` | rulings a graph cites |
| `graphFindings` | `Gates.Ledger.World → Gates.Ledger.Ledger → Gates.Ledger.Graph → IO (List String)` | per-graph pass |
| `leafFindings` | `Gates.Ledger.World → Gates.Ledger.Leaf → IO (List String)` | per-leaf pass |
| `ledgerInput` | `String` | projection header input |
| `run` | `Gates.Ledger.Ledger → Bool → IO UInt32` | the gate |
| `cli` | `Gates.Ledger.Ledger → List String → IO UInt32` | entry |

Data, modules `WhatwgTest.Ledger` and `WhatwgTest.Ledger.*`, namespace
`WhatwgTest.Ledger`:

| Declaration | Signature | Role |
| --- | --- | --- |
| `dataQueue` | `Gates.Ledger.Graph` | `DATA-PG-QUEUE` |
| `promiseFirst` | `Gates.Ledger.Graph` | `PROMISE-PG-FIRST` |
| `configurationOrdering` | `Gates.Ledger.Graph` | `CONFIGURATION-PG-ORDERING` |
| `infraInteger` | `Gates.Ledger.Leaf` | `INFRA-LF-INTEGER` |
| `ledger` | `Gates.Ledger.Ledger` | the ledger |
| `ledger_wellFormed` | `WhatwgTest.Ledger.ledger.wellFormed = true` | the structural theorem |

Entry point `whatwgbin/Ledger.lean`: `main : List String → IO UInt32`,
calling `Gates.Ledger.cli WhatwgTest.Ledger.ledger`.

Two changes the builder should make to the prototype, neither altering a
signature above other than `World`'s fields: replace `World.env` by two
functions read out of the environment (the kind of a constant, and module
existence), so that the whole reference pass is a pure function the battery
can probe with `#guard`, which addendum V2c.2 excludes from the refused
keywords; and add the check that each graph document links its projection.

## 4. Effect on frozen surfaces

No theorem statement, definition body or battery ascription changes: the
prototype builds with every existing `#check` unchanged (section 2.2), so
the count of altered ascriptions is zero. What changes:

| Surface | Change | Authority |
| --- | --- | --- |
| the eleven graph documents' "Current state" sections | the table is replaced by one paragraph and a link to `generated/graphs/<GRAPH-ID>.md`; no declaration, statement or "Rulings" row is touched | a ruling amending R-V4, which requires the table in the document |
| `docs/receipts/<GRAPH-ID>.md`, eleven logs | gain a section holding the replaced table verbatim | R-V4's verbatim-move rule |
| `docs/AGENT-ROUTING.md`, "Authored facts and generated facts" | the authored input of "graph obligations and leaf-receipt ledger" becomes `WhatwgTest/Ledger/` | coordinator |
| root `AGENTS.md` | an authority-map row for `WhatwgTest/Ledger/` and `generated/graphs/`; a gate-table row for `lake -q exe whatwg_ledger`; resume step 4 reads the projection | coordinator |
| `WhatwgTest/AGENTS.md`, `WhatwgGates/AGENTS.md`, `generated/AGENTS.md` | a ledger section, a gate-table row, an allowed-projection line with the regeneration command | coordinator |
| `COORDINATION.md` | the edge-token convention for rulings | coordinator |
| `lakefile.toml`, `WhatwgGates.lean`, `WhatwgTest.lean`, CI | one executable, one import line each, one CI step after `lake build` | builder, coordinator for CI |
| breaker-owned rows, `test/contracts/`, frozen batteries | none | none |

No graph document's breaker-owned content changes, so no breaker amendment
is needed for the documents. Debt D54's stale sentences are untouched.

Ownership. The coordinator owns `WhatwgTest/Ledger/`. A breaker that
freezes a new graph adds its entry, every applicable edge `requiredOpen`
with the packet's obligations named; a builder proposes cell changes on its
landing branch; the coordinator lands them with the ruling that carries the
edge tokens, and regenerates the projections in the same commit.

## 5. Effect on the trust gate

None to its lists. The prototype passes the gate with no
`metaprogrammingModules` entry, no `sourceTokenExemptions` entry, no strict
exception and no new token (section 2.2); `decide +kernel` is not a refused
spelling and adds no axiom; `#check_failure` and `#guard`, which the battery
would use, are excluded from the V2c.2 keyword set. The summary line's file
and declaration counts grow (230 and 17,501 with the prototype). No
trust-self-test row is needed for the ledger itself, since V2c already
refuses an unlisted ledger module that declares a command; the breaker may
add one plant row that a ledger module spelling `elab` is refused, as a
regression guard. The ledger modules sit under no strict prefix.

`lake exe whatwg_trustselftest` with the prototype present: see section 8.

## 6. Slices

### Breaker packet

- Contract `test/contracts/graph-ledger.contract.md`: the model's
  invariants (section 2.4), the reference-pass rules (section 2.7), the
  token grammar `GRAPH-ID/edge=status` and its latest-wins rule, the
  projection format and header, the regeneration command, the run-time file
  set (`COORDINATION.md`, `test/counterexamples/REGISTER.md`,
  `lakefile.toml`, each graph document and receipts log, each cited module
  source, each projection), and the claim scope: what the gate does not read
  (note prose, review judgments, rulings' wording beyond tokens and
  mentions, the reverse direction of a status change with no ruling).
- Battery `WhatwgTest/Audit/LedgerContract.lean`: exact ascriptions of every
  signature of section 3; one `decide +kernel` refusal theorem per plant of
  section 2.4 and the two controls; `#check_failure` for the omitted and the
  repeated edge field; `#guard` rows over planted `World` values for each
  finding of section 2.7, plus a wanted theorem that exists, an ascription
  count mismatch, a missing receipts heading, an undeclared executable, an
  unknown graph in a token, and a leaf whose document does not name it.
  Red until slice A lands; declared in `known-red.txt` for its red phase.
- Counterexample seeds, family `LEDGER-CE`: 001, a ruling moves an edge and
  no graph records it (the review's four contradictions); 002, an equal
  receipt count hides a renamed theorem (closed for named theorems, open for
  count-only grounds until W6); 003, a live table cites a removed executable
  (section 2.10); 004, a cached build replays the module-closure verdict
  (section 2.14); 005, a closed edge cites another graph's open edge.

### Builder slices

| Slice | File fence | Depends on |
| --- | --- | --- |
| A, model and gate | `WhatwgGates/Ledger/{Model,Render,Check}.lean`, `whatwgbin/Ledger.lean`, `WhatwgTest/Ledger.lean`, `WhatwgTest/Ledger/{DataQueue,PromiseFirst,ConfigurationOrdering}.lean`, one import line in each of `WhatwgGates.lean` and `WhatwgTest.lean`, the `[[lean_exe]]` and `defaultTargets` entry in `lakefile.toml`, `generated/graphs/` for three graphs | the breaker packet |
| B, seeding | `WhatwgTest/Ledger/*.lean` for the other eight graphs, `generated/graphs/*.md`, the "Current state" sections of the eleven graph documents, an appended section in each `docs/receipts/<GRAPH-ID>.md` | A; one seat, or one per graph family |
| C, routers and CI | the files of section 4 marked coordinator | B |
| D, routing | a module routing pass in `Check.lean`, `fence` for every graph, `unrouted` entries citing a new debt for `Whatwg.Html` and the Infra modules of section 2.12, `generated/graphs/INDEX.md` with the section 2.11 counts and the leaf records | B and decision 7 |

The independent reviewer checks: each encoded cell against its hand-written
cell, so that no status moved in the encoding and every sentence is a
ground, an item, a debt or note text, or is in the receipts log; that the
moved tables are verbatim; that the executable's response file lists no
object under `ir/Whatwg/`; that no list of the trust gate changed; and that
every plant fails for its frozen reason.

### Sibling slices

- W6 (freeze registry). Ledger evidence names constants, not registry
  entries: the registry is keyed by the constant, so the name is the join,
  and the ledger stays valid before W6 lands. W7 lands first. From W6 it
  needs: registry entries that name the graph by the identifier the ledger
  uses and the edge as `Gates.Ledger.Edge` (the model imports only `Init`,
  so W6 can import it), a way to read the registry from an executable over
  `.olean` files without running elaboration, which W6 should measure, and
  the declaration snapshot (debt D47) as a projection the ten identity cells
  can cite. Once those land, a `theorems` ground also requires a registry
  entry whose graph and edge are this cell's, which pins the statement.
- W10 (an executable gate over `.olean` files). The ledger gate is the first
  executable of that shape here. Its loader and `World` construction should
  be the code W10's shared gate reuses; the ledger checks read this
  repository's coordination record and register, so they stay here.
- W8 and W9. A graph either creates gets its ledger entry at its breaker's
  freeze, every applicable edge `requiredOpen` with the packet's
  obligations named.

## 7. Decisions for the coordinator

1. Where edge status lives. (a) The Lean ledger, one projection file per
   graph under `generated/graphs/`, the table removed from each document:
   one owner, generated-file rules apply, one more file to open. (b) The
   ledger, with the table as a marked generated block inside each authored
   document: the table stays where readers look, but an authored file holds
   generated bytes, against `generated/AGENTS.md`. (c) Keep the hand-written
   tables and have the gate parse them: no data migration, but markdown
   parsing is the check and prose stays the source. Recommend (a).
2. Where the data lives. (a) `WhatwgTest/Ledger/`, handed to
   `Gates.Ledger.cli` by the entry point, as the census numerators are:
   tooling decides, the test tree records. (b) Everything under
   `WhatwgGates/`: one tree, but frequent status edits land in the trust
   boundary's tree. (c) A new library: the gate's `auditedTrees` changes.
   Recommend (a).
3. How names are checked. (a) Single-backtick names resolved by the
   executable at run time: no production import, no metaprogramming, failure
   at gate time. (b) Double-backtick names in the data: existence at
   elaboration, but the data imports production modules and the executable
   compiles them natively (75 objects for the census today), and kind is
   still unchecked. (c) An elaboration-time check in a new listed
   metaprogramming module: earlier failure, but a breaker addendum to the
   trust-gate contract, a ninth gate command, and debt D49 for every file
   fact. (d) The same checks inside an existing listed module, such as the
   axiom gate's: no new list entry, but the trust gate's frozen contract
   grows a ledger pass and D49 still applies. Recommend (a).
4. How rulings reach the ledger. (a) The `GRAPH-ID/edge=status` token in
   every ruling that changes an edge, plus the mention check: a ruling the
   ledger does not follow fails the gate; costs one convention. (b) The
   mention check alone: catches rulings that name a graph, misses the four
   that changed edges by slice name. (c) No lexical coupling; review only:
   the status quo that produced the review's contradictions. Recommend (a),
   with the past rulings cited at seeding.
5. Freshness of the environment. (a) `needs = ["WhatwgTest"]`, run as
   `lake -q exe whatwg_ledger`: the gate never reads stale `.olean` files,
   and `-q` keeps the replayed messages out of the log. (b) No `needs`; the
   gate table says to run it after `lake build`: one dependency less, but a
   local run can read a stale environment. Recommend (a).
6. What notes hold. (a) Current grounds only; history sentences stay in the
   receipts log with the moved table: shorter cells, one home for history.
   (b) The hand-written cells verbatim as notes: no rewording at seeding,
   but history is kept in two places. Recommend (a).
7. The uncovered trees. (a) Open a debt now for `Whatwg/Html` and the twelve
   Infra modules, carry them as `unrouted` entries citing it, and decide
   graph or leaf for them in a later packet. (b) Seed leaf records for the
   Infra helpers in slice D: they look like passive values, but each needs
   a breaker's route decision under `docs/AGENT-ROUTING.md`. Recommend (a);
   the routing decision is not this slice.
8. The ledger tooling's assurance route. (a) A breaker contract and battery,
   as the census and the trust gate have. (b) A proof graph: nothing in it
   models the specification. Recommend (a).
9. Ceiling grounds. (a) The strict-ceiling claims of the trust cells are
   attested by R-V1 and R-V6 and enforced by the axiom gate, not re-checked
   per cell. (b) The executable re-runs `collectAxioms` on each named
   theorem against the strict list, which needs that list as data outside
   `WhatwgTest.Audit.AxiomGate` (W10's territory). Recommend (a) now, (b)
   with W10.
10. Order against W6. (a) W7 first; W6 later adds the registry check to the
    `theorems` ground. (b) Wait for W6: theorem grounds are statement-pinned
    from the start, but the contradictions stay open meanwhile. Recommend
    (a).
11. Attestation of a closed edge. (a) Add to `ledger_wellFormed` that every
    closed cell cites a ruling, a receipts-log heading or `CLOSED` register
    rows, so a ledger edit cannot close an edge on theorem names alone. Of
    the 39 closed cells today, five cite none of the three, all in
    `INFRA-PG-SCALAR` (semantics, laws, representation, bridges, trust), and
    seeding adds the heading "Proof repair and receipts" to them. `[C]` (b)
    Leave it to review. Recommend (a); it is the cheap half of the reverse
    direction that edge tokens do not cover.

## 8. Not checked

- The other eight graphs were not encoded; their counts in section 2.11 come
  from regular expressions over the tables, not from a ledger run.
- `lake exe whatwg_trustselftest` was run with the prototype present; its
  result is recorded below if it finished before this commit.
- The dependencies between graphs were not seeded; the prototype records
  one (`CONFIGURATION-PG-ORDERING` on `PROMISE-PG-FIRST`). That the full set
  is acyclic is `[H]`.
- Reading a W6-style persistent environment extension from an executable
  over imported `.olean` files was not tried `[H]`.
- The run was measured on this Windows host only; CI time on Linux, and the
  rendering of the projections on a markdown host, were not checked.
- `leanchecker` was not run over the prototype modules.
- That `lake -q` still prints a build error of the `needs` target, and not
  only the executable's output, was not tried `[H]`.
- The module routing pass of slice D was not prototyped; the counts in
  section 2.12 come from a probe over the environment and a source grep.
- No graph document, receipts log, router or contract was edited.

## Appendix A: prototype source

The prototype as it built and passed in section 2.2. Line endings and
trailing whitespace are normalised; nothing else differs.

### `lakefile.toml` addition

```toml
[[lean_exe]]
name = "whatwg_ledger"
root = "whatwgbin.Ledger"
needs = ["WhatwgTest"]
```

### `WhatwgGates/Ledger/Model.lean`

```lean
/-!
# Gates.Ledger.Model (W7 prototype)

The graph ledger's data model: plain first-order data, no metaprogramming.
A graph is a record with exactly ten edge fields, so a ledger entry that
omits or repeats an edge does not elaborate. The structural invariants are a
`Bool` function that the kernel can evaluate (`decide`), and the same
function, as findings with names, is what the executable prints. Imports
nothing beyond `Init`.
-/

namespace Gates.Ledger

/-- The ten edges of `docs/AGENT-ROUTING.md`, "The ten edges", in its order. -/
inductive Edge where
  | identity | construction | semantics | laws | representation
  | counterexamples | bridges | targets | trust | coverage
  deriving DecidableEq, Repr

/-- The ten edges in table order. -/
def Edge.all : List Edge :=
  [.identity, .construction, .semantics, .laws, .representation,
   .counterexamples, .bridges, .targets, .trust, .coverage]

/-- The edge's name as the graph documents spell it. -/
def Edge.label : Edge → String
  | .identity => "identity"
  | .construction => "construction"
  | .semantics => "semantics"
  | .laws => "laws"
  | .representation => "representation"
  | .counterexamples => "counterexamples"
  | .bridges => "bridges"
  | .targets => "targets"
  | .trust => "trust"
  | .coverage => "coverage"

/-- A gate of the root `AGENTS.md` "Gates" table, or a census mode. -/
inductive Gate where
  | build
  | vendorseal
  | citations
  | trustselftest
  | leanchecker
  | census (standard : String)
  | censusReport (standard : String)
  | urlinventory
  | urlcensus
  deriving DecidableEq, Repr

/-- The exact command the gate runs. -/
def Gate.command : Gate → String
  | .build => "lake build"
  | .vendorseal => "lake exe whatwg_vendorseal"
  | .citations => "lake exe whatwg_citations"
  | .trustselftest => "lake exe whatwg_trustselftest"
  | .leanchecker => "lake env leanchecker Whatwg WhatwgTest WhatwgGates"
  | .census s => s!"lake exe whatwg_census --standard {s}"
  | .censusReport s => s!"lake exe whatwg_census --standard {s} --report"
  | .urlinventory => "lake exe whatwg_urlinventory"
  | .urlcensus => "lake exe whatwg_urlcensus"

/-- The executable a gate needs declared in `lakefile.toml`, if any. -/
def Gate.executable? : Gate → Option String
  | .build | .leanchecker => none
  | .vendorseal => some "whatwg_vendorseal"
  | .citations => some "whatwg_citations"
  | .trustselftest => some "whatwg_trustselftest"
  | .census _ | .censusReport _ => some "whatwg_census"
  | .urlinventory => some "whatwg_urlinventory"
  | .urlcensus => some "whatwg_urlcensus"

/-- A status of `test/counterexamples/REGISTER.md` or a packet register. -/
inductive RowStatus where
  | closed
  | seeded
  deriving DecidableEq, Repr

/-- The status as the register spells it. -/
def RowStatus.text : RowStatus → String
  | .closed => "CLOSED"
  | .seeded => "SEEDED"

/-- A contiguous family of counterexample rows, `family-001` to `family-NNN`. -/
structure RowRange where
  family : String
  first : Nat
  last : Nat
  deriving DecidableEq, Repr

/-- A three-digit counterexample number, as every register spells it. -/
def threeDigits (n : Nat) : String :=
  let s := toString n
  if s.length ≥ 3 then s else String.ofList (List.replicate (3 - s.length) '0') ++ s

/-- The identifiers of a row range. -/
def RowRange.ids (r : RowRange) : List String :=
  (List.range (r.last + 1 - r.first)).map fun k => s!"{r.family}-{threeDigits (r.first + k)}"

/-- Evidence that can discharge an edge. Every constructor is either checked
by `lake exe whatwg_ledger` (a theorem, a module, a receipt count, a gate, a
register row, a receipts-log heading, another graph's closed edge) or
attested (a ruling, whose text the executable finds but does not read). -/
inductive Ground where
  /-- Each name is a theorem of the built environment. -/
  | theorems (names : List Lean.Name)
  /-- Each name is a constant of the built environment, of any kind. -/
  | declarations (names : List Lean.Name)
  /-- An axiom-report module whose source holds exactly `count` receipt commands. -/
  | receipts («module» : Lean.Name) (count : Nat)
  /-- A battery whose source holds exactly `count` ascription commands. -/
  | ascriptions («module» : Lean.Name) (count : Nat)
  /-- A battery or production module of the built environment. -/
  | modules (names : List Lean.Name)
  /-- A gate the edge relies on. -/
  | gate (g : Gate)
  /-- A ruling of `COORDINATION.md`, or of the graph document's "Rulings" table. -/
  | ruling (id : String)
  /-- A heading of the graph's receipts log, matched as a prefix. -/
  | receipt (heading : String)
  /-- Register rows with the stated status. -/
  | rows (range : RowRange) (status : RowStatus)
  /-- Another graph's edge, which must be closed. -/
  | edge (graph : String) (e : Edge)
  deriving DecidableEq, Repr

/-- What keeps an edge open. -/
inductive Item where
  /-- A remaining obligation by name; authored text, not checked. -/
  | named (label : String)
  /-- A debt of `COORDINATION.md` that holds the edge open. -/
  | debt (id : String)
  /-- Register rows that hold the edge open. -/
  | rows (range : RowRange) (status : RowStatus)
  /-- A theorem the edge waits for; the executable refuses it once it exists. -/
  | wanted (name : Lean.Name)
  /-- Another graph's edge, which must still be open. -/
  | edge (graph : String) (e : Edge)
  deriving DecidableEq, Repr

/-- The three statuses of `docs/AGENT-ROUTING.md`, "The ten edges". -/
inductive Status where
  | requiredOpen
  | requiredClosed
  | notApplicable
  deriving DecidableEq, Repr

/-- The status as the graph documents spell it. -/
def Status.text : Status → String
  | .requiredOpen => "required-open"
  | .requiredClosed => "required-closed"
  | .notApplicable => "not-applicable"

/-- One edge's state. `grounds` are what discharges a closed edge, or what is
already discharged on an open one; `remaining` is what holds an open edge
open; `debts` are debts recorded against the edge that do not hold it open;
`note` is authored prose, rendered verbatim and checked by nothing, and is
the reason of a `not-applicable` edge. -/
structure Cell where
  status : Status
  grounds : List Ground := []
  remaining : List Item := []
  debts : List String := []
  note : String := ""
  deriving DecidableEq, Repr

/-- Exactly the ten edges: a ledger entry that omits or repeats one does not
elaborate. -/
structure Edges where
  identity : Cell
  construction : Cell
  semantics : Cell
  laws : Cell
  representation : Cell
  counterexamples : Cell
  bridges : Cell
  targets : Cell
  trust : Cell
  coverage : Cell
  deriving DecidableEq, Repr

/-- The cell of one edge. -/
def Edges.get (es : Edges) : Edge → Cell
  | .identity => es.identity
  | .construction => es.construction
  | .semantics => es.semantics
  | .laws => es.laws
  | .representation => es.representation
  | .counterexamples => es.counterexamples
  | .bridges => es.bridges
  | .targets => es.targets
  | .trust => es.trust
  | .coverage => es.coverage

/-- One proof graph. `fence` is the production modules whose declarations the
graph owns; `dependsOn` the graphs it builds on; `acknowledged` the rulings
that name this graph and changed no edge (every other ruling that names it is
cited by a ground). -/
structure Graph where
  id : String
  document : String
  fence : List Lean.Name
  dependsOn : List String := []
  acknowledged : List String := []
  edges : Edges
  deriving DecidableEq, Repr

/-- The receipts log of ruling R-V4. -/
def Graph.receiptsLog (g : Graph) : String := s!"docs/receipts/{g.id}.md"

/-- The projection the executable writes. -/
def Graph.projection (g : Graph) : String := s!"generated/graphs/{g.id}.md"

/-- A leaf-receipt record (`docs/AGENT-ROUTING.md`, "Assurance threshold"):
the declaration, the graph edge its receipts contribute to (none for a
standalone leaf), and the receipts. -/
structure Leaf where
  id : String
  document : String
  declarations : List Lean.Name
  parent : Option (String × Edge)
  receipts : List Ground
  deriving DecidableEq, Repr

/-- A production module prefix no graph and no leaf covers, with the debt or
ruling that records the gap. -/
structure Unrouted where
  modulePrefix : Lean.Name
  recordedBy : String
  deriving DecidableEq, Repr

/-- The whole ledger. -/
structure Ledger where
  graphs : List Graph
  leaves : List Leaf := []
  unrouted : List Unrouted := []
  deriving DecidableEq, Repr

/-! ## Structural invariants

Written with equality, emptiness and list operations only, so that `decide`
evaluates them in the kernel: measured at `97a8715`, kernel reduction gets
stuck on `String.startsWith` and `String.trimAscii` but not on these. -/

/-- No element occurs twice. -/
def distinct {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

/-- A ground that may stand in a closed edge's evidence: every kind except
register rows cited with a status other than `CLOSED`. -/
def Ground.discharges : Ground → Bool
  | .rows _ status => status == .closed
  | _ => true

/-- One finding about one cell, or `none`. -/
def Cell.problem? (c : Cell) : Option String :=
  match c.status with
  | .requiredClosed =>
    if !c.remaining.isEmpty then some "closed with remaining items"
    else if c.grounds.isEmpty then some "closed with no ground"
    else if !c.grounds.all Ground.discharges then some "closed on rows that are not CLOSED"
    else none
  | .requiredOpen =>
    if c.remaining.isEmpty then some "open with no remaining item named"
    else none
  | .notApplicable =>
    if !c.remaining.isEmpty || !c.grounds.isEmpty then some "not-applicable with grounds or items"
    else if c.note.isEmpty then some "not-applicable with no reason"
    else none

/-- The status of another graph's edge, if the graph is in the ledger. -/
def Ledger.statusOf? (l : Ledger) (graph : String) (e : Edge) : Option Status :=
  (l.graphs.find? (·.id == graph)).map fun g => (g.edges.get e).status

/-- Every cross-graph reference of one cell, with the status it requires. -/
def Cell.crossReferences (c : Cell) : List (String × Edge × Status) :=
  (c.grounds.filterMap fun
    | .edge g e => some (g, e, Status.requiredClosed)
    | _ => none) ++
  (c.remaining.filterMap fun
    | .edge g e => some (g, e, Status.requiredOpen)
    | _ => none)

/-- Kahn's algorithm with the graph count as fuel: repeatedly remove every
graph none of whose dependencies remains; the dependencies are acyclic when
nothing remains. -/
def Ledger.dependenciesAcyclic (l : Ledger) : Bool :=
  let step (remaining : List Graph) : List Graph :=
    remaining.filter fun g => g.dependsOn.any fun d => remaining.any (·.id == d)
  let rec go : Nat → List Graph → List Graph
    | 0, remaining => remaining
    | n + 1, remaining => go n (step remaining)
  (go l.graphs.length l.graphs).isEmpty

/-- Every structural finding, each naming its graph and edge. -/
def Ledger.findings (l : Ledger) : List String :=
  let ids := l.graphs.map (·.id)
  let duplicate := if distinct ids then [] else ["two graphs share an identifier"]
  let perGraph := l.graphs.flatMap fun g =>
    let deps := g.dependsOn.filterMap fun d =>
      if ids.contains d then none else some s!"{g.id}: unknown dependency {d}"
    let self := if g.dependsOn.contains g.id then [s!"{g.id}: depends on itself"] else []
    let cells := Edge.all.flatMap fun e =>
      let c := g.edges.get e
      let own := match c.problem? with
        | some why => [s!"{g.id} {e.label}: {why}"]
        | none => []
      let cross := c.crossReferences.filterMap fun (other, oe, wanted) =>
        match l.statusOf? other oe with
        | none => some s!"{g.id} {e.label}: unknown graph {other}"
        | some actual =>
          if actual == wanted then none
          else some s!"{g.id} {e.label}: cites {other} {oe.label} as {wanted.text}, but it is {actual.text}"
      own ++ cross
    deps ++ self ++ cells
  let leaves := l.leaves.filterMap fun leaf =>
    match leaf.parent with
    | some (g, _) => if ids.contains g then none else some s!"leaf {leaf.id}: unknown parent graph {g}"
    | none => none
  let leafIds := if distinct (l.leaves.map (·.id) ++ ids) then [] else ["a leaf shares an identifier"]
  let cycle := if l.dependenciesAcyclic then [] else ["the graph dependencies have a cycle"]
  duplicate ++ perGraph ++ leaves ++ leafIds ++ cycle

/-- The ledger is well formed when it has no structural finding. -/
def Ledger.wellFormed (l : Ledger) : Bool := l.findings.isEmpty

end Gates.Ledger
```

### `WhatwgGates/Ledger/Render.lean`

```lean
import WhatwgGates.Ledger.Model

/-!
# Gates.Ledger.Render (W7 prototype)

The markdown projection of one graph's ledger entry: a header naming the
canonical input, the generator and the exact regeneration command, then the
ten-edge table of ruling R-V4. Byte-deterministic: no timestamp, no commit,
no absolute path. Imports only the model.
-/

namespace Gates.Ledger

/-- Projection format version, bumped when the rendered shape changes. -/
def formatVersion : Nat := 1

/-- A name in backticks. -/
def code (s : String) : String := "`" ++ s ++ "`"

/-- `a`, `a and b`, `a, b and c`. -/
def joinAnd : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => a ++ " and " ++ b
  | a :: rest => a ++ ", " ++ joinAnd rest

def Ground.render : Ground → String
  | .theorems ns => "theorems " ++ joinAnd (ns.map (code ∘ toString))
  | .declarations ns => "declarations " ++ joinAnd (ns.map (code ∘ toString))
  | .receipts m n => s!"{n} receipts of {code (toString m)}"
  | .ascriptions m n => s!"{n} ascriptions of {code (toString m)}"
  | .modules ms => "modules " ++ joinAnd (ms.map (code ∘ toString))
  | .gate g => code g.command
  | .ruling r => "ruling " ++ r
  | .receipt h => s!"receipt \"{h}\""
  | .rows r s =>
    if r.first == r.last then s!"{code (r.ids.headD r.family)} {code s.text}"
    else s!"{code (r.ids.headD r.family)} to {code (r.ids.getLastD r.family)} {code s.text}"
  | .edge g e => s!"{code g} {e.label} closed"

def Item.render : Item → String
  | .named l => l
  | .debt d => "debt " ++ d
  | .rows r s =>
    if r.first == r.last then s!"{code (r.ids.headD r.family)} {code s.text}"
    else s!"{code (r.ids.headD r.family)} to {code (r.ids.getLastD r.family)} {code s.text}"
  | .wanted n => "wanted " ++ code (toString n)
  | .edge g e => s!"{code g} {e.label} (open)"

/-- The ground cell: note, then what is open, what discharges, recorded debts. -/
def Cell.render (c : Cell) : String :=
  let parts : List String :=
    (if c.note.isEmpty then [] else [c.note]) ++
    (if c.remaining.isEmpty then [] else
      ["Open: " ++ String.intercalate "; " (c.remaining.map Item.render) ++ "."]) ++
    (if c.grounds.isEmpty then [] else
      [(if c.status == .requiredClosed then "Closed on: " else "Discharged: ") ++
        String.intercalate "; " (c.grounds.map Ground.render) ++ "."]) ++
    (if c.debts.isEmpty then [] else
      ["Debts recorded: " ++ joinAnd c.debts ++ "."])
  String.intercalate " " parts

/-- The rendered projection of one graph, ending in a newline. -/
def Graph.render (g : Graph) (input : String) : String :=
  let header := [
    s!"<!-- GENERATED by `lake exe whatwg_ledger --write` (Gates.Ledger, format {formatVersion}) from {input}; do not edit. -->",
    "",
    s!"# Current state of {code g.id}",
    "",
    s!"Graph document: {code g.document}. Receipts log: {code g.receiptsLog}.",
    s!"Fence: " ++ (if g.fence.isEmpty then "none" else joinAnd (g.fence.map (code ∘ toString))) ++ ".",
    s!"Depends on: " ++ (if g.dependsOn.isEmpty then "none" else joinAnd (g.dependsOn.map code)) ++ ".",
    "",
    "| Edge | Status | Ground |",
    "| --- | --- | --- |"]
  let rows := Edge.all.map fun e =>
    let c := g.edges.get e
    s!"| {e.label} | {code c.status.text} | {c.render} |"
  String.intercalate "\n" (header ++ rows) ++ "\n"

end Gates.Ledger
```

### `WhatwgGates/Ledger/Check.lean`

```lean
import Lean
import WhatwgGates.Common
import WhatwgGates.Ledger.Model
import WhatwgGates.Ledger.Render

/-!
# Gates.Ledger.Check (W7 prototype)

The reference pass and the drift gate of the graph ledger, run by
`lake exe whatwg_ledger`. It imports the built environment at run time with
`Lean.importModules`, as `leanchecker` does, so no production module is
compiled into the executable and no command or elaborator is declared. Files
are read at run time, so a cached build cannot replay a stale verdict.
-/

namespace Gates.Ledger
open Lean

/-- What the reference pass reads. -/
structure World where
  root : System.FilePath
  env : Environment
  coordination : List String
  register : List String
  lakefile : String

/-- The built environment, imported from `.olean` files on the search path
Lake gives an executable. -/
def loadEnvironment (modules : List Name) : IO Environment := do
  initSearchPath (← findSysroot)
  importModules (modules.map fun m => { module := m }).toArray {} (loadExts := false)

def readLines (path : System.FilePath) : IO (List String) := do
  return Gates.Common.lines (← IO.FS.readFile path)

/-- The source file of a module of this package. -/
def sourceOf (root : System.FilePath) (m : Name) : System.FilePath :=
  modToFilePath root m "lean"

/-- The count of receipt commands in a source: lines that begin `#print axioms`. -/
def receiptCount (text : List String) : Nat :=
  (text.filter fun l => l.startsWith "#print axioms").length

/-- The count of statement ascriptions in a source: lines that begin `#check (@`. -/
def ascriptionCount (text : List String) : Nat :=
  (text.filter fun l => l.startsWith "#check (@").length

/-- A ruling occurs as a bullet of `COORDINATION.md` or a row of the graph
document's rulings table. -/
def rulingPresent (w : World) (document : List String) (id : String) : Bool :=
  w.coordination.any (fun l => l.startsWith s!"- {id} ") ||
  document.any (fun l => l.startsWith s!"| `{id}` |")

/-- A debt occurs in `COORDINATION.md` as `(Dnn)`. -/
def debtPresent (w : World) (id : String) : Bool :=
  w.coordination.any fun l => (l.splitOn s!"({id})").length > 1

/-- The status a register row carries, if the row exists. -/
def rowStatus? (w : World) (id : String) : Option String :=
  (w.register.find? (·.startsWith s!"| `{id}` | `")).bind fun l =>
    match (l.splitOn "` | `") with
    | _ :: rest :: _ => some ((rest.splitOn "`").headD "")
    | _ => none

def rowFindings (w : World) (r : RowRange) (s : RowStatus) : List String :=
  r.ids.filterMap fun id =>
    match rowStatus? w id with
    | none => some s!"register row {id} does not exist"
    | some actual => if actual == s.text then none else some s!"register row {id} is {actual}, not {s.text}"

def moduleExists (w : World) (m : Name) : Bool := (w.env.getModuleIdx? m).isSome

def groundFindings (w : World) (document receiptsLog : List String) : Ground → IO (List String)
  | .theorems ns => pure <| ns.filterMap fun n =>
    match w.env.find? n with
    | some (.thmInfo _) => none
    | some _ => some s!"{n} is not a theorem"
    | none => some s!"{n} names no constant"
  | .declarations ns => pure <| ns.filterMap fun n =>
    if w.env.contains n then none else some s!"{n} names no constant"
  | .receipts m count => do
    if !moduleExists w m then return [s!"{m} is not a built module"]
    let found := receiptCount (← readLines (sourceOf w.root m))
    return if found == count then [] else [s!"{m} holds {found} receipts, not {count}"]
  | .ascriptions m count => do
    if !moduleExists w m then return [s!"{m} is not a built module"]
    let found := ascriptionCount (← readLines (sourceOf w.root m))
    return if found == count then [] else [s!"{m} holds {found} ascriptions, not {count}"]
  | .modules ms => pure <| ms.filterMap fun m =>
    if moduleExists w m then none else some s!"{m} is not a built module"
  | .gate g => pure <| match g.executable? with
    | some exe => if (w.lakefile.splitOn s!"name = \"{exe}\"").length > 1 then []
      else [s!"executable {exe} is not declared in lakefile.toml"]
    | none => []
  | .ruling id => pure <| if rulingPresent w document id then [] else [s!"ruling {id} is not recorded"]
  | .receipt h => pure <|
    if receiptsLog.any (fun l => l.startsWith s!"## {h}" || l.startsWith s!"### {h}") then []
    else [s!"receipts log has no heading \"{h}\""]
  | .rows r s => pure (rowFindings w r s)
  | .edge _ _ => pure []

def itemFindings (w : World) : Item → List String
  | .named l => if l.isEmpty then ["an open item has no name"] else []
  | .debt id => if debtPresent w id then [] else [s!"debt {id} is not recorded"]
  | .rows r s => rowFindings w r s
  | .wanted n => if w.env.contains n then [s!"wanted theorem {n} now exists; review the edge"] else []
  | .edge _ _ => []

/-- The identifier of a ruling bullet `- R-xx …`, if the line is one. -/
def rulingId? (l : String) : Option String :=
  if l.startsWith "- R-" then some (((Gates.Common.dropChars l 2).splitOn " ").headD "") else none

/-- Every ruling bullet of `COORDINATION.md` with each ledger graph it names,
by identifier or by document path. -/
def rulingMentions (coordination : List String) (graphs : List Graph) : List (String × String) :=
  coordination.flatMap fun l =>
    match rulingId? l with
    | some id => graphs.filterMap fun g =>
      if (l.splitOn g.id).length > 1 || (l.splitOn g.document).length > 1 then some (id, g.id) else none
    | none => []

/-- An edge token of a ruling, the code span `GRAPH-ID/edge=status`. -/
structure EdgeToken where
  ruling : String
  graph : String
  edge : Edge
  status : Status

/-- The code spans of a line: the odd-numbered pieces between backticks. -/
def codeSpans (l : String) : List String :=
  ((l.splitOn "`").zipIdx.filter fun (_, i) => i % 2 == 1).map (·.1)

def parseStatus? (s : String) : Option Status :=
  [Status.requiredOpen, .requiredClosed, .notApplicable].find? (·.text == s)

/-- Every edge token of every ruling bullet, in file order. -/
def edgeTokens (coordination : List String) : List EdgeToken :=
  coordination.flatMap fun l =>
    match rulingId? l with
    | none => []
    | some rid => (codeSpans l).filterMap fun span =>
      match span.splitOn "/" with
      | [graph, rest] => match rest.splitOn "=" with
        | [edgeText, statusText] => do
          let e ← Edge.all.find? (·.label == edgeText)
          let s ← parseStatus? statusText
          some { ruling := rid, graph, edge := e, status := s }
        | _ => none
      | _ => none

/-- The last token for each graph edge: a later ruling supersedes an earlier one. -/
def latestTokens (ts : List EdgeToken) : List EdgeToken :=
  ts.foldl (fun acc t => (acc.filter fun u => !(u.graph == t.graph && u.edge == t.edge)) ++ [t]) []

/-- Findings of the edge tokens against the ledger: the graph exists, the
ledger's status is the ruling's, and the cell cites the ruling. -/
def tokenFindings (l : Ledger) (ts : List EdgeToken) : List String :=
  (latestTokens ts).flatMap fun t =>
    match l.graphs.find? (·.id == t.graph) with
    | none => [s!"ruling {t.ruling} names {t.graph}/{t.edge.label}, which is not in the ledger"]
    | some g =>
      let c := g.edges.get t.edge
      (if c.status == t.status then [] else
        [s!"ruling {t.ruling} records {t.graph}/{t.edge.label}={t.status.text}; the ledger says {c.status.text}"]) ++
      (if c.grounds.contains (.ruling t.ruling) then [] else
        [s!"ruling {t.ruling} records {t.graph}/{t.edge.label}; that cell does not cite it"])

/-- The rulings a graph cites anywhere, with its acknowledgements. -/
def Graph.citedRulings (g : Graph) : List String :=
  g.acknowledged ++ Edge.all.flatMap fun e =>
    (g.edges.get e).grounds.filterMap fun
      | .ruling id => some id
      | _ => none

def graphFindings (w : World) (l : Ledger) (g : Graph) : IO (List String) := do
  let docPath := w.root / g.document
  let logPath := w.root / g.receiptsLog
  let mut out : List String := []
  if !(← docPath.pathExists) then out := out ++ [s!"{g.id}: document {g.document} does not exist"]
  if !(← logPath.pathExists) then out := out ++ [s!"{g.id}: receipts log {g.receiptsLog} does not exist"]
  let document ← if ← docPath.pathExists then readLines docPath else pure []
  let receiptsLog ← if ← logPath.pathExists then readLines logPath else pure []
  for m in g.fence do
    if !moduleExists w m then out := out ++ [s!"{g.id}: fence module {m} is not a built module"]
  for e in Edge.all do
    let c := g.edges.get e
    for gr in c.grounds do
      for f in ← groundFindings w document receiptsLog gr do
        out := out ++ [s!"{g.id} {e.label}: {f}"]
    for it in c.remaining do
      for f in itemFindings w it do
        out := out ++ [s!"{g.id} {e.label}: {f}"]
    for d in c.debts do
      if !debtPresent w d then out := out ++ [s!"{g.id} {e.label}: debt {d} is not recorded"]
  for (ruling, named) in rulingMentions w.coordination l.graphs do
    if named == g.id && !g.citedRulings.contains ruling then
      out := out ++ [s!"{g.id}: ruling {ruling} names this graph and the ledger neither cites nor acknowledges it"]
  return out

/-- A leaf record's document exists, its declarations are constants, and its
receipts resolve. -/
def leafFindings (w : World) (leaf : Leaf) : IO (List String) := do
  let docPath := w.root / leaf.document
  let exists_ ← docPath.pathExists
  let document ← if exists_ then readLines docPath else pure []
  let mut out : List String :=
    if exists_ then [] else [s!"{leaf.id}: document {leaf.document} does not exist"]
  if !document.any (fun l => (l.splitOn leaf.id).length > 1) then
    out := out ++ [s!"{leaf.id}: document {leaf.document} does not name the leaf"]
  for n in leaf.declarations do
    if !w.env.contains n then out := out ++ [s!"{leaf.id}: {n} names no constant"]
  for gr in leaf.receipts do
    for f in ← groundFindings w document [] gr do
      out := out ++ [s!"{leaf.id}: {f}"]
  return out

/-- The ledger source the projections name as their canonical input. -/
def ledgerInput : String := "`WhatwgTest/Ledger.lean`"

/-- Run every check; with `write`, write the projections instead of
comparing them. Returns the exit code. -/
def run (l : Ledger) (write : Bool) : IO UInt32 := do
  let root ← Gates.Common.projectRoot
  let env ← loadEnvironment [`WhatwgTest]
  let w : World := {
    root, env
    coordination := ← readLines (root / "COORDINATION.md")
    register := ← readLines (root / "test" / "counterexamples" / "REGISTER.md")
    lakefile := ← IO.FS.readFile (root / "lakefile.toml") }
  let mut findings := l.findings ++ tokenFindings l (edgeTokens w.coordination)
  for g in l.graphs do
    findings := findings ++ (← graphFindings w l g)
  for leaf in l.leaves do
    findings := findings ++ (← leafFindings w leaf)
  let mut drift : List String := []
  for g in l.graphs do
    let rendered := g.render ledgerInput
    let path := root / g.projection
    if write then
      if findings.isEmpty then
        IO.FS.createDirAll (root / "generated" / "graphs")
        IO.FS.writeFile path rendered
    else if !(← path.pathExists) then
      drift := drift ++ [s!"{g.projection} does not exist"]
    else if (← IO.FS.readFile path) != rendered then
      drift := drift ++ [s!"{g.projection} differs from a fresh rendering"]
  let all := findings ++ drift
  if all.isEmpty then
    IO.println s!"PASS whatwg_ledger: {l.graphs.length} graphs, {l.graphs.length * 10} edges; every reference resolves against the built environment and the authored files, and every projection is byte-identical to a fresh rendering{if write then " (written)" else ""}"
    return 0
  else
    IO.println s!"FAIL whatwg_ledger: {all.length} finding(s)"
    for f in all do IO.println s!"  {f}"
    return 1

def cli (l : Ledger) (args : List String) : IO UInt32 :=
  match args with
  | [] => run l false
  | ["--write"] => run l true
  | _ => do
    IO.eprintln "usage: lake exe whatwg_ledger [--write]"
    return 2

end Gates.Ledger
```

### `WhatwgTest/Ledger/DataQueue.lean`

```lean
import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `DATA-PG-QUEUE` (W7 prototype)

The "Current state" table of `docs/DATA-DAG.md` at `97a8715`, encoded.
References are single-backtick names: this module imports no production
module, and `lake exe whatwg_ledger` resolves every name against the built
environment.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

def dataQueue : Graph where
  id := "DATA-PG-QUEUE"
  document := "docs/DATA-DAG.md"
  fence := [`Whatwg.Streams.Data.Queue, `Whatwg.Streams.Data.Strategy,
    `Whatwg.Streams.Data.DyadicSize]
  acknowledged := []
  edges := {
    identity := {
      status := .requiredClosed
      grounds := [.receipt "5. The ten edges"]
      note := "Closed at the freeze: every row of section 3 names its census row id and that row's span digest from `generated/spec-algorithm-census.tsv`. The landing added the twelfth row, `Whatwg.Streams.Data.DyadicSize`, routed to the representation edge. This document states no generated-snapshot ground for the edge and no ruling adds one." }
    construction := {
      status := .requiredClosed
      grounds := [
        .receipts `WhatwgTest.Streams.Data.QueueAxiomReport 99,
        .modules [`Whatwg.Streams.Data.Queue, `Whatwg.Streams.Data.Strategy,
          `Whatwg.Streams.Data.DyadicSize],
        .ruling "P3-R1",
        .theorems [`Whatwg.Streams.Data.DyadicSize.classified,
          `Whatwg.Streams.Data.DyadicSize.ordered,
          `Whatwg.Streams.Data.DyadicSize.exact,
          `Whatwg.Streams.Data.DyadicSize.admissible_iff],
        .receipt "Landing"]
      note := "The 99 frozen theorems are proved with no battery edit; the D0 to D8 declarations are in the queue and strategy modules, and the `P3-R1` instance is `DyadicSize`." }
    semantics := {
      status := .requiredClosed
      grounds := [
        .theorems [`Whatwg.Streams.Data.enqueueValueWithSize_error_iff_not_admissible,
          `Whatwg.Streams.Data.dequeueValue_cons,
          `Whatwg.Streams.Data.peekQueueValue_agrees_dequeueValue,
          `Whatwg.Streams.Data.resetQueue_eq,
          `Whatwg.Streams.Data.extractHighWaterMark_error_iff,
          `Whatwg.Streams.Data.extractSizeAlgorithm_present],
        .receipt "Landing"]
      note := "The six apex statements are among the 99 proved theorems." }
    laws := {
      status := .requiredClosed
      grounds := [
        .ruling "P3-R1",
        .theorems [`Whatwg.Streams.Data.enqueueValueWithSize_wf,
          `Whatwg.Streams.Data.sizeSum_cons,
          `Whatwg.Streams.Data.dequeueValue_wf,
          `Whatwg.Streams.Data.dequeueValue_clamp_unreachable_of_exact],
        .receipt "Landing"]
      note := "`P3-R1` chose option (i), the exact carrier." }
    representation := {
      status := .requiredClosed
      grounds := [.modules [`Whatwg.Streams.Data.DyadicSize], .receipt "Landing"]
      note := "The four frozen representation decisions of the freeze, each forced by a counterexample row, and the `DyadicSize` carrier row." }
    counterexamples := {
      status := .requiredClosed
      grounds := [.rows ⟨"WS-DATA-CE", 1, 10⟩ .closed]
      debts := ["D50"]
      note := "The witness module `WhatwgTest/Streams/Counterexamples/Data/Queue.lean` imports no production module, so the link from each attack to the rejecting statement is stated in the register rather than checked in Lean." }
    bridges := {
      status := .notApplicable
      note := "The packet claims no relation to a host implementation. `DATA-FB-ROUNDING` is where a bridge would live, and it is refused at this stratum." }
    targets := {
      status := .notApplicable
      note := "No generated code. Lowering is `RS-5` of `docs/REIFICATION-STRATEGY.md` and P11." }
    trust := {
      status := .requiredClosed
      grounds := [.receipts `WhatwgTest.Streams.Data.QueueAxiomReport 99, .gate .build,
        .receipt "Landing"]
      note := "The receipts print inside the R-11 ceiling and the declared red set of `test/fixtures/trust-gate/known-red.txt` is empty. No declaration in `Whatwg.Streams.Data` reaches `Classical.choice` at `325d5d5`, by the census script of appendix B of `docs/research/2026-09-30-implementation-review.md`." }
    coverage := {
      status := .requiredClosed
      grounds := [.modules [`WhatwgTest.Audit.SpecCoverage], .gate (.censusReport "streams"),
        .receipt "Coverage landed"]
      note := "The section 6 rows landed in the numerator." } }

end WhatwgTest.Ledger
```

### `WhatwgTest/Ledger/PromiseFirst.lean`

```lean
import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `PROMISE-PG-FIRST` (W7 prototype)

The "Current state" table of `docs/PROMISE-DAG.md` at `97a8715`, encoded.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

def promiseFirst : Graph where
  id := "PROMISE-PG-FIRST"
  document := "docs/PROMISE-DAG.md"
  fence := [`Whatwg.Ecma262.Promise, `Whatwg.Ecma262.Jobs, `Whatwg.WebIdl.Promise,
    `Whatwg.WebIdl.Exceptions]
  acknowledged := []
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [.debt "D47"]
      grounds := [.receipt "Q3 landing", .receipt "Q4 landing, second pass"]
      note := "The generated declaration snapshot that joins each public declaration to exactly one declaration record has no generator. The six statement batteries' exact ascriptions and the constructor and instance census through the Streams `abbrev`s are delivered, and all 15 class [R] ascriptions of the Q4 battery elaborate since amendment A1." }
    construction := {
      status := .requiredOpen
      remaining := [.named "reachable-state and cross-owner freshness invariants"]
      grounds := [
        .declarations [`Whatwg.Streams.Readable.freshReadCell,
          `Whatwg.Streams.Readable.settleReadCell, `Whatwg.Streams.Readable.settleReadCells],
        .theorems [`Whatwg.Streams.Readable.readTable_freshReadCell,
          `Whatwg.Streams.Readable.readTable_settleReadCell,
          `Whatwg.Streams.Readable.readTable_settleReadCells],
        .receipt "Q4 landing"]
      note := "The `E-22` item is discharged." }
    semantics := {
      status := .requiredOpen
      remaining := [
        .named "the global configuration that threads the activation (the `G-08` remainder)",
        .named "the M2 mask projection",
        .named "the bounded runner"]
      grounds := [.ruling "R-P20", .ruling "R-P24",
        .theorems [`Whatwg.Ecma262.Jobs.run_to_completion,
          `Whatwg.Ecma262.Jobs.run_to_completion_nonvacuous],
        .receipt "Q3b landing"]
      debts := ["D46"]
      note := "R-P20 reopened the edge for COMPLETE (`requirement.jobs.3`); the Q3b landing closed that reopening, and R-P24 keeps the edge open: `startJob` and `completeJob` are reachable only inside the laws of `Whatwg/Ecma262/Jobs.lean` and `run` never consults the activation, so the remaining items stay P8 work." }
    laws := {
      status := .requiredClosed
      grounds := [
        .receipts `WhatwgTest.Ecma262.PromiseAxiomReport 125,
        .receipts `WhatwgTest.Ecma262.PromiseFidelityAxiomReport 57,
        .receipt "Q3 landing", .ruling "R-P20", .receipt "Q3b landing", .ruling "R-P24"]
      note := "182 named receipts are proved." }
    representation := {
      status := .requiredClosed
      grounds := [.receipt "Q3 landing", .ruling "R-P20", .receipt "Q3b landing",
        .receipt "Q4 landing"]
      note := "`Nat` identities with monotone cursors, first-order reactions and jobs, the two reaction lists with their one-list view, the per-cell handled bit with its identity-list bridge, and the exception universe with allocation identity, each by named theorems; `Reaction.capability` added and still `Repr`-only; the P4 to P7 record rows name `Whatwg.Ecma262.Promise` the shared owner with receipts `E-07` to `E-12`." }
    counterexamples := {
      status := .requiredOpen
      remaining := [
        .rows ⟨"WS-PROM-CE", 15, 15⟩ .seeded, .rows ⟨"WS-PROM-CE", 26, 26⟩ .seeded,
        .rows ⟨"WS-PROM-CE", 33, 33⟩ .seeded, .rows ⟨"WS-PROM-CE", 36, 38⟩ .seeded]
      grounds := [
        .rows ⟨"WS-PROM-CE", 1, 14⟩ .closed, .rows ⟨"WS-PROM-CE", 16, 25⟩ .closed,
        .rows ⟨"WS-PROM-CE", 27, 32⟩ .closed, .rows ⟨"WS-PROM-CE", 34, 35⟩ .closed,
        .rows ⟨"WS-PROM-CE", 39, 39⟩ .closed, .ruling "R-P24"]
      debts := ["D17"]
      note := "`WS-PROM-CE-015`: no witness pins the absent `DecidableEq`; `WS-PROM-CE-026`: the capability is stored and never read." }
    bridges := {
      status := .requiredClosed
      grounds := [
        .modules [`WhatwgTest.Streams.PromiseBridge], .receipt "Q3 landing", .ruling "R-P20",
        .theorems [`Whatwg.Streams.Writable.settlementTrace_bridge], .receipt "Q3b landing",
        .theorems [`Whatwg.Streams.Transform.notify_jobQueue_bridge,
          `Whatwg.Streams.Transform.settle_table_bridge,
          `Whatwg.Streams.Transform.settle_jobQueue_order,
          `Whatwg.Streams.Transform.settle_waiting_once,
          `Whatwg.Streams.Transform.runJob_writable_dequeue,
          `Whatwg.Streams.Transform.runJob_writable_blocked],
        .modules [`WhatwgTest.Streams.PromiseBridgeQ4], .receipt "Q4 landing"]
      note := "The 29 Q3 bridging lemmas with the preservation half of the Q3 bridge battery, and the bridges rows 14 to 16 of §4.4 of the Q3 contract deferred. Deferred with stated reasons, outside this edge's obligation: `E-63`'s readable settlement-trace bridge, and the host profiles and WPT settlement-order replay of P8." }
    targets := {
      status := .notApplicable
      note := "Q3, Q3b and Q4 land no lowering and no generated code; P11 owns the TypeScript target." }
    trust := {
      status := .requiredClosed
      grounds := [
        .receipts `WhatwgTest.Ecma262.PromiseAxiomReport 125,
        .receipts `WhatwgTest.Ecma262.PromiseFidelityAxiomReport 57,
        .gate .trustselftest, .receipt "Q3 landing", .receipt "Q3b landing",
        .ruling "R-P20", .ruling "R-P24", .ruling "R-V6", .ruling "R-V1", .gate .build]
      note := "At `325d5d5` seven receipts reached `Classical.choice`; lane V repaired all seven with no statement changed (slices V1 and V5), and the axiom gate holds `Whatwg.Ecma262`, `Whatwg.WebIdl` and `Whatwg.Streams` to `propext` and `Quot.sound` with no exception." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "a witness for any row of the Web IDL and ECMA-262 censuses; every row is `absent`"]
      grounds := [.ruling "R-P20",
        .modules [`WhatwgTest.Audit.WebIdl.SpecCoverage, `WhatwgTest.Audit.Ecma262.SpecCoverage]]
      note := "Ruling R-P20 set the edge `required-open` because both numerator modules exist. The later sentence of the Q3 landing section that says coverage stays `not-applicable` disagrees with R-P20, and R-P20 wins." } }

end WhatwgTest.Ledger
```

### `WhatwgTest/Ledger/ConfigurationOrdering.lean`

```lean
import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `CONFIGURATION-PG-ORDERING` (W7 prototype)

The "Current state" table of `docs/CONFIGURATION-DAG.md` at `97a8715`,
encoded. Its dependencies on the P4 to P7 graphs wait for their entries.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

def configurationOrdering : Graph where
  id := "CONFIGURATION-PG-ORDERING"
  document := "docs/CONFIGURATION-DAG.md"
  fence := [`Whatwg.Streams.Semantics.Configuration]
  dependsOn := ["PROMISE-PG-FIRST"]
  acknowledged := []
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [.debt "D47"]
      grounds := [
        .declarations [`Whatwg.Streams.Semantics.Ordering.phaseErase,
          `Whatwg.Streams.Semantics.Ordering.reactionErase],
        .receipt "Q4 landing, second pass"]
      note := "The generated declaration join has no generator. All 15 class [R] ascriptions elaborate since amendment A1, and the 86 `Source` names are added." }
    construction := {
      status := .requiredOpen
      remaining := [.named "CFG-START", .named "CFG-CELLS", .named "CFG-TOKENS",
        .named "CFG-STACK", .named "inductive reachable-state preservation", .debt "D38",
        .wanted `Whatwg.Streams.Semantics.Ordering.CellsWellFormed]
      note := "Debt D38: `notifySettled_eq`'s owner conjunct rests on `CellsWellFormed`, which is not yet stated (CFG-CELLS)." }
    semantics := {
      status := .requiredOpen
      remaining := [.named "CFG-EFFECTS",
        .named "CFG-FIFO (its PROCESS/ADVANCE corollary is still owed)", .named "CFG-RUNS",
        .named "the foreign profile", .named "the global scheduler", .named "the live frontiers"]
      grounds := [.receipt "Q4 landing, second pass"] }
    laws := {
      status := .requiredOpen
      remaining := [
        .named "`WellFormed` initialization and preservation",
        .named "the successful-profile progress theorem",
        .named "the ordered-effect receipts",
        .named "the token/mailbox correspondence",
        .named "the finite witness through the original start gate"]
      grounds := [.receipts `WhatwgTest.Streams.Semantics.OrderingAxiomReport 93,
        .receipt "Q4 landing, second pass"]
      note := "All 54 restated law ascriptions, the 15 Q4-owned bridging receipts and the 18 deferred-generalization ascriptions are proved. The edge stays open on the obligations §3.3 of the contract lists and no law here states." }
    representation := {
      status := .requiredOpen
      remaining := [
        .named "a stable typed address for the P4 read and closed cells (`E-24` keeps `Readable.State.closedPromise` by value)",
        .named "the freeze-time item \"typed references\"",
        .named "the freeze-time item \"no closures\""]
      grounds := [.ruling "R-V8", .receipt "Q4 landing, second pass"]
      note := "Ruled open by R-V8: the second pass keeps the edge open and names no remaining item. The landing records report one cell owner, one payload owner, no shadow scheduler, no second table, and the four view record rows of contract §4.1 with their twenty ascriptions." }
    counterexamples := {
      status := .requiredOpen
      remaining := [.named "the actual configuration witness",
        .named "the stable registered scheduler mutants",
        .named "the retained failing alternatives", .debt "D39"]
      grounds := [.rows ⟨"WS-PROM-CE", 39, 39⟩ .closed, .ruling "R-P27"]
      note := "D39: the `WS-CONFIG` register rows of the three certificate mutants `mutantSelectedD0`, `mutantAliasedResults` and `mutantFlushOnW0`." }
    bridges := {
      status := .requiredOpen
      remaining := [
        .wanted `Whatwg.Streams.Semantics.Ordering.run_erases_to_reference,
        .debt "D35", .named "the host replay", .named "CFG-LOCAL", .named "CFG-OBS",
        .named "CFG-HOST", .named "the full P4/P5/P6/P7 embeddings"]
      debts := ["D34", "D36", "D37"]
      note := "The P8 half of CFG-WPT: the existence half, the transcription gate to the sealed WPT bytes (D35) and the host replay. Debts D34, D36 and D37 are recorded against the CFG-WPT seam." }
    targets := {
      status := .notApplicable
      note := "This graph generates no target program; P11 owns target lowering." }
    trust := {
      status := .requiredClosed
      grounds := [.ruling "R-P27", .receipts `WhatwgTest.Streams.Semantics.OrderingAxiomReport 93,
        .gate .trustselftest, .receipt "Q4 landing, second pass", .ruling "R-V1", .ruling "R-V6",
        .ruling "R-V8", .gate .build]
      note := "The document held the edge open on independent review alone; ruling R-P27 records that review of `1d400b4` as done, so the edge closes on R-P27. Slice V5 of lane V repaired the nine receipts that reached `Classical.choice` at `325d5d5` with no statement changed; D43 is closed." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "the exact clause and numerator joins"]
      grounds := [.receipt "Q4 landing, second pass"]
      note := "The R-P5 re-disposition of `slot.promise-state` and `slot.promise-is-handled` to `owned` moved no coverage state." } }

end WhatwgTest.Ledger
```

### `WhatwgTest/Ledger.lean`

```lean
import WhatwgTest.Ledger.DataQueue
import WhatwgTest.Ledger.PromiseFirst
import WhatwgTest.Ledger.ConfigurationOrdering

/-!
# The graph ledger (W7 prototype)

Every graph's entry, every leaf-receipt record, and the kernel-checked
statement that the ledger has no structural finding. No metaprogramming:
`decide +kernel` evaluates `Gates.Ledger.Ledger.wellFormed` in the kernel
alone.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The one leaf-receipt record the tree has, `INFRA-LF-INTEGER`
(`docs/INFRA-INTEGER-CONSTRUCTIVE.md`), standalone. -/
def infraInteger : Leaf where
  id := "INFRA-LF-INTEGER"
  document := "docs/INFRA-INTEGER-CONSTRUCTIVE.md"
  declarations := [`Whatwg.Infra.Unsigned8, `Whatwg.Infra.Unsigned16, `Whatwg.Infra.Unsigned32,
    `Whatwg.Infra.Unsigned64, `Whatwg.Infra.Unsigned128, `Whatwg.Infra.Signed8,
    `Whatwg.Infra.Signed16, `Whatwg.Infra.Signed32, `Whatwg.Infra.Signed64]
  parent := none
  receipts := [
    .theorems [`Whatwg.Infra.Unsigned8.inRange, `Whatwg.Infra.Unsigned16.inRange,
      `Whatwg.Infra.Unsigned32.inRange, `Whatwg.Infra.Unsigned64.inRange,
      `Whatwg.Infra.Unsigned128.inRange, `Whatwg.Infra.Signed8.inRange,
      `Whatwg.Infra.Signed16.inRange, `Whatwg.Infra.Signed32.inRange,
      `Whatwg.Infra.Signed64.inRange],
    .ascriptions `WhatwgTest.Infra.IntegerConstructiveContract 9,
    .rows ⟨"INFRA-INTEGER-CE", 1, 1⟩ .closed]

def ledger : Ledger where
  graphs := [dataQueue, promiseFirst, configurationOrdering]
  leaves := [infraInteger]

theorem ledger_wellFormed : ledger.wellFormed = true := by decide +kernel

end WhatwgTest.Ledger
```

### `whatwgbin/Ledger.lean`

```lean
import WhatwgGates.Ledger.Check
import WhatwgTest.Ledger

/-- Entry point only; the audited logic is Gates.Ledger.cli, and the ledger is
the test-side data `WhatwgTest.Ledger.ledger`, which imports no production module. -/
def main (args : List String) : IO UInt32 :=
  Gates.Ledger.cli WhatwgTest.Ledger.ledger args
```

## Appendix B: a rendered projection

`generated/graphs/DATA-PG-QUEUE.md` as `lake exe whatwg_ledger --write` wrote it
from the entry above.

### `generated/graphs/DATA-PG-QUEUE.md`

```markdown
<!-- GENERATED by `lake exe whatwg_ledger --write` (Gates.Ledger, format 1) from `WhatwgTest/Ledger.lean`; do not edit. -->

# Current state of `DATA-PG-QUEUE`

Graph document: `docs/DATA-DAG.md`. Receipts log: `docs/receipts/DATA-PG-QUEUE.md`.
Fence: `Whatwg.Streams.Data.Queue`, `Whatwg.Streams.Data.Strategy` and `Whatwg.Streams.Data.DyadicSize`.
Depends on: none.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-closed` | Closed at the freeze: every row of section 3 names its census row id and that row's span digest from `generated/spec-algorithm-census.tsv`. The landing added the twelfth row, `Whatwg.Streams.Data.DyadicSize`, routed to the representation edge. This document states no generated-snapshot ground for the edge and no ruling adds one. Closed on: receipt "5. The ten edges". |
| construction | `required-closed` | The 99 frozen theorems are proved with no battery edit; the D0 to D8 declarations are in the queue and strategy modules, and the `P3-R1` instance is `DyadicSize`. Closed on: 99 receipts of `WhatwgTest.Streams.Data.QueueAxiomReport`; modules `Whatwg.Streams.Data.Queue`, `Whatwg.Streams.Data.Strategy` and `Whatwg.Streams.Data.DyadicSize`; ruling P3-R1; theorems `Whatwg.Streams.Data.DyadicSize.classified`, `Whatwg.Streams.Data.DyadicSize.ordered`, `Whatwg.Streams.Data.DyadicSize.exact` and `Whatwg.Streams.Data.DyadicSize.admissible_iff`; receipt "Landing". |
| semantics | `required-closed` | The six apex statements are among the 99 proved theorems. Closed on: theorems `Whatwg.Streams.Data.enqueueValueWithSize_error_iff_not_admissible`, `Whatwg.Streams.Data.dequeueValue_cons`, `Whatwg.Streams.Data.peekQueueValue_agrees_dequeueValue`, `Whatwg.Streams.Data.resetQueue_eq`, `Whatwg.Streams.Data.extractHighWaterMark_error_iff` and `Whatwg.Streams.Data.extractSizeAlgorithm_present`; receipt "Landing". |
| laws | `required-closed` | `P3-R1` chose option (i), the exact carrier. Closed on: ruling P3-R1; theorems `Whatwg.Streams.Data.enqueueValueWithSize_wf`, `Whatwg.Streams.Data.sizeSum_cons`, `Whatwg.Streams.Data.dequeueValue_wf` and `Whatwg.Streams.Data.dequeueValue_clamp_unreachable_of_exact`; receipt "Landing". |
| representation | `required-closed` | The four frozen representation decisions of the freeze, each forced by a counterexample row, and the `DyadicSize` carrier row. Closed on: modules `Whatwg.Streams.Data.DyadicSize`; receipt "Landing". |
| counterexamples | `required-closed` | The witness module `WhatwgTest/Streams/Counterexamples/Data/Queue.lean` imports no production module, so the link from each attack to the rejecting statement is stated in the register rather than checked in Lean. Closed on: `WS-DATA-CE-001` to `WS-DATA-CE-010` `CLOSED`. Debts recorded: D50. |
| bridges | `not-applicable` | The packet claims no relation to a host implementation. `DATA-FB-ROUNDING` is where a bridge would live, and it is refused at this stratum. |
| targets | `not-applicable` | No generated code. Lowering is `RS-5` of `docs/REIFICATION-STRATEGY.md` and P11. |
| trust | `required-closed` | The receipts print inside the R-11 ceiling and the declared red set of `test/fixtures/trust-gate/known-red.txt` is empty. No declaration in `Whatwg.Streams.Data` reaches `Classical.choice` at `325d5d5`, by the census script of appendix B of `docs/research/2026-09-30-implementation-review.md`. Closed on: 99 receipts of `WhatwgTest.Streams.Data.QueueAxiomReport`; `lake build`; receipt "Landing". |
| coverage | `required-closed` | The section 6 rows landed in the numerator. Closed on: modules `WhatwgTest.Audit.SpecCoverage`; `lake exe whatwg_census --standard streams --report`; receipt "Coverage landed". |
```
