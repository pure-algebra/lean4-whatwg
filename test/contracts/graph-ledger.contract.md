# Graph ledger contract (W7)

Status: FROZEN / RED, W7 breaker seat of review lane W, 2026-10-01, on
branch `review/w7-ledger-breaker` from
`b0d35e2bea772fc6dd2fb44a0cdac8f0afc2eaa7`. Ruling R-W6 of `COORDINATION.md`
adopts the design `docs/research/2026-10-01-w7-graph-ledger-design.md` with
three changes and the attestation rule; this packet freezes that design as
amended. Where the design and R-W6 disagree, R-W6 is what is frozen here.

Battery: `WhatwgTest/Audit/LedgerContract.lean`. The battery is the
authority on names and propositions; the Lean below is a reading aid. The
builder may repair elaboration but may not weaken, delete or replace a
frozen ascription, plant, finding text, count or byte of rendered output.

## 1. Claim boundary

The ledger is tooling. It owns no specification anchor, no stream judgment,
no denotation and no host observation, so `docs/AGENT-ROUTING.md` routes
none of it to a proof graph; its assurance route is this contract and its
battery, as for the census and the trust gate (design, decision 8). It
grants no coverage state and closes no edge of any graph.

What a green gate means, and nothing more: the ledger has no structural
finding (section 4, decided in the kernel at `lake build`); every reference
the ledger makes resolves against the built environment and the authored
files the gate reads at run time (section 5); every edge token of a ruling
agrees with the ledger and every ruling that names a ledger graph is cited
or acknowledged by it (section 7); and every projection under
`generated/graphs/` is byte-identical to a fresh rendering (section 8).
Section 13 lists what it does not read.

## 2. Modules and dependency direction

| Module | Imports | Holds |
| --- | --- | --- |
| `WhatwgGates.Ledger.Model` | `Init` only | the data types and the structural invariant |
| `WhatwgGates.Ledger.Render` | the model | the projection |
| `WhatwgGates.Ledger.Check` | the model, the renderer, `WhatwgGates.Common`, the shared loader `WhatwgGates.Trust.Load` | the reference pass as pure functions over `World`, and `cli` |
| `WhatwgTest.Ledger.<Graph>` | the model only | one graph's entry |
| `WhatwgTest.Ledger` | the graph modules | `ledger`, the leaf records, `ledger_wellFormed` |
| `whatwgbin.Ledger` | `Check` and `WhatwgTest.Ledger` | `main`, calling `Gates.Ledger.cli WhatwgTest.Ledger.ledger` |

No module of the ledger imports a production module (`Whatwg.*`), declares
syntax, a macro, an elaborator or an initializer, or joins any list of the
trust gate: no `metaprogrammingModules` entry, no `sourceTokenExemptions`
entry, no strict exception. The ledger modules sit under no strict prefix,
so R-11's ceiling binds them. Every declaration of these modules that this
contract does not list is `private`.

## 3. The model

Namespace `Gates.Ledger`, module `WhatwgGates.Ledger.Model`. Every type
derives `DecidableEq` and `Repr`.

```lean
inductive Edge where
  | identity | construction | semantics | laws | representation
  | counterexamples | bridges | targets | trust | coverage

inductive Gate where
  | build | vendorseal | citations | trustselftest | leanchecker
  | census (standard : String) | censusReport (standard : String)
  | urlinventory | urlcensus

inductive RowStatus where | closed | seeded

structure RowRange where
  family : String
  first : Nat
  last : Nat

inductive Ground where
  | theorems (names : List Lean.Name)
  | declarations (names : List Lean.Name)
  | receipts («module» : Lean.Name) (count : Nat)
  | ascriptions («module» : Lean.Name) (count : Nat)
  | modules (names : List Lean.Name)
  | gate (g : Gate)
  | ruling (id : String)
  | receipt (heading : String)
  | rows (range : RowRange) (status : RowStatus)
  | edge (graph : String) (e : Edge)

inductive Item where
  | named (label : String)
  | debt (id : String)
  | rows (range : RowRange) (status : RowStatus)
  | wanted (name : Lean.Name)
  | edge (graph : String) (e : Edge)

inductive Status where | requiredOpen | requiredClosed | notApplicable

structure Cell where
  status : Status
  grounds : List Ground := []
  remaining : List Item := []
  debts : List String := []
  note : String := ""

structure Edges where      -- exactly ten fields, in the order of Edge
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

structure Graph where
  id : String
  document : String
  fence : List Lean.Name
  dependsOn : List String := []
  acknowledged : List String := []
  edges : Edges

structure Leaf where
  id : String
  document : String
  declarations : List Lean.Name
  parent : Option (String × Edge)
  receipts : List Ground

structure Unrouted where
  modulePrefix : Lean.Name
  recordedBy : String

structure Ledger where
  graphs : List Graph
  leaves : List Leaf := []
  unrouted : List Unrouted := []
```

Functions of the model, with the spellings the battery pins:

| Declaration | Signature | Meaning |
| --- | --- | --- |
| `Edge.all` | `List Edge` | the ten edges in the order of `docs/AGENT-ROUTING.md`, "The ten edges" |
| `Edge.label` | `Edge → String` | `identity` … `coverage` |
| `Gate.command` | `Gate → String` | the exact command, e.g. `lake exe whatwg_census --standard streams --report` |
| `Gate.executable?` | `Gate → Option String` | the `[[lean_exe]]` name the gate needs; `none` for `build` and `leanchecker` |
| `RowStatus.text` | `RowStatus → String` | `CLOSED`, `SEEDED` |
| `threeDigits` | `Nat → String` | zero-padded to three digits, longer numbers unchanged |
| `RowRange.ids` | `RowRange → List String` | `family-NNN` from `first` to `last`; empty when `last < first` |
| `Ground.discharges` | `Ground → Bool` | false only for `rows` cited with a status other than `CLOSED` |
| `Ground.attests` | `Ground → Bool` | true for `ruling`, `receipt` and `rows … closed`; false for every other ground |
| `Status.text` | `Status → String` | `required-open`, `required-closed`, `not-applicable` |
| `Edges.get` | `Edges → Edge → Cell` | the field of that edge |
| `Graph.receiptsLog` | `Graph → String` | `docs/receipts/<id>.md` (ruling R-V4) |
| `Graph.projection` | `Graph → String` | `generated/graphs/<id>.md` |
| `distinct` | `{α : Type} → [DecidableEq α] → List α → Bool` | no element twice |
| `Cell.problem?` | `Cell → Option String` | the cell's structural finding |
| `Ledger.statusOf?` | `Ledger → String → Edge → Option Status` | another graph's edge status |
| `Cell.crossReferences` | `Cell → List (String × Edge × Status)` | `edge` grounds wanting `requiredClosed`, then `edge` items wanting `requiredOpen` |
| `Ledger.dependenciesAcyclic` | `Ledger → Bool` | Kahn's algorithm, the graph count as fuel |
| `Ledger.findings` | `Ledger → List String` | every structural finding, named |
| `Ledger.wellFormed` | `Ledger → Bool` | `findings` is empty |

A ledger entry that omits an edge field fails to elaborate with
"Fields missing: `coverage`", and one that repeats a field with "field
'identity' has already been specified" (battery section 2).

## 4. The structural invariant, decided in the kernel

`WhatwgTest.Ledger.ledger_wellFormed : WhatwgTest.Ledger.ledger.wellFormed =
true` is proved by `decide +kernel`. `Gates.Ledger.Ledger.wellFormed` is
written with equality, emptiness, pattern matching and list operations only,
because kernel reduction gets stuck on `String.startsWith` and
`String.trimAscii` (design, section 2.3). `Ledger.findings` is, in order:

1. `two graphs share an identifier`, when graph identifiers repeat;
2. per graph, in ledger order: `<G>: unknown dependency <D>` for each
   dependency that is no graph of the ledger, `<G>: depends on itself`, and,
   per edge in `Edge.all` order, the cell's problem as `<G> <edge>: <why>`,
   then each cross-graph citation whose graph is unknown
   (`<G> <edge>: unknown graph <H>`) or whose edge has the wrong status
   (`<G> <edge>: cites <H> <edge'> as <wanted>, but it is <actual>`);
3. `leaf <L>: unknown parent graph <G>`, per leaf whose parent is not a graph;
4. `a leaf shares an identifier`, when leaf identifiers repeat or a leaf
   identifier is a graph identifier;
5. `the graph dependencies have a cycle`.

The cell problems, `Cell.problem?`, first match wins:

| Status | Condition | Finding |
| --- | --- | --- |
| `requiredClosed` | an item remains | `closed with remaining items` |
| `requiredClosed` | no ground | `closed with no ground` |
| `requiredClosed` | a ground does not discharge | `closed on rows that are not CLOSED` |
| `requiredClosed` | no ground attests (R-W6) | `closed with no ruling, receipts-log heading or CLOSED rows` |
| `requiredOpen` | no item remains | `open with no remaining item named` |
| `notApplicable` | an item remains, or a ground is not a `ruling` | `not-applicable with an item or a ground other than a ruling` |
| `notApplicable` | the note is empty | `not-applicable with no reason` |

The attestation rule is R-W6's: every closed cell cites a ruling, a
receipts-log heading or `CLOSED` register rows, so that an edit to the
ledger cannot close an edge on theorem names, counts or gates alone. A
cross-graph `edge` ground does not attest.

A not-applicable cell may carry `ruling` grounds and nothing else. This is a
deviation from the design, whose prototype refused every ground on such a
cell: a ruling that sets an edge `not-applicable` writes an edge token, and
the token check requires the cell to cite that ruling (section 7).

The battery holds seventeen kernel-decided refusals and three controls, each
with a `#guard` pinning its finding:

| Id | Plant | Finding |
| --- | --- | --- |
| P1 | closed cell with a remaining item | `closed with remaining items` |
| P2 | closed cell with no ground | `closed with no ground` |
| P3 | open cell with nothing named | `open with no remaining item named` |
| P4 | not-applicable cell with no reason | `not-applicable with no reason` |
| P5 | two graphs with one identifier | `two graphs share an identifier` |
| P6 | dependency on an unknown graph | `unknown dependency` |
| P7 | closed cell citing another graph's open edge (`LEDGER-CE-005`) | `cites … as required-closed, but it is required-open` |
| P8 | closed cell on register rows cited `SEEDED` | `closed on rows that are not CLOSED` |
| P9 | graph depending on itself | `depends on itself`, and the cycle |
| P10 | two graphs depending on each other | the cycle |
| P11 | leaf whose parent graph is unknown | `unknown parent graph` |
| P12 | leaf sharing a graph's identifier | `a leaf shares an identifier` |
| P13 | closed cell with no attestation (R-W6) | `closed with no ruling, receipts-log heading or CLOSED rows` |
| P14 | not-applicable cell with a non-ruling ground | `not-applicable with an item or a ground other than a ruling` |
| P15 | open item citing another graph's closed edge | `cites … as required-open, but it is required-closed` |
| P16 | cross-graph citation of an unknown graph | `unknown graph` |
| P17 | two leaves with one identifier | `a leaf shares an identifier` |
| C1 | one well-formed graph | accepted |
| C2 | two graphs, one depending on the other, citing each other's edges with the right status | accepted |
| C3 | each attestation kind alone, and a not-applicable cell citing its ruling | accepted |

The build-time theorem is a tripwire: a defect makes the kernel refuse with
no name. The executable prints the same findings, named (section 9).

## 5. The reference pass

### 5.1 `World`: what the pass reads, as data

Module `WhatwgGates.Ledger.Check`, namespace `Gates.Ledger`.

```lean
inductive ConstantKind where
  | thm     -- a `theorem`
  | other   -- any other constant

structure World where
  constantKind? : Lean.Name → Option ConstantKind
  moduleBuilt : Lean.Name → Bool
  file? : String → Option String
  projectionFiles : List String
```

`constantKind? n` is the kind of the constant `n` of the built environment,
or `none`. `moduleBuilt m` says whether `m` is a module of the built
environment. `file? p` is the text of the file at the forward-slash path `p`
relative to the repository root, or `none` when it does not exist.
`projectionFiles` is the forward-slash relative path of every regular file
under `generated/graphs/`, sorted.

Every check is a pure function of a `World` and the ledger. Only `cli`
(section 10) does IO: it builds the one `World` of a run and acts on the
`Outcome`. The battery plants `World` values.

### 5.2 Grounds

`groundFindings w document receiptsLog g` takes the lines of the graph
document and of its receipts log (`[]` when absent). Each finding is
reported prefixed `<GRAPH-ID> <edge>: ` for a graph cell and `<LEAF-ID>: `
for a leaf's receipts.

| Ground | Resolved against | Finding |
| --- | --- | --- |
| `theorems ns` | `constantKind?` | `<n> names no constant`; `<n> is not a theorem` |
| `declarations ns` | `constantKind?` | `<n> names no constant` |
| `receipts m k` | `moduleBuilt`, then the source `sourcePath m` | `<m> is not a built module`; `<m> has no source <path>`; `<m> holds <found> receipts, not <k>` |
| `ascriptions m k` | the same | the same with `ascriptions` |
| `modules ms` | `moduleBuilt` | `<m> is not a built module` |
| `gate g` | `lakefile.toml` contains `name = "<exe>"` for `g.executable?` | `executable <exe> is not declared in lakefile.toml` |
| `ruling r` | a ruling bullet of `COORDINATION.md` (a line beginning `- `, `r`, a space), or a row of the graph document's rulings table (rule R below) | `ruling <r> is not recorded` |
| `receipt h` | a line of the receipts log beginning `## <h>` or `### <h>` | `receipts log has no heading "<h>"` |
| `rows r s` | each id of `r` as a row of `test/counterexamples/REGISTER.md` (rule T below) | `register row <id> does not exist`; `register row <id> is <actual>, not <s>` |
| `edge h e` | nothing: the kernel checks it (section 4) | none |

Rule R: a rulings-table row of the graph document is a line that begins
with the Lean string `"| `" ++ r ++ "` |"`, as the `P3-R1` row of
`docs/DATA-DAG.md` does. Rule T: a register row is the first line of the
register that begins with `"| `" ++ id ++ "` | `"`; its status is the text
after that prefix up to the next backtick. Both are line-prefix rules over
the file's lines.

`sourcePath` spells a module's components joined by `/` with `.lean`:
`WhatwgTest.Streams.Data.QueueAxiomReport` is
`WhatwgTest/Streams/Data/QueueAxiomReport.lean`. The heading rule is a
prefix rule, so `receipt "Q4 landing"` matches `## Q4 landing, 2026-09-07,
branch …`; a level-one title and a level-four heading do not match.

### 5.3 Items and recorded debts

| Item | Resolved against | Finding |
| --- | --- | --- |
| `named l` | nothing; authored text | `an open item has no name` when `l` is empty |
| `debt d` | a line of `COORDINATION.md` containing `(<d>)` | `debt <d> is not recorded` |
| `rows r s` | the register, as for the ground | as for the ground |
| `wanted n` | `constantKind?` | `wanted theorem <n> now exists; review the edge`, when `n` names any constant |
| `edge h e` | nothing: the kernel checks it | none |

Each entry of a cell's `debts` is checked as a `debt` item.

### 5.4 Graphs, leaves and unrouted prefixes

`graphFindings w l g` reports, in this order: `<G>: document <path> does
not exist`; `<G>: receipts log <path> does not exist`; when the document
exists and does not contain the text `generated/graphs/<G>.md`, `<G>:
document <path> does not link generated/graphs/<G>.md`; `<G>: fence module
<m> is not a built module`; then, per edge in `Edge.all` order, every ground
finding, every item finding and every recorded-debt finding of the cell; then
the mention findings of section 7.3.

`leafFindings w leaf`: `<L>: document <path> does not exist`; otherwise,
when the document's text does not contain the leaf identifier, `<L>: document
<path> does not name the leaf`; `<L>: <n> names no constant` for each
declaration; then every ground finding of its receipts, with the leaf's
document as the rulings table and no receipts log.

`unroutedFindings w u`: `unrouted <prefix>: not a built module`, when the
prefix is not a module of the built environment; `unrouted <prefix>:
<recordedBy> is not a recorded debt or ruling`, when `recordedBy` is neither
a debt (`(<id>)` in `COORDINATION.md`) nor a ruling bullet.

`referenceFindings w l` is `l.findings`, then the token findings of section
7, then `graphFindings` for every graph, `leafFindings` for every leaf and
`unroutedFindings` for every unrouted entry, in ledger order.

### 5.5 Evidence names production constants (R-W6, change 3)

Ledger data names constants and modules with single-backtick `Lean.Name`
literals, which elaborate without importing the module that declares them;
existence and kind are checked by the executable (design, section 2.8). A
double-backtick literal is not used: it would make the data import
production modules. Once R-W5's conversion has landed, a follow-up packet
adds the check that a `theorems` ground has a freeze-registry entry; this
packet does not wait for it, and `LEDGER-CE-002` stays open for count-only
grounds until then.

## 6. Counts over both spellings (R-W6, change 2)

An ascription is a `#check (@…)` command or a `#whatwg_freeze (@…)` command.
A receipt is a `#print axioms` command or a `#whatwg_freeze` command with an
`axioms` clause. R-W5's conversion turns each `#check (@n : T)` into
`#whatwg_freeze (@n : T)`, with `axioms [..]` for a theorem, so no
ascription count changes; it retires the `*AxiomReport.lean` modules, and
the conversion slice retargets in the same commit every `receipts` ground
that names a retired module.

Counts are taken from the module source, by this lexical rule:

1. Code text. Every character of a comment and every character inside a
   literal is replaced by a space, except LF and CR, which are kept, so
   lines and columns are unchanged. Comments are line comments (`--` to the
   end of the line) and block comments (`/-` to the matching `-/`, nested;
   docstrings `/--` and module documentation `/-!` included); the delimiters
   of a comment are blanked too. Literals are strings (`"` to the next `"`
   not escaped by `\`), characters (a `'` not preceded by an identifier
   character, to the next `'` not escaped by `\`; an identifier character is
   a letter, a digit, `_`, `'`, `!`, `?` or any character above U+007F) and
   raw strings (`r` not preceded by an identifier character, then `n` ≥ 0
   `#` and `"`, to the next `"` followed by `n` `#`); a literal's delimiters
   are kept. A comment opener inside a literal, and a quote inside a comment,
   open nothing. `codeLines` is that text split into lines by
   `Gates.Common.lines`.
2. A command counts only when its line of code text begins with it, at
   column zero.
3. `ascriptionCount` counts the lines beginning `#check (@` or
   `#whatwg_freeze (@`.
4. `receiptCount` counts the lines beginning `#print axioms`, and the freeze
   commands that carry an `axioms` clause. A freeze command's text is its
   first line and every following line that is empty or begins with a space
   or a tab. It carries the clause when, after the parenthesis that closes
   the `(` following `#whatwg_freeze `, and after any whitespace, the text
   begins with `axioms` followed by a character that is not an identifier
   character, or by nothing. Parentheses are counted on code text, so one
   inside a literal does not count.

Measured on the design's prototype at `97a8715`: every receipt and
ascription count the eleven current tables state recomputes with the
comment-blind rule; section 15 records the same counts under this rule.

## 7. Rulings

### 7.1 The edge token

A ruling that changes an edge writes one code span per changed edge:

```text
`GRAPH-ID/edge=status`
```

`GRAPH-ID` is the graph identifier, `edge` an `Edge.label` and `status` a
`Status.text`. A ruling is a line of `COORDINATION.md` beginning `- R-`; its
identifier is the text from the third character to the first space
(`rulingId?`). A ruling occupies one line, as every ruling of
`COORDINATION.md` does. `edgeTokens` reads the code spans of every ruling
line, the odd-numbered pieces between backticks, and keeps a span exactly
when it splits at its one `/` and then at its one `=` into a known edge
label and a known status text. Any other span is not a token: the R-W6
bullet's own `GRAPH-ID/edge=status` is not one, and no ruling at the base
commit carries one.

### 7.2 Latest wins, and the token check

The latest token for a graph edge is the last in `COORDINATION.md` order,
and within one ruling the last on the line (`latestTokens`). The
coordinator appends rulings, so file order is the order of record. For each
latest token, `tokenFindings` reports:

- `ruling <R> names <G>/<edge>, which is not in the ledger`, when no graph
  has that identifier;
- `ruling <R> records <G>/<edge>=<status>; the ledger says <actual>`, when
  the cell's status differs;
- `ruling <R> records <G>/<edge>; that cell does not cite it`, when the
  cell's grounds hold no `ruling <R>`.

### 7.3 The mention check

`rulingMentions` pairs every ruling line with each ledger graph whose
identifier or document path occurs in it. A graph that a ruling names and
that neither cites the ruling in a ground of any cell nor lists it in
`acknowledged` (`Graph.citedRulings`) is reported by `graphFindings` as
`<G>: ruling <R> names this graph and the ledger neither cites nor
acknowledges it`.

### 7.4 From when the convention binds

The edge-token convention binds every ruling recorded from the ledger's
landing on `main` (slice A's merge). Rulings before that date carry no token
and are cited at seeding as `ruling` grounds; at `b0d35e2` the mention check
is met for the slice A graphs by citing R-P20 (`docs/PROMISE-DAG.md`) and
R-V8 (`CONFIGURATION-PG-ORDERING`), the only rulings that name them. The
gate does not read dates: it checks every token it finds and every mention.

## 8. The projection

`generated/graphs/<GRAPH-ID>.md`, one per graph, rendered by
`Gates.Ledger.Graph.render g ledgerInput`, where `ledgerInput` is
`` `WhatwgTest/Ledger.lean` `` and `formatVersion` is `1`. The text, LF line
ends, ending in one LF:

```text
<!-- GENERATED by `lake exe whatwg_ledger --write` (Gates.Ledger, format 1) from `WhatwgTest/Ledger.lean`; do not edit. -->

# Current state of `<GRAPH-ID>`

Graph document: `<document>`. Receipts log: `docs/receipts/<GRAPH-ID>.md`.
Fence: <modules, each in backticks, joined by joinAnd, or none>.
Depends on: <graph ids, each in backticks, joined by joinAnd, or none>.

| Edge | Status | Ground |
| --- | --- | --- |
| <edge> | `<status>` | <Cell.render> |
```

with one row per edge in `Edge.all` order. `Cell.render` joins with one
space, omitting empty parts: the note; `Open: ` and the items joined by `; `
and a full stop; then the grounds, prefixed `Closed on: ` for a closed cell,
`Discharged: ` for an open one and `Recorded by: ` for a not-applicable one,
joined by `; ` with a full stop; then `Debts recorded: ` and the debts joined
by `joinAnd` with a full stop. `joinAnd` writes `a`, `a and b`, `a, b and c`.
The ground and item spellings are those the battery pins (section 7 of the
battery). The text holds no timestamp, commit or absolute path.

`lake exe whatwg_ledger` compares each projection with a fresh rendering,
byte for byte: `<path> does not exist`, `<path> differs from a fresh
rendering`; and every file under `generated/graphs/` that is no graph's
projection is reported as `<path> is not the projection of a ledger graph`.
`.gitattributes` turns off end-of-line conversion, so a checkout reproduces
the bytes; a CRLF copy differs.

`lake exe whatwg_ledger --write` runs every check but the projection
comparison and, only when there is no finding, writes every projection. It
creates `generated/graphs/` when absent and deletes nothing. That is the
regeneration command; a drift failure is repaired in the ledger data or the
renderer, never in the projection.

## 9. The outcome of a run

`outcome w l write : Outcome` decides a run:

- no finding: exit code 0, one line, and with `write` the list of
  `(projection path, rendering)` to write, in ledger order:

  ```text
  PASS whatwg_ledger: <g> graph(s), <10g> edges, <k> leaf record(s), <u> unrouted prefix(es); every reference resolves against the built environment and the authored files, and every projection is byte-identical to a fresh rendering
  ```

  followed by ` (written)` in write mode;
- otherwise: exit code 1, nothing written, the line
  `FAIL whatwg_ledger: <n> finding(s)` and every finding on its own line
  indented by two spaces, untruncated: the reference findings, then, when
  not writing, the projection findings.

## 10. The executable and freshness (R-W6, change 1)

`cli : Ledger → List String → IO UInt32`. With no argument it compares, with
`--write` it writes; any other argument list prints `usage: lake exe
whatwg_ledger [--write]` on standard error and returns 2 having read
nothing. Otherwise it:

1. finds the repository root with `Gates.Common.projectRoot`;
2. imports the built environment of the library roots `Whatwg`,
   `WhatwgTest` and `WhatwgGates` through the shared loader
   `WhatwgGates/Trust/Load.lean` (ruling R-W7), frozen by the trust breaker.
   This packet depends on the loader's behaviour only: the `.olean` files
   are imported with environment extensions not loaded, so no initializer,
   parser or elaborator of an audited module runs in the process; and a
   module whose `.olean` is missing or stale against its source is refused.
   On a refusal `cli` prints a `FAIL whatwg_ledger:` line carrying the
   loader's diagnostic, writes nothing and returns 1;
3. reads the run-time file set (section 11) and lists `generated/graphs/`;
4. builds the `World`: `constantKind?` from the environment's constant map
   (a theorem is `thm`, every other constant `other`), `moduleBuilt` from
   its module table, `file?` from the files read;
5. computes `outcome`, writes `writes`, prints `output` on standard output
   and returns `exitCode`.

The lakefile entry is `[[lean_exe]] name = "whatwg_ledger"`, `root =
"whatwgbin.Ledger"`, with no `needs`, and the executable joins
`defaultTargets`. The gate table says to run it after `lake build`; a run
against an environment `lake build` has not refreshed is refused by the
loader rather than answered from stale `.olean` files. The executable links
no object under `ir/Whatwg/` (design, section 2.5), and its file facts are
read at run time, so no cached build replays its verdict (debt D49 does not
reach it).

## 11. The run-time file set

`Ledger.files` is, with repeats removed keeping the first:
`COORDINATION.md`, `test/counterexamples/REGISTER.md`, `lakefile.toml`;
for each graph its document, its receipts log, its projection and the
source of each module a `receipts` or `ascriptions` ground of its cells
names, in edge order; for each leaf its document and the source of each
module its count grounds name. `cli` reads exactly these files and the
listing of `generated/graphs/`; the loader reads the `.olean` files and
their Lake traces. Nothing else under the root is read.

## 12. Ownership, data, and the builder slices

The coordinator owns `WhatwgTest/Ledger/`. A breaker that freezes a new
graph adds its entry, every applicable edge `requiredOpen` with the
packet's obligations named; a builder proposes cell changes on its landing
branch; the coordinator lands them with the ruling that carries the edge
tokens, and regenerates the projections in the same commit. Notes hold
current grounds only; history stays in the receipts log (R-W6).

`Whatwg/Html` and the twelve Infra modules outside the UTF-8, scalar and
integer records (`Whatwg.Infra.Namespaces`, `Bytes.Byte`, `Bytes.Sequence`,
`Primitive.Singleton`, `Text.Case`, `Text.Codec`, `Text.CodePoint`,
`Text.Order`, `Text.Scan`, `Text.String`, `Text.Substring`,
`Text.Whitespace`) are carried as thirteen `unrouted` entries,
`⟨`Whatwg.Html, "D57"⟩` and `⟨`Whatwg.Infra.<module>, "D57"⟩`, citing debt
D57. Their graph-or-leaf decision is a later packet.

| Slice | File fence | Depends on |
| --- | --- | --- |
| A, model and gate | `WhatwgGates/Ledger/{Model,Render,Check}.lean`; `whatwgbin/Ledger.lean`; `WhatwgTest/Ledger.lean`; `WhatwgTest/Ledger/{DataQueue,PromiseFirst,ConfigurationOrdering}.lean`; one import line in each of `WhatwgGates.lean` and `WhatwgTest.lean` (the latter also importing this battery); the `[[lean_exe]]` and `defaultTargets` entry in `lakefile.toml`; `generated/graphs/` for the three graphs; one sentence in the "Current state" section of `docs/DATA-DAG.md`, `docs/PROMISE-DAG.md` and `docs/CONFIGURATION-DAG.md` naming its projection's path; the removal of this packet's `known-red.txt` entry | this packet; the shared loader |
| B, seeding | `WhatwgTest/Ledger/*.lean` for the other eight graphs and `PROMISE-PG-AGENT`; their `generated/graphs/*.md`; the "Current state" sections of the graph documents, each becoming one paragraph and a link to its projection; one appended section in each `docs/receipts/<GRAPH-ID>.md` holding the moved table verbatim | A |
| D, routing | the thirteen `unrouted` entries above; `fence` for every graph; a module routing pass in `Check.lean`; `generated/graphs/INDEX.md` with the leaf records | B, and an addendum to this packet |

Slice A's data module entries are the design's appendix A encodings, with
each closed cell attested and with the notes reduced to current grounds.
The battery pins that the three graphs and the leaf are present, not their
cells: the cells move by ruling, not by battery amendment.

Slice D is not frozen here. Its routing pass was not prototyped (design,
section 8), so under R-W9 its statements are frozen by an addendum to this
packet after a breaker has evaluated them; that addendum also decides how
`generated/graphs/INDEX.md` is exempted from the stray-file finding of
section 8. Slice A's pass already checks `unrouted` entries (section 5.4).

The coordinator's routers and CI follow slice B, outside any builder fence.

## 13. Claim scope

The gate does not read, and a green gate says nothing about:

- note text, the `named` items' wording, or whether a ground is the right
  evidence for its edge: that is review;
- review judgments, such as "independent review matched the two spans";
- a ruling's wording beyond its edge tokens and its mentions of a graph
  identifier or document path; a ruling that changes an edge by a short name
  ("the PROMISE graph") and writes no token is not caught;
- a status change made in the ledger with no ruling, beyond the attestation
  rule of section 4: an open edge closed on a stale receipts heading, or a
  closed edge reopened with no ruling, passes the gate;
- a ruling that spans more than one line, or a token outside a ruling line;
- what a counted command proves: a count equal to the stated one can hide a
  renamed or replaced theorem until the freeze registry check (R-W6, change
  3; `LEDGER-CE-002`);
- an indented command, or a command sharing its line with a preceding
  comment, in a counted module;
- whether a `gate` ground's gate passes: the gate checks that its executable
  is declared, by a substring of `lakefile.toml`, not that it was run;
- whether a theorem lies within its module's ceiling: the axiom gate does
  that, over every declaration (design, decision 9);
- the content of a leaf record beyond its document naming it, its
  declarations existing and its receipts resolving;
- module routing, before slice D.

## 14. Counterexample rows

`LEDGER-CE-001` to `LEDGER-CE-005` are appended to
`test/counterexamples/REGISTER.md` under "Graph-ledger witnesses":

| Id | Attack | Rejected by |
| --- | --- | --- |
| `LEDGER-CE-001` | a ruling moves an edge and no graph records it | the token check and the mention check, battery section 6.1 and 6.2 |
| `LEDGER-CE-002` | an equal receipt count hides a renamed theorem | `theorems` grounds resolve by name, battery section 6.3; open for count-only grounds until the registry check |
| `LEDGER-CE-003` | a live table cites a removed executable | the typed `Gate` and the declared-executable check, battery section 6.3 |
| `LEDGER-CE-004` | a cached build replays the module-closure verdict | the executable reads files at run time and its environment through the loader, which refuses a stale `.olean` |
| `LEDGER-CE-005` | a closed edge cites another graph's open edge | plant P7, decided in the kernel |

## 15. Fence and verification

Frozen breaker files:

- `test/contracts/graph-ledger.contract.md`
- `WhatwgTest/Audit/LedgerContract.lean`
- the `LEDGER-CE` block of `test/counterexamples/REGISTER.md`
- the W7 block of `test/fixtures/trust-gate/known-red.txt`

Red-phase registration: `known-red.txt` entry
`WhatwgTest.Audit.LedgerContract`, removed by the slice A builder the moment
the battery is green. Per R-W9, the battery is not imported by
`WhatwgTest.lean` until then, and this packet reaches `main` with slice A.

Narrow command:

```text
lake env lean WhatwgTest/Audit/LedgerContract.lean
```

and, once slice A has added the root import, `lake build
WhatwgTest.Audit.LedgerContract`.

The preimplementation red cause is the absence of the four modules the
battery imports. The freeze receipt below records the command, the result
and the validation of each frozen item against the reinstated prototype.

## 16. Deviations from the design

| Design | Here | Reason |
| --- | --- | --- |
| `World` holds `env : Environment`, the coordination, register and lakefile texts; checks run in `IO` | `World` holds `constantKind?`, `moduleBuilt`, `file?` and `projectionFiles`; every check is pure | the brief and the design's own section 3: the battery plants worlds |
| `loadEnvironment`, `readLines`, `sourceOf`, `moduleExists`, `run` | the shared loader; `World.linesOf`; `sourcePath`; `World.moduleBuilt`; `outcome` | R-W6 change 1; pure checks |
| `receiptCount`, `ascriptionCount : List String → Nat`, comment-blind | `String → Nat` over code text, both spellings | R-W6 change 2 |
| `lakefile.toml` entry with `needs = ["WhatwgTest"]` | no `needs`; the loader refuses stale `.olean` files | R-W6 change 1 |
| no attestation rule | `Ground.attests` and the fourth closed-cell problem | R-W6 |
| a not-applicable cell holds no ground | it may hold `ruling` grounds | the token check of a ruling that sets an edge `not-applicable` |
| `a leaf shares an identifier` also fires on duplicate graph identifiers | leaf identifiers only, against each other and the graphs | one finding per defect |
| a leaf whose document is absent is also reported as not naming the leaf | only the absence is reported | one finding per defect |
| no stray-projection check | `<path> is not the projection of a ledger graph` | a removed graph's projection must not stay authoritative |
| no document-link check in the prototype; section 3 asks for one | `does not link generated/graphs/<G>.md`; slice A adds the sentence to its three documents | the design's section 3 |
| PASS line counts graphs and edges | also leaf records and unrouted prefixes | the line states what was checked |
| `Cell.render` prefixes non-closed grounds `Discharged: ` | not-applicable cells use `Recorded by: ` | the new ruling grounds of such cells |
