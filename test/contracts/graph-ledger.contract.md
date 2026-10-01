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
| `WhatwgGates.Ledger.Check` | the model, the renderer, `WhatwgGates.Common`, `Lean`, and the shared loader `WhatwgGates.Trust.Load` | the reference pass as pure functions over `World`, and `cli` |
| `WhatwgTest.Ledger.<Graph>` | the model only | one graph's entry |
| `WhatwgTest.Ledger` | the graph modules | `ledger`, the leaf records, `ledger_wellFormed` |
| `whatwgbin.Ledger` | `Check` and `WhatwgTest.Ledger` | `main`, calling `Gates.Ledger.cli WhatwgTest.Ledger.ledger` |

No module of the ledger imports a production module (`Whatwg.*`), declares
syntax, a macro, an elaborator or an initializer, or joins any list of the
trust gate: no `metaprogrammingModules` entry, no `sourceTokenExemptions`
entry, no strict exception. The ledger modules sit under no strict prefix,
so R-11's ceiling binds them. Every authored declaration of the three
`WhatwgGates.Ledger` modules that this contract does not list is `private`;
what Lean generates (recursors, `noConfusion`, derived instances, equation
lemmas) is not counted. The data names frozen for slice A are
`WhatwgTest.Ledger.dataQueue`, `promiseFirst`, `configurationOrdering`,
`infraInteger`, `ledger` and
`ledger_wellFormed : WhatwgTest.Ledger.ledger.wellFormed = true`; the battery
pins that the three graphs and the leaf are in `ledger`, and slice B names its
own graph values.

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
`identity` has already been specified" (battery section 2, pinned with
`#guard_msgs (substring := true)` because `#check_failure` also prints a hint
and the elaborator's recovery term).

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
with a `#guard` pinning its finding, and a fourth control,
`fixture_wellFormed`, for the fixture ledger of its reference rows. Each
theorem is `(…).wellFormed = false` or `= true` by `decide +kernel`; on the
prototype each prints `[propext]` under `#print axioms`, as
`ledger_wellFormed` does.

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
with the Lean string ``"| `" ++ r ++ "` |"``, as the `P3-R1` row of
`docs/DATA-DAG.md` does. Rule T: a register row is the first line of the
register that begins with ``"| `" ++ id ++ "` | `"``; its status is the text
after that prefix up to the next backtick. Both are line-prefix rules over
the file's lines, split by `Gates.Common.lines`, which drops a final CR, so
the CRLF register reads like an LF one.

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

Measured at `b0d35e2` with the validation prototype (section 15): every
count the design recomputed is unchanged under this rule, namely 99, 125,
57, 119, 46, 94, 93, 118, 108, 1, 2 and 95 receipts in the twelve
`*AxiomReport.lean` modules and 80, 119 and 95 ascriptions in
`WhatwgTest/Infra/Utf8Contract.lean`, `Utf8Laws.lean` and
`WhatwgTest/Url/PercentEncodingLaws.lean`. Over every `.lean` file under
`Whatwg/`, `WhatwgTest/` and `WhatwgGates/` (221 files) the rule finds the
same 1,031 receipt lines as a comment-blind line count, and 2,446
ascriptions where a comment-blind count finds 2,451: the five others are
superseded ascriptions quoted in module documentation, three in
`WhatwgTest/Ecma262/PromiseContract.lean` (75, not 78) and two in
`WhatwgTest/Ecma262/PromiseLaws.lean` (44, not 46). A ground over either
module states the lower number.

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
R-V8 (`CONFIGURATION-PG-ORDERING`), the only rulings that name them. For
slice B the rulings that name a graph at `b0d35e2` are R-V6, R-V8 and R-U5
(`INFRA-PG-UTF8`), R-U1 and R-U5 (`URL-PG-PERCENT`) and R-W3 and R-W6
(`PROMISE-PG-AGENT`); no ruling names the other six by identifier or
document path. No ruling line at `b0d35e2` holds an edge token. The gate
does not read dates: it checks every token it finds and every mention.

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
``⟨`Whatwg.Html, "D57"⟩`` and ``⟨`Whatwg.Infra.<module>, "D57"⟩``, citing
debt D57, which `COORDINATION.md` records. Each of the thirteen prefixes is
a module of the environment the gate loads (measured, section 15.2), so the
entries pass the checks of section 5.4. Their graph-or-leaf decision is a
later packet.

| Slice | File fence | Depends on |
| --- | --- | --- |
| A, model and gate | `WhatwgGates/Ledger/{Model,Render,Check}.lean`; `whatwgbin/Ledger.lean`; `WhatwgTest/Ledger.lean`; `WhatwgTest/Ledger/{DataQueue,PromiseFirst,ConfigurationOrdering}.lean`; three import lines in `WhatwgGates.lean` (the three modules) and two in `WhatwgTest.lean` (`WhatwgTest.Ledger` and this battery); the `[[lean_exe]]` and `defaultTargets` entry in `lakefile.toml`; `generated/graphs/` for the three graphs; one sentence in the "Current state" section of `docs/DATA-DAG.md`, `docs/PROMISE-DAG.md` and `docs/CONFIGURATION-DAG.md` naming its projection's path; the removal of this packet's `known-red.txt` entry | this packet; the shared loader |
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
- an indented command, a command sharing its line with a preceding
  comment, or another spelling of a counted command (`#check(@`, two
  spaces, `#whatwg_freeze(@`), in a counted module;
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

### 15.1 Freeze receipt

Observed in the breaker's worktree on Lean 4.33.1, Windows 11, with no
ledger module present. `lake env lean WhatwgTest/Audit/LedgerContract.lean`
stops at the first import:

```text
error: object file '…\.lake\build\lib\lean\WhatwgGates\Ledger\Model.olean' of module WhatwgGates.Ledger.Model does not exist
```

and `lake build WhatwgTest.Audit.LedgerContract` fails with `no such file or
directory` for the sources of `WhatwgGates.Ledger.Model`, `.Render`,
`.Check` and `WhatwgTest.Ledger`, and nothing else. A default `lake build` at
the breaker head also stops at the root's module-closure gate, `…\WhatwgTest\
Audit\LedgerContract.lean is not reachable from the WhatwgTest audit root`,
because R-W9 keeps the battery out of `WhatwgTest.lean` until slice A; that
is the state R-W9 describes ("the root gate cannot run there").

### 15.2 Validation against the prototype (R-W9)

The design's appendix A was reinstated as uncommitted files in the
breaker's worktree, adapted to R-W6's three changes, the attestation rule and
sections 4 to 11 above (the `World` of section 5.1, the code-text counter of
section 6, `outcome`, the stray-projection and link checks, and `cli` with
`Lean.importModules (loadExts := false)` standing in for the shared loader),
with the appendix's three graph entries and leaf unchanged. Then:

| Item | Command | Result |
| --- | --- | --- |
| the model, the three graphs, the leaf, `ledger_wellFormed` | `lake build WhatwgGates.Ledger.Check WhatwgTest.Ledger` | 9 jobs, green; the attestation rule and the not-applicable rule hold for the appendix data unchanged |
| the whole battery | `lake env lean -DmaxErrors=5000 WhatwgTest/Audit/LedgerContract.lean` | exit 0, no error and no warning: 174 ascriptions, 32 instance checks, 2 `#check_failure` probes, 21 kernel theorems, 264 `#guard` rows |
| that the rows discriminate | seven mutants of the prototype (character literals not lexed, no attestation, `axioms` matched anywhere in a freeze command, no latest-wins, line comments not blanked, headings matched at any level, not-applicable cells refusing ruling grounds) | every mutant fails the battery, with 1 to 52 errors |
| axioms of the kernel theorems | `#print axioms` on `ledger_wellFormed`, `plant_closedWithItem`, `plant_closedUnattested`, `control_dependentGraphs`, `fixture_wellFormed` | `[propext]` for each |
| the trust gate with the battery and the prototype imported (temporary root import lines) | `lake build` | 397 jobs, green; "checked 231 source files and 17748 declarations; Classical.choice is reached by 84 of 12766 declarations in Whatwg, 123 of 2468 in WhatwgTest and 210 of 2514 in WhatwgGates"; five strict prefixes, no exception, no exemption; the one new `Classical.choice` reach in `WhatwgTest` is the battery's private `fixWorld` |
| kernel replay | `lake env leanchecker` naming the eight modules | exit 0, 16.9 s |
| the reference pass on the real tree | `lake -q exe whatwg_ledger` (temporary lakefile entry) | exit 1 with exactly six findings: each of the three documents does not link its projection, and the three projections do not exist; every theorem, declaration, module, count, ruling, heading, register row, debt, gate and the leaf resolve |
| the run with the slice A sentences | `outcome … true` over the real files, each document given the sentence in memory | the PASS line with "3 graph(s), 30 edges, 1 leaf record(s), 0 unrouted prefix(es)" and three projections written; `generated/graphs/DATA-PG-QUEUE.md` is byte-identical to the design's appendix B (3,686 characters) |
| the run-time file set of the real ledger | `Ledger.files` | 18 paths: the three fixed files, three per graph, the four report sources, the leaf's document and `WhatwgTest/Infra/IntegerConstructiveContract.lean` |
| tokens and mentions on the real `COORDINATION.md` | `edgeTokens`, `rulingMentions` | no token; mentions `(R-P20, PROMISE-PG-FIRST)` and `(R-V8, CONFIGURATION-PG-ORDERING)` |
| the thirteen `unrouted` prefixes | `getModuleIdx?` over the imported roots | each is a built module |
| the executable's link | its response file | 9 objects, none under `ir/Whatwg/` |
| usage | `lake -q exe whatwg_ledger --bogus` | the usage line, exit 2 |

Not validated, because the code does not exist yet: the shared loader's
refusal of a missing or stale `.olean` and `cli`'s FAIL line on that refusal
(section 10, item 2); slice D (section 12). After validation every prototype
file, the temporary root and lakefile lines and the prototype's build
outputs were removed, and the battery fails as in 15.1.

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
| the environment of `[WhatwgTest]` | the roots `Whatwg`, `WhatwgTest` and `WhatwgGates`, the set `leanchecker` replays | a ground may name a production module no battery imports |
| `unrouted` entries checked by nobody until slice D | `unroutedFindings` from slice A | a cheap check of data slice D adds |
| public declarations of section 3 | also `Ground.attests`, `ConstantKind`, `World.linesOf`, `codeLines`, `unroutedFindings`, `Ledger.files`, `referenceFindings`, `projectionFindings`, `Outcome` and `outcome` | the changes above; each is ascribed by the battery |

## Addendum D. Module routing and the index (slice D)

Status: FROZEN / RED, slice D breaker seat of review lane W, 2026-10-01, on
branch `review/w7-ledger-d-breaker` from
`fc0b9fbf69cf209eba43de161e0d6715d7fb187b`, "the base commit" below. Section
12 left slice D unfrozen because its routing pass was not prototyped; rulings
R-W6, R-W11 and R-W18(5) give it to this addendum. The addendum is appended
and no line above it changes. Where it and a section above disagree, the
addendum is what slice D builds, and D.13 names each such point.

Battery: `WhatwgTest/Audit/LedgerRoutingContract.lean`, new. As for the base
packet, the battery is the authority on names and propositions and the Lean
here is a reading aid; the builder may repair elaboration but may not weaken,
delete or replace a frozen ascription, plant, finding text, count or byte of
rendered output. The slice A battery `WhatwgTest/Audit/LedgerContract.lean`
stays green and unedited.

Evidence class (R-W9). Nothing in this addendum is a theorem. Every rule of
D.2 to D.8 was evaluated on concrete instances, the battery's planted module
tables, ledgers and worlds, against a scratch prototype of the pass and the
renderer; the measurement of D.5 is a run of that prototype over the built
environment at the base commit. D.12 records both, and what was not run.

### D.1 Claim boundary

The routing pass is tooling, like the rest of the ledger (section 1): it owns
no specification anchor, grants no coverage state and closes no edge. What a
green routing pass means, and nothing more: every module of the environment
the gate loads that rule M (D.2) selects has exactly one owner among the
ledger's graph fences, leaf records and unrouted prefixes (D.3); and every
unrouted prefix that names a module of that environment claims at least one
module rule M selects (D.4). Whether an owner's obligations cover the
declarations of the modules it claims is review, not this pass (D.11).

### D.2 The module table and rule M

Module `WhatwgGates.Ledger.Check`, namespace `Gates.Ledger`:

```lean
structure ModuleTable where
  modules : List (Lean.Name × List Lean.Name)
  deriving DecidableEq, Repr

def productionRoot : Lean.Name := `Whatwg
def ModuleTable.mustRoute : ModuleTable → List Lean.Name
def ModuleTable.declaringModule? : ModuleTable → Lean.Name → Option Lean.Name
```

The module table is a second set of facts the pass reads, beside `World`
(section 5.1), and like it is plain data that a battery plants. `World` is not
extended: `World.mk` is ascribed with four fields by the slice A battery, and
`moduleBuilt` is a predicate, which cannot list modules. `cli` fills the
table with every module of the loaded environment, in the order of
`Environment.header.moduleNames`, each paired with
`Gates.Trust.moduleDeclarations env i` as a list: the constants the
environment attributes to that module. That is the shared loader's read, so
the trust gate, the declaration snapshot and the ledger agree on which module
declares which constant. At the base commit the table holds 2,627 modules and
228,259 constants.

Rule M. A module must be routed when both hold:

1. `productionRoot` is a prefix of its name by component
   (`Lean.Name.isPrefixOf`): the module `Whatwg` and every module `Whatwg.*`,
   never `WhatwgTest.*`, `WhatwgGates.*`, `whatwgbin.*`, another package's
   module, or a name whose first component merely begins with `Whatwg`;
2. it declares at least one constant whose name is not internal
   (`Lean.Name.isInternal`: no string component begins with `_`).

A private name begins with the component `_private`, so a module whose
constants are all private, or all internal (`_auxLemma`, `_sunfold` and the
like), is not routed. An umbrella module that only imports, and a scaffold
module with no declaration, declare no constant and are not routed.
`ModuleTable.mustRoute t` lists the modules that must be routed in table
order, each once, at its first position. `ModuleTable.declaringModule? t n` is
the first module of the table whose constants include `n`, or `none`.

The eight production libraries of `lakefile.toml` own exactly the modules
under `Whatwg`: the umbrella library owns the module `Whatwg` by an exact
glob, and the seven others own `Whatwg.Infra`, `Whatwg.Ecma262`,
`Whatwg.WebIdl`, `Whatwg.Url`, `Whatwg.Html`, `Whatwg.Streams` and
`Whatwg.Signatures` with every module under them. The component rule and the
library boundary therefore select the same modules.

Measured at the base commit (D.12): the loaded environment holds 134
production modules. 77 declare at least one constant, and each of the 77 also
declares one that is not private and one that is not internal, so the three
readings ("any constant", "a constant that is not private", rule M) select
the same 77 modules today; the other 57 declare nothing. Rule M is the
reading that does not count what Lean generates for a private or auxiliary
declaration.

### D.3 Claims and owners

`Ledger.claimsOn t l m : List (String × String)` lists every claim on module
`m` as a pair (claimant, owner): the graphs first, then the leaf records, then
the unrouted entries, each in ledger order.

| Claimant | Claims `m` when | Claimant text | Owner |
| --- | --- | --- | --- |
| graph `G` | `m` is an entry of `G.fence`, exactly | `graph G` | `graph G` |
| leaf record `L` | `ModuleTable.declaringModule? t d = some m` for some declaration `d` of `L` | `leaf L` | `graph G` when `L.parent = some (G, e)`; `leaf L` when `L.parent = none` |
| unrouted entry with prefix `P` | `P.isPrefixOf m`: `P` is `m`, or a prefix of `m` by component | `unrouted P` | `unrouted P` |

A fence entry names one module, exactly. That is what the landed field
already means: section 3 calls `fence` "the production modules whose
declarations the graph owns", section 5.4 checks each entry as a built
module, section 8 renders the entries one by one, and nothing in the base
packet or in `WhatwgGates/Ledger/Check.lean` reads an entry as a prefix. None
of the 47 entries of the twelve fences at the base commit is a proper prefix
of another module of the environment (measured, D.12), so the exact and the
prefix reading give the same claims today. They differ for a module added later under a fenced one: the
exact reading reports it as claimed by nobody (D.4) instead of absorbing it,
and that is the event the pass exists to catch.

`Unrouted.modulePrefix` is a prefix, by its name and its docstring ("a
production module prefix"), matched by component: `Whatwg.Ecma262.Agent`
claims `Whatwg.Ecma262.Agent` and `Whatwg.Ecma262.Agent.X`, and never
`Whatwg.Ecma262.AgentInvariant`; `Whatwg.Html` claims the module `Whatwg.Html`
and every module under it. Section 5.4 still requires the prefix itself to be
a built module.

A leaf whose parent is a graph counts for that graph: under
`docs/AGENT-ROUTING.md`, "Assurance threshold", such a leaf "links its
receipts to one named edge of that graph". So a module that a graph fences
and that a leaf of the same graph declares into has one owner, and a leaf of
graph `G` routes a module to `G` even when `G` does not fence it. A standalone
leaf is its own owner.

Claims are computed for any module; rule M decides which modules the findings
look at. A fence entry that names a tooling module (`URL-PG-CENSUS` fences
three `WhatwgGates` modules) or a module with no constant claims nothing the
pass checks and raises nothing.

### D.4 The routing findings

`routingFindings t l : List String` reports, in this order:

1. for each module `m` of `t.mustRoute`, in that order, at most one of
   - `module <m> is claimed by no graph fence, leaf record or unrouted
     prefix`, when `l.claimsOn t m` is empty;
   - `module <m> is claimed by <claimants>`, when its claims have two owners
     or more, each owner counted once; `<claimants>` is the claimant texts,
     each once, in claim order, joined by `joinAnd`:
     `module Whatwg.X is claimed by graph A-PG-X and unrouted Whatwg.X`, and
     with three, `… by graph G, leaf L and unrouted P`;
2. for each unrouted entry, in ledger order, whose prefix is a module of the
   table: `unrouted <P>: claims no module that must be routed`, when no module
   of `t.mustRoute` has `P` as a prefix by component.

A claim repeated by one owner is one owner and no finding: a fence that lists
a module twice, the same unrouted entry given twice, a leaf of the graph that
fences the module. An unrouted prefix that is no module of the table raises no
routing finding, because `unrouted <P>: not a built module` of section 5.4
reports it, so one defect gives one finding. An unrouted prefix that is a
built module outside the production root, or a module none of whose
constants rule M counts, claims nothing and is reported.

Placement. `World` and `referenceFindings` keep their slice A signatures,
which the slice A battery ascribes, and the module table is not in `World`, so
the routing findings cannot enter `referenceFindings`. They follow it: after
its last `unroutedFindings` line and before every projection finding, as D.7
composes them.

### D.5 The tree at the base commit, and the data slice D adds

The prototype's pass over the unchanged ledger at the base commit (twelve
graphs, one leaf, no unrouted entry) reports exactly 32 modules claimed by
nobody, and no other routing finding:

| Modules claimed by nobody at the base commit | Count | Claim slice D makes |
| --- | ---: | --- |
| under `Whatwg.Html`: `Content.Admission`, `Content.Lattice`, `Content.Transparent`, `Node.Combinators`, `Node.Erasure`, `Node.Raw`, `Node.Typed`, `Print.Escape`, `Print.Render`, `Schema.Attributes`, `Schema.ContentModel`, `Schema.Families`, `Schema.Tags` | 13 | the one entry ``⟨`Whatwg.Html, "D57"⟩`` |
| under `Whatwg.Infra`: `Namespaces`, `Bytes.Byte`, `Bytes.Sequence`, `Primitive.Singleton`, `Text.Case`, `Text.Codec`, `Text.CodePoint`, `Text.Order`, `Text.Scan`, `Text.String`, `Text.Substring`, `Text.Whitespace` | 12 | one entry ``⟨`Whatwg.Infra.<module>, "D57"⟩`` each |
| under `Whatwg.Streams.Semantics`: `Step`, `Runs`, `Source`, `Frontier`, `Mask`, `Invariants` | 6 | entries of the fence of `CONFIGURATION-PG-ORDERING` |
| `Whatwg.Streams.Kernel` | 1 | none until the coordinator rules (D.14, point 1) |

The other 45 modules rule M selects have one owner each at the base commit:
44 through the entries of the twelve fences, and
`Whatwg.Infra.Primitive.Integer` through the leaf `INFRA-LF-INTEGER`, all of
whose nine declarations it declares.

D57 data. The thirteen unrouted entries are those of section 12, in its
order, each citing `D57`: ``⟨`Whatwg.Html, "D57"⟩``, then
`Whatwg.Infra.Namespaces`, `Bytes.Byte`, `Bytes.Sequence`,
`Primitive.Singleton`, `Text.Case`, `Text.Codec`, `Text.CodePoint`,
`Text.Order`, `Text.Scan`, `Text.String`, `Text.Substring` and
`Text.Whitespace`, each under `Whatwg.Infra`. They are the ledger's only
entries citing `D57`, which the battery pins. Each prefix is a built module
(`Whatwg.Html` is the HTML umbrella, with no constant; each Infra module
declares constants and has no module under it), so section 5.4 passes them,
and each claims at least one module rule M selects, so item 2 of D.4 passes
them. One prefix serves the HTML tree; the Infra modules need one each,
because a `Whatwg.Infra` prefix would also claim `Text.Utf8`, `Text.Scalar`
and `Primitive.Integer`, which `INFRA-PG-UTF8`, `INFRA-PG-SCALAR` and
`INFRA-LF-INTEGER` own.

Fence additions. Each of the six `Whatwg.Streams.Semantics` modules names
`CONFIGURATION-PG-ORDERING` in its module docstring: `Source`, `Step`,
`Frontier`, `Mask` and `Runs` were opened by slice Q4 for that graph under
`test/contracts/configuration-ordering.contract.md`, and `Invariants`, opened
by slice W8a.3, reads "Owner: `CONFIGURATION-PG-ORDERING`, construction edge".
The graph document's declaration table places `Step.lean`, `Runs.lean`,
`Frontier.lean` and the source judgments in the same graph. The builder adds
the six entries to `WhatwgTest.Ledger.configurationOrdering.fence`, after
`Whatwg.Streams.Semantics.Configuration`; the battery pins membership, not
order (the prototype's order is `Step`, `Runs`, `Source`, `Frontier`, `Mask`,
`Invariants`).

`Whatwg.Streams.Kernel`. Ruling R-W4 gives it "local receipts on the laws
edge of the five calculus graphs" (`READABLE-PG-DEFAULT`,
`WRITABLE-PG-DEFAULT`, `TRANSFORM-PG-BACKPRESSURE`,
`PIPING-PG-FORWARD-SHUTDOWN` and `CONFIGURATION-PG-ORDERING`). The pass admits
one owner per module and a leaf record has one parent edge, so none of the
three kinds of claim states that route as written. The builder does not
choose: the gate reports the module until the coordinator rules, and the
ruling names the claim and the file it goes in.

`Whatwg.Ecma262.AgentInvariant` is not in the base commit. Its docstring on
`review/w9-q5b-builder` names graph `PROMISE-PG-AGENT` (addendum Q5b of
`test/contracts/promise-agent-q5.contract.md`, slice B5). Whichever of slice D
and that slice reaches `main` second adds `` `Whatwg.Ecma262.AgentInvariant ``
to `WhatwgTest.Ledger.promiseAgent.fence` in its landing: before the module is
built the entry is a finding of section 5.4, and once it is built the module
without the entry is a finding of D.4.

These counts describe the tree at the base commit, and the battery does not
pin them: a count of today's tree would fail when the next module lands. It
pins the thirteen D57 entries and the six fence entries, and decides every
rule on planted tables.

### D.6 The index projection

`generated/graphs/INDEX.md` is rendered by
`Gates.Ledger.Ledger.renderIndex l ledgerInput`, a function of the ledger
alone: neither the environment nor a file is an input, so the index changes
only with `WhatwgTest/Ledger.lean` and its graph modules, which are its
canonical inputs as they are the graph projections'. The text has LF line
ends, ends in one LF, and holds no timestamp, commit or absolute path:

```text
<!-- GENERATED by `lake exe whatwg_ledger --write` (Gates.Ledger, format 1) from `WhatwgTest/Ledger.lean`; do not edit. -->

# Graph ledger index

Totals: <g> graph(s), <10g> edges (<o> required-open, <c> required-closed, <n> not-applicable), <k> leaf record(s), <u> unrouted prefix(es).

## Graphs

| Graph | Document | Open | Closed | Not applicable |
| --- | --- | ---: | ---: | ---: |
| [`<GRAPH-ID>`](<GRAPH-ID>.md) | `<document>` | <open> | <closed> | <not applicable> |

## Leaf records

| Leaf | Document | Parent | Declarations |
| --- | --- | --- | ---: |
| `<LEAF-ID>` | `<document>` | <parent> | <number of declarations> |

## Unrouted prefixes

| Prefix | Recorded by |
| --- | --- |
| `<prefix>` | <recordedBy> |
```

- One row per graph, leaf record and unrouted entry, in ledger order. A
  section with no row holds the single line `None.` in place of its table.
- The first line is the graph projections' header, with the same
  `formatVersion` (1), command and input.
- `Graph.countStatus g s` is the number of the ten edges of `g` whose cell has
  status `s`. The totals sum it over the graphs; the edge total is ten per
  graph.
- The graph cell links the graph's projection with a relative link, which
  resolves inside `generated/graphs/`.
- `<parent>` is `standalone`, or the parent graph's identifier in backticks, a
  space and the edge label.
- `<recordedBy>` is the entry's debt or ruling identifier as written.

On the real ledger with the slice D data and the scratch-only claim of D.12,
the prototype wrote the totals line "Totals: 12 graph(s), 120 edges (68
required-open, 39 required-closed, 13 not-applicable), 1 leaf record(s), 14
unrouted prefix(es)."; without that claim the last count is 13. The three
edge totals are those of R-W18.

Drift and writing. `indexFindings w l` reports `generated/graphs/INDEX.md does
not exist` when `w.file? indexPath` is `none`, and `generated/graphs/INDEX.md
differs from a fresh rendering` when its text is not byte-identical to
`l.renderIndex ledgerInput`; a CRLF copy differs, and `.gitattributes` turns
conversion off as section 8 says. `lake exe whatwg_ledger --write` compares
neither the projections nor the index and, when there is no reference finding
and no routing finding, writes every projection in ledger order and then the
index. It is the regeneration command; a drift failure is repaired in the
ledger data or the renderer, never in the file.

Stray-file exemption (R-W11). `projectionFindings` does not report the one
path `generated/graphs/INDEX.md` (`indexPath`) as `is not the projection of a
ledger graph`. Every other file under `generated/graphs/` that is no graph's
projection is still reported, `generated/graphs/index.md` among them, since
the path is compared exactly. This is the only change to the behaviour of a
slice A function, and no row of the slice A battery lists `INDEX.md` among
the projection files, so none of its rows moves.

A graph whose identifier is `INDEX` would have the index's path as its
projection. Nothing refuses that identifier; a compare run then fails,
because the file can equal at most one of the two renderings (D.11).

### D.7 The routed run

```lean
def routedOutcome (w : World) (t : ModuleTable) (l : Ledger) (write : Bool) : Outcome
```

The findings are `referenceFindings w l`, then `routingFindings t l`, then,
unless writing, `projectionFindings w l` and `indexFindings w l`. With no
finding: exit code 0 and one line,

```text
PASS whatwg_ledger: <g> graph(s), <10g> edges, <k> leaf record(s), <u> unrouted prefix(es), <r> production module(s) with one owner each; every reference resolves against the built environment and the authored files, and every projection and the index are byte-identical to a fresh rendering
```

where `<r>` is `t.mustRoute.length`, followed by ` (written)` in write mode,
whose writes are `(g.projection, g.render ledgerInput)` for each graph in
ledger order and then `(indexPath, l.renderIndex ledgerInput)`. Otherwise:
exit code 1, nothing written, the line `FAIL whatwg_ledger: <n> finding(s)`
and each finding on its own line indented by two spaces, untruncated.

`cli` keeps its signature, its usage line, its exit codes and its refusal of a
missing or stale `.olean` (section 10), and changes in three places: it reads
`Ledger.runFiles l` instead of `Ledger.files l`; it builds the `ModuleTable`
of D.2 from the loaded environment; and it acts on `routedOutcome` instead of
`outcome`. `outcome` keeps its slice A body and meaning, a run with neither
the routing pass nor the index; the slice A battery pins it, and `cli` no
longer calls it.

The run-time file set gains one path (section 11). `Ledger.runFiles l` is
`Ledger.files l` followed by `generated/graphs/INDEX.md`, repeats removed
keeping the first. `cli` reads exactly those files and the listing of
`generated/graphs/`; the loader reads what section 10 says.

### D.8 Public declaration record

The declarations slice D adds, namespace `Gates.Ledger`. Every other
declaration the builder adds to the three ledger modules is `private`; what
Lean generates is not counted (section 2). Each is `canonical`: no `Gates.*`
or `Whatwg.*` constant routes modules or renders an index at the base commit.
The one name shared with another declaration is the last component of
`productionRoot`: `Gates.TrustSelfTest.productionRoot` is a file path, the
self-test's `Whatwg.lean` under a probe directory, in another namespace and
with another role. The assurance route of the declarations below is this
addendum and its battery, as for the base packet (section 1).

| Declaration | Module | Signature | Role |
| --- | --- | --- | --- |
| `productionRoot` | `WhatwgGates.Ledger.Check` | `Lean.Name` | the root of rule M, `` `Whatwg `` |
| `ModuleTable` | `WhatwgGates.Ledger.Check` | `Type`, the one field `modules`, deriving `DecidableEq` and `Repr` | the module table |
| `ModuleTable.mk` | `WhatwgGates.Ledger.Check` | `List (Lean.Name × List Lean.Name) → ModuleTable` | its constructor |
| `ModuleTable.modules` | `WhatwgGates.Ledger.Check` | `ModuleTable → List (Lean.Name × List Lean.Name)` | its field |
| `ModuleTable.mustRoute` | `WhatwgGates.Ledger.Check` | `ModuleTable → List Lean.Name` | rule M |
| `ModuleTable.declaringModule?` | `WhatwgGates.Ledger.Check` | `ModuleTable → Lean.Name → Option Lean.Name` | the module that declares a constant |
| `Ledger.claimsOn` | `WhatwgGates.Ledger.Check` | `ModuleTable → Ledger → Lean.Name → List (String × String)` | D.3 |
| `routingFindings` | `WhatwgGates.Ledger.Check` | `ModuleTable → Ledger → List String` | D.4 |
| `indexFindings` | `WhatwgGates.Ledger.Check` | `World → Ledger → List String` | the index's drift |
| `Ledger.runFiles` | `WhatwgGates.Ledger.Check` | `Ledger → List String` | the run-time file set |
| `routedOutcome` | `WhatwgGates.Ledger.Check` | `World → ModuleTable → Ledger → Bool → Outcome` | the run |
| `indexPath` | `WhatwgGates.Ledger.Render` | `String` | `generated/graphs/INDEX.md` |
| `Graph.countStatus` | `WhatwgGates.Ledger.Render` | `Graph → Status → Nat` | edge counts |
| `Ledger.renderIndex` | `WhatwgGates.Ledger.Render` | `Ledger → String → String` | the index |

The battery ascribes each with `#check (@n : T)` under its full
`Gates.Ledger` name (14 ascriptions), as the slice A battery does, and checks
the `DecidableEq` and `Repr` instances of `ModuleTable`. `indexPath` and
`Graph.countStatus` sit in the renderer because the index is a projection and
`WhatwgGates/Ledger/Model.lean` is outside the builder's fence.

Changed bodies, unchanged signatures: `projectionFindings` (D.6) and `cli`
(D.7). Unchanged: `WhatwgGates/Ledger/Model.lean`, `whatwgbin/Ledger.lean`,
`lakefile.toml`. Data: `WhatwgTest.Ledger.ledger` gains its `unrouted` entries
and `WhatwgTest.Ledger.configurationOrdering` six fence entries (D.5); no data
name is added.

### D.9 Counterexample rows

`LEDGER-CE-006` to `LEDGER-CE-009` are appended to
`test/counterexamples/REGISTER.md` under "Graph-ledger witnesses", each
`SEEDED`:

| Id | Attack | Rejected by |
| --- | --- | --- |
| `LEDGER-CE-006` | a production module with public theorems that no fence, leaf or debt claims passes the gate: at the base commit `lake exe whatwg_ledger` passes while 32 modules are claimed by nobody, among them `Whatwg.Streams.Kernel` (23 public theorems) and `Whatwg.Streams.Semantics.Source` (113) | battery section 5, plant R1; section 7.3, where the slice A `outcome` passes a planted world that `routedOutcome` refuses in both modes |
| `LEDGER-CE-007` | one module claimed by two owners: two fences, a fence and a debt, a fence and a leaf of another graph, or two nested unrouted prefixes | battery section 5, plants R4 to R9 |
| `LEDGER-CE-008` | a claim read by spelling: an unrouted prefix `Whatwg.Ecma262.Agent` read as a string prefix absorbs `Whatwg.Ecma262.AgentInvariant`, and a fence entry read as a prefix absorbs every module later added under it | battery sections 4 and 5, plants R2 and R3 |
| `LEDGER-CE-009` | an unrouted entry outlives what it records: its prefix comes to name a scaffold, a module of private constants only, or a module outside the production root, and the debt still reads as carried | battery section 5, plant R10 |

### D.10 Builder fence and acceptance conditions

One builder slice, D, branched from this packet's head; under R-W9 the packet
reaches `main` with the slice.

Files the builder edits:

- `WhatwgGates/Ledger/Render.lean` and `WhatwgGates/Ledger/Check.lean`: the
  declarations of D.8, the exemption in `projectionFindings`, and the three
  changes to `cli`;
- `WhatwgTest/Ledger.lean`: the `unrouted` field of `ledger` (D.5), and its
  docstring where it describes slice D;
- `WhatwgTest/Ledger/ConfigurationOrdering.lean`: the six fence entries, and
  its docstring where it describes the fence;
- `WhatwgTest/Ledger/PromiseAgent.lean`: the fence entry
  `` `Whatwg.Ecma262.AgentInvariant ``, only when Q5b's slice B5 is on `main`
  as slice D merges (D.5);
- the claim on `Whatwg.Streams.Kernel` the coordinator rules, in the file the
  ruling names (D.14, point 1);
- `generated/graphs/INDEX.md`, new, and each projection whose `Fence:` line a
  fence edit changes, all written by `lake exe whatwg_ledger --write`;
- `WhatwgTest.lean`: the line `import WhatwgTest.Audit.LedgerRoutingContract`
  after `import WhatwgTest.Audit.LedgerContract`, once the battery is green;
- `test/fixtures/trust-gate/known-red.txt`: this packet's entry removed, with a
  dated note in its block.

Byte-identical: this packet's files; `WhatwgGates/Ledger/Model.lean`;
`whatwgbin/Ledger.lean`; `lakefile.toml`; every file under `Whatwg/`; the
graph data modules apart from the fence edits above; and every projection
under `generated/graphs/` whose graph's fence does not change. The `fence`
field is rendered, in the `Fence:` line of section 8, so a fence edit moves
exactly that line of that graph's projection, and the index shows no fence.
In the prototype's run only `generated/graphs/CONFIGURATION-PG-ORDERING.md`
changed among the twelve projections.

Acceptance:

1. `lake env lean WhatwgTest/Audit/LedgerRoutingContract.lean` exits 0 with no
   error or warning and no token of the battery changed;
   `WhatwgTest/Audit/LedgerContract.lean` stays green and unedited.
2. `lake build` is green with the root import added and this packet's
   `known-red.txt` entry removed; the gate line keeps 6 strict prefixes and 0
   exceptions, and its numbers for `Whatwg` do not move.
3. `lake exe whatwg_ledger` passes on the real tree and the builder reports
   its PASS line; a second `lake exe whatwg_ledger --write` changes no byte.
4. `lake exe whatwg_vendorseal`, `lake exe whatwg_citations` and
   `lake exe whatwg_declsnapshot` pass, and
   `lake env leanchecker Whatwg WhatwgTest WhatwgGates` exits 0. The trust
   self-test is the coordinator's run; it is red on `main` on its executable
   rows until the executable gate lands.
5. The builder plants on the real tree, one at a time, and restores: a fence
   entry removed, a production module fenced by a second graph, an unrouted
   entry whose prefix is a scaffold module, `INDEX.md` deleted, `INDEX.md`
   edited, and a stray file under `generated/graphs/`. Each is reported with
   its D.4 or D.6 text and exit code 1.
6. No list of the trust gate changes; no ledger module declares syntax, a
   macro, an elaborator or an initializer, or imports a production module;
   every declaration added beyond D.8 is `private`.

### D.11 Claim scope

The routing pass does not decide, and a green gate says nothing about:

- whether an owner's obligations cover the module it claims: a fence entry or
  a leaf claims a module wholesale, whatever its declarations are, and the
  cells say what is proved;
- whether a claim is the right one: a module fenced by the wrong graph
  passes, and so does a leaf's choice of parent edge;
- what an unrouted entry owes: it is a recorded debt, not a route; it claims
  modules so that the gap is named and counted, and the debt it cites says
  what is owed;
- private and internal constants: a module whose constants are all private or
  internal is not routed, and a routed module's private constants are not
  looked at;
- the test and tooling trees and every module outside `Whatwg`: rule M does
  not select them, and a fence entry naming one claims nothing the findings
  check (an unrouted prefix naming one is reported by item 2 of D.4);
- a module with no constant, umbrella or scaffold: not routed, and a fence
  entry naming one is not a finding;
- a module the loaded environment does not hold: rule M reads the environment
  of the roots `Whatwg`, `WhatwgTest` and `WhatwgGates`, so a source no root
  imports is outside it; the module-closure gate of `lake build` refuses such
  a source, subject to debt D61;
- repetition: a fence that lists a module twice, an unrouted entry given
  twice, or two unrouted entries with one prefix and different debts;
- anything in the index beyond the ledger: it lists no routed module, no
  fence and nothing of the environment;
- a graph whose identifier is `INDEX` (D.6);
- routing by declaration: claims are by module, and the declaration snapshot
  of R-W5 owns the per-declaration records.

The last bullet of section 13, "module routing, before slice D", is
superseded by this list.

### D.12 Freeze receipt and validation

Observed in the breaker's worktree on Lean 4.33.1, Windows 11, with no slice
D code and no slice D data present.

`lake env lean -DmaxErrors=5000 WhatwgTest/Audit/LedgerRoutingContract.lean`
exits 1 with 174 errors, no warning, no parse error and no import error:

| Class | Errors |
| --- | ---: |
| unknown identifier or constant: the 14 names of D.8, in 21 spellings | 64 |
| invalid field notation on a missing name, or on a term whose type is the missing `ModuleTable` | 37 |
| `cannot evaluate code` for a `#guard` whose term did not elaborate | 52 |
| anonymous constructor or implicit argument of the missing `ModuleTable` | 19 |
| `#guard` that evaluates to `false`: the two data rows of battery section 2, because the slice D data is not in the ledger yet | 2 |

`lake build` finishes 480 jobs and fails exactly the target
`WhatwgTest.Audit.LedgerRoutingContract`; the root `WhatwgTest` is replayed
from the cache (debt D61). A fresh `lake env lean WhatwgTest.lean` reports one
error, `Whatwg module-closure gate: …\WhatwgTest\Audit\LedgerRoutingContract.lean
is not reachable from the WhatwgTest audit root`, because R-W9 keeps the
battery out of `WhatwgTest.lean` until the builder turns it green; that is the
state R-W9 describes, not a second defect.

`lake exe whatwg_ledger` at this head refuses before reading the ledger, with
exit code 1 and the one line `FAIL whatwg_ledger: module
WhatwgTest.Audit.LedgerRoutingContract has no built .olean; run lake build
before lake exe whatwg_ledger`: the freshness check of section 10 covers every
module source of the three trees, and a red battery has no `.olean`. On the
base commit the gate passes. So on this branch, and on the builder's until the
battery is green, the ledger gate cannot run; the builder runs it once the
battery builds. `lake exe whatwg_declsnapshot`, which snapshots the
production libraries, passes at this head, and so do
`lake exe whatwg_vendorseal` and `lake exe whatwg_citations`.

Validation against the prototype (R-W9). The pass and the renderer were
written as uncommitted changes to `WhatwgGates/Ledger/Check.lean` and
`Render.lean`, with the data of D.5, in a scratch copy of the worktree at the
base commit, and kept in the seat's scratch directory for the builder:

| Item | Command | Result |
| --- | --- | --- |
| the battery | `lake env lean -DmaxErrors=5000 WhatwgTest/Audit/LedgerRoutingContract.lean` | exit 0, no error and no warning: 14 ascriptions, 2 instance checks, 82 `#guard` rows |
| that the rows discriminate | fourteen one-line mutants of the prototype: a fence matched as a prefix; an unrouted prefix matched on its string; rule M counting private and internal constants; a parented leaf as its own owner; the index as a stray file; an unbuilt unrouted prefix reported as claiming nothing; no production-root filter; claimants counted instead of owners; the index written before the projections; the routing findings skipped in write mode; the index not compared; not-applicable edges counted as closed; a leaf's parent rendered without its edge; claimants listed with repeats | every mutant fails the battery, with 1 to 32 errors |
| the trust gate with the battery imported (a temporary root import) | `lake build` | 480 jobs, green: "checked 280 source files and 20007 declarations; Classical.choice is reached by 84 of 13965 declarations in Whatwg, 89 of 2318 in WhatwgTest and 384 of 3724 in WhatwgGates; strict ceiling propext and Quot.sound over 6 module prefix(es) with 0 exact exception(s); 0 source-token exemption(s)"; the slice A battery green and unedited |
| kernel replay | `lake env leanchecker` naming the three ledger modules, `WhatwgTest.Ledger`, `WhatwgTest.Ledger.ConfigurationOrdering` and both batteries | exit 0, 18.7 s |
| the pass on the base data | `lake -q exe whatwg_ledger` | exit 1 with 33 findings: the 32 modules of D.5, then `generated/graphs/INDEX.md does not exist` |
| the pass with the slice D data | the same | exit 1 with 3 findings: `Whatwg.Streams.Kernel` claimed by nobody, `generated/graphs/CONFIGURATION-PG-ORDERING.md` differs (its `Fence:` line), and the index does not exist |
| a write with a scratch-only claim on the kernel (an unrouted entry citing R-W4, removed afterwards) | `lake -q exe whatwg_ledger --write`, then `lake -q exe whatwg_ledger` | both PASS, "12 graph(s), 120 edges, 1 leaf record(s), 14 unrouted prefix(es), 77 production module(s) with one owner each"; `INDEX.md` written; `CONFIGURATION-PG-ORDERING.md` changed in its `Fence:` line and the eleven other projections byte-identical; about 3 s per run |
| the measurements of D.2, D.3 and D.5 | probes importing the three roots through the shared loader, at the base commit | 2,627 modules and 228,259 constants in the table; 134 production modules, 77 selected by each of the three readings; each of the 47 fence entries is a module and none is a proper prefix of a module; `Whatwg.Html` has 19 modules under it, and none of the twelve Infra prefixes of D57 has one |

Not run: the coordinator's claim on `Whatwg.Streams.Kernel` and the fence
entry for `Whatwg.Ecma262.AgentInvariant`, which do not exist yet; `cli`'s
refusal paths, which slice D does not change; the trust self-test; a run on
Linux. After validation nothing of the prototype entered this branch.

### D.13 Deviations and amendments

| Design or section | Here | Reason |
| --- | --- | --- |
| design, slice row D: "a module routing pass in `Check.lean`" | a second fact table, `ModuleTable`, and `routedOutcome`; the routing findings follow `referenceFindings` | `World.mk`, `referenceFindings` and `outcome` are ascribed and pinned by the slice A battery |
| brief: the new findings placed in `referenceFindings`' order | immediately after it, before the projection findings | the same |
| section 9: `outcome` decides a run | `routedOutcome` decides it; `outcome` stays, and `cli` no longer calls it | the same |
| section 8: every file under `generated/graphs/` that is no graph's projection is reported | except the one path `generated/graphs/INDEX.md` | R-W11 |
| section 11: the run-time file set | `Ledger.runFiles`, one path more | the index's drift check |
| section 12: slice D not frozen; design row D: "`fence` for every graph" | the twelve fences stay, `CONFIGURATION-PG-ORDERING` gains six entries, the kernel waits for a ruling and `AgentInvariant` for its landing | measured, D.5 |
| design, row D: "`INDEX.md` with the section 2.11 counts" | the open, closed and not-applicable counts per graph; not the evidence-kind columns of the design's section 2.11 | those columns were counted by regular expressions over the old tables, and the cells do not determine them; a later format can add them under a new `formatVersion` |
| section 13, last bullet | D.11 | the pass exists |
| brief: at least two counterexample rows | four | the component rule and the stale debt entry are attacks the battery pins |

### D.14 Points for the coordinator

1. The owner of `Whatwg.Streams.Kernel`. R-W4's route, local receipts on the
   laws edges of five graphs, has no single owner in the ledger. Options: (a)
   an entry of one graph's fence; (b) a leaf record, standalone or with one
   of the five laws edges as parent, whose document names it (the
   threshold's leaf conditions 3 and 4 exclude composition laws, which R-W4
   overrode for the receipts, and a leaf has one parent); (c) an `unrouted`
   entry citing a new debt until a packet decides. This seat recommends (c):
   it names the gap without inventing a route, as D57 does, at the cost of one
   debt and one entry. Slice D cannot pass its gate until one is ruled.
2. `Whatwg.Ecma262.AgentInvariant`: the second of slice D and Q5b slice B5 to
   land adds the fence entry (D.5).
3. From slice D on, a packet that adds a production module with a constant
   must add its claim in the same landing, or `lake exe whatwg_ledger` fails.
   The coordinator owns `WhatwgTest/Ledger/` (section 12): either a builder's
   fence includes the one fence line of its graph's data module, or the
   coordinator adds it in the landing commit. A ruling should say which.
4. The leaf rule of D.3, a leaf with a parent counting for its parent graph,
   reads `docs/AGENT-ROUTING.md`; it makes a module fenced by a graph and
   declared into by that graph's leaf one owner. Confirm or amend.
5. Routers: `generated/AGENTS.md` describes the ledger's projection as one
   file per proof graph, and neither the root gate row of
   `lake exe whatwg_ledger` nor the gate table of `WhatwgGates/AGENTS.md`
   mentions routing or the index. These are the coordinator's, after the
   slice lands.
6. `outcome` stays as a function `cli` no longer calls, pinned by the slice A
   battery; retiring it needs a breaker amendment of that battery.
7. On any branch that holds a red battery under `WhatwgTest`, `Whatwg` or
   `WhatwgGates`, `lake exe whatwg_ledger` refuses for the missing `.olean`
   before it reads the ledger (D.12). R-W9 keeps such branches off `main`, so
   `main` is not affected, but the gate cannot be used to judge a breaker
   head, this one included.
