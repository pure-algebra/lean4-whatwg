/-!
# Gates.Ledger.Model

The data model of the graph ledger (`test/contracts/graph-ledger.contract.md`,
ruling R-W6): plain first-order data and the structural invariant, with no
metaprogramming. Imports nothing beyond `Init`.

A graph is a record with exactly ten edge fields, so a ledger entry that omits
or repeats an edge does not elaborate. A cell is `requiredOpen`,
`requiredClosed` or `notApplicable` and carries grounds, open items, recorded
debts and a note. Names of constants and modules are `Lean.Name` values
written with single-backtick literals, which elaborate without importing the
module that declares them; `lake exe whatwg_ledger` resolves them against the
built environment.

The structural invariant is `Ledger.wellFormed`, a `Bool` function written
with equality, emptiness, pattern matching and list operations only: kernel
reduction gets stuck on `String.startsWith` and `String.trimAscii`, and
`WhatwgTest.Ledger.ledger_wellFormed` decides the invariant with
`decide +kernel`. `Ledger.findings` is the same check with each finding named,
which is what the executable prints.

What a well-formed ledger means, and nothing more: graph and leaf identifiers
are distinct; every dependency names a graph of the ledger, none is reflexive,
and the dependencies are acyclic; every closed cell has a ground, no open item,
no register rows cited other than `CLOSED`, and at least one attesting ground
(a ruling, a receipts-log heading or `CLOSED` register rows, ruling R-W6);
every open cell names an item; every not-applicable cell has a reason and
carries no item and no ground other than a ruling; every cross-graph ground
cites a closed edge and every cross-graph item an open one; every leaf's parent
is a graph. Whether a name resolves, a count holds or a ruling exists is the
reference pass of `Gates.Ledger.Check`, not this module.
-/

namespace Gates.Ledger

/-- The ten edges of `docs/AGENT-ROUTING.md`, "The ten edges", in its order. -/
inductive Edge where
  | identity
  | construction
  | semantics
  | laws
  | representation
  | counterexamples
  | bridges
  | targets
  | trust
  | coverage
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

/-- A gate of the root `AGENTS.md` "Gates" table, or a census mode. A removed
executable has no constructor, so a cell cannot cite one. -/
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
  | .census standard => "lake exe whatwg_census --standard " ++ standard
  | .censusReport standard => "lake exe whatwg_census --standard " ++ standard ++ " --report"
  | .urlinventory => "lake exe whatwg_urlinventory"
  | .urlcensus => "lake exe whatwg_urlcensus"

/-- The `[[lean_exe]]` name the gate needs declared in `lakefile.toml`;
`none` for the two gates that run no executable of this package. -/
def Gate.executable? : Gate → Option String
  | .build | .leanchecker => none
  | .vendorseal => some "whatwg_vendorseal"
  | .citations => some "whatwg_citations"
  | .trustselftest => some "whatwg_trustselftest"
  | .census _ | .censusReport _ => some "whatwg_census"
  | .urlinventory => some "whatwg_urlinventory"
  | .urlcensus => some "whatwg_urlcensus"

/-- A status of a row of `test/counterexamples/REGISTER.md`. -/
inductive RowStatus where
  | closed
  | seeded
  deriving DecidableEq, Repr

/-- The status as the register spells it. -/
def RowStatus.text : RowStatus → String
  | .closed => "CLOSED"
  | .seeded => "SEEDED"

/-- A contiguous run of counterexample rows, `family-first` to `family-last`. -/
structure RowRange where
  family : String
  first : Nat
  last : Nat
  deriving DecidableEq, Repr

/-- A counterexample number zero-padded to three digits, as every register
spells it; a longer number is unchanged. -/
def threeDigits (n : Nat) : String :=
  let digits := toString n
  if digits.length ≥ 3 then digits
  else String.ofList (List.replicate (3 - digits.length) '0') ++ digits

/-- The identifiers of a row range, `family-NNN` from `first` to `last`;
empty when `last < first`. -/
def RowRange.ids (r : RowRange) : List String :=
  (List.range (r.last + 1 - r.first)).map fun k => r.family ++ "-" ++ threeDigits (r.first + k)

/-- Evidence that discharges an edge. Every constructor but `edge` is resolved
by `lake exe whatwg_ledger`; `edge` is checked in the kernel by
`Ledger.findings`. -/
inductive Ground where
  /-- Each name is a theorem of the built environment. -/
  | theorems (names : List Lean.Name)
  /-- Each name is a constant of the built environment, of any kind. -/
  | declarations (names : List Lean.Name)
  /-- A built module whose source holds exactly `count` receipt commands. -/
  | receipts («module» : Lean.Name) (count : Nat)
  /-- A built module whose source holds exactly `count` ascription commands. -/
  | ascriptions («module» : Lean.Name) (count : Nat)
  /-- Each name is a module of the built environment. -/
  | modules (names : List Lean.Name)
  /-- A gate the edge relies on; its executable is declared. -/
  | gate (g : Gate)
  /-- A ruling of `COORDINATION.md`, or a row of the graph document's rulings table. -/
  | ruling (id : String)
  /-- A level-two or level-three heading of the graph's receipts log, matched as a prefix. -/
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
  /-- Register rows that hold the edge open, with their status. -/
  | rows (range : RowRange) (status : RowStatus)
  /-- A theorem the edge waits for; the executable reports it once it exists. -/
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

/-- One edge's state. `grounds` discharge a closed edge, or record what is
already discharged on an open one, or, on a not-applicable edge, the rulings
that made it so; `remaining` is what holds an open edge open; `debts` are
debts recorded against the edge that do not hold it open; `note` is authored
prose, rendered verbatim and checked by nothing, and is the reason of a
not-applicable edge. It holds current grounds only (ruling R-W6). -/
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
that name this graph and that no ground of its cells cites. -/
structure Graph where
  id : String
  document : String
  fence : List Lean.Name
  dependsOn : List String := []
  acknowledged : List String := []
  edges : Edges
  deriving DecidableEq, Repr

/-- The receipts log of ruling R-V4. -/
def Graph.receiptsLog (g : Graph) : String := "docs/receipts/" ++ g.id ++ ".md"

/-- The projection `lake exe whatwg_ledger --write` writes. -/
def Graph.projection (g : Graph) : String := "generated/graphs/" ++ g.id ++ ".md"

/-- A leaf-receipt record (`docs/AGENT-ROUTING.md`, "Assurance threshold"):
its declarations, the graph edge its receipts contribute to (`none` for a
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

/-! ## The structural invariant

Written with equality, emptiness, pattern matching and list operations only,
so that the kernel evaluates it. -/

/-- No element occurs twice. -/
def distinct {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

/-- A ground that may stand in a closed cell: every kind except register rows
cited with a status other than `CLOSED`. -/
def Ground.discharges : Ground → Bool
  | .rows _ status => status == .closed
  | _ => true

/-- A ground that attests a closed cell (ruling R-W6): a ruling, a
receipts-log heading or `CLOSED` register rows. Theorem names, counts, gates
and another graph's edge do not attest. -/
def Ground.attests : Ground → Bool
  | .ruling _ => true
  | .receipt _ => true
  | .rows _ status => status == .closed
  | _ => false

/-- A ruling ground, the one kind a not-applicable cell may carry. -/
private def Ground.isRuling : Ground → Bool
  | .ruling _ => true
  | _ => false

/-- The cell's structural finding, or `none`; the first matching row of the
contract's section 4 wins. -/
def Cell.problem? (c : Cell) : Option String :=
  match c.status with
  | .requiredClosed =>
    if !c.remaining.isEmpty then some "closed with remaining items"
    else if c.grounds.isEmpty then some "closed with no ground"
    else if !c.grounds.all Ground.discharges then some "closed on rows that are not CLOSED"
    else if !c.grounds.any Ground.attests then
      some "closed with no ruling, receipts-log heading or CLOSED rows"
    else none
  | .requiredOpen =>
    if c.remaining.isEmpty then some "open with no remaining item named" else none
  | .notApplicable =>
    if !c.remaining.isEmpty || !c.grounds.all Ground.isRuling then
      some "not-applicable with an item or a ground other than a ruling"
    else if c.note.isEmpty then some "not-applicable with no reason"
    else none

/-- The status of another graph's edge, if the graph is in the ledger. -/
def Ledger.statusOf? (l : Ledger) (graph : String) (e : Edge) : Option Status :=
  (l.graphs.find? (·.id == graph)).map fun g => (g.edges.get e).status

/-- Every cross-graph reference of one cell with the status it requires: the
`edge` grounds, wanting `requiredClosed`, then the `edge` items, wanting
`requiredOpen`. -/
def Cell.crossReferences (c : Cell) : List (String × Edge × Status) :=
  (c.grounds.filterMap fun
    | .edge g e => some (g, e, Status.requiredClosed)
    | _ => none) ++
  (c.remaining.filterMap fun
    | .edge g e => some (g, e, Status.requiredOpen)
    | _ => none)

/-- One round of Kahn's algorithm: keep the graphs some dependency of which
is still kept. -/
private def kahnStep (remaining : List Graph) : List Graph :=
  remaining.filter fun g => g.dependsOn.any fun d => remaining.any (·.id == d)

/-- `fuel` rounds of Kahn's algorithm. -/
private def kahn : Nat → List Graph → List Graph
  | 0, remaining => remaining
  | fuel + 1, remaining => kahn fuel (kahnStep remaining)

/-- Kahn's algorithm with the graph count as fuel: repeatedly remove every
graph none of whose dependencies remains; the dependencies are acyclic when
nothing remains. -/
def Ledger.dependenciesAcyclic (l : Ledger) : Bool :=
  (kahn l.graphs.length l.graphs).isEmpty

/-- The findings of one cell of graph `g` at edge `e`: its own problem, then
each cross-graph citation of an unknown graph or of an edge with the wrong
status. -/
private def cellFindings (l : Ledger) (g : Graph) (e : Edge) : List String :=
  let c := g.edges.get e
  let own := match c.problem? with
    | some why => [g.id ++ " " ++ e.label ++ ": " ++ why]
    | none => []
  let cross := c.crossReferences.filterMap fun (other, oe, wanted) =>
    match l.statusOf? other oe with
    | none => some (g.id ++ " " ++ e.label ++ ": unknown graph " ++ other)
    | some actual =>
      if actual == wanted then none
      else some (g.id ++ " " ++ e.label ++ ": cites " ++ other ++ " " ++ oe.label ++ " as " ++
        wanted.text ++ ", but it is " ++ actual.text)
  own ++ cross

/-- The findings of one graph: unknown dependencies, a dependency on itself,
then the findings of each cell in `Edge.all` order. -/
private def graphStructureFindings (l : Ledger) (ids : List String) (g : Graph) : List String :=
  let unknown := g.dependsOn.filterMap fun d =>
    if ids.contains d then none else some (g.id ++ ": unknown dependency " ++ d)
  let self := if g.dependsOn.contains g.id then [g.id ++ ": depends on itself"] else []
  unknown ++ self ++ Edge.all.flatMap (cellFindings l g)

/-- Every structural finding, each naming its graph, edge or leaf, in the
order of the contract's section 4. -/
def Ledger.findings (l : Ledger) : List String :=
  let ids := l.graphs.map (·.id)
  let duplicate := if distinct ids then [] else ["two graphs share an identifier"]
  let perGraph := l.graphs.flatMap (graphStructureFindings l ids)
  let parents := l.leaves.filterMap fun leaf =>
    match leaf.parent with
    | some (g, _) =>
      if ids.contains g then none else some ("leaf " ++ leaf.id ++ ": unknown parent graph " ++ g)
    | none => none
  let leafIds := l.leaves.map (·.id)
  let leafShared :=
    if distinct leafIds && !leafIds.any ids.contains then [] else ["a leaf shares an identifier"]
  let cycle := if l.dependenciesAcyclic then [] else ["the graph dependencies have a cycle"]
  duplicate ++ perGraph ++ parents ++ leafShared ++ cycle

/-- The ledger is well formed when it has no structural finding. -/
def Ledger.wellFormed (l : Ledger) : Bool := l.findings.isEmpty

end Gates.Ledger
