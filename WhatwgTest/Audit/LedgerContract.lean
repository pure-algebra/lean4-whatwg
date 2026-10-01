import WhatwgGates.Ledger.Model
import WhatwgGates.Ledger.Render
import WhatwgGates.Ledger.Check
import WhatwgTest.Ledger
import WhatwgTest.Audit.Freeze

/-!
# WhatwgTest.Audit.LedgerContract

Frozen battery of `test/contracts/graph-ledger.contract.md` (ruling R-W6),
by the W7 breaker seat of review lane W, 2026-10-01, on branch
`review/w7-ledger-breaker` from `b0d35e2`. The packet states what the graph
ledger means; this module is the authority on names and propositions.

1. Exact ascriptions of every public declaration of
   `WhatwgGates.Ledger.Model`, `WhatwgGates.Ledger.Render` and
   `WhatwgGates.Ledger.Check`, of the slice A data names and of the
   structural theorem, with a constructor census by exhaustive `match`.
2. The edge record: an entry that omits or repeats an edge field does not
   elaborate, and the `#guard_msgs` above each probe pins the reason.
3. One kernel-decided theorem per structural plant and per control
   (`decide +kernel`), each with a `#guard` that pins the finding it raises.
4. The counting rule over both spellings, comments and literals excluded.
5. Edge tokens, the latest-wins rule and the mention check.
6. The reference pass over planted `World` values: the environment facts and
   the file texts as data. Every finding is pinned by its exact text.
7. The projection: its exact rendering, the drift findings and the run-time
   file set.
8. The outcome of a run: exit code, printed lines, written files.

Nothing here does IO and nothing here declares syntax: `Gates.Ledger.cli`
is the one IO function of the packet and is only ascribed. Every helper
below is `private`.
-/

namespace WhatwgTest.Audit.LedgerContract

open Gates.Ledger

/-! ## 1. Signatures -/

/-! ### 1.1 `WhatwgGates.Ledger.Model` -/

#whatwg_freeze (@Gates.Ledger.Edge : Type)
#whatwg_freeze (@Gates.Ledger.Edge.identity : Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.construction : Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.semantics : Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.laws : Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.representation : Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.counterexamples : Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.bridges : Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.targets : Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.trust : Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.coverage : Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.all : List Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.Edge.label : Gates.Ledger.Edge → String)

#whatwg_freeze (@Gates.Ledger.Gate : Type)
#whatwg_freeze (@Gates.Ledger.Gate.build : Gates.Ledger.Gate)
#whatwg_freeze (@Gates.Ledger.Gate.vendorseal : Gates.Ledger.Gate)
#whatwg_freeze (@Gates.Ledger.Gate.citations : Gates.Ledger.Gate)
#whatwg_freeze (@Gates.Ledger.Gate.trustselftest : Gates.Ledger.Gate)
#whatwg_freeze (@Gates.Ledger.Gate.leanchecker : Gates.Ledger.Gate)
#whatwg_freeze (@Gates.Ledger.Gate.census : String → Gates.Ledger.Gate)
#whatwg_freeze (@Gates.Ledger.Gate.censusReport : String → Gates.Ledger.Gate)
#whatwg_freeze (@Gates.Ledger.Gate.urlinventory : Gates.Ledger.Gate)
#whatwg_freeze (@Gates.Ledger.Gate.urlcensus : Gates.Ledger.Gate)
#whatwg_freeze (@Gates.Ledger.Gate.command : Gates.Ledger.Gate → String)
#whatwg_freeze (@Gates.Ledger.Gate.executable? : Gates.Ledger.Gate → Option String)

#whatwg_freeze (@Gates.Ledger.RowStatus : Type)
#whatwg_freeze (@Gates.Ledger.RowStatus.closed : Gates.Ledger.RowStatus)
#whatwg_freeze (@Gates.Ledger.RowStatus.seeded : Gates.Ledger.RowStatus)
#whatwg_freeze (@Gates.Ledger.RowStatus.text : Gates.Ledger.RowStatus → String)

#whatwg_freeze (@Gates.Ledger.RowRange : Type)
#whatwg_freeze (@Gates.Ledger.RowRange.mk : String → Nat → Nat → Gates.Ledger.RowRange)
#whatwg_freeze (@Gates.Ledger.RowRange.family : Gates.Ledger.RowRange → String)
#whatwg_freeze (@Gates.Ledger.RowRange.first : Gates.Ledger.RowRange → Nat)
#whatwg_freeze (@Gates.Ledger.RowRange.last : Gates.Ledger.RowRange → Nat)
#whatwg_freeze (@Gates.Ledger.RowRange.ids : Gates.Ledger.RowRange → List String)
#whatwg_freeze (@Gates.Ledger.threeDigits : Nat → String)

#whatwg_freeze (@Gates.Ledger.Ground : Type)
#whatwg_freeze (@Gates.Ledger.Ground.theorems : List Lean.Name → Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Ground.declarations : List Lean.Name → Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Ground.receipts : Lean.Name → Nat → Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Ground.ascriptions : Lean.Name → Nat → Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Ground.modules : List Lean.Name → Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Ground.gate : Gates.Ledger.Gate → Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Ground.ruling : String → Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Ground.receipt : String → Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Ground.rows :
  Gates.Ledger.RowRange → Gates.Ledger.RowStatus → Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Ground.edge : String → Gates.Ledger.Edge → Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Ground.discharges : Gates.Ledger.Ground → Bool)
#whatwg_freeze (@Gates.Ledger.Ground.attests : Gates.Ledger.Ground → Bool)

#whatwg_freeze (@Gates.Ledger.Item : Type)
#whatwg_freeze (@Gates.Ledger.Item.named : String → Gates.Ledger.Item)
#whatwg_freeze (@Gates.Ledger.Item.debt : String → Gates.Ledger.Item)
#whatwg_freeze (@Gates.Ledger.Item.rows :
  Gates.Ledger.RowRange → Gates.Ledger.RowStatus → Gates.Ledger.Item)
#whatwg_freeze (@Gates.Ledger.Item.wanted : Lean.Name → Gates.Ledger.Item)
#whatwg_freeze (@Gates.Ledger.Item.edge : String → Gates.Ledger.Edge → Gates.Ledger.Item)

#whatwg_freeze (@Gates.Ledger.Status : Type)
#whatwg_freeze (@Gates.Ledger.Status.requiredOpen : Gates.Ledger.Status)
#whatwg_freeze (@Gates.Ledger.Status.requiredClosed : Gates.Ledger.Status)
#whatwg_freeze (@Gates.Ledger.Status.notApplicable : Gates.Ledger.Status)
#whatwg_freeze (@Gates.Ledger.Status.text : Gates.Ledger.Status → String)

#whatwg_freeze (@Gates.Ledger.Cell : Type)
#whatwg_freeze (@Gates.Ledger.Cell.mk : Gates.Ledger.Status → List Gates.Ledger.Ground →
  List Gates.Ledger.Item → List String → String → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Cell.status : Gates.Ledger.Cell → Gates.Ledger.Status)
#whatwg_freeze (@Gates.Ledger.Cell.grounds : Gates.Ledger.Cell → List Gates.Ledger.Ground)
#whatwg_freeze (@Gates.Ledger.Cell.remaining : Gates.Ledger.Cell → List Gates.Ledger.Item)
#whatwg_freeze (@Gates.Ledger.Cell.debts : Gates.Ledger.Cell → List String)
#whatwg_freeze (@Gates.Ledger.Cell.note : Gates.Ledger.Cell → String)

#whatwg_freeze (@Gates.Ledger.Edges : Type)
#whatwg_freeze (@Gates.Ledger.Edges.mk : Gates.Ledger.Cell → Gates.Ledger.Cell →
  Gates.Ledger.Cell → Gates.Ledger.Cell → Gates.Ledger.Cell → Gates.Ledger.Cell →
  Gates.Ledger.Cell → Gates.Ledger.Cell → Gates.Ledger.Cell → Gates.Ledger.Cell →
  Gates.Ledger.Edges)
#whatwg_freeze (@Gates.Ledger.Edges.identity : Gates.Ledger.Edges → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Edges.construction : Gates.Ledger.Edges → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Edges.semantics : Gates.Ledger.Edges → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Edges.laws : Gates.Ledger.Edges → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Edges.representation : Gates.Ledger.Edges → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Edges.counterexamples : Gates.Ledger.Edges → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Edges.bridges : Gates.Ledger.Edges → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Edges.targets : Gates.Ledger.Edges → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Edges.trust : Gates.Ledger.Edges → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Edges.coverage : Gates.Ledger.Edges → Gates.Ledger.Cell)
#whatwg_freeze (@Gates.Ledger.Edges.get :
  Gates.Ledger.Edges → Gates.Ledger.Edge → Gates.Ledger.Cell)

#whatwg_freeze (@Gates.Ledger.Graph : Type)
#whatwg_freeze (@Gates.Ledger.Graph.mk : String → String → List Lean.Name → List String →
  List String → Gates.Ledger.Edges → Gates.Ledger.Graph)
#whatwg_freeze (@Gates.Ledger.Graph.id : Gates.Ledger.Graph → String)
#whatwg_freeze (@Gates.Ledger.Graph.document : Gates.Ledger.Graph → String)
#whatwg_freeze (@Gates.Ledger.Graph.fence : Gates.Ledger.Graph → List Lean.Name)
#whatwg_freeze (@Gates.Ledger.Graph.dependsOn : Gates.Ledger.Graph → List String)
#whatwg_freeze (@Gates.Ledger.Graph.acknowledged : Gates.Ledger.Graph → List String)
#whatwg_freeze (@Gates.Ledger.Graph.edges : Gates.Ledger.Graph → Gates.Ledger.Edges)
#whatwg_freeze (@Gates.Ledger.Graph.receiptsLog : Gates.Ledger.Graph → String)
#whatwg_freeze (@Gates.Ledger.Graph.projection : Gates.Ledger.Graph → String)

#whatwg_freeze (@Gates.Ledger.Leaf : Type)
#whatwg_freeze (@Gates.Ledger.Leaf.mk : String → String → List Lean.Name →
  Option (String × Gates.Ledger.Edge) → List Gates.Ledger.Ground → Gates.Ledger.Leaf)
#whatwg_freeze (@Gates.Ledger.Leaf.id : Gates.Ledger.Leaf → String)
#whatwg_freeze (@Gates.Ledger.Leaf.document : Gates.Ledger.Leaf → String)
#whatwg_freeze (@Gates.Ledger.Leaf.declarations : Gates.Ledger.Leaf → List Lean.Name)
#whatwg_freeze (@Gates.Ledger.Leaf.parent : Gates.Ledger.Leaf → Option (String × Gates.Ledger.Edge))
#whatwg_freeze (@Gates.Ledger.Leaf.receipts : Gates.Ledger.Leaf → List Gates.Ledger.Ground)

#whatwg_freeze (@Gates.Ledger.Unrouted : Type)
#whatwg_freeze (@Gates.Ledger.Unrouted.mk : Lean.Name → String → Gates.Ledger.Unrouted)
#whatwg_freeze (@Gates.Ledger.Unrouted.modulePrefix : Gates.Ledger.Unrouted → Lean.Name)
#whatwg_freeze (@Gates.Ledger.Unrouted.recordedBy : Gates.Ledger.Unrouted → String)

#whatwg_freeze (@Gates.Ledger.Ledger : Type)
#whatwg_freeze (@Gates.Ledger.Ledger.mk : List Gates.Ledger.Graph → List Gates.Ledger.Leaf →
  List Gates.Ledger.Unrouted → Gates.Ledger.Ledger)
#whatwg_freeze (@Gates.Ledger.Ledger.graphs : Gates.Ledger.Ledger → List Gates.Ledger.Graph)
#whatwg_freeze (@Gates.Ledger.Ledger.leaves : Gates.Ledger.Ledger → List Gates.Ledger.Leaf)
#whatwg_freeze (@Gates.Ledger.Ledger.unrouted : Gates.Ledger.Ledger → List Gates.Ledger.Unrouted)

#whatwg_freeze (@Gates.Ledger.distinct : {α : Type} → [DecidableEq α] → List α → Bool)
#whatwg_freeze (@Gates.Ledger.Cell.problem? : Gates.Ledger.Cell → Option String)
#whatwg_freeze (@Gates.Ledger.Ledger.statusOf? : Gates.Ledger.Ledger → String →
  Gates.Ledger.Edge → Option Gates.Ledger.Status)
#whatwg_freeze (@Gates.Ledger.Cell.crossReferences : Gates.Ledger.Cell →
  List (String × Gates.Ledger.Edge × Gates.Ledger.Status))
#whatwg_freeze (@Gates.Ledger.Ledger.dependenciesAcyclic : Gates.Ledger.Ledger → Bool)
#whatwg_freeze (@Gates.Ledger.Ledger.findings : Gates.Ledger.Ledger → List String)
#whatwg_freeze (@Gates.Ledger.Ledger.wellFormed : Gates.Ledger.Ledger → Bool)

/-! ### 1.2 `WhatwgGates.Ledger.Render` -/

#whatwg_freeze (@Gates.Ledger.formatVersion : Nat)
#whatwg_freeze (@Gates.Ledger.code : String → String)
#whatwg_freeze (@Gates.Ledger.joinAnd : List String → String)
#whatwg_freeze (@Gates.Ledger.Ground.render : Gates.Ledger.Ground → String)
#whatwg_freeze (@Gates.Ledger.Item.render : Gates.Ledger.Item → String)
#whatwg_freeze (@Gates.Ledger.Cell.render : Gates.Ledger.Cell → String)
#whatwg_freeze (@Gates.Ledger.Graph.render : Gates.Ledger.Graph → String → String)

/-! ### 1.3 `WhatwgGates.Ledger.Check` -/

#whatwg_freeze (@Gates.Ledger.ConstantKind : Type)
#whatwg_freeze (@Gates.Ledger.ConstantKind.thm : Gates.Ledger.ConstantKind)
#whatwg_freeze (@Gates.Ledger.ConstantKind.other : Gates.Ledger.ConstantKind)
#whatwg_freeze (@Gates.Ledger.World : Type)
#whatwg_freeze (@Gates.Ledger.World.mk : (Lean.Name → Option Gates.Ledger.ConstantKind) →
  (Lean.Name → Bool) → (String → Option String) → List String → Gates.Ledger.World)
#whatwg_freeze (@Gates.Ledger.World.constantKind? :
  Gates.Ledger.World → Lean.Name → Option Gates.Ledger.ConstantKind)
#whatwg_freeze (@Gates.Ledger.World.moduleBuilt : Gates.Ledger.World → Lean.Name → Bool)
#whatwg_freeze (@Gates.Ledger.World.file? : Gates.Ledger.World → String → Option String)
#whatwg_freeze (@Gates.Ledger.World.projectionFiles : Gates.Ledger.World → List String)
#whatwg_freeze (@Gates.Ledger.World.linesOf : Gates.Ledger.World → String → List String)
#whatwg_freeze (@Gates.Ledger.sourcePath : Lean.Name → String)
#whatwg_freeze (@Gates.Ledger.codeLines : String → List String)
#whatwg_freeze (@Gates.Ledger.receiptCount : String → Nat)
#whatwg_freeze (@Gates.Ledger.ascriptionCount : String → Nat)
#whatwg_freeze (@Gates.Ledger.rulingPresent : Gates.Ledger.World → List String → String → Bool)
#whatwg_freeze (@Gates.Ledger.debtPresent : Gates.Ledger.World → String → Bool)
#whatwg_freeze (@Gates.Ledger.rowStatus? : Gates.Ledger.World → String → Option String)
#whatwg_freeze (@Gates.Ledger.rowFindings : Gates.Ledger.World → Gates.Ledger.RowRange →
  Gates.Ledger.RowStatus → List String)
#whatwg_freeze (@Gates.Ledger.groundFindings : Gates.Ledger.World → List String → List String →
  Gates.Ledger.Ground → List String)
#whatwg_freeze (@Gates.Ledger.itemFindings :
  Gates.Ledger.World → Gates.Ledger.Item → List String)
#whatwg_freeze (@Gates.Ledger.rulingId? : String → Option String)
#whatwg_freeze (@Gates.Ledger.rulingMentions :
  List String → List Gates.Ledger.Graph → List (String × String))
#whatwg_freeze (@Gates.Ledger.EdgeToken : Type)
#whatwg_freeze (@Gates.Ledger.EdgeToken.mk : String → String → Gates.Ledger.Edge →
  Gates.Ledger.Status → Gates.Ledger.EdgeToken)
#whatwg_freeze (@Gates.Ledger.EdgeToken.ruling : Gates.Ledger.EdgeToken → String)
#whatwg_freeze (@Gates.Ledger.EdgeToken.graph : Gates.Ledger.EdgeToken → String)
#whatwg_freeze (@Gates.Ledger.EdgeToken.edge : Gates.Ledger.EdgeToken → Gates.Ledger.Edge)
#whatwg_freeze (@Gates.Ledger.EdgeToken.status : Gates.Ledger.EdgeToken → Gates.Ledger.Status)
#whatwg_freeze (@Gates.Ledger.codeSpans : String → List String)
#whatwg_freeze (@Gates.Ledger.parseStatus? : String → Option Gates.Ledger.Status)
#whatwg_freeze (@Gates.Ledger.edgeTokens : List String → List Gates.Ledger.EdgeToken)
#whatwg_freeze (@Gates.Ledger.latestTokens :
  List Gates.Ledger.EdgeToken → List Gates.Ledger.EdgeToken)
#whatwg_freeze (@Gates.Ledger.tokenFindings :
  Gates.Ledger.Ledger → List Gates.Ledger.EdgeToken → List String)
#whatwg_freeze (@Gates.Ledger.Graph.citedRulings : Gates.Ledger.Graph → List String)
#whatwg_freeze (@Gates.Ledger.graphFindings :
  Gates.Ledger.World → Gates.Ledger.Ledger → Gates.Ledger.Graph → List String)
#whatwg_freeze (@Gates.Ledger.leafFindings :
  Gates.Ledger.World → Gates.Ledger.Leaf → List String)
#whatwg_freeze (@Gates.Ledger.unroutedFindings :
  Gates.Ledger.World → Gates.Ledger.Unrouted → List String)
#whatwg_freeze (@Gates.Ledger.ledgerInput : String)
#whatwg_freeze (@Gates.Ledger.Ledger.files : Gates.Ledger.Ledger → List String)
#whatwg_freeze (@Gates.Ledger.referenceFindings :
  Gates.Ledger.World → Gates.Ledger.Ledger → List String)
#whatwg_freeze (@Gates.Ledger.projectionFindings :
  Gates.Ledger.World → Gates.Ledger.Ledger → List String)
#whatwg_freeze (@Gates.Ledger.Outcome : Type)
#whatwg_freeze (@Gates.Ledger.Outcome.mk :
  UInt32 → List String → List (String × String) → Gates.Ledger.Outcome)
#whatwg_freeze (@Gates.Ledger.Outcome.exitCode : Gates.Ledger.Outcome → UInt32)
#whatwg_freeze (@Gates.Ledger.Outcome.output : Gates.Ledger.Outcome → List String)
#whatwg_freeze (@Gates.Ledger.Outcome.writes : Gates.Ledger.Outcome → List (String × String))
#whatwg_freeze (@Gates.Ledger.outcome :
  Gates.Ledger.World → Gates.Ledger.Ledger → Bool → Gates.Ledger.Outcome)
#whatwg_freeze (@Gates.Ledger.cli : Gates.Ledger.Ledger → List String → IO UInt32)

/-! ### 1.4 Slice A data and the structural theorem -/

#whatwg_freeze (@WhatwgTest.Ledger.dataQueue : Gates.Ledger.Graph)
#whatwg_freeze (@WhatwgTest.Ledger.promiseFirst : Gates.Ledger.Graph)
#whatwg_freeze (@WhatwgTest.Ledger.configurationOrdering : Gates.Ledger.Graph)
#whatwg_freeze (@WhatwgTest.Ledger.infraInteger : Gates.Ledger.Leaf)
#whatwg_freeze (@WhatwgTest.Ledger.ledger : Gates.Ledger.Ledger)
#whatwg_freeze (@WhatwgTest.Ledger.ledger_wellFormed :
  WhatwgTest.Ledger.ledger.wellFormed = true) axioms [propext]

#guard WhatwgTest.Ledger.dataQueue.id == "DATA-PG-QUEUE"
#guard WhatwgTest.Ledger.dataQueue.document == "docs/DATA-DAG.md"
#guard WhatwgTest.Ledger.promiseFirst.id == "PROMISE-PG-FIRST"
#guard WhatwgTest.Ledger.promiseFirst.document == "docs/PROMISE-DAG.md"
#guard WhatwgTest.Ledger.configurationOrdering.id == "CONFIGURATION-PG-ORDERING"
#guard WhatwgTest.Ledger.configurationOrdering.document == "docs/CONFIGURATION-DAG.md"
#guard WhatwgTest.Ledger.infraInteger.id == "INFRA-LF-INTEGER"
#guard WhatwgTest.Ledger.infraInteger.document == "docs/INFRA-INTEGER-CONSTRUCTIVE.md"
#guard WhatwgTest.Ledger.infraInteger.parent == none
#guard [WhatwgTest.Ledger.dataQueue, WhatwgTest.Ledger.promiseFirst,
  WhatwgTest.Ledger.configurationOrdering].all WhatwgTest.Ledger.ledger.graphs.contains
#guard WhatwgTest.Ledger.ledger.leaves.contains WhatwgTest.Ledger.infraInteger

/-! ### 1.5 Instances -/

#check (inferInstance : DecidableEq Gates.Ledger.Edge)
#check (inferInstance : DecidableEq Gates.Ledger.Gate)
#check (inferInstance : DecidableEq Gates.Ledger.RowStatus)
#check (inferInstance : DecidableEq Gates.Ledger.RowRange)
#check (inferInstance : DecidableEq Gates.Ledger.Ground)
#check (inferInstance : DecidableEq Gates.Ledger.Item)
#check (inferInstance : DecidableEq Gates.Ledger.Status)
#check (inferInstance : DecidableEq Gates.Ledger.Cell)
#check (inferInstance : DecidableEq Gates.Ledger.Edges)
#check (inferInstance : DecidableEq Gates.Ledger.Graph)
#check (inferInstance : DecidableEq Gates.Ledger.Leaf)
#check (inferInstance : DecidableEq Gates.Ledger.Unrouted)
#check (inferInstance : DecidableEq Gates.Ledger.Ledger)
#check (inferInstance : DecidableEq Gates.Ledger.ConstantKind)
#check (inferInstance : DecidableEq Gates.Ledger.EdgeToken)
#check (inferInstance : DecidableEq Gates.Ledger.Outcome)
#check (inferInstance : Repr Gates.Ledger.Edge)
#check (inferInstance : Repr Gates.Ledger.Gate)
#check (inferInstance : Repr Gates.Ledger.RowStatus)
#check (inferInstance : Repr Gates.Ledger.RowRange)
#check (inferInstance : Repr Gates.Ledger.Ground)
#check (inferInstance : Repr Gates.Ledger.Item)
#check (inferInstance : Repr Gates.Ledger.Status)
#check (inferInstance : Repr Gates.Ledger.Cell)
#check (inferInstance : Repr Gates.Ledger.Edges)
#check (inferInstance : Repr Gates.Ledger.Graph)
#check (inferInstance : Repr Gates.Ledger.Leaf)
#check (inferInstance : Repr Gates.Ledger.Unrouted)
#check (inferInstance : Repr Gates.Ledger.Ledger)
#check (inferInstance : Repr Gates.Ledger.ConstantKind)
#check (inferInstance : Repr Gates.Ledger.EdgeToken)
#check (inferInstance : Repr Gates.Ledger.Outcome)

/-! ### 1.6 Constructor census

Each `match` below is exhaustive over the frozen constructors and names no
other: a constructor added, removed or renamed fails to elaborate here. -/

private def edgeIndex : Gates.Ledger.Edge → Nat
  | .identity => 0 | .construction => 1 | .semantics => 2 | .laws => 3
  | .representation => 4 | .counterexamples => 5 | .bridges => 6
  | .targets => 7 | .trust => 8 | .coverage => 9

private def gateIndex : Gates.Ledger.Gate → Nat
  | .build => 0 | .vendorseal => 1 | .citations => 2 | .trustselftest => 3
  | .leanchecker => 4 | .census _ => 5 | .censusReport _ => 6
  | .urlinventory => 7 | .urlcensus => 8

private def rowStatusIndex : Gates.Ledger.RowStatus → Nat
  | .closed => 0 | .seeded => 1

private def groundIndex : Gates.Ledger.Ground → Nat
  | .theorems _ => 0 | .declarations _ => 1 | .receipts _ _ => 2
  | .ascriptions _ _ => 3 | .modules _ => 4 | .gate _ => 5 | .ruling _ => 6
  | .receipt _ => 7 | .rows _ _ => 8 | .edge _ _ => 9

private def itemIndex : Gates.Ledger.Item → Nat
  | .named _ => 0 | .debt _ => 1 | .rows _ _ => 2 | .wanted _ => 3 | .edge _ _ => 4

private def statusIndex : Gates.Ledger.Status → Nat
  | .requiredOpen => 0 | .requiredClosed => 1 | .notApplicable => 2

private def constantKindIndex : Gates.Ledger.ConstantKind → Nat
  | .thm => 0 | .other => 1

#guard Edge.all.map edgeIndex == List.range 10
#guard Edge.all.map Edge.label ==
  ["identity", "construction", "semantics", "laws", "representation",
   "counterexamples", "bridges", "targets", "trust", "coverage"]
#guard [Gate.build, .vendorseal, .citations, .trustselftest, .leanchecker,
  .census "streams", .censusReport "webidl", .urlinventory, .urlcensus].map gateIndex ==
  List.range 9
#guard [RowStatus.closed, .seeded].map rowStatusIndex == [0, 1]
#guard [Status.requiredOpen, .requiredClosed, .notApplicable].map statusIndex == [0, 1, 2]
#guard [ConstantKind.thm, .other].map constantKindIndex == [0, 1]
#guard [Ground.theorems [], .declarations [], .receipts `M 0, .ascriptions `M 0,
  .modules [], .gate .build, .ruling "R", .receipt "H", .rows ⟨"F", 1, 1⟩ .closed,
  .edge "G" .laws].map groundIndex == List.range 10
#guard [Item.named "x", .debt "D1", .rows ⟨"F", 1, 1⟩ .seeded, .wanted `n,
  .edge "G" .laws].map itemIndex == List.range 5

/-! ### 1.7 Spellings of the finite alphabets -/

#guard Gate.build.command == "lake build"
#guard Gate.vendorseal.command == "lake exe whatwg_vendorseal"
#guard Gate.citations.command == "lake exe whatwg_citations"
#guard Gate.trustselftest.command == "lake exe whatwg_trustselftest"
#guard Gate.leanchecker.command == "lake env leanchecker Whatwg WhatwgTest WhatwgGates"
#guard (Gate.census "infra").command == "lake exe whatwg_census --standard infra"
#guard (Gate.censusReport "streams").command ==
  "lake exe whatwg_census --standard streams --report"
#guard Gate.urlinventory.command == "lake exe whatwg_urlinventory"
#guard Gate.urlcensus.command == "lake exe whatwg_urlcensus"
#guard Gate.build.executable? == none
#guard Gate.leanchecker.executable? == none
#guard Gate.vendorseal.executable? == some "whatwg_vendorseal"
#guard Gate.citations.executable? == some "whatwg_citations"
#guard Gate.trustselftest.executable? == some "whatwg_trustselftest"
#guard (Gate.census "ecma262").executable? == some "whatwg_census"
#guard (Gate.censusReport "streams").executable? == some "whatwg_census"
#guard Gate.urlinventory.executable? == some "whatwg_urlinventory"
#guard Gate.urlcensus.executable? == some "whatwg_urlcensus"
#guard RowStatus.closed.text == "CLOSED"
#guard RowStatus.seeded.text == "SEEDED"
#guard Status.requiredOpen.text == "required-open"
#guard Status.requiredClosed.text == "required-closed"
#guard Status.notApplicable.text == "not-applicable"
#guard threeDigits 1 == "001"
#guard threeDigits 39 == "039"
#guard threeDigits 123 == "123"
#guard threeDigits 1234 == "1234"
#guard (RowRange.mk "WS-PROM-CE" 36 38).ids ==
  ["WS-PROM-CE-036", "WS-PROM-CE-037", "WS-PROM-CE-038"]
#guard (RowRange.mk "LEDGER-CE" 5 5).ids == ["LEDGER-CE-005"]
#guard (RowRange.mk "LEDGER-CE" 5 4).ids == []
private def naEdges : Edges :=
  let c : Cell := ⟨.notApplicable, [], [], [], "n"⟩
  ⟨c, c, c, c, c, c, c, c, c, c⟩

#guard (Graph.mk "G-PG-X" "d" [] [] [] naEdges).receiptsLog == "docs/receipts/G-PG-X.md"
#guard (Graph.mk "G-PG-X" "d" [] [] [] naEdges).projection == "generated/graphs/G-PG-X.md"
#guard Edge.all.all fun e => naEdges.get e == ⟨.notApplicable, [], [], [], "n"⟩

/-! ### 1.8 Field names and defaults -/

#guard ({ status := .notApplicable } : Cell) == ⟨.notApplicable, [], [], [], ""⟩
#guard ({ status := .requiredOpen, grounds := [.ruling "R"], remaining := [.named "x"],
          debts := ["D1"], note := "n" } : Cell) ==
  ⟨.requiredOpen, [.ruling "R"], [.named "x"], ["D1"], "n"⟩
#guard ({ family := "F", first := 1, last := 2 } : RowRange) == ⟨"F", 1, 2⟩
#guard ({ modulePrefix := `Whatwg.Html, recordedBy := "D57" } : Unrouted) ==
  ⟨`Whatwg.Html, "D57"⟩
#guard ({ graphs := [] } : Ledger) == ⟨[], [], []⟩
#guard ({ id := "L", document := "d", declarations := [], parent := none,
          receipts := [] } : Leaf) == ⟨"L", "d", [], none, []⟩

/-! ## 2. Exactly ten edges

`Edges` is a record with one field per edge. The positive control
elaborates; the two probes do not, and the pinned message says why. -/

private def oc : Cell := { status := .requiredOpen, remaining := [.named "x"] }

example : Gates.Ledger.Edges :=
  { identity := oc, construction := oc, semantics := oc, laws := oc,
    representation := oc, counterexamples := oc, bridges := oc, targets := oc,
    trust := oc, coverage := oc }

-- The `coverage` field omitted. The message also carries a hint and the
-- elaborator's recovery term, which are not pinned; `substring := true`
-- pins the reason.
/-- info: Fields missing: `coverage` -/
#guard_msgs (substring := true) in
#check_failure ({ identity := oc, construction := oc, semantics := oc, laws := oc,
                  representation := oc, counterexamples := oc, bridges := oc, targets := oc,
                  trust := oc } : Gates.Ledger.Edges)

-- The `identity` field given twice.
/-- info: field `identity` has already been specified -/
#guard_msgs (substring := true) in
#check_failure ({ identity := oc, identity := oc, construction := oc, semantics := oc,
                  laws := oc, representation := oc, counterexamples := oc, bridges := oc,
                  targets := oc, trust := oc, coverage := oc } : Gates.Ledger.Edges)

/-! ## 3. Structural plants, decided in the kernel

Each plant is a ledger that `Gates.Ledger.Ledger.wellFormed` must refuse;
the theorem is checked by `decide +kernel`, and the `#guard` after it pins
the exact finding, so a plant refused for another reason fails this file. -/

private def cc : Cell := { status := .requiredClosed, grounds := [.receipt "Landing"] }

private def closedOn (gs : List Ground) (debts : List String := []) : Cell :=
  { status := .requiredClosed, grounds := gs, debts }

private def openOn (items : List Item) (gs : List Ground := []) : Cell :=
  { status := .requiredOpen, grounds := gs, remaining := items }

private def naOn (note : String) (gs : List Ground := []) : Cell :=
  { status := .notApplicable, grounds := gs, note }

private def leafOf (id : String) (parent : Option (String × Edge) := none) : Leaf :=
  { id, document := "docs/L.md", declarations := [], parent, receipts := [] }

private def setCell (es : Edges) : Edge → Cell → Edges
  | .identity, c => { es with identity := c }
  | .construction, c => { es with construction := c }
  | .semantics, c => { es with semantics := c }
  | .laws, c => { es with laws := c }
  | .representation, c => { es with representation := c }
  | .counterexamples, c => { es with counterexamples := c }
  | .bridges, c => { es with bridges := c }
  | .targets, c => { es with targets := c }
  | .trust, c => { es with trust := c }
  | .coverage, c => { es with coverage := c }

private def allOpen : Edges :=
  { identity := oc, construction := oc, semantics := oc, laws := oc,
    representation := oc, counterexamples := oc, bridges := oc, targets := oc,
    trust := oc, coverage := oc }

private def graphOf (id : String) (deps : List String := []) (es : Edges := allOpen) :
    Graph :=
  { id, document := "docs/X.md", fence := [], dependsOn := deps, edges := es }

private def withCell (id : String) (e : Edge) (c : Cell) : Graph :=
  graphOf id [] (setCell allOpen e c)

-- P1: a closed cell with a remaining item.
private def plantClosedWithItem : Ledger :=
  { graphs := [withCell "G1" .laws { cc with remaining := [.named "x"] }] }
theorem plant_closedWithItem : plantClosedWithItem.wellFormed = false := by
  decide +kernel
#guard plantClosedWithItem.findings == ["G1 laws: closed with remaining items"]

-- P2: a closed cell with no ground.
private def plantClosedNoGround : Ledger :=
  { graphs := [withCell "G1" .trust { status := .requiredClosed }] }
theorem plant_closedNoGround : plantClosedNoGround.wellFormed = false := by
  decide +kernel
#guard plantClosedNoGround.findings == ["G1 trust: closed with no ground"]

-- P3: an open cell with nothing named.
private def plantOpenNothingNamed : Ledger :=
  { graphs := [withCell "G1" .semantics (openOn [] [.receipt "Landing"])] }
theorem plant_openNothingNamed : plantOpenNothingNamed.wellFormed = false := by
  decide +kernel
#guard plantOpenNothingNamed.findings == ["G1 semantics: open with no remaining item named"]

-- P4: a not-applicable cell with no reason.
private def plantNotApplicableNoReason : Ledger :=
  { graphs := [withCell "G1" .targets { status := .notApplicable }] }
theorem plant_notApplicableNoReason : plantNotApplicableNoReason.wellFormed = false := by
  decide +kernel
#guard plantNotApplicableNoReason.findings == ["G1 targets: not-applicable with no reason"]

-- P5: two graphs with one identifier.
private def plantDuplicateGraph : Ledger :=
  { graphs := [graphOf "G1", graphOf "G1"] }
theorem plant_duplicateGraph : plantDuplicateGraph.wellFormed = false := by
  decide +kernel
#guard plantDuplicateGraph.findings == ["two graphs share an identifier"]

-- P6: a dependency on an unknown graph.
private def plantUnknownDependency : Ledger :=
  { graphs := [graphOf "G1" ["G9"]] }
theorem plant_unknownDependency : plantUnknownDependency.wellFormed = false := by
  decide +kernel
#guard plantUnknownDependency.findings == ["G1: unknown dependency G9"]

-- P7: a closed cell citing another graph's open edge (LEDGER-CE-005).
private def plantClosedOnOpenEdge : Ledger :=
  { graphs := [graphOf "G1",
      withCell "G2" .identity (closedOn [.edge "G1" .laws, .receipt "Landing"])] }
theorem plant_closedOnOpenEdge : plantClosedOnOpenEdge.wellFormed = false := by
  decide +kernel
#guard plantClosedOnOpenEdge.findings ==
  ["G2 identity: cites G1 laws as required-closed, but it is required-open"]

-- P8: a closed cell on register rows cited `SEEDED`.
private def plantClosedOnSeededRows : Ledger :=
  { graphs := [withCell "G1" .counterexamples
      (closedOn [.rows ⟨"F-CE", 1, 2⟩ .seeded, .receipt "Landing"])] }
theorem plant_closedOnSeededRows : plantClosedOnSeededRows.wellFormed = false := by
  decide +kernel
#guard plantClosedOnSeededRows.findings ==
  ["G1 counterexamples: closed on rows that are not CLOSED"]

-- P9: a graph depending on itself.
private def plantSelfDependency : Ledger :=
  { graphs := [graphOf "G1" ["G1"]] }
theorem plant_selfDependency : plantSelfDependency.wellFormed = false := by
  decide +kernel
#guard plantSelfDependency.findings ==
  ["G1: depends on itself", "the graph dependencies have a cycle"]

-- P10: two graphs depending on each other.
private def plantMutualDependency : Ledger :=
  { graphs := [graphOf "G1" ["G2"], graphOf "G2" ["G1"]] }
theorem plant_mutualDependency : plantMutualDependency.wellFormed = false := by
  decide +kernel
#guard plantMutualDependency.findings == ["the graph dependencies have a cycle"]

-- P11: a leaf whose parent graph is unknown.
private def plantLeafUnknownParent : Ledger :=
  { graphs := [graphOf "G1"], leaves := [leafOf "L1" (some ("G9", .laws))] }
theorem plant_leafUnknownParent : plantLeafUnknownParent.wellFormed = false := by
  decide +kernel
#guard plantLeafUnknownParent.findings == ["leaf L1: unknown parent graph G9"]

-- P12: a leaf sharing a graph's identifier.
private def plantLeafSharesId : Ledger :=
  { graphs := [graphOf "G1"], leaves := [leafOf "G1"] }
theorem plant_leafSharesId : plantLeafSharesId.wellFormed = false := by
  decide +kernel
#guard plantLeafSharesId.findings == ["a leaf shares an identifier"]

-- P13 (R-W6): a closed cell that cites no ruling, no receipts-log heading
-- and no `CLOSED` rows, on theorem names alone.
private def plantClosedUnattested : Ledger :=
  { graphs := [withCell "G1" .laws
      (closedOn [.theorems [`Whatwg.Streams.Data.sizeSum_cons],
        .receipts `WhatwgTest.Streams.Data.QueueAxiomReport 99, .gate .build,
        .edge "G2" .laws]),
      graphOf "G2" [] (setCell allOpen .laws cc)] }
theorem plant_closedUnattested : plantClosedUnattested.wellFormed = false := by
  decide +kernel
#guard plantClosedUnattested.findings ==
  ["G1 laws: closed with no ruling, receipts-log heading or CLOSED rows"]

-- P14: a not-applicable cell with a ground other than a ruling.
private def plantNotApplicableWithGround : Ledger :=
  { graphs := [withCell "G1" .bridges (naOn "no host" [.receipt "Landing"])] }
theorem plant_notApplicableWithGround : plantNotApplicableWithGround.wellFormed = false := by
  decide +kernel
#guard plantNotApplicableWithGround.findings ==
  ["G1 bridges: not-applicable with an item or a ground other than a ruling"]

-- P15: an open item citing another graph's edge that is closed.
private def plantOpenOnClosedEdge : Ledger :=
  { graphs := [graphOf "G1" [] (setCell allOpen .trust cc),
      withCell "G2" .coverage (openOn [.edge "G1" .trust])] }
theorem plant_openOnClosedEdge : plantOpenOnClosedEdge.wellFormed = false := by
  decide +kernel
#guard plantOpenOnClosedEdge.findings ==
  ["G2 coverage: cites G1 trust as required-open, but it is required-closed"]

-- P16: a cross-graph reference to an unknown graph.
private def plantUnknownCrossGraph : Ledger :=
  { graphs := [withCell "G1" .bridges (openOn [.edge "G9" .bridges])] }
theorem plant_unknownCrossGraph : plantUnknownCrossGraph.wellFormed = false := by
  decide +kernel
#guard plantUnknownCrossGraph.findings == ["G1 bridges: unknown graph G9"]

-- P17: two leaves with one identifier.
private def plantDuplicateLeaf : Ledger :=
  { graphs := [graphOf "G1"], leaves := [leafOf "L1", leafOf "L1" (some ("G1", .laws))] }
theorem plant_duplicateLeaf : plantDuplicateLeaf.wellFormed = false := by
  decide +kernel
#guard plantDuplicateLeaf.findings == ["a leaf shares an identifier"]

-- Control C1: one well-formed graph.
private def controlOneGraph : Ledger := { graphs := [graphOf "G1"] }
theorem control_oneGraph : controlOneGraph.wellFormed = true := by
  decide +kernel
#guard controlOneGraph.findings == []

-- Control C2: two graphs, one depending on the other, with cross-graph
-- citations of the right status in both directions.
private def controlDependentGraphs : Ledger :=
  { graphs := [graphOf "G1" [] (setCell allOpen .trust cc),
      graphOf "G2" ["G1"]
        (setCell (setCell allOpen
          .trust (closedOn [.edge "G1" .trust, .ruling "R-X1"]))
          .laws (openOn [.edge "G1" .laws]))] }
theorem control_dependentGraphs : controlDependentGraphs.wellFormed = true := by
  decide +kernel
#guard controlDependentGraphs.findings == []

-- Control C3: each attestation alone suffices, and a not-applicable cell may
-- cite the ruling that made it so.
private def controlAttestations : Ledger :=
  { graphs := [graphOf "G1" []
      (setCell (setCell (setCell (setCell allOpen
        .identity (closedOn [.ruling "R-X1"]))
        .laws (closedOn [.receipt "Landing"]))
        .counterexamples (closedOn [.rows ⟨"F-CE", 1, 3⟩ .closed]))
        .targets (naOn "No generated code." [.ruling "R-X2"]))],
    leaves := [leafOf "L1" (some ("G1", .laws))] }
theorem control_attestations : controlAttestations.wellFormed = true := by
  decide +kernel
#guard controlAttestations.findings == []

/-! ### 3.1 The pieces of the structural check -/

#guard distinct ([] : List Nat)
#guard distinct [1, 2, 3]
#guard !distinct [1, 2, 1]
#guard Ground.discharges (.rows ⟨"F", 1, 1⟩ .closed)
#guard !Ground.discharges (.rows ⟨"F", 1, 1⟩ .seeded)
#guard Ground.discharges (.theorems [])
#guard Ground.discharges (.edge "G" .laws)
#guard Ground.attests (.ruling "R")
#guard Ground.attests (.receipt "Landing")
#guard Ground.attests (.rows ⟨"F", 1, 1⟩ .closed)
#guard !Ground.attests (.rows ⟨"F", 1, 1⟩ .seeded)
#guard !Ground.attests (.theorems [`a])
#guard !Ground.attests (.declarations [`a])
#guard !Ground.attests (.receipts `M 1)
#guard !Ground.attests (.ascriptions `M 1)
#guard !Ground.attests (.modules [`M])
#guard !Ground.attests (.gate .build)
#guard !Ground.attests (.edge "G" .laws)
#guard Cell.problem? oc == none
#guard Cell.problem? cc == none
#guard Cell.problem? { status := .notApplicable, note := "n" } == none
#guard Cell.problem? { status := .notApplicable, note := "n",
                       remaining := [.named "x"] } ==
  some "not-applicable with an item or a ground other than a ruling"
#guard controlDependentGraphs.statusOf? "G1" .trust == some .requiredClosed
#guard controlDependentGraphs.statusOf? "G1" .laws == some .requiredOpen
#guard controlDependentGraphs.statusOf? "G9" .laws == none
#guard Cell.crossReferences (openOn [.named "x", .edge "B" .laws] [.edge "A" .trust, .receipt "Landing"]) ==
  [("A", .trust, .requiredClosed), ("B", .laws, .requiredOpen)]
#guard Ledger.dependenciesAcyclic
  { graphs := [graphOf "C" ["B"], graphOf "B" ["A"], graphOf "A"] }
#guard !Ledger.dependenciesAcyclic
  { graphs := [graphOf "A", graphOf "B" ["C"], graphOf "C" ["D"], graphOf "D" ["B"]] }

/-! ## 4. The counting rule (R-W6, change 2)

An ascription is a `#check (@` or a `#whatwg_freeze (@` command; a receipt is
a `#print axioms` command or a `#whatwg_freeze` command with an `axioms`
clause. Commands are counted on the code lines of the module source: every
character of a comment (docstrings and module documentation included) and
every character inside a string, character or raw-string literal is blanked,
line breaks are kept, and a command counts only when it begins its line. -/

private def sp (n : Nat) : String := String.ofList (List.replicate n ' ')

#guard codeLines "a -- b\nc" == ["a" ++ sp 5, "c"]
#guard codeLines "x \"y z\" 'w' /- c\nd -/ e" ==
  ["x \"" ++ sp 3 ++ "\" ' ' " ++ sp 4, sp 5 ++ "e"]
#guard codeLines "/-- doc /- nested -/ still doc -/ t\n" == [sp 33 ++ " t"]
#guard codeLines "r#\"a\"b\"# c" == ["r#\"" ++ sp 3 ++ "\"# c"]
#guard codeLines "#print axioms a\r\n#print axioms b\r\n" ==
  ["#print axioms a", "#print axioms b"]

-- The `#print axioms` spelling.
#guard receiptCount "#print axioms a\n#print axioms b\n" == 2
#guard receiptCount "#print axioms a\r\n#print axioms b\r\n" == 2
#guard receiptCount
  "-- #print axioms a\n/- #print axioms b\n#print axioms c -/\n/-- doc\n#print axioms d -/\n#print axioms e\n" == 1
#guard receiptCount "/- outer /- inner -/\n#print axioms a\n-/\n#print axioms b\n" == 1
#guard receiptCount "/-! module doc\n#print axioms a\n-/\n#print axioms b\n" == 1
#guard receiptCount "#guard s == \"\n#print axioms a\"\n#print axioms b\n" == 1
#guard receiptCount "#guard s == \"/-\"\n#print axioms a\n" == 1
#guard receiptCount "#guard s == \"a\\\"/-\"\n#print axioms a\n" == 1
#guard receiptCount "#guard c == '\"'\n#print axioms a\n" == 1
#guard receiptCount "#guard c == '\\''\n#print axioms a\n" == 1
#guard receiptCount "#check f'.1 /- '\n#print axioms a\n-/\n" == 0
#guard receiptCount "#guard s == r#\"\n#print axioms a\n\"#\n#print axioms b\n" == 1
#guard receiptCount "  #print axioms a\n" == 0
#guard receiptCount "#check (@a : True)\n" == 0

-- The `#whatwg_freeze` spelling.
#guard receiptCount "#whatwg_freeze (@a : True) axioms []\n" == 1
#guard receiptCount "#whatwg_freeze (@a : True) axioms[]\n" == 1
#guard receiptCount "#whatwg_freeze (@a : True)\n" == 0
#guard receiptCount "#whatwg_freeze (@a : True) mask M1\n" == 0
#guard receiptCount "#whatwg_freeze (@a : True) axiomsX\n" == 0
#guard receiptCount "#whatwg_freeze (@a :\n  b = (c, d)) axioms [propext]\n" == 1
#guard receiptCount "#whatwg_freeze (@a : axioms = (x)) mask M1\n" == 0
#guard receiptCount "#whatwg_freeze (@a : f \")\" = 1) axioms []\n" == 1
#guard receiptCount "#whatwg_freeze (@a : True) -- note\n  axioms []\n" == 1
#guard receiptCount "#whatwg_freeze (@a : True)\n\n  axioms []\n" == 1
#guard receiptCount "#whatwg_freeze (@a : True)\n#check axioms\n" == 0
#guard receiptCount "/-\n#whatwg_freeze (@a : True) axioms []\n-/\n" == 0
#guard receiptCount
  "#print axioms a\n#whatwg_freeze (@b : True) axioms [propext]\n#whatwg_freeze (@c : True)\n" == 2

-- Ascriptions, in both spellings.
#guard ascriptionCount "#check (@a : True)\n#whatwg_freeze (@b : True) axioms []\n" == 2
#guard ascriptionCount
  "#check (@a : True)\n#check (a : True)\n#whatwg_freeze (@b : True)\n-- #check (@c : True)\n/-- #whatwg_freeze (@d : True) -/\n  #check (@e : True)\n" == 2
#guard ascriptionCount "#print axioms a\n" == 0
#guard ascriptionCount "/-\n#check (@a : True)\n-/\n#guard s == \"\n#check (@b : True)\"\n" == 0

#guard sourcePath `WhatwgTest.Streams.Data.QueueAxiomReport ==
  "WhatwgTest/Streams/Data/QueueAxiomReport.lean"
#guard sourcePath `WhatwgTest == "WhatwgTest.lean"

/-! ## 5. Edge tokens and the mention check -/

#guard rulingId? "- R-W6 (W7: the graph ledger). Adopted as designed" == some "R-W6"
#guard rulingId? "- R-P3 Ids: ES2026 row ids" == some "R-P3"
#guard rulingId? "- Lane W debts (2026-10-01): (D57) `Whatwg/Html`" == none
#guard rulingId? "  - R-W6 indented" == none
#guard codeSpans "a `b` c `d` e" == ["b", "d"]
#guard parseStatus? "required-open" == some .requiredOpen
#guard parseStatus? "required-closed" == some .requiredClosed
#guard parseStatus? "not-applicable" == some .notApplicable
#guard parseStatus? "closed" == none

#guard edgeTokens
  ["- R-T9 sets `TEST-PG-ONE/laws=required-open` and `X-PG-TWO/trust=not-applicable`."] ==
  [⟨"R-T9", "TEST-PG-ONE", .laws, .requiredOpen⟩, ⟨"R-T9", "X-PG-TWO", .trust, .notApplicable⟩]
-- Not a ruling bullet, so not a token.
#guard edgeTokens ["Note: `TEST-PG-ONE/laws=required-open`."] == []
#guard edgeTokens ["  - R-T9 `TEST-PG-ONE/laws=required-open`."] == []
-- The grammar's own spelling, an unknown status and an unknown edge.
#guard edgeTokens
  ["- R-W6 writes `GRAPH-ID/edge=status` as a code span.",
   "- R-T9 `TEST-PG-ONE/laws=closed` `TEST-PG-ONE/law=required-open` `TEST-PG-ONE/laws=required-open=x`."] == []
-- Latest wins: a later ruling supersedes an earlier one for the same edge.
#guard latestTokens
  [⟨"R-T8", "A", .laws, .requiredOpen⟩, ⟨"R-T8", "A", .trust, .requiredOpen⟩,
   ⟨"R-T9", "A", .laws, .requiredClosed⟩] ==
  [⟨"R-T8", "A", .trust, .requiredOpen⟩, ⟨"R-T9", "A", .laws, .requiredClosed⟩]

/-! ## 6. The reference pass over planted worlds

The fixture is one graph, `TEST-PG-ONE`, with every ground and item kind,
one leaf and one unrouted prefix, in a world whose files and constants make
every reference resolve. Each plant changes one thing. -/

private def worldOf (constants : List (Lean.Name × ConstantKind)) (modules : List Lean.Name)
    (files : List (String × String)) (projections : List String) : World where
  constantKind? n := constants.lookup n
  moduleBuilt m := modules.contains m
  file? p := files.lookup p
  projectionFiles := projections

private def withFile (w : World) (path text : String) : World :=
  { w with file? := fun p => if p == path then some text else w.file? p }

private def withoutFile (w : World) (path : String) : World :=
  { w with file? := fun p => if p == path then none else w.file? p }

private def withConstant (w : World) (n : Lean.Name) (k : ConstantKind) : World :=
  { w with constantKind? := fun m => if m == n then some k else w.constantKind? m }

private def withModule (w : World) (m : Lean.Name) : World :=
  { w with moduleBuilt := fun x => x == m || w.moduleBuilt x }

private def fixGraph : Graph where
  id := "TEST-PG-ONE"
  document := "docs/ONE-DAG.md"
  fence := [`Fix.Mod]
  edges := {
    identity :=
      { status := .requiredClosed, grounds := [.theorems [`Fix.thm1], .receipt "Landing"] }
    construction :=
      { status := .requiredClosed, grounds := [.receipts `Fix.Report 2, .ruling "R-T1"] }
    semantics :=
     
    (closedOn [.declarations [`Fix.def1], .modules [`Fix.Mod], .receipt "Landing"])
    laws :=
     
    (closedOn [.ascriptions `Fix.Battery 2, .gate .citations, .receipt "Landing"])
    representation :=
      { status := .requiredOpen, grounds := [.receipt "Landing"],
        remaining := [.named "a stable address", .debt "D1",
          .rows ⟨"FIX-CE", 3, 3⟩ .seeded, .wanted `Fix.later] }
    counterexamples :=
      { status := .requiredClosed, grounds := [.rows ⟨"FIX-CE", 1, 2⟩ .closed] }
    bridges := { status := .notApplicable, note := "No host relation is claimed." }
    targets :=
      { status := .notApplicable, grounds := [.ruling "R-T1"], note := "No generated code." }
    trust :=
      { status := .requiredClosed, grounds := [.gate .build, .receipt "Landing"],
        debts := ["D1"] }
    coverage := { status := .requiredOpen, remaining := [.named "the coverage rows"] } }

private def fixLeaf : Leaf where
  id := "TEST-LF-ONE"
  document := "docs/ONE-LEAF.md"
  declarations := [`Fix.def1]
  parent := none
  receipts := [.theorems [`Fix.thm1], .rows ⟨"FIX-CE", 1, 1⟩ .closed]

private def fixLedger : Ledger :=
  { graphs := [fixGraph], leaves := [fixLeaf], unrouted := [⟨`Fix.Mod2, "D1"⟩] }

private def ledgerWith (g : Graph) : Ledger := { fixLedger with graphs := [g] }

private def withEdge (e : Edge) (c : Cell) : Graph :=
  { fixGraph with edges := setCell fixGraph.edges e c }

private def fixCoordination : String :=
  "# Coordination\n\n- R-T1 (fixture ruling) moves nothing.\n- Fixture debts: (D1) a debt.\n"

private def coordinationWith (extra : List String) : String :=
  fixCoordination ++ String.intercalate "\n" extra ++ "\n"

private def fixWorld : World :=
  worldOf [(`Fix.thm1, .thm), (`Fix.thm2, .thm), (`Fix.def1, .other)]
    [`Fix.Mod, `Fix.Mod2, `Fix.Report, `Fix.Battery]
    [("COORDINATION.md", fixCoordination),
     ("test/counterexamples/REGISTER.md",
      "| ID | Status | Statement |\n| --- | --- | --- |\n| `FIX-CE-001` | `CLOSED` | a |\n| `FIX-CE-002` | `CLOSED` | b |\n| `FIX-CE-003` | `SEEDED` | c |\n"),
     ("lakefile.toml", "[[lean_exe]]\nname = \"whatwg_citations\"\nroot = \"whatwgbin.Citations\"\n"),
     ("docs/ONE-DAG.md",
      "# One graph\n\n## Current state\n\nSee `generated/graphs/TEST-PG-ONE.md`.\n\n| `P9-R1` | a document ruling |\n"),
     ("docs/receipts/TEST-PG-ONE.md",
      "# Receipts log of `TEST-PG-ONE`\n\n## Landing (fixture, 2026-10-01)\n\n### Verification\n"),
     ("generated/graphs/TEST-PG-ONE.md", fixGraph.render ledgerInput),
     ("Fix/Report.lean",
      "/-! Receipts. -/\n#print axioms Fix.thm1\n-- #print axioms Fix.old\n#print axioms Fix.thm2\n"),
     ("Fix/Battery.lean",
      "#check (@Fix.thm1 : True)\n#whatwg_freeze (@Fix.thm2 :\n  True) axioms []\n/-- #check (@Fix.old : True) -/\n#check (Fix.def1 : Nat)\n"),
     ("docs/ONE-LEAF.md", "# Leaf `TEST-LF-ONE`\n")]
    ["generated/graphs/TEST-PG-ONE.md"]

-- The fixture itself: structurally well formed, every reference resolves,
-- the projection is current.
theorem fixture_wellFormed : fixLedger.wellFormed = true := by
  decide +kernel
#guard referenceFindings fixWorld fixLedger == []
#guard projectionFindings fixWorld fixLedger == []

/-! ### 6.1 Edge tokens against the ledger (LEDGER-CE-001) -/

-- A ruling records a status the ledger does not hold, and the cell does not
-- cite it; the ruling also names the graph.
#guard referenceFindings
  (withFile fixWorld "COORDINATION.md"
    (coordinationWith ["- R-T9 sets `TEST-PG-ONE/laws=required-open`."])) fixLedger ==
  ["ruling R-T9 records TEST-PG-ONE/laws=required-open; the ledger says required-closed",
   "ruling R-T9 records TEST-PG-ONE/laws; that cell does not cite it",
   "TEST-PG-ONE: ruling R-T9 names this graph and the ledger neither cites nor acknowledges it"]

-- The status agrees but the cell does not cite the ruling.
#guard tokenFindings fixLedger
  (edgeTokens ["- R-T9 sets `TEST-PG-ONE/laws=required-closed`."]) ==
  ["ruling R-T9 records TEST-PG-ONE/laws; that cell does not cite it"]

-- The status agrees and the cell cites the ruling: no finding at all.
#guard referenceFindings
  (withFile fixWorld "COORDINATION.md"
    (coordinationWith ["- R-T9 sets `TEST-PG-ONE/laws=required-closed`."]))
  (ledgerWith (withEdge .laws
    (closedOn [.ascriptions `Fix.Battery 2, .gate .citations, .ruling "R-T9"]))) == []

-- A token naming a graph the ledger does not hold.
#guard referenceFindings
  (withFile fixWorld "COORDINATION.md"
    (coordinationWith ["- R-T9 sets `NO-PG-SUCH/laws=required-open`."])) fixLedger ==
  ["ruling R-T9 names NO-PG-SUCH/laws, which is not in the ledger"]

-- Latest wins: R-T9 supersedes R-T8 for the same edge.
#guard tokenFindings
  (ledgerWith (withEdge .laws
    (closedOn [.ascriptions `Fix.Battery 2, .ruling "R-T9"])))
  (edgeTokens ["- R-T8 sets `TEST-PG-ONE/laws=required-open`.",
               "- R-T9 sets `TEST-PG-ONE/laws=required-closed`."]) == []
#guard tokenFindings
  (ledgerWith (withEdge .laws
    (closedOn [.ascriptions `Fix.Battery 2, .ruling "R-T9"])))
  (edgeTokens ["- R-T9 sets `TEST-PG-ONE/laws=required-closed`.",
               "- R-T8 sets `TEST-PG-ONE/laws=required-open`."]) ==
  ["ruling R-T8 records TEST-PG-ONE/laws=required-open; the ledger says required-closed",
   "ruling R-T8 records TEST-PG-ONE/laws; that cell does not cite it"]

-- A not-applicable cell cites the ruling that set it.
#guard tokenFindings fixLedger
  (edgeTokens ["- R-T1 sets `TEST-PG-ONE/targets=not-applicable`."]) == []

/-! ### 6.2 The mention check -/

#guard rulingMentions
  ["- R-T6 reviews TEST-PG-ONE.", "- R-T7 edits docs/ONE-DAG.md.",
   "Not a ruling: TEST-PG-ONE.", "- R-T8 names nothing."] [fixGraph] ==
  [("R-T6", "TEST-PG-ONE"), ("R-T7", "TEST-PG-ONE")]
#guard fixGraph.citedRulings == ["R-T1", "R-T1"]
#guard { fixGraph with acknowledged := ["R-T6"] }.citedRulings == ["R-T6", "R-T1", "R-T1"]

-- A ruling names the graph by identifier and the ledger does not cite it.
#guard referenceFindings
  (withFile fixWorld "COORDINATION.md"
    (coordinationWith ["- R-T6 reviews TEST-PG-ONE and changes nothing."])) fixLedger ==
  ["TEST-PG-ONE: ruling R-T6 names this graph and the ledger neither cites nor acknowledges it"]

-- The same, by document path.
#guard referenceFindings
  (withFile fixWorld "COORDINATION.md"
    (coordinationWith ["- R-T6 edits docs/ONE-DAG.md."])) fixLedger ==
  ["TEST-PG-ONE: ruling R-T6 names this graph and the ledger neither cites nor acknowledges it"]

-- Acknowledged, so no finding.
#guard referenceFindings
  (withFile fixWorld "COORDINATION.md"
    (coordinationWith ["- R-T6 reviews TEST-PG-ONE and changes nothing."]))
  (ledgerWith { fixGraph with acknowledged := ["R-T6"] }) == []

/-! ### 6.3 Ground kinds -/

-- A receipt count off by one, `#print axioms` spelling.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .construction
    (closedOn [.receipts `Fix.Report 3, .ruling "R-T1"]))) ==
  ["TEST-PG-ONE construction: Fix.Report holds 2 receipts, not 3"]

-- A receipt count off by one, `#whatwg_freeze … axioms` spelling.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .construction
    (closedOn [.receipts `Fix.Battery 2, .ruling "R-T1"]))) ==
  ["TEST-PG-ONE construction: Fix.Battery holds 1 receipts, not 2"]

-- An ascription count off by one, both spellings in one module.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .laws
    (closedOn [.ascriptions `Fix.Battery 3, .receipt "Landing"]))) ==
  ["TEST-PG-ONE laws: Fix.Battery holds 2 ascriptions, not 3"]

-- An ascription count off by one, `#whatwg_freeze` spelling alone.
#guard referenceFindings
  (withModule (withFile fixWorld "Fix/Freezes.lean"
    "#whatwg_freeze (@Fix.thm1 : True) axioms []\n#whatwg_freeze (@Fix.thm2 : True)\n")
    `Fix.Freezes)
  (ledgerWith (withEdge .laws
    (closedOn [.ascriptions `Fix.Freezes 1, .receipts `Fix.Freezes 1, .receipt "Landing"]))) ==
  ["TEST-PG-ONE laws: Fix.Freezes holds 2 ascriptions, not 1"]

-- A count on a module that is not built, and on a built module with no source.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .construction
    (closedOn [.receipts `Fix.Gone 1, .ruling "R-T1"]))) ==
  ["TEST-PG-ONE construction: Fix.Gone is not a built module"]
#guard referenceFindings (withModule fixWorld `Fix.Nosource)
  (ledgerWith (withEdge .construction
    (closedOn [.ascriptions `Fix.Nosource 1, .ruling "R-T1"]))) ==
  ["TEST-PG-ONE construction: Fix.Nosource has no source Fix/Nosource.lean"]

-- A ruling that is recorded nowhere.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .construction
    (closedOn [.receipts `Fix.Report 2, .ruling "R-T7"]))) ==
  ["TEST-PG-ONE construction: ruling R-T7 is not recorded"]

-- A ruling recorded in the graph document's rulings table.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .construction
    (closedOn [.receipts `Fix.Report 2, .ruling "P9-R1"]))) == []

-- A theorem ground naming no constant (LEDGER-CE-002), and one naming a
-- constant that is not a theorem.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .identity
    (closedOn [.theorems [`Fix.gone], .receipt "Landing"]))) ==
  ["TEST-PG-ONE identity: Fix.gone names no constant"]
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .identity
    (closedOn [.theorems [`Fix.def1], .receipt "Landing"]))) ==
  ["TEST-PG-ONE identity: Fix.def1 is not a theorem"]

-- A declaration ground naming no constant; a module ground naming no module.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .semantics
    (closedOn [.declarations [`Fix.gone], .modules [`Fix.Gone], .receipt "Landing"]))) ==
  ["TEST-PG-ONE semantics: Fix.gone names no constant",
   "TEST-PG-ONE semantics: Fix.Gone is not a built module"]

-- Register rows: one with another status, one that does not exist.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .counterexamples
    (closedOn [.rows ⟨"FIX-CE", 1, 4⟩ .closed]))) ==
  ["TEST-PG-ONE counterexamples: register row FIX-CE-003 is SEEDED, not CLOSED",
   "TEST-PG-ONE counterexamples: register row FIX-CE-004 does not exist"]

-- A receipts-log heading that does not exist; one at level three, which
-- resolves; and the log's title, which is not a heading the rule reads.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .identity
    (closedOn [.theorems [`Fix.thm1], .receipt "Second landing"]))) ==
  ["TEST-PG-ONE identity: receipts log has no heading \"Second landing\""]
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .identity
    (closedOn [.theorems [`Fix.thm1], .receipt "Verification"]))) == []
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .identity
    (closedOn [.theorems [`Fix.thm1], .receipt "Receipts log"]))) ==
  ["TEST-PG-ONE identity: receipts log has no heading \"Receipts log\""]

-- A gate whose executable `lakefile.toml` does not declare (LEDGER-CE-003),
-- and the two gates that need no executable.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .laws
    (closedOn [.ascriptions `Fix.Battery 2, .gate .urlcensus, .gate (.census "streams"),
      .gate .leanchecker, .gate .build, .receipt "Landing"]))) ==
  ["TEST-PG-ONE laws: executable whatwg_urlcensus is not declared in lakefile.toml",
   "TEST-PG-ONE laws: executable whatwg_census is not declared in lakefile.toml"]

-- R-W6's attestation rule, as the executable reports it.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .identity
    (closedOn [.theorems [`Fix.thm1]]))) ==
  ["TEST-PG-ONE identity: closed with no ruling, receipts-log heading or CLOSED rows"]

/-! ### 6.4 Item kinds and recorded debts -/

-- A wanted theorem that now exists, as a theorem and as any other constant.
#guard referenceFindings (withConstant fixWorld `Fix.later .thm) fixLedger ==
  ["TEST-PG-ONE representation: wanted theorem Fix.later now exists; review the edge"]
#guard referenceFindings (withConstant fixWorld `Fix.later .other) fixLedger ==
  ["TEST-PG-ONE representation: wanted theorem Fix.later now exists; review the edge"]

-- A debt item and a recorded debt that `COORDINATION.md` does not carry.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .representation (openOn [.debt "D99"] [.receipt "Landing"]))) ==
  ["TEST-PG-ONE representation: debt D99 is not recorded"]
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .trust
    (closedOn [.gate .build, .receipt "Landing"] ["D98"]))) ==
  ["TEST-PG-ONE trust: debt D98 is not recorded"]

-- Open register rows with another status; an open item with no name.
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .representation (openOn [.rows ⟨"FIX-CE", 1, 1⟩ .seeded]))) ==
  ["TEST-PG-ONE representation: register row FIX-CE-001 is CLOSED, not SEEDED"]
#guard referenceFindings fixWorld
  (ledgerWith (withEdge .coverage (openOn [.named ""]))) ==
  ["TEST-PG-ONE coverage: an open item has no name"]

/-! ### 6.5 The graph's own files -/

#guard referenceFindings (withoutFile fixWorld "docs/ONE-DAG.md") fixLedger ==
  ["TEST-PG-ONE: document docs/ONE-DAG.md does not exist"]
#guard referenceFindings (withFile fixWorld "docs/ONE-DAG.md" "# One graph\n") fixLedger ==
  ["TEST-PG-ONE: document docs/ONE-DAG.md does not link generated/graphs/TEST-PG-ONE.md"]
#guard referenceFindings (withoutFile fixWorld "docs/receipts/TEST-PG-ONE.md") fixLedger ==
  ["TEST-PG-ONE: receipts log docs/receipts/TEST-PG-ONE.md does not exist",
   "TEST-PG-ONE identity: receipts log has no heading \"Landing\"",
   "TEST-PG-ONE semantics: receipts log has no heading \"Landing\"",
   "TEST-PG-ONE laws: receipts log has no heading \"Landing\"",
   "TEST-PG-ONE representation: receipts log has no heading \"Landing\"",
   "TEST-PG-ONE trust: receipts log has no heading \"Landing\""]
#guard referenceFindings fixWorld (ledgerWith { fixGraph with fence := [`Fix.Gone] }) ==
  ["TEST-PG-ONE: fence module Fix.Gone is not a built module"]

-- Without `COORDINATION.md`, no ruling and no debt resolves.
#guard referenceFindings (withoutFile fixWorld "COORDINATION.md") fixLedger ==
  ["TEST-PG-ONE construction: ruling R-T1 is not recorded",
   "TEST-PG-ONE representation: debt D1 is not recorded",
   "TEST-PG-ONE targets: ruling R-T1 is not recorded",
   "TEST-PG-ONE trust: debt D1 is not recorded",
   "unrouted Fix.Mod2: D1 is not a recorded debt or ruling"]

-- Without the register, no row resolves.
#guard referenceFindings (withoutFile fixWorld "test/counterexamples/REGISTER.md") fixLedger ==
  ["TEST-PG-ONE representation: register row FIX-CE-003 does not exist",
   "TEST-PG-ONE counterexamples: register row FIX-CE-001 does not exist",
   "TEST-PG-ONE counterexamples: register row FIX-CE-002 does not exist",
   "TEST-LF-ONE: register row FIX-CE-001 does not exist"]

/-! ### 6.6 Leaf records -/

#guard referenceFindings (withFile fixWorld "docs/ONE-LEAF.md" "# A leaf\n") fixLedger ==
  ["TEST-LF-ONE: document docs/ONE-LEAF.md does not name the leaf"]
#guard referenceFindings (withoutFile fixWorld "docs/ONE-LEAF.md") fixLedger ==
  ["TEST-LF-ONE: document docs/ONE-LEAF.md does not exist"]
#guard referenceFindings fixWorld
  { fixLedger with leaves := [{ fixLeaf with declarations := [`Fix.gone] }] } ==
  ["TEST-LF-ONE: Fix.gone names no constant"]
#guard referenceFindings fixWorld
  { fixLedger with leaves := [{ fixLeaf with receipts := [.theorems [`Fix.def1]] }] } ==
  ["TEST-LF-ONE: Fix.def1 is not a theorem"]

/-! ### 6.7 Unrouted prefixes (debt D57) -/

#guard referenceFindings fixWorld { fixLedger with unrouted := [⟨`Fix.Mod2, "D97"⟩] } ==
  ["unrouted Fix.Mod2: D97 is not a recorded debt or ruling"]
#guard referenceFindings fixWorld { fixLedger with unrouted := [⟨`Fix.Gone, "D1"⟩] } ==
  ["unrouted Fix.Gone: not a built module"]
#guard referenceFindings fixWorld { fixLedger with unrouted := [⟨`Fix.Mod2, "R-T1"⟩] } == []

/-! ### 6.8 The pieces of the reference pass -/

#guard fixWorld.linesOf "docs/ONE-LEAF.md" == ["# Leaf `TEST-LF-ONE`"]
#guard fixWorld.linesOf "absent.md" == []
#guard rulingPresent fixWorld [] "R-T1"
#guard !rulingPresent fixWorld [] "R-T"
#guard rulingPresent fixWorld ["| `P9-R1` | a document ruling |"] "P9-R1"
#guard debtPresent fixWorld "D1"
#guard !debtPresent fixWorld "D"
#guard rowStatus? fixWorld "FIX-CE-001" == some "CLOSED"
#guard rowStatus? fixWorld "FIX-CE-003" == some "SEEDED"
#guard rowStatus? fixWorld "FIX-CE-00" == none
#guard rowFindings fixWorld ⟨"FIX-CE", 2, 3⟩ .closed ==
  ["register row FIX-CE-003 is SEEDED, not CLOSED"]
#guard groundFindings fixWorld [] [] (.edge "G" .laws) == []
#guard itemFindings fixWorld (.edge "G" .laws) == []
#guard itemFindings fixWorld (.named "x") == []
#guard graphFindings fixWorld fixLedger fixGraph == []
#guard leafFindings fixWorld fixLeaf == []
#guard unroutedFindings fixWorld ⟨`Fix.Mod2, "D1"⟩ == []

/-! ## 7. The projection -/

#guard formatVersion == 1
#guard code "x" == "`x`"
#guard joinAnd [] == ""
#guard joinAnd ["a"] == "a"
#guard joinAnd ["a", "b"] == "a and b"
#guard joinAnd ["a", "b", "c"] == "a, b and c"
#guard ledgerInput == "`WhatwgTest/Ledger.lean`"

#guard Ground.render (.theorems [`A.t, `A.u]) == "theorems `A.t` and `A.u`"
#guard Ground.render (.declarations [`A.d]) == "declarations `A.d`"
#guard Ground.render (.receipts `A.R 3) == "3 receipts of `A.R`"
#guard Ground.render (.ascriptions `A.C 2) == "2 ascriptions of `A.C`"
#guard Ground.render (.modules [`A.M, `A.N]) == "modules `A.M` and `A.N`"
#guard Ground.render (.gate (.census "streams")) ==
  "`lake exe whatwg_census --standard streams`"
#guard Ground.render (.ruling "R-1") == "ruling R-1"
#guard Ground.render (.receipt "Landing") == "receipt \"Landing\""
#guard Ground.render (.rows ⟨"X-CE", 1, 2⟩ .closed) == "`X-CE-001` to `X-CE-002` `CLOSED`"
#guard Ground.render (.rows ⟨"X-CE", 4, 4⟩ .closed) == "`X-CE-004` `CLOSED`"
#guard Ground.render (.edge "TEST-PG-Q" .trust) == "`TEST-PG-Q` trust closed"
#guard Item.render (.named "x") == "x"
#guard Item.render (.debt "D3") == "debt D3"
#guard Item.render (.rows ⟨"X-CE", 3, 3⟩ .seeded) == "`X-CE-003` `SEEDED`"
#guard Item.render (.wanted `A.w) == "wanted `A.w`"
#guard Item.render (.edge "TEST-PG-Q" .laws) == "`TEST-PG-Q` laws (open)"

private def naCell : Cell := { status := .notApplicable, note := "n" }

private def renderGraph : Graph where
  id := "TEST-PG-R"
  document := "docs/R.md"
  fence := [`A.B]
  dependsOn := ["TEST-PG-Q"]
  edges := {
    identity :=
      { status := .requiredClosed, note := "Note.", debts := ["D1", "D2"],
        grounds := [.theorems [`A.t], .receipts `A.R 3, .rows ⟨"X-CE", 1, 2⟩ .closed,
          .gate (.census "streams"), .ruling "R-1", .receipt "Landing"] }
    construction :=
      { status := .requiredOpen, grounds := [.receipt "Landing"],
        remaining := [.named "x", .debt "D3", .wanted `A.w, .edge "TEST-PG-Q" .laws] }
    semantics := naCell
    laws := naCell
    representation := naCell
    counterexamples := naCell
    bridges := naCell
    targets := { status := .notApplicable, grounds := [.ruling "R-2"], note := "n" }
    trust := naCell
    coverage := naCell }

#guard renderGraph.render ledgerInput == String.intercalate "\n"
  ["<!-- GENERATED by `lake exe whatwg_ledger --write` (Gates.Ledger, format 1) from `WhatwgTest/Ledger.lean`; do not edit. -->",
   "",
   "# Current state of `TEST-PG-R`",
   "",
   "Graph document: `docs/R.md`. Receipts log: `docs/receipts/TEST-PG-R.md`.",
   "Fence: `A.B`.",
   "Depends on: `TEST-PG-Q`.",
   "",
   "| Edge | Status | Ground |",
   "| --- | --- | --- |",
   "| identity | `required-closed` | Note. Closed on: theorems `A.t`; 3 receipts of `A.R`; `X-CE-001` to `X-CE-002` `CLOSED`; `lake exe whatwg_census --standard streams`; ruling R-1; receipt \"Landing\". Debts recorded: D1 and D2. |",
   "| construction | `required-open` | Open: x; debt D3; wanted `A.w`; `TEST-PG-Q` laws (open). Discharged: receipt \"Landing\". |",
   "| semantics | `not-applicable` | n |",
   "| laws | `not-applicable` | n |",
   "| representation | `not-applicable` | n |",
   "| counterexamples | `not-applicable` | n |",
   "| bridges | `not-applicable` | n |",
   "| targets | `not-applicable` | n Recorded by: ruling R-2. |",
   "| trust | `not-applicable` | n |",
   "| coverage | `not-applicable` | n |"] ++ "\n"

#guard (((graphOf "TEST-PG-E").render ledgerInput).splitOn "\n").take 7 ==
  ["<!-- GENERATED by `lake exe whatwg_ledger --write` (Gates.Ledger, format 1) from `WhatwgTest/Ledger.lean`; do not edit. -->",
   "", "# Current state of `TEST-PG-E`", "",
   "Graph document: `docs/X.md`. Receipts log: `docs/receipts/TEST-PG-E.md`.",
   "Fence: none.", "Depends on: none."]

-- Drift: a projection that differs, one that is missing, one checked out
-- with CRLF line ends, and a file under `generated/graphs/` that no graph
-- renders.
#guard projectionFindings
  (withFile fixWorld "generated/graphs/TEST-PG-ONE.md" "stale\n") fixLedger ==
  ["generated/graphs/TEST-PG-ONE.md differs from a fresh rendering"]
#guard projectionFindings
  (withFile fixWorld "generated/graphs/TEST-PG-ONE.md"
    ((fixGraph.render ledgerInput).replace "\n" "\r\n")) fixLedger ==
  ["generated/graphs/TEST-PG-ONE.md differs from a fresh rendering"]
#guard projectionFindings (withoutFile fixWorld "generated/graphs/TEST-PG-ONE.md") fixLedger ==
  ["generated/graphs/TEST-PG-ONE.md does not exist"]
#guard projectionFindings
  { fixWorld with projectionFiles := ["generated/graphs/OLD-PG-GONE.md",
      "generated/graphs/TEST-PG-ONE.md"] } fixLedger ==
  ["generated/graphs/OLD-PG-GONE.md is not the projection of a ledger graph"]
-- A graph whose cell changed is drift until the projection is regenerated.
#guard projectionFindings fixWorld
  (ledgerWith (withEdge .coverage (openOn [.named "the coverage rows", .named "a second item"]))) ==
  ["generated/graphs/TEST-PG-ONE.md differs from a fresh rendering"]

/-! ### 7.1 The run-time file set -/

#guard fixLedger.files ==
  ["COORDINATION.md", "test/counterexamples/REGISTER.md", "lakefile.toml",
   "docs/ONE-DAG.md", "docs/receipts/TEST-PG-ONE.md", "generated/graphs/TEST-PG-ONE.md",
   "Fix/Report.lean", "Fix/Battery.lean", "docs/ONE-LEAF.md"]
#guard ({ graphs := [] } : Ledger).files ==
  ["COORDINATION.md", "test/counterexamples/REGISTER.md", "lakefile.toml"]

/-! ## 8. The outcome of a run -/

private def passLine : String :=
  "PASS whatwg_ledger: 1 graph(s), 10 edges, 1 leaf record(s), 1 unrouted prefix(es); every reference resolves against the built environment and the authored files, and every projection is byte-identical to a fresh rendering"

#guard outcome fixWorld fixLedger false == ⟨0, [passLine], []⟩
#guard outcome fixWorld fixLedger true ==
  ⟨0, [passLine ++ " (written)"],
    [("generated/graphs/TEST-PG-ONE.md", fixGraph.render ledgerInput)]⟩
-- `--write` does not compare projections, so a stale one is rewritten.
#guard outcome (withFile fixWorld "generated/graphs/TEST-PG-ONE.md" "stale\n") fixLedger true ==
  ⟨0, [passLine ++ " (written)"],
    [("generated/graphs/TEST-PG-ONE.md", fixGraph.render ledgerInput)]⟩
-- Findings: exit code 1, every finding printed, nothing written.
#guard outcome (withFile fixWorld "generated/graphs/TEST-PG-ONE.md" "stale\n") fixLedger false ==
  ⟨1, ["FAIL whatwg_ledger: 1 finding(s)",
       "  generated/graphs/TEST-PG-ONE.md differs from a fresh rendering"], []⟩
#guard outcome (withoutFile fixWorld "docs/ONE-LEAF.md")
  { fixLedger with unrouted := [⟨`Fix.Gone, "D1"⟩] } true ==
  ⟨1, ["FAIL whatwg_ledger: 2 finding(s)",
       "  TEST-LF-ONE: document docs/ONE-LEAF.md does not exist",
       "  unrouted Fix.Gone: not a built module"], []⟩
#guard outcome (withoutFile fixWorld "generated/graphs/TEST-PG-ONE.md")
  (ledgerWith (withEdge .identity
    (closedOn [.theorems [`Fix.thm1]]))) false ==
  ⟨1, ["FAIL whatwg_ledger: 2 finding(s)",
       "  TEST-PG-ONE identity: closed with no ruling, receipts-log heading or CLOSED rows",
       "  generated/graphs/TEST-PG-ONE.md does not exist"], []⟩

end WhatwgTest.Audit.LedgerContract
