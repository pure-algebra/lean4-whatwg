import WhatwgGates.Ledger.Model
import WhatwgGates.Ledger.Render
import WhatwgGates.Ledger.Check
import WhatwgTest.Ledger
import WhatwgTest.Audit.Freeze

/-!
# WhatwgTest.Audit.LedgerRoutingContract

Frozen battery of addendum D, "Module routing and the index (slice D)", of
`test/contracts/graph-ledger.contract.md` (rulings R-W6, R-W11 and R-W18), by
the slice D breaker seat of review lane W, 2026-10-01, on branch
`review/w7-ledger-d-breaker` from `fc0b9fb`. The addendum states what module
routing and the index mean; this module is the authority on names and
propositions.

1. Exact ascriptions of every declaration slice D adds to
   `WhatwgGates.Ledger.Render` and `WhatwgGates.Ledger.Check`.
2. The slice D data: the thirteen unrouted prefixes of debt D57 and the six
   fence entries that `CONFIGURATION-PG-ORDERING` gains.
3. Rule M: which modules of a planted module table must be routed.
4. Claims: a fence entry claims one module exactly, a leaf record the
   declaring modules of its declarations, an unrouted prefix every module it
   is a component-wise prefix of.
5. The routing findings over planted module tables, one plant per finding and
   the controls that are accepted (rows `LEDGER-CE-006` to `LEDGER-CE-009`).
6. The index projection: its exact bytes on planted ledgers.
7. The routed run: the stray-file exemption of the index, its drift findings,
   the run-time file set, the order of the findings, and the outcome.

Nothing here does IO and nothing here declares syntax: every helper below is
`private`, and every check runs over planted data with `#guard`.
-/

namespace WhatwgTest.Audit.LedgerRoutingContract

open Gates.Ledger

/-! ## 1. Signatures -/

#whatwg_freeze (@Gates.Ledger.productionRoot : Lean.Name)
#whatwg_freeze (@Gates.Ledger.ModuleTable : Type)
#whatwg_freeze (@Gates.Ledger.ModuleTable.mk :
  List (Lean.Name × List Lean.Name) → Gates.Ledger.ModuleTable)
#whatwg_freeze (@Gates.Ledger.ModuleTable.modules :
  Gates.Ledger.ModuleTable → List (Lean.Name × List Lean.Name))
#whatwg_freeze (@Gates.Ledger.ModuleTable.mustRoute : Gates.Ledger.ModuleTable → List Lean.Name)
#whatwg_freeze (@Gates.Ledger.ModuleTable.declaringModule? :
  Gates.Ledger.ModuleTable → Lean.Name → Option Lean.Name)
#whatwg_freeze (@Gates.Ledger.Ledger.claimsOn : Gates.Ledger.ModuleTable → Gates.Ledger.Ledger →
  Lean.Name → List (String × String))
#whatwg_freeze (@Gates.Ledger.routingFindings :
  Gates.Ledger.ModuleTable → Gates.Ledger.Ledger → List String)
#whatwg_freeze (@Gates.Ledger.indexPath : String)
#whatwg_freeze (@Gates.Ledger.Graph.countStatus : Gates.Ledger.Graph → Gates.Ledger.Status → Nat)
#whatwg_freeze (@Gates.Ledger.Ledger.renderIndex : Gates.Ledger.Ledger → String → String)
#whatwg_freeze (@Gates.Ledger.indexFindings : Gates.Ledger.World → Gates.Ledger.Ledger → List String)
#whatwg_freeze (@Gates.Ledger.Ledger.runFiles : Gates.Ledger.Ledger → List String)
#whatwg_freeze (@Gates.Ledger.routedOutcome : Gates.Ledger.World → Gates.Ledger.ModuleTable →
  Gates.Ledger.Ledger → Bool → Gates.Ledger.Outcome)

#check (inferInstance : DecidableEq Gates.Ledger.ModuleTable)
#check (inferInstance : Repr Gates.Ledger.ModuleTable)

#guard ({ modules := [] } : ModuleTable) == ⟨[]⟩
#guard productionRoot == `Whatwg
#guard indexPath == "generated/graphs/INDEX.md"

/-! ## 2. The slice D data

The thirteen unrouted prefixes of debt D57, in the order of the contract's
section 12, are exactly the ledger's entries that cite `D57`. The six
`Whatwg.Streams.Semantics` modules whose docstrings name
`CONFIGURATION-PG-ORDERING` are in that graph's fence. Which owner takes
`Whatwg.Streams.Kernel` is a coordinator ruling (addendum D.5), not pinned here. -/

#guard WhatwgTest.Ledger.ledger.unrouted.filter (·.recordedBy == "D57") ==
  [⟨`Whatwg.Html, "D57"⟩, ⟨`Whatwg.Infra.Namespaces, "D57"⟩,
   ⟨`Whatwg.Infra.Bytes.Byte, "D57"⟩, ⟨`Whatwg.Infra.Bytes.Sequence, "D57"⟩,
   ⟨`Whatwg.Infra.Primitive.Singleton, "D57"⟩, ⟨`Whatwg.Infra.Text.Case, "D57"⟩,
   ⟨`Whatwg.Infra.Text.Codec, "D57"⟩, ⟨`Whatwg.Infra.Text.CodePoint, "D57"⟩,
   ⟨`Whatwg.Infra.Text.Order, "D57"⟩, ⟨`Whatwg.Infra.Text.Scan, "D57"⟩,
   ⟨`Whatwg.Infra.Text.String, "D57"⟩, ⟨`Whatwg.Infra.Text.Substring, "D57"⟩,
   ⟨`Whatwg.Infra.Text.Whitespace, "D57"⟩]

#guard [`Whatwg.Streams.Semantics.Configuration, `Whatwg.Streams.Semantics.Step,
  `Whatwg.Streams.Semantics.Runs, `Whatwg.Streams.Semantics.Source,
  `Whatwg.Streams.Semantics.Frontier, `Whatwg.Streams.Semantics.Mask,
  `Whatwg.Streams.Semantics.Invariants].all
    WhatwgTest.Ledger.configurationOrdering.fence.contains

/-! ## 3. Rule M: the modules that must be routed

A module must be routed when `Whatwg` is a component-wise prefix of its name
and it declares at least one constant whose name is not internal
(`Lean.Name.isInternal`; a private name begins `_private`, so it is
internal). The result is in table order, each module once. -/

/-- The private name Lean gives the declaration `n` of module `m`. -/
private def priv (m n : Lean.Name) : Lean.Name :=
  Lean.Name.num (`_private ++ m) 0 ++ n

private def ruleTable : ModuleTable := ⟨[
  (`Init.Prelude, [`Nat.add]),
  (`Whatwg, []),
  (`Whatwg.A, [`Whatwg.A.x]),
  (`Whatwg.A.Scaffold, []),
  (`Whatwg.B, [priv `Whatwg.B `Whatwg.B.helper, priv `Whatwg.B `Whatwg.B.helper.eq_1]),
  (`Whatwg.C, [`Whatwg.C._auxLemma, `Whatwg.C.f._sunfold]),
  (`Whatwg.D, [`Whatwg.D._auxLemma, `Whatwg.D.y]),
  (`Whatwg.I, [`Whatwg.I.instReprT]),
  (`WhatwgTest.E, [`WhatwgTest.E.z]),
  (`WhatwgGates.F, [`Gates.F.cli]),
  (`Whatwgx.G, [`Whatwgx.G.v]),
  (`Whatwg.A, [`Whatwg.A.x])]⟩

#guard Lean.isPrivateName (priv `Whatwg.B `Whatwg.B.helper)
#guard (priv `Whatwg.B `Whatwg.B.helper).isInternal
#guard ruleTable.mustRoute == [`Whatwg.A, `Whatwg.D, `Whatwg.I]
-- The production root itself is routed once it declares a constant.
#guard (ModuleTable.mk [(`Whatwg, [`Whatwg.version]), (`Whatwg.A, [])]).mustRoute == [`Whatwg]
#guard (ModuleTable.mk []).mustRoute == []

#guard ruleTable.declaringModule? `Whatwg.D.y == some `Whatwg.D
#guard ruleTable.declaringModule? `Whatwg.A.x == some `Whatwg.A
#guard ruleTable.declaringModule? `Gates.F.cli == some `WhatwgGates.F
#guard ruleTable.declaringModule? `Whatwg.A == none
#guard ruleTable.declaringModule? `Whatwg.Gone.x == none

/-! ## 4. Claims

The fixture table holds seven modules that must be routed, an umbrella, a
scaffold with no constant, a module with only private constants, and a test
and a tooling module. The control ledger claims each of the seven exactly
once: by a fence, by a standalone leaf, by a leaf whose parent graph is the
owner, and by two unrouted prefixes. -/

private def table : ModuleTable := ⟨[
  (`Whatwg, []),
  (`Whatwg.Ecma262.Agent, [`Whatwg.Ecma262.Agent.step]),
  (`Whatwg.Ecma262.AgentInvariant, [`Whatwg.Ecma262.Agent.Coherent]),
  (`Whatwg.Html, []),
  (`Whatwg.Html.Node.Raw, [`Whatwg.Html.Node.Raw.render]),
  (`Whatwg.Html.Print, [`Whatwg.Html.Print.escape]),
  (`Whatwg.Infra.Primitive.Integer, [`Whatwg.Infra.Unsigned8]),
  (`Whatwg.Infra.Text.Case, [`Whatwg.Infra.Text.asciiLowercase]),
  (`Whatwg.Streams.Kernel, [`Whatwg.Streams.Kernel.Path]),
  (`Whatwg.Streams.Readable.Stream, []),
  (`Whatwg.Streams.Hidden, [priv `Whatwg.Streams.Hidden `Whatwg.Streams.Hidden.h]),
  (`WhatwgGates.UrlCensus, [`Gates.UrlCensus.cli]),
  (`WhatwgTest.Ledger, [`WhatwgTest.Ledger.ledger])]⟩

#guard table.mustRoute ==
  [`Whatwg.Ecma262.Agent, `Whatwg.Ecma262.AgentInvariant, `Whatwg.Html.Node.Raw,
   `Whatwg.Html.Print, `Whatwg.Infra.Primitive.Integer, `Whatwg.Infra.Text.Case,
   `Whatwg.Streams.Kernel]

private def oc : Cell := { status := .requiredOpen, remaining := [.named "x"] }

private def allOpen : Edges :=
  { identity := oc, construction := oc, semantics := oc, laws := oc,
    representation := oc, counterexamples := oc, bridges := oc, targets := oc,
    trust := oc, coverage := oc }

private def graphOf (id : String) (fence : List Lean.Name) : Graph :=
  { id, document := "docs/" ++ id ++ ".md", fence, edges := allOpen }

private def leafOf (id : String) (declarations : List Lean.Name)
    (parent : Option (String × Edge) := none) : Leaf :=
  { id, document := "docs/" ++ id ++ ".md", declarations, parent, receipts := [] }

private def agentGraph : Graph :=
  graphOf "TEST-PG-AGENT"
    [`Whatwg.Ecma262.Agent, `Whatwg.Ecma262.AgentInvariant, `WhatwgGates.UrlCensus]

private def streamsGraph : Graph := graphOf "TEST-PG-STREAMS" [`Whatwg.Streams.Readable.Stream]

private def integerLeaf : Leaf := leafOf "TEST-LF-INTEGER" [`Whatwg.Infra.Unsigned8]

private def kernelLeaf : Leaf :=
  leafOf "TEST-LF-KERNEL" [`Whatwg.Streams.Kernel.Path] (some ("TEST-PG-STREAMS", .laws))

private def control : Ledger :=
  { graphs := [agentGraph, streamsGraph], leaves := [integerLeaf, kernelLeaf],
    unrouted := [⟨`Whatwg.Html, "D1"⟩, ⟨`Whatwg.Infra.Text.Case, "D1"⟩] }

-- A fence entry claims its module exactly: not a module it is a prefix of,
-- and not a module whose last component merely begins with its own.
#guard control.claimsOn table `Whatwg.Ecma262.Agent ==
  [("graph TEST-PG-AGENT", "graph TEST-PG-AGENT")]
#guard control.claimsOn table `Whatwg.Ecma262.Agent.Sub == []
#guard ({ control with graphs := [graphOf "TEST-PG-AGENT" [`Whatwg.Ecma262.Agent]] }).claimsOn
  table `Whatwg.Ecma262.AgentInvariant == []
-- An unrouted prefix claims itself and every module below it, by component.
#guard control.claimsOn table `Whatwg.Html == [("unrouted Whatwg.Html", "unrouted Whatwg.Html")]
#guard control.claimsOn table `Whatwg.Html.Node.Raw ==
  [("unrouted Whatwg.Html", "unrouted Whatwg.Html")]
#guard control.claimsOn table `Whatwg.Htmlx == []
#guard ({ graphs := [], unrouted := [⟨`Whatwg.Ecma262.Agent, "D1"⟩] } : Ledger).claimsOn
  table `Whatwg.Ecma262.AgentInvariant == []
#guard ({ graphs := [], unrouted := [⟨`Whatwg.Ecma262.Agent, "D1"⟩] } : Ledger).claimsOn
  table `Whatwg.Ecma262.Agent == [("unrouted Whatwg.Ecma262.Agent", "unrouted Whatwg.Ecma262.Agent")]
-- A standalone leaf claims the declaring module of each declaration, for itself.
#guard control.claimsOn table `Whatwg.Infra.Primitive.Integer ==
  [("leaf TEST-LF-INTEGER", "leaf TEST-LF-INTEGER")]
-- A leaf with a parent graph claims for that graph.
#guard control.claimsOn table `Whatwg.Streams.Kernel ==
  [("leaf TEST-LF-KERNEL", "graph TEST-PG-STREAMS")]
-- A leaf declaration that names no constant claims nothing.
#guard ({ control with leaves := [leafOf "TEST-LF-X" [`Whatwg.Gone.x]] }).claimsOn
  table `Whatwg.Gone == []
-- Claims are computed for any module; only rule M decides which are checked.
#guard control.claimsOn table `WhatwgGates.UrlCensus ==
  [("graph TEST-PG-AGENT", "graph TEST-PG-AGENT")]
#guard control.claimsOn table `Whatwg.Streams.Hidden == []
-- Claim order: graphs, then leaves, then unrouted entries, each in ledger order.
#guard ({ control with
    graphs := [agentGraph, graphOf "TEST-PG-OTHER" [`Whatwg.Infra.Primitive.Integer]],
    unrouted := [⟨`Whatwg.Infra, "D1"⟩] }).claimsOn table `Whatwg.Infra.Primitive.Integer ==
  [("graph TEST-PG-OTHER", "graph TEST-PG-OTHER"),
   ("leaf TEST-LF-INTEGER", "leaf TEST-LF-INTEGER"),
   ("unrouted Whatwg.Infra", "unrouted Whatwg.Infra")]

/-! ## 5. The routing findings

Each plant changes the control in one way. Findings come per module that must
be routed, in `mustRoute` order, then per unrouted entry, in ledger order. -/

-- Control: every module that must be routed has exactly one owner. The
-- umbrella, the scaffold, the private-only module and the two modules outside
-- the production root are claimed by nobody, or only by a fence, and raise
-- nothing.
#guard routingFindings table control == []

-- R1 (LEDGER-CE-006): a production module with public constants that no
-- fence, leaf or unrouted prefix claims.
#guard routingFindings table
    { control with graphs := [graphOf "TEST-PG-AGENT" [`Whatwg.Ecma262.Agent], streamsGraph] } ==
  ["module Whatwg.Ecma262.AgentInvariant is claimed by no graph fence, leaf record or unrouted prefix"]

-- R2: an unrouted prefix is matched by component, so `Whatwg.Ecma262.Agent`
-- does not claim `Whatwg.Ecma262.AgentInvariant`.
#guard routingFindings table
    { control with
      graphs := [graphOf "TEST-PG-AGENT" [`WhatwgGates.UrlCensus], streamsGraph],
      unrouted := control.unrouted ++ [⟨`Whatwg.Ecma262.Agent, "D1"⟩] } ==
  ["module Whatwg.Ecma262.AgentInvariant is claimed by no graph fence, leaf record or unrouted prefix"]

-- R3: a fence entry is exact, so a fence naming the umbrella `Whatwg.Html`
-- claims none of the modules below it.
#guard routingFindings table
    { control with
      graphs := [agentGraph, streamsGraph, graphOf "TEST-PG-HTML" [`Whatwg.Html]],
      unrouted := [⟨`Whatwg.Infra.Text.Case, "D1"⟩] } ==
  ["module Whatwg.Html.Node.Raw is claimed by no graph fence, leaf record or unrouted prefix",
   "module Whatwg.Html.Print is claimed by no graph fence, leaf record or unrouted prefix"]

-- R4 (LEDGER-CE-007): two graphs fence one module.
#guard routingFindings table
    { control with graphs := [agentGraph, streamsGraph,
      graphOf "TEST-PG-OTHER" [`Whatwg.Ecma262.Agent]] } ==
  ["module Whatwg.Ecma262.Agent is claimed by graph TEST-PG-AGENT and graph TEST-PG-OTHER"]

-- R5: a graph fence and an unrouted prefix.
#guard routingFindings table
    { control with unrouted := control.unrouted ++ [⟨`Whatwg.Ecma262.Agent, "D1"⟩] } ==
  ["module Whatwg.Ecma262.Agent is claimed by graph TEST-PG-AGENT and unrouted Whatwg.Ecma262.Agent"]

-- R6: a graph fence and a standalone leaf.
#guard routingFindings table
    { control with leaves := [leafOf "TEST-LF-INTEGER"
      [`Whatwg.Infra.Unsigned8, `Whatwg.Ecma262.Agent.step], kernelLeaf] } ==
  ["module Whatwg.Ecma262.Agent is claimed by graph TEST-PG-AGENT and leaf TEST-LF-INTEGER"]

-- R7: a leaf whose parent graph is not the graph that fences the module.
#guard routingFindings table
    { control with graphs := [graphOf "TEST-PG-AGENT"
      [`Whatwg.Ecma262.Agent, `Whatwg.Ecma262.AgentInvariant, `Whatwg.Streams.Kernel],
      streamsGraph] } ==
  ["module Whatwg.Streams.Kernel is claimed by graph TEST-PG-AGENT and leaf TEST-LF-KERNEL"]

-- Control: a leaf whose parent graph also fences the module is one owner.
#guard routingFindings table
    { control with graphs := [agentGraph,
      graphOf "TEST-PG-STREAMS" [`Whatwg.Streams.Readable.Stream, `Whatwg.Streams.Kernel]] } == []

-- Control: a fence that lists a module twice is one owner.
#guard routingFindings table
    { control with graphs := [graphOf "TEST-PG-AGENT"
      [`Whatwg.Ecma262.Agent, `Whatwg.Ecma262.AgentInvariant, `Whatwg.Ecma262.Agent],
      streamsGraph] } == []

-- Control: a repeated unrouted entry is one owner.
#guard routingFindings table
    { control with unrouted := control.unrouted ++ [⟨`Whatwg.Infra.Text.Case, "D1"⟩] } == []

-- The claimants of a finding are listed once each.
#guard routingFindings table
    { control with unrouted := control.unrouted ++
      [⟨`Whatwg.Ecma262.Agent, "D1"⟩, ⟨`Whatwg.Ecma262.Agent, "D1"⟩] } ==
  ["module Whatwg.Ecma262.Agent is claimed by graph TEST-PG-AGENT and unrouted Whatwg.Ecma262.Agent"]

-- R8: two unrouted prefixes, one inside the other.
#guard routingFindings table
    { control with unrouted := control.unrouted ++ [⟨`Whatwg.Html.Node, "D1"⟩] } ==
  ["module Whatwg.Html.Node.Raw is claimed by unrouted Whatwg.Html and unrouted Whatwg.Html.Node"]

-- R9: three owners, listed once each in ledger order.
#guard routingFindings table
    { control with
      graphs := [agentGraph, streamsGraph, graphOf "TEST-PG-OTHER" [`Whatwg.Infra.Primitive.Integer]],
      unrouted := control.unrouted ++ [⟨`Whatwg.Infra.Primitive, "D1"⟩] } ==
  ["module Whatwg.Infra.Primitive.Integer is claimed by graph TEST-PG-OTHER, leaf TEST-LF-INTEGER and unrouted Whatwg.Infra.Primitive"]

-- R10: an unrouted prefix that is a built module and claims no module that
-- must be routed: a scaffold, a module with only private constants, a module
-- outside the production root.
#guard routingFindings table
    { control with unrouted := control.unrouted ++ [⟨`Whatwg.Streams.Readable.Stream, "D1"⟩] } ==
  ["unrouted Whatwg.Streams.Readable.Stream: claims no module that must be routed"]
#guard routingFindings table
    { control with unrouted := control.unrouted ++ [⟨`Whatwg.Streams.Hidden, "D1"⟩] } ==
  ["unrouted Whatwg.Streams.Hidden: claims no module that must be routed"]
#guard routingFindings table
    { control with unrouted := control.unrouted ++ [⟨`WhatwgGates.UrlCensus, "D1"⟩] } ==
  ["unrouted WhatwgGates.UrlCensus: claims no module that must be routed"]

-- Control: an unrouted prefix that is no module of the table raises no
-- routing finding; `unroutedFindings` reports it as not a built module.
#guard routingFindings table
    { control with unrouted := control.unrouted ++ [⟨`Whatwg.Gone, "D1"⟩] } == []

-- Order: per module in `mustRoute` order, then per unrouted entry.
#guard routingFindings table
    { control with
      graphs := [graphOf "TEST-PG-AGENT" [`Whatwg.Ecma262.Agent], streamsGraph,
        graphOf "TEST-PG-OTHER" [`Whatwg.Ecma262.Agent, `Whatwg.Infra.Text.Case]],
      unrouted := [⟨`Whatwg.Streams.Readable.Stream, "D1"⟩, ⟨`Whatwg.Html, "D1"⟩,
        ⟨`Whatwg.Infra.Text.Case, "D1"⟩, ⟨`WhatwgTest.Ledger, "D1"⟩] } ==
  ["module Whatwg.Ecma262.Agent is claimed by graph TEST-PG-AGENT and graph TEST-PG-OTHER",
   "module Whatwg.Ecma262.AgentInvariant is claimed by no graph fence, leaf record or unrouted prefix",
   "module Whatwg.Infra.Text.Case is claimed by graph TEST-PG-OTHER and unrouted Whatwg.Infra.Text.Case",
   "unrouted Whatwg.Streams.Readable.Stream: claims no module that must be routed",
   "unrouted WhatwgTest.Ledger: claims no module that must be routed"]

-- A table with no module to route: every unrouted prefix that is a module of
-- the table claims nothing.
#guard routingFindings ⟨[(`Whatwg.Html, [])]⟩ { graphs := [], unrouted := [⟨`Whatwg.Html, "D57"⟩] } ==
  ["unrouted Whatwg.Html: claims no module that must be routed"]

/-! ## 6. The index projection -/

private def cc : Cell := { status := .requiredClosed, grounds := [.receipt "Landing"] }

private def na : Cell := { status := .notApplicable, note := "n" }

private def mixedGraph : Graph :=
  { id := "TEST-PG-MIXED", document := "docs/MIXED-DAG.md", fence := [],
    edges := { allOpen with identity := cc, construction := cc, laws := cc, targets := na } }

#guard (graphOf "TEST-PG-A" []).countStatus .requiredOpen == 10
#guard (graphOf "TEST-PG-A" []).countStatus .requiredClosed == 0
#guard mixedGraph.countStatus .requiredOpen == 6
#guard mixedGraph.countStatus .requiredClosed == 3
#guard mixedGraph.countStatus .notApplicable == 1

private def indexLedger : Ledger :=
  { graphs := [graphOf "TEST-PG-A" [`Whatwg.A], mixedGraph],
    leaves := [leafOf "TEST-LF-ONE" [`Whatwg.B.x, `Whatwg.B.y],
      leafOf "TEST-LF-TWO" [`Whatwg.C.z] (some ("TEST-PG-MIXED", .laws))],
    unrouted := [⟨`Whatwg.Html, "D57"⟩, ⟨`Whatwg.Infra.Text.Case, "R-T1"⟩] }

#guard indexLedger.renderIndex ledgerInput == String.intercalate "\n"
  ["<!-- GENERATED by `lake exe whatwg_ledger --write` (Gates.Ledger, format 1) from `WhatwgTest/Ledger.lean`; do not edit. -->",
   "",
   "# Graph ledger index",
   "",
   "Totals: 2 graph(s), 20 edges (16 required-open, 3 required-closed, 1 not-applicable), 2 leaf record(s), 2 unrouted prefix(es).",
   "",
   "## Graphs",
   "",
   "| Graph | Document | Open | Closed | Not applicable |",
   "| --- | --- | ---: | ---: | ---: |",
   "| [`TEST-PG-A`](TEST-PG-A.md) | `docs/TEST-PG-A.md` | 10 | 0 | 0 |",
   "| [`TEST-PG-MIXED`](TEST-PG-MIXED.md) | `docs/MIXED-DAG.md` | 6 | 3 | 1 |",
   "",
   "## Leaf records",
   "",
   "| Leaf | Document | Parent | Declarations |",
   "| --- | --- | --- | ---: |",
   "| `TEST-LF-ONE` | `docs/TEST-LF-ONE.md` | standalone | 2 |",
   "| `TEST-LF-TWO` | `docs/TEST-LF-TWO.md` | `TEST-PG-MIXED` laws | 1 |",
   "",
   "## Unrouted prefixes",
   "",
   "| Prefix | Recorded by |",
   "| --- | --- |",
   "| `Whatwg.Html` | D57 |",
   "| `Whatwg.Infra.Text.Case` | R-T1 |"] ++ "\n"

-- An empty ledger: each section says "None.".
#guard ({ graphs := [] } : Ledger).renderIndex ledgerInput == String.intercalate "\n"
  ["<!-- GENERATED by `lake exe whatwg_ledger --write` (Gates.Ledger, format 1) from `WhatwgTest/Ledger.lean`; do not edit. -->",
   "",
   "# Graph ledger index",
   "",
   "Totals: 0 graph(s), 0 edges (0 required-open, 0 required-closed, 0 not-applicable), 0 leaf record(s), 0 unrouted prefix(es).",
   "",
   "## Graphs",
   "",
   "None.",
   "",
   "## Leaf records",
   "",
   "None.",
   "",
   "## Unrouted prefixes",
   "",
   "None."] ++ "\n"

-- The input named in the header is the argument; the bytes hold no CR.
#guard ((indexLedger.renderIndex "`X.lean`").splitOn "\n").head? ==
  some "<!-- GENERATED by `lake exe whatwg_ledger --write` (Gates.Ledger, format 1) from `X.lean`; do not edit. -->"
#guard !(indexLedger.renderIndex ledgerInput).contains '\r'

/-! ## 7. The routed run

The fixture is one graph, one leaf and one unrouted prefix over a world and a
module table that agree, in which every reference resolves, every module that
must be routed has one owner, and the projection and the index are current. -/

private def runTable : ModuleTable := ⟨[
  (`Whatwg, []),
  (`Whatwg.One, [`Whatwg.One.x]),
  (`Whatwg.Leaf, [`Whatwg.Leaf.v]),
  (`Whatwg.U, []),
  (`Whatwg.U.V, [`Whatwg.U.V.w]),
  (`WhatwgTest.Ledger, [`WhatwgTest.Ledger.ledger])]⟩

private def runGraph : Graph :=
  { id := "TEST-PG-ONE", document := "docs/ONE-DAG.md", fence := [`Whatwg.One], edges := allOpen }

private def runLeaf : Leaf := leafOf "TEST-LF-ONE" [`Whatwg.Leaf.v]

private def runLedger : Ledger :=
  { graphs := [runGraph], leaves := [runLeaf], unrouted := [⟨`Whatwg.U, "D1"⟩] }

private def worldFor (t : ModuleTable) (l : Ledger) (files : List (String × String))
    (projections : List String) : World where
  constantKind? n := if t.modules.any (·.2.contains n) then some .other else none
  moduleBuilt m := t.modules.any (·.1 == m)
  file? p := (files ++ [
      ("COORDINATION.md", "# Coordination\n\n- Fixture debts: (D1) a debt.\n"),
      ("docs/ONE-DAG.md", "# One graph\n\nSee `generated/graphs/TEST-PG-ONE.md`.\n"),
      ("docs/receipts/TEST-PG-ONE.md", "# Receipts log of `TEST-PG-ONE`\n"),
      ("docs/TEST-LF-ONE.md", "# Leaf `TEST-LF-ONE`\n"),
      ("generated/graphs/TEST-PG-ONE.md", runGraph.render ledgerInput),
      ("generated/graphs/INDEX.md", l.renderIndex ledgerInput)]).lookup p
  projectionFiles := projections

private def runWorld : World :=
  worldFor runTable runLedger [] ["generated/graphs/INDEX.md", "generated/graphs/TEST-PG-ONE.md"]

private def withFile (w : World) (path text : String) : World :=
  { w with file? := fun p => if p == path then some text else w.file? p }

private def withoutFile (w : World) (path : String) : World :=
  { w with file? := fun p => if p == path then none else w.file? p }

private def passLine : String :=
  "PASS whatwg_ledger: 1 graph(s), 10 edges, 1 leaf record(s), 1 unrouted prefix(es), 3 production module(s) with one owner each; every reference resolves against the built environment and the authored files, and every projection and the index are byte-identical to a fresh rendering"

#guard runTable.mustRoute == [`Whatwg.One, `Whatwg.Leaf, `Whatwg.U.V]
#guard referenceFindings runWorld runLedger == []
#guard routingFindings runTable runLedger == []

/-! ### 7.1 The index is not a stray file, and it is compared -/

#guard projectionFindings runWorld runLedger == []
#guard projectionFindings
  { runWorld with projectionFiles := ["generated/graphs/INDEX.md", "generated/graphs/TEST-PG-ONE.md",
      "generated/graphs/index.md"] } runLedger ==
  ["generated/graphs/index.md is not the projection of a ledger graph"]
#guard indexFindings runWorld runLedger == []
#guard indexFindings (withoutFile runWorld "generated/graphs/INDEX.md") runLedger ==
  ["generated/graphs/INDEX.md does not exist"]
#guard indexFindings (withFile runWorld "generated/graphs/INDEX.md" "stale\n") runLedger ==
  ["generated/graphs/INDEX.md differs from a fresh rendering"]
#guard indexFindings
  (withFile runWorld "generated/graphs/INDEX.md"
    ((runLedger.renderIndex ledgerInput).replace "\n" "\r\n")) runLedger ==
  ["generated/graphs/INDEX.md differs from a fresh rendering"]
-- A ledger change the index renders is drift until the index is regenerated.
#guard indexFindings runWorld { runLedger with unrouted := [] } ==
  ["generated/graphs/INDEX.md differs from a fresh rendering"]

/-! ### 7.2 The run-time file set -/

#guard runLedger.runFiles ==
  ["COORDINATION.md", "test/counterexamples/REGISTER.md", "lakefile.toml",
   "docs/ONE-DAG.md", "docs/receipts/TEST-PG-ONE.md", "generated/graphs/TEST-PG-ONE.md",
   "docs/TEST-LF-ONE.md", "generated/graphs/INDEX.md"]
#guard ({ graphs := [] } : Ledger).runFiles ==
  ["COORDINATION.md", "test/counterexamples/REGISTER.md", "lakefile.toml",
   "generated/graphs/INDEX.md"]
#guard runLedger.runFiles == runLedger.files ++ [indexPath]

/-! ### 7.3 The outcome -/

#guard routedOutcome runWorld runTable runLedger false == ⟨0, [passLine], []⟩
#guard routedOutcome runWorld runTable runLedger true ==
  ⟨0, [passLine ++ " (written)"],
    [("generated/graphs/TEST-PG-ONE.md", runGraph.render ledgerInput),
     ("generated/graphs/INDEX.md", runLedger.renderIndex ledgerInput)]⟩
-- `--write` compares neither the projections nor the index, so it rewrites both.
#guard routedOutcome
  (withFile (withoutFile runWorld "generated/graphs/INDEX.md")
    "generated/graphs/TEST-PG-ONE.md" "stale\n") runTable runLedger true ==
  ⟨0, [passLine ++ " (written)"],
    [("generated/graphs/TEST-PG-ONE.md", runGraph.render ledgerInput),
     ("generated/graphs/INDEX.md", runLedger.renderIndex ledgerInput)]⟩
-- Comparing, a missing index is a finding.
#guard routedOutcome (withoutFile runWorld "generated/graphs/INDEX.md") runTable runLedger false ==
  ⟨1, ["FAIL whatwg_ledger: 1 finding(s)", "  generated/graphs/INDEX.md does not exist"], []⟩

-- LEDGER-CE-006: a module that nobody claims passes the slice A outcome and
-- fails the routed one, in both modes, and nothing is written.
private def unclaimedTable : ModuleTable :=
  ⟨runTable.modules ++ [(`Whatwg.Streams.Kernel, [`Whatwg.Streams.Kernel.Path])]⟩

#guard (outcome (worldFor unclaimedTable runLedger [] ["generated/graphs/TEST-PG-ONE.md"])
    runLedger false).exitCode == 0
#guard routedOutcome runWorld unclaimedTable runLedger false ==
  ⟨1, ["FAIL whatwg_ledger: 1 finding(s)",
       "  module Whatwg.Streams.Kernel is claimed by no graph fence, leaf record or unrouted prefix"],
   []⟩
#guard routedOutcome runWorld unclaimedTable runLedger true ==
  ⟨1, ["FAIL whatwg_ledger: 1 finding(s)",
       "  module Whatwg.Streams.Kernel is claimed by no graph fence, leaf record or unrouted prefix"],
   []⟩

-- A module with two owners, a fence and an unrouted prefix, in a world whose
-- projection and index are current: the one finding, in both modes, and
-- nothing is written.
private def doubleLedger : Ledger :=
  { runLedger with unrouted := [⟨`Whatwg.U, "D1"⟩, ⟨`Whatwg.One, "D1"⟩] }

private def doubleWorld : World :=
  worldFor runTable doubleLedger [] ["generated/graphs/INDEX.md", "generated/graphs/TEST-PG-ONE.md"]

#guard routedOutcome doubleWorld runTable doubleLedger false ==
  ⟨1, ["FAIL whatwg_ledger: 1 finding(s)",
       "  module Whatwg.One is claimed by graph TEST-PG-ONE and unrouted Whatwg.One"], []⟩
#guard routedOutcome doubleWorld runTable doubleLedger true ==
  ⟨1, ["FAIL whatwg_ledger: 1 finding(s)",
       "  module Whatwg.One is claimed by graph TEST-PG-ONE and unrouted Whatwg.One"], []⟩

-- Order: the reference findings, the routing findings, the projection
-- findings, then the index findings.
#guard routedOutcome
  (withFile (withoutFile runWorld "docs/TEST-LF-ONE.md")
    "generated/graphs/TEST-PG-ONE.md" "stale\n")
  unclaimedTable { runLedger with unrouted := [] } false ==
  ⟨1, ["FAIL whatwg_ledger: 5 finding(s)",
       "  TEST-LF-ONE: document docs/TEST-LF-ONE.md does not exist",
       "  module Whatwg.U.V is claimed by no graph fence, leaf record or unrouted prefix",
       "  module Whatwg.Streams.Kernel is claimed by no graph fence, leaf record or unrouted prefix",
       "  generated/graphs/TEST-PG-ONE.md differs from a fresh rendering",
       "  generated/graphs/INDEX.md differs from a fresh rendering"], []⟩

end WhatwgTest.Audit.LedgerRoutingContract
