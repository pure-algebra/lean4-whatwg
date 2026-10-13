import Whatwg.Svg.Scene.Layers

/-!
# WhatwgTest.Svg.UseLayers

The two rankings of lean4-effect4's view on `Whatwg/Svg/Scene/Layers.lean`, and d3-sankey's
example graph against d3's own expected file (slice S22). The consumer is read at its checkout
`6ad8f7b8d`. This module imports nothing of that package: it restates the consumer's types
under the consumer's names, with the fields that the rankings read.

**What is ported, and what it was.**

| The consumer's | Here |
| --- | --- |
| `Graph.preds`, `rankOf`, `rankStep`, `ranksUpTo`, `ranks` (`tools/Tools/View/Graph.lean`, lines 62 to 80) | `ranks`, one line on `Layers.heights` |
| `ranksUpTo_succ`, `length_ranksUpTo`, `ranksUpTo_getD_stable`, `ranksUpTo_getD_self`, `le_foldl_max`, `ranks_forward` (lines 82 to 142) | `ranks_forward`, from `Layers.heights_meets` and `Layers.serves_range` |
| `Flow.relax`, `assign` (`tools/Tools/View/Flow.lean`, lines 577 to 592) | `Layers.relax`, `Layers.along` at the reading `reading h` |
| `Flow.before`, `orders` (lines 633 to 640), `Serves`, `before_spec`, `orders_serves` (`tools/Tools/View/FlowLaws.lean`, lines 1267 to 1290) | `Layers.serves`, `Layers.Serves`, `Layers.serves_iff` |
| `relax_ge_start`, `relax_ge_term`, `assign_not_mem`, `assign_append`, `assign_meets` (`FlowLaws.lean`, lines 177 to 240) | `Layers.heights_meets` |
| `nodup_range'`, `orderFor_serves` (lines 1485 to 1508) | `orderFor_serves`, four lines |
| `heightsOf_edge`, `heightsOf_reach` (lines 1523 to 1540) | the same two statements, on `Layers.heights_meets` |
| `Flow.kahn` (`Flow.lean`, lines 670 to 679) | `kahn`, as it is written there: the module makes no order |

The consumer's tables (`assignHeights`, `assignTable`, `ordersTable`, with their connectors)
are not ported. They are its fast forms, and each is tied to `assign` or `orders` by a law of
its own, so they stand on the kit's functions as they stood on its own.

**What the consumer gains that it did not have.** `ranks_least`: no ranking with a step between
the two ends of each forward edge has a lesser rank anywhere. `heightsOf_any_order`: the heights
do not depend on which order `orderFor` took, Kahn's or the items' own, where both serve the
same edges. Its laws say today that each order gives heights that meet the edges, and not that
the two pictures are one.

**d3-sankey.** `computeNodeDepths` of `src/sankey.js` (commit `bb7233ea0004`) is the count in
steps of one, and `justify` of `src/align.js` puts a node with no link out of it in the last
column. `test/energy.json` has 48 nodes and 68 links, and `test/energy-nodes.json` the
expected place of each node. The column of a node is read from its `x`: the columns are
134.7 apart from 1 to 944, so `x` rounded to a tenth names a column exactly. The guard below
finds all 48 columns. d3 marks that test `tape.skip`, so d3 itself does not run the comparison:
the file is its expected output and not a result of its test run.

The lines of this module are of four kinds: the port, whose theorems hold for every graph; one
reader, a law of the kit applied to the 48 nodes; the finite evaluation against d3's file; and
controls, which are orders that do not serve.
-/

namespace WhatwgTest.Svg.UseLayers

open Whatwg.Svg.Scene

/-! ## `Graph.ranks`: the longest forward path into each node -/

/-- An edge between two nodes, by their positions in the graph's order: the consumer's
`GEdge`. -/
structure GEdge where
  key : String
  src : Nat
  dst : Nat

/-- A graph: how many nodes it has, and its edges. The consumer's `Graph` holds the nodes
themselves, and its ranking reads their count only. -/
structure Graph where
  size : Nat
  edges : List GEdge

/-- A step of one from the source of an edge to its target. -/
def step : Layers.Reading GEdge Nat := ⟨(·.src), (·.dst), fun _ => 1⟩

/-- The edges from an earlier node to a later one. Every other edge is a back edge, and is
drawn in a lane. -/
def forward (g : Graph) : List GEdge :=
  g.edges.filter fun e => decide (e.src < e.dst) && decide (e.dst < g.size)

/-- **The ranks** of a graph's nodes: the consumer's `Graph.ranks`. -/
def ranks (g : Graph) : Nat → Int := Layers.heights step (forward g) 0 (List.range g.size)

theorem mem_forward {g : Graph} {e : GEdge} :
    e ∈ forward g ↔ e ∈ g.edges ∧ e.src < e.dst ∧ e.dst < g.size := by
  rw [forward, List.mem_filter, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]

/-- The nodes' own order serves the forward edges. -/
theorem forward_serves (g : Graph) : Layers.Serves step (forward g) (List.range g.size) :=
  Layers.serves_range fun _ he => (mem_forward.mp he).2

/-- **The forward law**, the consumer's `ranks_forward`: every forward edge descends at least
one rank. -/
theorem ranks_forward (g : Graph) (e : GEdge) (he : e ∈ g.edges) (hf : e.src < e.dst)
    (hd : e.dst < g.size) : ranks g e.src < ranks g e.dst := by
  have h : ranks g e.src + 1 ≤ ranks g e.dst :=
    Layers.heights_meets (forward_serves g) 0 (mem_forward.mpr ⟨he, hf, hd⟩)
  omega

/-- No rank is negative. -/
theorem ranks_nonneg (g : Graph) (v : Nat) : 0 ≤ ranks g v :=
  Layers.heights_start step (forward g) 0 (List.range g.size) v

/-- **No ranking is lower.** A ranking from `0` on with a step between the two ends of each
forward edge gives no node a lesser rank. The consumer has no such law. -/
theorem ranks_least (g : Graph) {z : Nat → Int} (h0 : ∀ v, 0 ≤ z v)
    (hz : ∀ e ∈ g.edges, e.src < e.dst → e.dst < g.size → z e.src < z e.dst) (v : Nat) :
    ranks g v ≤ z v :=
  Layers.heights_least step (forward g) 0 (List.range g.size) h0 (fun e he => by
    have h := hz e (mem_forward.mp he).1 (mem_forward.mp he).2.1 (mem_forward.mp he).2.2
    show z e.src + 1 ≤ z e.dst
    omega) v

/-! ## `Flow.heightsOf`: heights in pixels, along an order that is checked -/

/-- An edge of a part, by the positions of its two ends: the consumer's `Flow.Edge`. -/
structure Edge where
  fr : Nat
  to : Nat
  pad : Int := 0
  drawn : Bool := true
  share : Nat := 1000000

/-- The gap between an item and the next one down: the consumer's `VGAP`, one row. -/
def VGAP : Int := 24

/-- **How the flow's edges are read**: the target of an edge stands below its source by the
source's height, a gap and the edge's room. `h` is the height of the item at a position. -/
def reading (h : Nat → Int) : Layers.Reading Edge Nat :=
  ⟨(·.fr), (·.to), fun e => h e.fr + VGAP + e.pad⟩

/-- The consumer's `relax` is the kit's, to the grouping of one sum. -/
theorem relax_eq (h : Nat → Int) (es : List Edge) (y : Nat → Int) (start : Int) (v : Nat) :
    Layers.relax (reading h) es y start v =
      es.foldl (fun m e => if e.to = v then max m (y e.fr + h e.fr + VGAP + e.pad) else m)
        start := by
  have e : (fun (m : Int) (e : Edge) =>
      if e.to = v then max m (y e.fr + (h e.fr + VGAP + e.pad)) else m) =
      fun m e => if e.to = v then max m (y e.fr + h e.fr + VGAP + e.pad) else m := by
    funext m e
    rw [Int.add_assoc (y e.fr), Int.add_assoc (y e.fr)]
  show es.foldl (fun (m : Int) (e : Edge) =>
    if e.to = v then max m (y e.fr + (h e.fr + VGAP + e.pad)) else m) start = _
  rw [e]

/-- The step of Kahn's order: the consumer's `kahn.go`. -/
def kahnGo : Nat → List Nat → List Edge → List Nat → List Nat
  | 0, _, _, out => out
  | _ + 1, [], _, out => out
  | fuel + 1, k :: queue, es, out =>
    let rest := es.filter (·.fr != k)
    let ready := ((es.filter (·.fr == k)).map (·.to)).eraseDups.filter fun v =>
      (rest.filter (·.to == v)).length == 0
    kahnGo fuel (queue ++ ready) rest (out ++ [k])

/-- **Kahn's order** of `n` items under the edges: the consumer's `Flow.kahn`. No law reads it.
`orderFor` checks the order it takes. -/
def kahn (n : Nat) (es : List Edge) : List Nat :=
  kahnGo (n + 1) ((List.range n).filter fun k => (es.filter (·.to == k)).length == 0) es []

/-- **The order the heights follow**, with the edges it serves: the consumer's `orderFor`.
Kahn's order of the flow's edges and the accepted waits, when it serves them all; else the
items' own order, which serves the flow's edges. -/
def orderFor (n : Nat) (own dag : List Edge) : List Edge × List Nat :=
  if Layers.serves (reading fun _ => 0) dag (kahn n dag) then (dag, kahn n dag)
  else (own, List.range n)

/-- An order serves the edges whatever the heights of the items: the test reads the two ends
of an edge only. -/
theorem serves_any {h h' : Nat → Int} {es : List Edge} {order : List Nat}
    (s : Layers.Serves (reading h) es order) : Layers.Serves (reading h') es order := s

/-- **The order the heights follow serves the flow's own edges**: the consumer's
`orderFor_serves`. -/
theorem orderFor_serves (h : Nat → Int) {n : Nat} {own dag : List Edge}
    (hsub : ∀ e ∈ own, e ∈ dag) (hfwd : ∀ e ∈ own, e.fr < e.to ∧ e.to < n) :
    (∀ e ∈ own, e ∈ (orderFor n own dag).1) ∧
      Layers.Serves (reading h) (orderFor n own dag).1 (orderFor n own dag).2 := by
  unfold orderFor
  by_cases hs : Layers.serves (reading fun _ => 0) dag (kahn n dag) = true
  · rw [if_pos hs]
    exact ⟨hsub, serves_any ((Layers.serves_iff _ dag (kahn n dag)).mp hs)⟩
  · rw [if_neg hs]
    exact ⟨fun _ he => he, Layers.serves_range hfwd⟩

/-- **The heights of a part's items**: the consumer's `heightsOf`. `h` is the height of the
item at a position, `own` the part's edges, `dag` those with the waits that close no cycle,
and `topPad` the room above its entry. -/
def heightsOf (h : Nat → Int) (n : Nat) (own dag : List Edge) (topPad : Int) : Nat → Int :=
  Layers.heights (reading h) (orderFor n own dag).1 topPad (orderFor n own dag).2

/-- Every edge of the flow stands its target below its source's bottom: the consumer's
`heightsOf_edge`. -/
theorem heightsOf_edge {h : Nat → Int} {n : Nat} {own dag : List Edge} {topPad : Int}
    (hsub : ∀ e ∈ own, e ∈ dag) (hfwd : ∀ e ∈ own, e.fr < e.to ∧ e.to < n)
    (hpad : ∀ e ∈ own, -VGAP ≤ e.pad) {e : Edge} (he : e ∈ own) :
    heightsOf h n own dag topPad e.fr + h e.fr ≤ heightsOf h n own dag topPad e.to := by
  have hs := orderFor_serves h hsub hfwd
  have h1 : heightsOf h n own dag topPad e.fr + (h e.fr + VGAP + e.pad) ≤
      heightsOf h n own dag topPad e.to := Layers.heights_meets hs.2 topPad (hs.1 e he)
  have h2 := hpad e he
  omega

/-- Positions reached from a position along edges: the consumer's `Reach`. -/
inductive Reach (es : List Edge) : Nat → Nat → Prop
  | refl (i : Nat) : Reach es i i
  | step {k : Nat} (e : Edge) : e ∈ es → Reach es e.to k → Reach es e.fr k

/-- What an item reaches along the flow's edges stands at its height or below, and below its
bottom where it is another item: the consumer's `heightsOf_reach`. -/
theorem heightsOf_reach {h : Nat → Int} {n : Nat} {own dag : List Edge} {topPad : Int}
    (hsub : ∀ e ∈ own, e ∈ dag) (hfwd : ∀ e ∈ own, e.fr < e.to ∧ e.to < n)
    (hpad : ∀ e ∈ own, -VGAP ≤ e.pad) (hh : ∀ i, 0 ≤ h i) {i j : Nat} (r : Reach own i j) :
    heightsOf h n own dag topPad i ≤ heightsOf h n own dag topPad j ∧
      (i ≠ j → heightsOf h n own dag topPad i + h i ≤ heightsOf h n own dag topPad j) := by
  induction r with
  | refl => exact ⟨Int.le_refl _, fun hne => absurd rfl hne⟩
  | step e he _ ih =>
    have h1 := heightsOf_edge (h := h) (topPad := topPad) hsub hfwd hpad he
    have h2 := hh e.fr
    have h3 := ih.1
    exact ⟨by omega, fun _ => by omega⟩

/-- **The heights do not depend on the order.** Where Kahn's order serves the flow's own edges
alone, the heights along it are the heights along the items' own order. The consumer has no
such law: its two branches are two pictures that are each right. -/
theorem heightsOf_any_order (h : Nat → Int) {n : Nat} {own : List Edge}
    (hfwd : ∀ e ∈ own, e.fr < e.to ∧ e.to < n) (topPad : Int) :
    heightsOf h n own own topPad = Layers.heights (reading h) own topPad (List.range n) := by
  have hs := orderFor_serves h (fun _ he => he) hfwd
  have hown : (orderFor n own own).1 = own := by
    unfold orderFor
    by_cases hk : Layers.serves (reading fun _ => 0) own (kahn n own) = true
    · rw [if_pos hk]
    · rw [if_neg hk]
  unfold heightsOf
  rw [hown] at hs ⊢
  exact Layers.heights_unique hs.2 (Layers.serves_range hfwd) topPad

/-! ## d3-sankey's example -/

/-- The 68 links of `test/energy.json` of d3-sankey at `bb7233ea0004`, each from the index of
its source to the index of its target, in the order of the file. -/
def energy : List Edge :=
  [(0, 1), (1, 2), (1, 3), (1, 4), (1, 5), (6, 2), (7, 4), (8, 9), (10, 9), (9, 4), (11, 12),
    (11, 13), (11, 14), (15, 16), (15, 14), (15, 17), (15, 12), (15, 18), (15, 19), (15, 13),
    (15, 3), (15, 20), (15, 21), (15, 22), (23, 24), (25, 24), (5, 13), (5, 3), (5, 26), (5, 19),
    (5, 12), (27, 15), (17, 28), (17, 3), (28, 18), (29, 15), (2, 12), (2, 30), (2, 18), (2, 31),
    (2, 32), (2, 19), (2, 33), (2, 20), (34, 1), (24, 5), (35, 26), (36, 37), (38, 37), (37, 2),
    (39, 4), (39, 1), (40, 14), (40, 13), (41, 15), (42, 14), (43, 42), (43, 41), (4, 19),
    (4, 26), (4, 12), (26, 15), (26, 3), (26, 11), (44, 15), (45, 1), (46, 15),
    (47, 15)].map fun p => { fr := p.1, to := p.2 }

/-- A step of one for each link, as `computeNodeDepths` counts. -/
def unit : Layers.Reading Edge Nat := ⟨(·.fr), (·.to), fun _ => 1⟩

/-- The order that the consumer's `kahn` gives the 48 nodes. -/
def energyOrder : List Nat := kahn 48 energy

/-- The depth of each node: the longest way into it, in links. -/
def energyDepth : Nat → Int := Layers.read 0 (Layers.table unit energy 0 energyOrder)

/-- The column of a node as d3-sankey's default alignment has it (`justify` of
`src/align.js`): its depth, or the last column for a node with no link out of it. -/
def energyColumn (k : Nat) : Int :=
  if energy.any (·.fr == k) then energyDepth k
  else ((List.range 48).map energyDepth).foldl max 0

-- The nodes of the file are not listed in an order that serves its links: the link from
-- node 26 to node 15 goes back. A control for `serves_range`, which asks that links go
-- forward.
#guard !Layers.serves unit energy (List.range 48)

-- Kahn's order, as the consumer writes it, has each of the 48 nodes once and serves the 68
-- links.
#guard energyOrder.length == 48
#guard Layers.serves unit energy energyOrder

-- **The 48 columns of d3's expected file** (`test/energy-nodes.json`, each `x` read as the
-- index of its column).
#guard (List.range 48).map energyColumn ==
  [0, 1, 2, 7, 2, 2, 0, 0, 0, 1, 0, 4, 7, 7, 7, 4, 7, 5, 7, 7, 7, 7, 7, 0, 1, 0, 3, 0, 6, 0, 7, 7,
    7, 7, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]

-- `computeNodeHeights` is the same count along the links turned round, in the order turned
-- round. The longest way out of a node and the longest way into a node are one length over the
-- whole graph, seven links.
#guard Layers.serves unit.turned energy energyOrder.reverse
#guard ((List.range 48).map
  (Layers.read 0 (Layers.table unit.turned energy 0 energyOrder.reverse))).foldl max 0 == 7

/-- A second order of the 48 nodes: by the columns of d3's file, and within a column by index.
It is not the order that Kahn's algorithm gives. -/
def energyByColumn : List Nat :=
  (List.range 8).flatMap fun c =>
    (List.range 48).filter fun k =>
      ([0, 1, 2, 7, 2, 2, 0, 0, 0, 1, 0, 4, 7, 7, 7, 4, 7, 5, 7, 7, 7, 7, 7, 0, 1, 0, 3, 0, 6, 0,
        7, 7, 7, 7, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0] : List Nat).getD k 0 == c

#guard energyByColumn != energyOrder

/-- A reader: `Layers.heights_unique` at the 48 nodes. Both orders pass the test, so the two
give every node one depth, with no evaluation of a depth. -/
theorem energy_one_picture :
    Layers.heights unit energy 0 energyOrder = Layers.heights unit energy 0 energyByColumn :=
  Layers.heights_unique ((Layers.serves_iff unit energy energyOrder).mp (by decide))
    ((Layers.serves_iff unit energy energyByColumn).mp (by decide)) 0

/-! ## Controls: orders that do not serve -/

/-- Two links in a row: from `0` to `1`, and from `1` to `2`. -/
def chain : List Edge := [{ fr := 0, to := 1 }, { fr := 1, to := 2 }]

-- Along the order turned round, the second link is not met: `2` is placed while `1` still
-- stands at the start, and `1` then moves down beside it. This is why `heights_meets` asks
-- that the order serves. Along the order that serves, `2` stands two steps down.
#guard !Layers.serves unit chain [2, 1, 0]
#guard Layers.read 0 (Layers.table unit chain 0 [2, 1, 0]) 1 == 1
#guard Layers.read 0 (Layers.table unit chain 0 [2, 1, 0]) 2 == 1
#guard Layers.read 0 (Layers.table unit chain 0 [0, 1, 2]) 2 == 2

-- One link alone is met along either order, since its source stands at the start until it is
-- placed. So the test is sufficient for a picture that meets its links, and not necessary.
#guard !Layers.serves unit [{ fr := 0, to := 1 }] [1, 0]
#guard Layers.read 0 (Layers.table unit [{ fr := 0, to := 1 }] 0 [1, 0]) 1 == 1

-- No order serves a cycle, in either direction, and none serves a link from a thing to itself.
#guard !Layers.serves unit [{ fr := 0, to := 1 }, { fr := 1, to := 0 }] [0, 1]
#guard !Layers.serves unit [{ fr := 0, to := 1 }, { fr := 1, to := 0 }] [1, 0]
#guard !Layers.serves unit [{ fr := 0, to := 0 }] [0]

-- An order with a thing twice does not serve: the second placing of `0` reads `1` above it.
#guard !Layers.serves unit [{ fr := 0, to := 1 }] [0, 1, 0]

-- A distance may be negative, as the consumer's hidden edges have it (`pad := -VGAP`): the
-- target may then stand above its source, and never above the start.
#guard Layers.read 10 (Layers.table (reading fun _ => 0) [{ fr := 0, to := 1, pad := -100 }] 10
  [0, 1]) 1 == 10

end WhatwgTest.Svg.UseLayers
