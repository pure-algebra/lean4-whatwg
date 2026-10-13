import WhatwgTest.Svg.UseLayers
import WhatwgTest.Svg.UseLayout
import Whatwg.Svg.Scene.Layered

/-!
# WhatwgTest.Svg.UseLayered

The two finite checks of lean4-effect4's graph view, as theorems of a picture built on
`Whatwg/Svg/Scene/Layered.lean` (slice S22). The consumer is read at its checkout `6ad8f7b8d`.
This module imports nothing of that package. It takes the consumer's `GEdge` and its ranks from
`WhatwgTest/Svg/UseLayers.lean` and its `GNode` and `Placed` from
`WhatwgTest/Svg/UseLayout.lean`, where they are restated under the consumer's names.

**What is ported, and what it was.**

| The consumer's (`tools/Tools/View/Graph.lean`) | Here |
| --- | --- |
| `Laid.boxesApart` (lines 713 to 720) | `Laid.boxesApart`, the same test, and `boxesApart_layout`: every graph passes it |
| `Laid.segmentDescends`, `downRouteDescends`, `edgesDescend` (lines 724 to 747) | the same three tests, and `edgesDescend_layout`: every graph with distinct keys passes |
| `downRouteDescends_iff`, `edgesDescend_down_pairs` (lines 737 to 757) | not ported: they say what a passing test means, and here the test is not run |
| `Graph.layout` (lines 293 to 319): `ranks`, the rows of `orders`, the heights of the rows, the routes of the forward edges | `layout`: `Layers.rows` of the ranks, `Layout.layered`, a route for each forward edge |

**What is not ported.** The points that a long edge passes through at each rank between its two
ends (`chain`, `items`); the order of a rank by barycentres (`reorder`, `orders`); and the
places across by Brandes and Köpf (`Place.centres`). Here an edge that passes several ranks is
one route of its two ends, each rank has its nodes in their own order, and a row is its boxes
from the left, a gap apart. So the pictures differ across; the heights are the consumer's, a
row for each rank. The two laws do not read what is left out: `Layers.Down.members` says that a
row may be put in any order, and `Layout.layered_below` holds of any part of a row.

**What the consumer gains.** It runs the two checks on each picture that it draws, and a
picture that fails is found when it is drawn. Here no picture fails: the checks are theorems
of the layout, for every graph (`boxesApart_layout`) and for every graph whose nodes have
distinct keys (`edgesDescend_layout`).

The guards are of two kinds. A finite evaluation: one graph, laid out, against places computed
by hand. Controls: a route that is drawn up, a graph with one key twice, and two boxes at one
place, each of which fails its check.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UseLayered

open Whatwg.Svg.Scene
open WhatwgTest.Svg.UseLayout (GNode Placed itemH BOXH HGAP VGAP six)
open WhatwgTest.Svg.UseLayers (GEdge)

/-! ## The graph, and its picture -/

/-- A graph: its nodes in their order, and its edges. The consumer's `Graph`, with lists where
it has arrays. -/
structure Graph where
  nodes : List GNode
  edges : List GEdge

/-- The graph as the ranking reads it: how many nodes, and the edges. -/
def Graph.ranked (g : Graph) : UseLayers.Graph := ⟨g.nodes.length, g.edges⟩

/-- The node at a position. A position past the last has a node with no text; no row holds
one. -/
def nodeAt (g : Graph) (i : Nat) : GNode := (g.nodes[i]?).getD ⟨"", "", "", false⟩

/-- The key of the node at a position: the consumer's `key` of `Graph.layout`. -/
def keyAt (g : Graph) (i : Nat) : String := (nodeAt g i).key

/-- The box of the node at a position, at the origin. -/
def item (width : GNode → Nat) (g : Graph) (i : Nat) : Placed :=
  { key := keyAt g i, x := 0, y := 0, w := width (nodeAt g i), node := some (nodeAt g i) }

/-- The box of a node as a part: one thing in a room of its width and a box's rows. -/
def part (width : GNode → Nat) (g : Graph) (i : Nat) : Layout Placed :=
  Layout.leaf (width (nodeAt g i)) BOXH (item width g i)

/-- **The rows of a graph**: the positions of the nodes of each rank, in their order. The
consumer's `orders` before its sweeps. The ranks are computed once, as a list. -/
def rows (g : Graph) : List (List Nat) :=
  let table :=
    Layers.table UseLayers.step (UseLayers.forward g.ranked) 0 (List.range g.nodes.length)
  Layers.rows (Layers.read 0 table) (List.range g.nodes.length)

/-- **The picture of a graph in layers**: the boxes of each rank in a row, and the rows one
above the next. -/
def picture (width : GNode → Nat) (g : Graph) : Layout Placed :=
  Layout.layered HGAP VGAP ((rows g).map fun row => row.map (part width g))

/-- A laid-out graph: its placed items, and the keys of each route that is drawn down. The
consumer's `Laid`, less its regions, its marks and its routes in lanes. -/
structure Laid where
  placed : List Placed
  routes : List (List String)

/-- **The layout of a graph**: its picture, and a route down for each forward edge. -/
def layout (width : GNode → Nat) (g : Graph) : Laid where
  placed := (picture width g).items
  routes := (UseLayers.forward g.ranked).map fun e => [keyAt g e.src, keyAt g e.dst]

/-! ## The consumer's two checks -/

namespace Laid

/-- The placed item with a key: the first that has it. The consumer's `Laid.find`. -/
def find (l : Laid) (k : String) : Option Placed := l.placed.find? (·.key == k)

/-- Two boxes share no pixel. The consumer writes this inside `boxesApart`. -/
def apart (p q : Placed) : Bool :=
  decide (p.x + p.w ≤ q.x) || decide (q.x + q.w ≤ p.x) || decide (p.y + (BOXH : Int) ≤ q.y) ||
    decide (q.y + (BOXH : Int) ≤ p.y)

/-- Each box is apart from each later one. The consumer's `go` of `boxesApart`. -/
def apartAll : List Placed → Bool
  | [] => true
  | p :: rest => rest.all (apart p) && apartAll rest

/-- **No two boxes share a pixel**: the consumer's `Laid.boxesApart`. -/
def boxesApart (l : Laid) : Bool := apartAll (l.placed.filter (·.node.isSome))

/-- One segment drawn down descends when both keys resolve and the target's top is at or below
its source's bottom. The consumer's `segmentDescends`. -/
def segmentDescends (l : Laid) (u v : String) : Bool :=
  match l.find u, l.find v with
  | some a, some b => decide (a.y + (if a.node.isSome then (BOXH : Int) else 0) ≤ b.y)
  | _, _ => false

/-- Every adjacent pair of a route drawn down descends. The consumer's `downRouteDescends`. -/
def downRouteDescends (l : Laid) (ks : List String) : Bool :=
  (ks.zip ks.tail).all fun pair => l.segmentDescends pair.1 pair.2

/-- **Every segment drawn down descends**: the consumer's `Laid.edgesDescend`. -/
def edgesDescend (l : Laid) : Bool := l.routes.all l.downRouteDescends

end Laid

/-! ## The first check is a theorem -/

theorem part_fits (width : GNode → Nat) (g : Graph) (i : Nat) : (part width g i).Fits :=
  Layout.fits_leaf ⟨Int.le_refl 0, Int.le_of_eq (Int.zero_add _), Int.le_refl 0,
    Int.le_of_eq (Int.zero_add _)⟩

/-- Each part of each row of the picture fits. -/
theorem parts_fit (width : GNode → Nat) (g : Graph) :
    ∀ r ∈ (rows g).map (fun row => row.map (part width g)), ∀ l ∈ r, l.Fits := fun r hr l hl => by
  obtain ⟨row, _, e⟩ := List.mem_map.mp hr
  rw [← e] at hl
  obtain ⟨i, _, e'⟩ := List.mem_map.mp hl
  rw [← e']
  exact part_fits width g i

/-- **No two things of the picture share room**, for every graph. -/
theorem picture_clear (width : GNode → Nat) (g : Graph) : (picture width g).Clear :=
  Layout.Clear.layered (parts_fit width g) fun r hr l hl => by
    obtain ⟨row, _, e⟩ := List.mem_map.mp hr
    rw [← e] at hl
    obtain ⟨i, _, e'⟩ := List.mem_map.mp hl
    rw [← e']
    exact Layout.clear_leaf _ _ _

/-- Two boxes whose rooms are disjoint are apart, as the check reads it. -/
theorem apart_of_disjoint {p q : Placed} (hp : p.node.isSome = true) (hq : q.node.isSome = true)
    (h : (Boxed.box p).Disjoint (Boxed.box q)) : Laid.apart p q = true := by
  have ep : itemH p = (BOXH : Int) := if_pos hp
  have eq : itemH q = (BOXH : Int) := if_pos hq
  have h' : p.x + p.w ≤ q.x ∨ q.x + q.w ≤ p.x ∨ p.y + itemH p ≤ q.y ∨ q.y + itemH q ≤ p.y := h
  rw [ep, eq] at h'
  simp only [Laid.apart, Bool.or_eq_true, decide_eq_true_iff]
  cases h' with
  | inl a => exact Or.inl (Or.inl (Or.inl a))
  | inr h' =>
    cases h' with
    | inl a => exact Or.inl (Or.inl (Or.inr a))
    | inr h' =>
      cases h' with
      | inl a => exact Or.inl (Or.inr a)
      | inr a => exact Or.inr a

/-- Boxes that are apart, each from each later one, pass the check. -/
theorem apartAll_of_pairwise : ∀ {l : List Placed},
    l.Pairwise (fun p q => Laid.apart p q = true) → Laid.apartAll l = true
  | [], _ => rfl
  | p :: rest, h => by
    have h' := List.pairwise_cons.mp h
    show (rest.all (Laid.apart p) && Laid.apartAll rest) = true
    rw [Bool.and_eq_true]
    exact ⟨List.all_eq_true.mpr h'.1, apartAll_of_pairwise h'.2⟩

/-- **The consumer's `boxesApart` holds of the layout of every graph.** It is `Layout.Clear` of
the picture, read at the boxes. -/
theorem boxesApart_layout (width : GNode → Nat) (g : Graph) :
    (layout width g).boxesApart = true :=
  apartAll_of_pairwise
    (((picture_clear width g).filter (fun p : Placed => p.node.isSome)).imp_of_mem
      fun hp hq h => apart_of_disjoint (List.mem_filter.mp hp).2 (List.mem_filter.mp hq).2 h)

/-! ## The second check is a theorem -/

/-- The rows are the rows of the ranks: the list of the ranks reads as the ranks. -/
theorem rows_eq (g : Graph) :
    rows g = Layers.rows (UseLayers.ranks g.ranked) (List.range g.nodes.length) := by
  have e : Layers.read 0 (Layers.table UseLayers.step (UseLayers.forward g.ranked) 0
      (List.range g.nodes.length)) = UseLayers.ranks g.ranked :=
    funext fun k => Layers.read_table _ _ _ _ k
  show Layers.rows (Layers.read 0 _) _ = _
  rw [e]

/-- **The rows go down the forward edges.** `Layers.rows_down` at the consumer's ranks. -/
theorem rows_down (g : Graph) :
    Layers.Down UseLayers.step (UseLayers.forward g.ranked) (rows g) := by
  rw [rows_eq]
  exact Layers.rows_down (UseLayers.forward_serves g.ranked) fun _ _ => Int.le_refl 1

/-- The keys of the parts of one row. -/
theorem row_keys (width : GNode → Nat) (g : Graph) : ∀ row : List Nat,
    ((row.map (part width g)).flatMap fun l => l.items).map (fun p : Placed => p.key) =
      row.map (keyAt g)
  | [] => rfl
  | i :: row => congrArg (keyAt g i :: ·) (row_keys width g row)

/-- **The keys of the picture are the keys of the rows**, row after row. -/
theorem picture_keys (width : GNode → Nat) (g : Graph) :
    (picture width g).items.map (fun p : Placed => p.key) =
      (rows g).flatMap fun row => row.map (keyAt g) := by
  rw [picture, Layout.layered_items_map (f := fun p : Placed => p.key) (fun _ _ => rfl)]
  generalize rows g = rs
  induction rs with
  | nil => rfl
  | cons row rest ih =>
    show (((row.map (part width g)).flatMap fun l => l.items) ++
        (rest.map fun row => row.map (part width g)).flatMap
          fun r => r.flatMap fun l => l.items).map (fun p : Placed => p.key) =
      row.map (keyAt g) ++ rest.flatMap fun row => row.map (keyAt g)
    rw [List.map_append, ih, row_keys]

/-- The keys of the positions are the keys of the nodes. -/
theorem range_keys (d : GNode) : ∀ nodes : List GNode,
    (List.range nodes.length).map (fun i => ((nodes[i]?).getD d).key) = nodes.map (·.key)
  | [] => rfl
  | n :: nodes => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.map_cons]
    exact congrArg (n.key :: ·) (range_keys d nodes)

/-- **The keys of the picture are distinct** where the keys of the nodes are. -/
theorem picture_distinct (width : GNode → Nat) (g : Graph) (hk : (g.nodes.map (·.key)).Nodup) :
    ((picture width g).items.map (fun p : Placed => p.key)).Nodup := by
  rw [picture_keys, rows_eq]
  refine Layers.rows_distinct (key := keyAt g) _ ?_
  show ((List.range g.nodes.length).map fun i => ((g.nodes[i]?).getD ⟨"", "", "", false⟩).key).Nodup
  rw [range_keys]
  exact hk

/-- **The consumer's `edgesDescend` holds of the layout of every graph whose nodes have
distinct keys.** A forward edge goes to a later rank (`Layers.rows_down`), a later rank is a
later row, and a part of an earlier row ends above every part of a later one
(`Layout.layered_link`). The keys are distinct so that the check finds the two boxes that the
law is about. -/
theorem edgesDescend_layout (width : GNode → Nat) (g : Graph)
    (hk : (g.nodes.map (·.key)).Nodup) : (layout width g).edgesDescend = true := by
  rw [Laid.edgesDescend, List.all_eq_true]
  intro ks hks
  obtain ⟨e, he, eks⟩ := List.mem_map.mp hks
  obtain ⟨d, d', hs, ht, hy⟩ :=
    Layout.layered_link (rows_down g) (part width g) HGAP VGAP he
  have hd := picture_distinct width g hk
  have ma : Moves.move d (item width g e.src) ∈ (picture width g).items :=
    hs _ List.mem_cons_self
  have mb : Moves.move d' (item width g e.dst) ∈ (picture width g).items :=
    ht _ List.mem_cons_self
  have fa : (layout width g).find (keyAt g e.src) = some (Moves.move d (item width g e.src)) :=
    find_of_distinct (fun p : Placed => p.key) hd ma rfl
  have fb : (layout width g).find (keyAt g e.dst) = some (Moves.move d' (item width g e.dst)) :=
    find_of_distinct (fun p : Placed => p.key) hd mb rfl
  rw [← eks]
  show ((layout width g).segmentDescends (keyAt g e.src) (keyAt g e.dst) && true) = true
  rw [Bool.and_true, Laid.segmentDescends, fa, fb]
  refine decide_eq_true ?_
  show (0 : Int) + d.y + (BOXH : Int) ≤ 0 + d'.y
  have hy' : d.y + (BOXH : Int) + (VGAP : Int) ≤ d'.y := hy
  omega

/-! ## One graph, laid out -/

/-- Four nodes: `a` forks to `b` and `c`, which join at `d`. One edge goes from `a` to `d` past
a rank, and one goes back from `d` to `a`. -/
def diamond : Graph where
  nodes := [⟨"a", "", "", false⟩, ⟨"b", "", "", false⟩, ⟨"c", "", "", false⟩, ⟨"d", "", "", false⟩]
  edges := [⟨"ab", 0, 1⟩, ⟨"ac", 0, 2⟩, ⟨"bd", 1, 3⟩, ⟨"cd", 2, 3⟩, ⟨"ad", 0, 3⟩, ⟨"da", 3, 0⟩]

-- The places, by hand. The ranks are 0 for `a`, 1 for `b` and `c`, and 2 for `d`. A box is 48
-- by 48, the rows stand 48 + 24 = 72 apart, and `c` stands 48 + 16 = 64 right of `b`.
#guard rows diamond == [[0], [1, 2], [3]]
#guard (layout six diamond).placed.map (fun p => (p.key, p.x, p.y)) ==
  [("a", 0, 0), ("b", 0, 72), ("c", 64, 72), ("d", 0, 144)]

-- A route for each forward edge, the long one among them, and none for the edge back.
#guard (layout six diamond).routes ==
  [["a", "b"], ["a", "c"], ["b", "d"], ["c", "d"], ["a", "d"]]

/-! ## Controls -/

-- A route that is drawn up does not pass: the check tests something.
#guard !({ (layout six diamond) with routes := [["d", "a"]] } : Laid).edgesDescend

/-- Three nodes in a line, the first and the last with one key. -/
def twice : Graph where
  nodes := [⟨"a", "", "", false⟩, ⟨"b", "", "", false⟩, ⟨"a", "", "", false⟩]
  edges := [⟨"ab", 0, 1⟩, ⟨"ba", 1, 2⟩]

-- With one key twice the check finds the first box of that key, which is the one at the top,
-- and the second edge is tested against it. `edgesDescend_layout` asks for distinct keys, and
-- this is why. The boxes are apart all the same.
#guard !(layout six twice).edgesDescend
#guard (layout six twice).boxesApart

-- Two boxes at one place are not apart.
#guard !({ placed := [item six diamond 0, item six diamond 1], routes := [] } : Laid).boxesApart

end WhatwgTest.Svg.UseLayered
