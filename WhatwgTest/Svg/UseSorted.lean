import WhatwgTest.Svg.UseLayers
import Whatwg.Svg.Scene.Layers.Sorted

/-!
# WhatwgTest.Svg.UseSorted

lean4-effect4's use of Kahn's algorithm, on `Whatwg/Svg/Scene/Layers/Sorted.lean` (slice S22).
The consumer is read at its checkout `6ad8f7b8d`. This module imports nothing of that package.
It takes the consumer's `Edge`, its reading of an edge and its `kahn` from
`WhatwgTest/Svg/UseLayers.lean`, where they are restated under the consumer's names.

**What is ported, and what it was.**

| The consumer's | Here |
| --- | --- |
| `Flow.kahn` (`tools/Tools/View/Flow.lean`, lines 670 to 679), and its form by tables: `kahnTake`, `kahnGo`, `kahnTable` (lines 683 to 715) | `order`, one line on `Layers.sorted` |
| `orderFor` (lines 750 to 752): Kahn's order where the test passes, else the items' own order with the flow's own edges | `order`, with no second branch: `acceptWaits_serves` says that the test passes |
| `searchNext`, `reaches` (lines 718 to 728), the search that `acceptWaits` (lines 739 to 745) asks whether a wait closes a cycle | `acceptWaits`, which asks `Layers.serves` of `Layers.sorted` whether the edges with the wait still have an order |
| `acceptWaits_keeps` (`tools/Tools/View/FlowLaws.lean`, lines 1466 to 1483) | `acceptWaits_keeps`, by the same fold |
| `orderFor_serves` (lines 1485 to 1508) | `acceptWaits_serves`: the order serves the flow's edges and every wait that was taken |
| `heightsOf` (`Flow.lean`, lines 760 to 762), `heightsOf_edge` (`FlowLaws.lean`, lines 1523 to 1532) | `heightsOf`, `heightsOf_edge`, and `heightsOf_wait` for a wait that was taken |

**What the consumer gains.**

- One picture. `orderFor` has two branches, and the consumer's laws hold of each. Which of them
  a flow takes is not known before it runs, since no law says that Kahn's order serves. Here
  the order always serves (`acceptWaits_serves`), so the heights always meet the flow's edges
  and the waits that were taken, and there is no second branch.
- `heightsOf_wait`: a wait that was taken is met, as an edge is. The consumer's
  `heightsOf_edge` speaks of the flow's own edges only, because the waits are met in one of the
  two branches.
- `order_own`: a flow with no wait keeps its items in their own order. So a flow that gains no
  wait does not change its order.
- A wait is refused exactly when no order serves the edges with it (`Layers.serves_sorted_iff`),
  and this needs no fuel: the consumer's search stops after `n + 1` steps.

**One difference.** A wait whose exit or await is no item of the part (a position `n` or more)
is refused here, since the order is of the positions below `n`. The consumer's search would
take it. Its waits come from the part's own items, so the case does not arise.

The guards: finite evaluations on d3-sankey's graph of `UseLayers.lean`, and controls with a
cycle and with an end that is no thing.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UseSorted

open Whatwg.Svg.Scene
open WhatwgTest.Svg.UseLayers (Edge reading VGAP)

/-! ## The order, and the waits that are taken -/

/-- The reading of an edge's two ends. An order serves the edges whatever their distances. -/
def ends : Layers.Reading Edge Nat := reading fun _ => 0

/-- **The order of a part's items** under some edges: the positions below `n`, by peeling
sources. The consumer's `kahnTable`. -/
def order (n : Nat) (dag : List Edge) : List Nat := Layers.sorted ends dag (List.range n)

/-- One wait, from a fiber's exit to its await: an edge where the edges with it still have an
order, and a lane where they have not. The consumer's step of `acceptWaits`. -/
def accept (n : Nat) (acc : List Edge × List (Nat × Nat) × List (Nat × Nat)) (c : Nat × Nat) :
    List Edge × List (Nat × Nat) × List (Nat × Nat) :=
  if Layers.serves ends (acc.1 ++ [{ fr := c.1, to := c.2, drawn := false }])
      (order n (acc.1 ++ [{ fr := c.1, to := c.2, drawn := false }])) then
    (acc.1 ++ [{ fr := c.1, to := c.2, drawn := false }], acc.2.1 ++ [c], acc.2.2)
  else (acc.1, acc.2.1, acc.2.2 ++ [c])

/-- **The waits as edges**, each from a fiber's exit to its await, where it closes no cycle;
and every wait, for a lane: first those that are edges, then those that would close a cycle.
The consumer's `acceptWaits`. -/
def acceptWaits (n : Nat) (es : List Edge) (candidates : List (Nat × Nat)) :
    List Edge × List (Nat × Nat) :=
  ((candidates.foldl (accept n) (es, [], [])).1,
    (candidates.foldl (accept n) (es, [], [])).2.1 ++
      (candidates.foldl (accept n) (es, [], [])).2.2)

/-- The positions below `n` have no position twice. -/
theorem range_nodup (n : Nat) : (List.range n).Nodup :=
  (Layers.serves_range (r := ends) (links := []) (n := n) fun _ h => nomatch h).1

/-- An order serves the edges whatever the heights of the items. -/
theorem serves_any {h h' : Nat → Int} {es : List Edge} {o : List Nat}
    (s : Layers.Serves (reading h) es o) : Layers.Serves (reading h') es o := s

/-- A fold of `accept` keeps what holds of the edges at the start and of each step. -/
theorem accept_fold (n : Nat) (p : List Edge → Prop)
    (step : ∀ (acc : List Edge × List (Nat × Nat) × List (Nat × Nat)) (c : Nat × Nat),
      p acc.1 → p (accept n acc c).1) :
    ∀ (cs : List (Nat × Nat)) (acc : List Edge × List (Nat × Nat) × List (Nat × Nat)),
      p acc.1 → p (cs.foldl (accept n) acc).1
  | [], _, h => h
  | c :: cs, acc, h => accept_fold n p step cs (accept n acc c) (step acc c h)

/-- **The flow's own edges are kept**: the consumer's `acceptWaits_keeps`. -/
theorem acceptWaits_keeps (n : Nat) (es : List Edge) (c : List (Nat × Nat)) :
    ∀ e ∈ es, e ∈ (acceptWaits n es c).1 :=
  accept_fold n (fun dag => ∀ e ∈ es, e ∈ dag)
    (fun acc c h e he => by
      unfold accept
      by_cases ht : Layers.serves ends (acc.1 ++ [{ fr := c.1, to := c.2, drawn := false }])
          (order n (acc.1 ++ [{ fr := c.1, to := c.2, drawn := false }])) = true
      · rw [if_pos ht]
        exact List.mem_append_left _ (h e he)
      · rw [if_neg ht]
        exact h e he)
    c (es, [], []) fun _ he => he

/-- **The order serves the flow's edges and every wait that was taken.** The consumer's
`orderFor_serves`, with no second branch. The flow's own edges go from an earlier item to a
later one, so they have an order; a wait is taken only where the edges with it still have
one. -/
theorem acceptWaits_serves (h : Nat → Int) {n : Nat} {es : List Edge}
    (hfwd : ∀ e ∈ es, e.fr < e.to ∧ e.to < n) (c : List (Nat × Nat)) :
    Layers.Serves (reading h) (acceptWaits n es c).1 (order n (acceptWaits n es c).1) :=
  serves_any (accept_fold n (fun dag => Layers.Serves ends dag (order n dag))
    (fun acc c hs => by
      unfold accept
      by_cases ht : Layers.serves ends (acc.1 ++ [{ fr := c.1, to := c.2, drawn := false }])
          (order n (acc.1 ++ [{ fr := c.1, to := c.2, drawn := false }])) = true
      · rw [if_pos ht]
        exact (Layers.serves_iff _ _ _).mp ht
      · rw [if_neg ht]
        exact hs)
    c (es, [], [])
    (Layers.sorted_serves (range_nodup n)
      (fun e he => ⟨List.mem_range.mpr (Nat.lt_trans (hfwd e he).1 (hfwd e he).2),
        List.mem_range.mpr (hfwd e he).2⟩)
      ⟨List.range n, Layers.serves_range hfwd⟩))

/-- **A flow with no wait keeps its items in their own order.** -/
theorem order_own {n : Nat} {es : List Edge} (hfwd : ∀ e ∈ es, e.fr < e.to ∧ e.to < n) :
    order n es = List.range n :=
  Layers.sorted_of_serves (Layers.serves_range (r := ends) hfwd)

/-! ## The heights -/

/-- **The heights of a part's items**: the consumer's `heightsOf`. `h` is the height of the item
at a position, `es` the part's edges, `waits` its waits, and `topPad` the room above its
entry. -/
def heightsOf (h : Nat → Int) (n : Nat) (es : List Edge) (waits : List (Nat × Nat))
    (topPad : Int) : Nat → Int :=
  Layers.heights (reading h) (acceptWaits n es waits).1 topPad (order n (acceptWaits n es waits).1)

/-- Every edge of the flow stands its target below its source's bottom: the consumer's
`heightsOf_edge`. -/
theorem heightsOf_edge {h : Nat → Int} {n : Nat} {es : List Edge} {waits : List (Nat × Nat)}
    {topPad : Int} (hfwd : ∀ e ∈ es, e.fr < e.to ∧ e.to < n) (hpad : ∀ e ∈ es, -VGAP ≤ e.pad)
    {e : Edge} (he : e ∈ es) :
    heightsOf h n es waits topPad e.fr + h e.fr ≤ heightsOf h n es waits topPad e.to := by
  have h1 : heightsOf h n es waits topPad e.fr + (h e.fr + VGAP + e.pad) ≤
      heightsOf h n es waits topPad e.to :=
    Layers.heights_meets (acceptWaits_serves h hfwd waits) topPad
      (acceptWaits_keeps n es waits e he)
  have h2 := hpad e he
  omega

/-- **A wait that was taken is met as an edge is**: whatever stands among the edges that the
heights follow stands its target at its distance below its source. -/
theorem heightsOf_wait {h : Nat → Int} {n : Nat} {es : List Edge} {waits : List (Nat × Nat)}
    {topPad : Int} (hfwd : ∀ e ∈ es, e.fr < e.to ∧ e.to < n) {e : Edge}
    (he : e ∈ (acceptWaits n es waits).1) :
    heightsOf h n es waits topPad e.fr + (h e.fr + VGAP + e.pad) ≤
      heightsOf h n es waits topPad e.to :=
  Layers.heights_meets (acceptWaits_serves h hfwd waits) topPad he

/-! ## d3-sankey's graph, and the consumer's Kahn -/

open WhatwgTest.Svg.UseLayers (energy energyOrder unit)

-- The order by peeling sources has each of the 48 nodes once and serves the 68 links. It is
-- not the order that the consumer's `kahn` gives.
#guard (Layers.sorted unit energy (List.range 48)).length == 48
#guard Layers.serves unit energy (Layers.sorted unit energy (List.range 48))
#guard Layers.sorted unit energy (List.range 48) != energyOrder

/-- A reader: `Layers.sorted_serves` at the 48 nodes. Kahn's order serves, so the order by
peeling sources does. No step of `sorted` is evaluated. -/
theorem energy_sorted : Layers.Serves unit energy (Layers.sorted unit energy (List.range 48)) :=
  Layers.sorted_serves (range_nodup 48) (by decide)
    ⟨energyOrder, (Layers.serves_iff unit energy energyOrder).mp (by decide)⟩

/-- A reader: the two orders give every node one depth (`Layers.heights_unique`). -/
theorem energy_one_picture :
    Layers.heights unit energy 0 (Layers.sorted unit energy (List.range 48)) =
      Layers.heights unit energy 0 energyOrder :=
  Layers.heights_unique energy_sorted
    ((Layers.serves_iff unit energy energyOrder).mp (by decide)) 0

/-! ## Waits -/

/-- A part of three items in a line. -/
def line : List Edge := [{ fr := 0, to := 1 }, { fr := 1, to := 2 }]

-- A wait from the last item back to the first would close a cycle: it is no edge, and it keeps
-- its lane. A wait from the first item to the last closes none, and is an edge.
#guard (acceptWaits 3 line [(2, 0)]).1.length == 2
#guard (acceptWaits 3 line [(2, 0)]).2 == [(2, 0)]
#guard (acceptWaits 3 line [(0, 2)]).1.length == 3

-- Two waits that close a cycle between them: the first is taken, and the second is refused
-- because of the first.
#guard (acceptWaits 4 [{ fr := 0, to := 1 }, { fr := 2, to := 3 }] [(1, 2), (3, 0)]).1.length == 3
#guard (acceptWaits 4 [{ fr := 0, to := 1 }, { fr := 2, to := 3 }] [(1, 2), (3, 0)]).2 ==
  [(1, 2), (3, 0)]

-- A wait that turns the order round: item 1 waits for item 2. The order is no longer the
-- items' own, and it serves.
#guard order 3 (acceptWaits 3 [{ fr := 0, to := 1 }, { fr := 0, to := 2 }] [(2, 1)]).1 == [0, 2, 1]

/-! ## Controls -/

-- On a cycle no order serves, and `sorted` gives the things back all the same.
#guard !Layers.serves unit [{ fr := 0, to := 1 }, { fr := 1, to := 0 }]
  (Layers.sorted unit [{ fr := 0, to := 1 }, { fr := 1, to := 0 }] [0, 1])
#guard Layers.sorted unit [{ fr := 0, to := 1 }, { fr := 1, to := 0 }] [0, 1] == [0, 1]

-- What stands on a cycle or after one is not lost: 2 has a link from the cycle of 0 and 1, no
-- thing is a source, and the three come back as they were given.
#guard Layers.sorted unit [{ fr := 0, to := 1 }, { fr := 1, to := 0 }, { fr := 1, to := 2 }]
  [2, 1, 0] == [2, 1, 0]

-- `sorted_serves` asks that both ends of each link are among the things, and this is why: the
-- link has an order, and its target is not among the things given.
#guard Layers.serves unit [{ fr := 0, to := 1 }] [0, 1]
#guard !Layers.serves unit [{ fr := 0, to := 1 }] (Layers.sorted unit [{ fr := 0, to := 1 }] [0])

-- Things in an order that does not serve are put in one that does.
#guard Layers.sorted unit line [2, 1, 0] == [0, 1, 2]

end WhatwgTest.Svg.UseSorted
