import WhatwgTest.Svg.UseLayout
import Whatwg.Svg.Scene.Layout.Order

/-!
# WhatwgTest.Svg.UseOrder

A flow's order and the layout that keeps it, on `Whatwg/Svg/Scene/Order.lean` and
`Whatwg/Svg/Scene/Layout/Order.lean` (slice S22). The consumer is read at its checkout
`6ad8f7b8d`. This module imports nothing of that package. It takes the consumer's `Flow`, its
`Placed` and the fold `lay` from `WhatwgTest/Svg/UseLayout.lean`, where they are restated under
the consumer's names.

**What is ported, and what it was.**

| The consumer's | Here |
| --- | --- |
| `AGraph`, `Rel`, `denote`, `edge_has`, the eight laws, `overlay_idem`, `absorb` (`tools/Tools/View/AlgGraph.lean`, lines 27 to 215) | the kit's `AGraph`, with the same names; `Rel` is `AGraph.Rel` |
| `Flow.order`, `orderSeq`, `orderPar` (`tools/Tools/View/FlowOrder.lean`, lines 36 to 52) | `order`, `orderAll`: a series is `AGraph.connects`, branches are `AGraph.overlays` |
| `Realizes`, `Realizes.congr`, `realizes_none`, `Realizes.moved` (lines 56 to 77) | `Layout.Realizes`, `Realizes.congr`, `realizes_none`, `Realizes.stands` |
| `series_subL`, `series_subR`, `series_across`, `realizes_series` (lines 81 to 124) | `Layout.Realizes.above` |
| `orderSeq_has`, `orderPar_has`, `orderPar_edge`, `connect_none_left`, `connect_congr_right` (lines 128 to 166) | `AGraph.has_connects`, `has_overlays`, `edge_overlays`, `connect_none_left`, `connect_congr` |
| `layAllWith_map`, `stackIn_realizes`, `stack_realizes` (lines 170 to 270) | `Layout.Realizes.stack`, with `AGraph.connects_filter` for the parts that are empty |
| `parAround_realizes`, `sideBySide_realizes`, `Realizes.reshare` (lines 276 to 367) | `Layout.Realizes.row` |
| `lay_realizes`, `layAll_realizes` (lines 371 to 408) | `lay_realizes`, `layAll_realizes`: one case for each constructor |
| `place_keeps_order` (lines 415 to 425) | `place_keeps_order`, at every origin and with the gap; `place_keeps_order_all` with distinct keys |

**What differs.** The consumer's `Realizes` says that the first node reaches the second along
the layout's edges, and its `place_keeps_order` then reads the heights that follow those edges.
Here the layout of `UseLayout.lean` places on both axes at once, a series is a stack, and
`Realizes` says the heights directly. So the consumer's `Good`, its `Reach` and its ports of a
fork are not read. The consumer's law says that the first node's bottom is at or above the
second's top. This one says that it is a row's gap above.

**What the consumer gains.** The law that its layout keeps its order follows by a fold with one
line for each constructor, from laws that hold of any layout built with `above`, `beside` and
`inset`. `place_keeps_order_all` says it of every node with a key and not of one, where keys
are distinct.

The guards: finite evaluations of the order of one flow, and controls. The converse of the law
is false, and with one key twice the law of every node is false.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UseOrder

open Whatwg.Svg.Scene
open WhatwgTest.Svg.UseLayout (Flow Placed GNode lay layAll lay_fits layAll_fits VGAP HGAP itemH
  six fork)

/-! ## A flow's order -/

mutual

/-- **A flow's order**: a fold of the flow into the algebra. A series connects its parts,
branches side by side are overlaid, and a region and a loop keep their body's order. The
consumer's `Flow.order`. -/
def order : Flow → AGraph String
  | .node k _ _ => .vertex k
  | .seq ps => AGraph.connects (orderAll ps)
  | .par _ bs => AGraph.overlays (orderAll bs)
  | .region _ _ b => order b
  | .loop _ b => order b

/-- The orders of some flows. -/
def orderAll : List Flow → List (AGraph String)
  | [] => []
  | f :: fs => order f :: orderAll fs

end

theorem orderAll_map : ∀ fs : List Flow, orderAll fs = fs.map order
  | [] => by rw [orderAll, List.map_nil]
  | f :: fs => by rw [orderAll, List.map_cons, orderAll_map fs]

theorem layAll_map (width : GNode → Nat) : ∀ fs : List Flow, layAll width fs = fs.map (lay width)
  | [] => by rw [layAll, List.map_nil]
  | f :: fs => by rw [layAll, List.map_cons, layAll_map width fs]

/-- The key of a placed item. -/
def key (p : Placed) : String := p.key

/-- A move does not change a key. -/
theorem key_move (d : IVec) (p : Placed) : key (Moves.move d p) = key p := rfl

/-! ## The layout realizes the order -/

mutual

/-- **The layout of a flow realizes the flow's order**, a row's gap apart: the consumer's
`lay_realizes`. One case for each constructor. -/
theorem lay_realizes (width : GNode → Nat) :
    ∀ f : Flow, Layout.Realizes key VGAP (order f) (lay width f)
  | .node k l1 l2 => by
    rw [order, lay]
    exact Layout.realizes_leaf key VGAP (width ⟨k, l1, l2, false⟩) UseLayout.BOXH
      { key := k, x := 0, y := 0, w := width ⟨k, l1, l2, false⟩, node := some ⟨k, l1, l2, false⟩ }
  | .seq ps => by
    rw [order, lay, orderAll_map, layAll_map, List.filter_map]
    refine (Layout.Realizes.stack key_move order (lay width) _
      (fun f hf => layAll_realizes width ps f (List.mem_filter.mp hf).1)
      fun f _ => lay_fits width f).congr ?_
    refine AGraph.connects_filter order _ ps fun f hf hp => ?_
    have he : (lay width f).items.isEmpty = true := by
      cases hb : (lay width f).items.isEmpty with
      | true => rfl
      | false =>
        have hp' : (!(lay width f).items.isEmpty) = false := hp
        rw [hb] at hp'
        exact nomatch hp'
    exact (layAll_realizes width ps f hf).no_vertex (List.isEmpty_iff.mp he)
  | .par _ bs => by
    rw [order, lay, orderAll_map, layAll_map]
    exact Layout.Realizes.row key_move order (lay width) HGAP bs (layAll_realizes width bs)
  | .region _ _ body => by
    rw [order, lay]
    exact (lay_realizes width body).stands key_move (Layout.stands_inset _ _ _ _ _)
  | .loop _ body => by
    rw [order, lay]
    exact lay_realizes width body

/-- The same for each flow of a list. -/
theorem layAll_realizes (width : GNode → Nat) :
    ∀ (fs : List Flow), ∀ f ∈ fs, Layout.Realizes key VGAP (order f) (lay width f)
  | [], _, h => nomatch h
  | f :: fs, g, h => by
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact lay_realizes width f
    | inr h' => exact layAll_realizes width fs g h'

end

/-- **What a flow orders, its layout draws above**: the consumer's `place_keeps_order`. Where
the order of a flow puts one node before another, the layout, placed at any origin, has a box
of the first key whose bottom is a row's gap above the top of a box of the second key. -/
theorem place_keeps_order (width : GNode → Nat) (f : Flow) (origin : IVec) {u v : String}
    (h : (AGraph.denote (order f)).edge u v) :
    ∃ p ∈ Layout.place origin (lay width f), ∃ q ∈ Layout.place origin (lay width f),
      p.key = u ∧ q.key = v ∧ p.y + itemH p + VGAP ≤ q.y :=
  (lay_realizes width f).place key_move origin h

/-- **With distinct keys, every box of the first key is above every box of the second.** -/
theorem place_keeps_order_all (width : GNode → Nat) (f : Flow)
    (hd : Distinct key (lay width f).items) {u v : String}
    (h : (AGraph.denote (order f)).edge u v) :
    ∀ p ∈ (lay width f).items, ∀ q ∈ (lay width f).items, p.key = u → q.key = v →
      p.y + itemH p + VGAP ≤ q.y :=
  (lay_realizes width f).all hd h

/-! ## One flow -/

-- `fork` of `UseLayout.lean`: `a`, then `b` and `c` side by side, then `d`. Its order puts `a`
-- before the three others, and `b` and `c` before `d`.
#guard decide ((AGraph.denote (order fork)).edge "a" "b")
#guard decide ((AGraph.denote (order fork)).edge "a" "d")
#guard decide ((AGraph.denote (order fork)).edge "c" "d")
#guard !decide ((AGraph.denote (order fork)).edge "d" "a")

-- The keys of its layout are distinct, so `place_keeps_order_all` reads it.
#guard decide ((lay six fork).items.map key).Nodup

/-! ## Controls -/

-- The converse of the law is false. The order has nothing between `b` and `c`, in either
-- direction, and they stand at one height.
#guard !decide ((AGraph.denote (order fork)).edge "b" "c")
#guard !decide ((AGraph.denote (order fork)).edge "c" "b")
#guard ((lay six fork).items.filter fun p => p.key == "b" || p.key == "c").map (·.y) == [72, 72]

/-- A series with one key twice: `a`, `b`, and `a` again. -/
def again : Flow := .seq [.node "a" "" "", .node "b" "" "", .node "a" "" ""]

-- With one key twice the order puts `b` before `a`, and a box of `a` is below `b`: the law of
-- one box of each key holds. The first box of `a` is above `b`, so the law of every box does
-- not: `place_keeps_order_all` asks for distinct keys, and this is why.
#guard decide ((AGraph.denote (order again)).edge "b" "a")
#guard !decide ((lay six again).items.map key).Nodup
#guard (lay six again).items.map (fun p => (p.key, p.y)) == [("a", 0), ("b", 72), ("a", 144)]

end WhatwgTest.Svg.UseOrder
