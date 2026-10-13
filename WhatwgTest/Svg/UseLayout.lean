import Whatwg.Svg.Scene.Layout

/-!
# WhatwgTest.Svg.UseLayout

Where lean4-effect4's view places its boxes, on `Whatwg/Svg/Scene/Extent.lean` and
`Whatwg/Svg/Scene/Layout.lean` (slice S22). The consumer is read at its checkout `6ad8f7b8d`.
This module imports nothing of that package: it restates the consumer's types under the
consumer's names.

**What is ported, and what it was.**

| The consumer's | Here |
| --- | --- |
| `Rect`, `Rect.Disjoint`, `Rect.holds`, `Rect.move` (`tools/Tools/View/Picture.lean`, lines 54 to 59, 203 to 206, 280) | `IBox`, `IBox.Disjoint`, `IBox.Holds`, `Moves.move` |
| `frameSides`, `frameSides_pairwise` (lines 140 to 143, 249 to 271) | the same two, and `frameSides_no_pixel`, which is what the consumer's sentence says of them |
| `Placed`, with `Flow.moveX` and `Box.shift` (`tools/Tools/View/Graph.lean`, line 150; `Flow.lean`, line 374; `FlowLaws.lean`, line 281) | `Placed` with an instance of `Moves` and one of `Boxed` |
| `nodeBox`, `span`, `stackIn`, `stack`, `framed`, and the fold `layWith` with `layAllWith` (`Flow.lean`, lines 413 to 446, 539 to 562) | `lay`, a fold into `Layout Placed`: `leaf`, `row`, `stack`, `inset` |
| `XApart`, `Within`, `Within.moveX`, `Within.mono`, `centre_bounds`, `good_centred`, `span_nonneg`, and the parts of `good_moved`, `good_series`, `good_stack`, `good_sideBySide`, `good_framed`, `lay_good` and `place_apart` that are about places (`FlowLaws.lean`, lines 250 to 335, 488 to 620, 1245, 1580) | `lay_fits`, `lay_clear`, `place_apart`, each one case for each constructor |
| the frame of a region as two folds of `min` and `max` (`Flow.layout`, `Flow.lean`, lines 824 to 831) | `frameOf`, with the law that it holds what the region holds |

**What the fold here is, and is not.** `lay` places the boxes of a flow on both axes at once:
a series is a `stack`, so each part stands below the part before it, and branches are a `row`.
The consumer's fold places across only, and finds the heights afterwards, as the layers of the
part's edges and its waits (`WhatwgTest/Svg/UseLayers.lean` is that half). For a flow with no
wait the two give one picture of the boxes, since the layers of parts in series add and the
layers of branches side by side are the greatest; no theorem here says so. The edges, the
ports of a fork, the marks and the lanes are not placed here: `Layout` gives a link no room.

**What the consumer gains.** `place_apart` and `lay_fits` hold of every flow by a fold with one
line for each constructor, where `lay_good` has the same facts among others over a thousand
lines. A frame that holds its region is a theorem (`item_inside_frame`), where the consumer
has the folds and no law of them. And a part may be built in any grouping
(`Layout.beside_assoc`).

The guards are of two kinds. Finite evaluations: one flow placed, against numbers computed by
hand in the comment above it. Controls: parts in one room, and a thing wider than its room,
where the laws of `Clear` do not hold and why they ask what they ask.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UseLayout

open Whatwg.Svg.Scene

/-! ## A box of whole pixels: the consumer's `Rect` -/

/-- The four sides of a frame, `w` thick inside the box: top, bottom, left, right. The
consumer's `frameSides`. -/
def frameSides (b : IBox) (w : Int) : List IBox :=
  [⟨b.x0, b.y0, b.x1, b.y0 + w⟩, ⟨b.x0, b.y1 - w, b.x1, b.y1⟩,
    ⟨b.x0, b.y0 + w, b.x0 + w, b.y1 - w⟩, ⟨b.x1 - w, b.y0 + w, b.x1, b.y1 - w⟩]

/-- The four sides of a frame share no pixel: the consumer's `frameSides_pairwise`, with its
proof. -/
theorem frameSides_pairwise (b : IBox) (w : Int) (hx : 2 * w < b.x1 - b.x0)
    (hy : 2 * w < b.y1 - b.y0) : (frameSides b w).Pairwise IBox.Disjoint := by
  unfold frameSides
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by show b.y0 + w ≤ b.y1 - w; omega)))
    · exact Or.inr (Or.inr (Or.inl (Int.le_refl _)))
    · exact Or.inr (Or.inr (Or.inl (Int.le_refl _)))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Int.le_refl _)))
    · exact Or.inr (Or.inr (Or.inr (Int.le_refl _)))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact Or.inl (by show b.x0 + w ≤ b.x1 - w; omega)
  · intro r hr
    cases hr

/-- **No pixel is in two sides of a frame.** The consumer says this in words; its law states
four inequalities. `IBox.Disjoint.not_holds` is the step between the two. -/
theorem frameSides_no_pixel (b : IBox) (w : Int) (hx : 2 * w < b.x1 - b.x0)
    (hy : 2 * w < b.y1 - b.y0) :
    (frameSides b w).Pairwise fun s t => ∀ p : IVec, s.Holds p → ¬t.Holds p :=
  (frameSides_pairwise b w hx hy).imp fun h (p : IVec) hs => IBox.Disjoint.not_holds h (p := p) hs

/-! ## A placed item: the consumer's `Placed` -/

/-- A node: its key, two short lines of text, and whether it is lit. The consumer's `GNode`. -/
structure GNode where
  key : String
  line1 : String
  line2 : String := ""
  lit : Bool := false
  deriving DecidableEq, Repr

/-- A placed item: a node's box, or a point that a long edge passes through. The consumer's
`Placed`. -/
structure Placed where
  key : String
  x : Int
  y : Int
  w : Int
  node : Option GNode := none
  grow : Nat := 1000
  deriving DecidableEq, Repr

/-- The grid: the consumer's `CELL`, `ROWH`, `GAP` and `BOXROWS`, and what its flow makes of
them (`VGAP`, `MARGIN`, `LABEL`). -/
def CELL : Nat := 8
def ROWH : Nat := 24
def HGAP : Nat := CELL * 2
def BOXH : Nat := ROWH * 2
def VGAP : Nat := ROWH
def MARGIN : Nat := CELL
def LABEL : Nat := ROWH

/-- An item's height: a box's rows; a point has none. The consumer's `itemH`. -/
def itemH (p : Placed) : Int := if p.node.isSome then BOXH else 0

/-- An item moves by whole pixels: the consumer's `moveX`, on both axes. -/
instance : Moves IVec Placed where
  move d p := { p with x := p.x + d.x, y := p.y + d.y }
  move_zero p := by
    cases p
    simp only [IVec.zero_x, IVec.zero_y, Int.add_zero]
  move_move d e p := by
    cases p
    simp only [IVec.add_x, IVec.add_y, Int.add_assoc]

/-- The room of an item: its width across, and its rows down. -/
instance : Boxed Placed where
  box p := ⟨p.x, p.y, p.x + p.w, p.y + itemH p⟩
  box_move d p := IBox.ext rfl rfl (Int.add_right_comm p.x d.x p.w)
    (Int.add_right_comm p.y d.y (itemH p))

/-! ## The layout of a flow -/

/-- A program's flow, as far as its places read it: the consumer's `Flow`, less the waits of a
node and the kind of a branching. -/
inductive Flow where
  | node (key line1 line2 : String)
  | seq (parts : List Flow)
  | par (key : String) (branches : List Flow)
  | region (name key : String) (body : Flow)
  | loop (key : String) (body : Flow)

/-- A node's box as a part: the consumer's `nodeBox`. -/
def nodeBox (width : GNode → Nat) (k l1 l2 : String) : Layout Placed :=
  Layout.leaf (width ⟨k, l1, l2, false⟩) BOXH
    { key := k, x := 0, y := 0, w := width ⟨k, l1, l2, false⟩, node := some ⟨k, l1, l2, false⟩ }

mutual

/-- **The layout of a flow**, its nodes at a given width: a fold. A series is its parts one
above the other, each centred in the widest; branches stand side by side; a region is its part
inside a margin, under a row for its name. The consumer's `layWith`. -/
def lay (width : GNode → Nat) : Flow → Layout Placed
  | .node k l1 l2 => nodeBox width k l1 l2
  | .seq ps => Layout.stack VGAP ((layAll width ps).filter fun l => !l.items.isEmpty)
  | .par _ bs => Layout.row HGAP (layAll width bs)
  | .region _ _ body => Layout.inset MARGIN (MARGIN + LABEL) MARGIN MARGIN (lay width body)
  | .loop _ body => lay width body

/-- Flows laid out. -/
def layAll (width : GNode → Nat) : List Flow → List (Layout Placed)
  | [] => []
  | f :: fs => lay width f :: layAll width fs

end

/-- A node's box fits its own room. -/
theorem nodeBox_fits (width : GNode → Nat) (k l1 l2 : String) : (nodeBox width k l1 l2).Fits :=
  Layout.fits_leaf ⟨Int.le_refl 0, Int.le_of_eq (Int.zero_add _), Int.le_refl 0,
    Int.le_of_eq (Int.zero_add _)⟩

mutual

/-- **Every box of a flow's layout stands inside the layout's room**: the consumer's `Within`
of `lay_good`, on both axes. -/
theorem lay_fits (width : GNode → Nat) : ∀ f : Flow, (lay width f).Fits
  | .node k l1 l2 => by
    rw [lay]
    exact nodeBox_fits width k l1 l2
  | .seq ps => by
    rw [lay]
    exact Layout.Fits.stack VGAP fun l hl => layAll_fits width ps l (List.mem_filter.mp hl).1
  | .par _ bs => by
    rw [lay]
    exact Layout.Fits.row HGAP _ (layAll_fits width bs)
  | .region _ _ body => by
    rw [lay]
    exact (lay_fits width body).inset
  | .loop _ body => by
    rw [lay]
    exact lay_fits width body

/-- The same for a list of flows. -/
theorem layAll_fits (width : GNode → Nat) : ∀ (fs : List Flow), ∀ l ∈ layAll width fs, l.Fits
  | [], _, h => by
    rw [layAll] at h
    exact nomatch h
  | f :: fs, l, h => by
    rw [layAll] at h
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact lay_fits width f
    | inr h' => exact layAll_fits width fs l h'

end

mutual

/-- **No two boxes of a flow's layout share a pixel.** -/
theorem lay_clear (width : GNode → Nat) : ∀ f : Flow, (lay width f).Clear
  | .node k l1 l2 => by
    rw [lay]
    exact Layout.clear_leaf _ _ _
  | .seq ps => by
    rw [lay]
    exact Layout.Clear.stack VGAP
      (fun l hl => layAll_fits width ps l (List.mem_filter.mp hl).1)
      fun l hl => layAll_clear width ps l (List.mem_filter.mp hl).1
  | .par _ bs => by
    rw [lay]
    exact Layout.Clear.row HGAP _ (layAll_fits width bs) (layAll_clear width bs)
  | .region _ _ body => by
    rw [lay]
    exact (lay_clear width body).inset
  | .loop _ body => by
    rw [lay]
    exact lay_clear width body

/-- The same for a list of flows. -/
theorem layAll_clear (width : GNode → Nat) : ∀ (fs : List Flow), ∀ l ∈ layAll width fs, l.Clear
  | [], _, h => by
    rw [layAll] at h
    exact nomatch h
  | f :: fs, l, h => by
    rw [layAll] at h
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact lay_clear width f
    | inr h' => exact layAll_clear width fs l h'

end

/-- **Any two boxes of a flow's layout stand apart**, wherever the layout is placed: side by
side, or one above the other. The consumer's `place_apart`, for every flow and every origin. -/
theorem place_apart (width : GNode → Nat) (f : Flow) (origin : IVec) :
    (Layout.place origin (lay width f)).Pairwise fun p q =>
      p.x + p.w ≤ q.x ∨ q.x + q.w ≤ p.x ∨ p.y + itemH p ≤ q.y ∨ q.y + itemH q ≤ p.y :=
  (lay_clear width f).place origin

/-- Every box of a placed layout is inside the room of the layout where it stands. -/
theorem place_within (width : GNode → Nat) (f : Flow) (origin : IVec) :
    ∀ p ∈ Layout.place origin (lay width f),
      (Boxed.box p).Inside (Moves.move origin (lay width f).room) :=
  (lay_fits width f).place origin

/-! ## The frame of a region -/

/-- **The frame of a region**: the least box that holds its items and the frames inside it,
with the region's margin and the row of its name. `none` for a region that holds nothing. The
consumer writes it as a fold of `min` over the tops and a fold of `max` over the bottoms. -/
def frameOf (mine : List Placed) (inner : List IBox) : Option IBox :=
  (IBox.merge (boxAll mine) (IBox.hullAll inner)).map
    (IBox.grow MARGIN (MARGIN + LABEL) MARGIN MARGIN)

/-- A box is inside the frame that is made from a room that holds it. -/
theorem inside_frame {mine : List Placed} {inner : List IBox} {x h f : IBox}
    (hm : IBox.merge (boxAll mine) (IBox.hullAll inner) = some h) (hx : x.Inside h)
    (hf : frameOf mine inner = some f) : x.Inside f := by
  rw [frameOf, hm] at hf
  rw [← Option.some.inj hf]
  exact hx.trans (IBox.inside_grow (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    (Int.natCast_nonneg _) (Int.natCast_nonneg _) h)

/-- **Every item of a region is inside the region's frame.** -/
theorem item_inside_frame {mine : List Placed} {inner : List IBox} {p : Placed} {f : IBox}
    (hp : p ∈ mine) (hf : frameOf mine inner = some f) : (Boxed.box p).Inside f := by
  cases hm : IBox.merge (boxAll mine) (IBox.hullAll inner) with
  | none =>
    rw [frameOf, hm] at hf
    exact nomatch hf
  | some h =>
    cases hb : boxAll mine with
    | none =>
      have e : mine.map Boxed.box = [] := IBox.hullAll_eq_none hb
      rw [List.map_eq_nil_iff.mp e] at hp
      exact nomatch hp
    | some m =>
      exact inside_frame hm ((inside_boxAll hp hb).trans (IBox.inside_merge_left hb hm)) hf

/-- **Every frame inside a region is inside the region's frame.** -/
theorem inner_inside_frame {mine : List Placed} {inner : List IBox} {r f : IBox}
    (hr : r ∈ inner) (hf : frameOf mine inner = some f) : r.Inside f := by
  cases hm : IBox.merge (boxAll mine) (IBox.hullAll inner) with
  | none =>
    rw [frameOf, hm] at hf
    exact nomatch hf
  | some h =>
    cases hi : IBox.hullAll inner with
    | none =>
      rw [IBox.hullAll_eq_none hi] at hr
      exact nomatch hr
    | some m =>
      exact inside_frame hm ((IBox.inside_hullAll hr hi).trans (IBox.inside_merge_right hi hm)) hf

/-! ## One flow, placed -/

/-- Every box six cells wide. -/
def six : GNode → Nat := fun _ => 6 * CELL

/-- A node, a fork of two nodes, and a node, in series. -/
def fork : Flow :=
  .seq [.node "a" "" "", .par "p" [.node "b" "" "", .node "c" "" ""], .node "d" "" ""]

-- The room and the places, by hand. A box is 48 by 48. The two branches side by side are
-- 48 + 16 + 48 = 112 wide, which is the widest part. `a` and `d` are centred in it, at
-- (112 - 48) / 2 = 32. The rows stand 48 + 24 = 72 apart: at 0, 72 and 144. The room is 112
-- by 144 + 48 = 192.
#guard ((lay six fork).w, (lay six fork).h) == (112, 192)
#guard (lay six fork).items.map (fun p => (p.key, p.x, p.y)) ==
  [("a", 32, 0), ("b", 0, 72), ("c", 64, 72), ("d", 32, 144)]

-- The same flow in a region stands a margin in and a margin and a row down, and the room is
-- wider by two margins and higher by two margins and a row.
#guard ((lay six (.region "scoped" "r" fork)).w, (lay six (.region "scoped" "r" fork)).h) ==
  (128, 232)
#guard (lay six (.region "scoped" "r" fork)).items.map (fun p => (p.key, p.x, p.y)) ==
  [("a", 40, 32), ("b", 8, 104), ("c", 72, 104), ("d", 40, 176)]

-- The frame of the region's items is its room: the least box that holds the four boxes, grown
-- by the margins, is the box from the origin, 128 by 232.
#guard frameOf (lay six (.region "scoped" "r" fork)).items [] == some ⟨0, 0, 128, 232⟩

-- An empty part of a series takes no row and no gap, as the consumer's filter has it.
#guard (lay six (.seq [.node "a" "" "", .seq [], .node "d" "" ""])).h == 120

/-! ## Controls -/

/-- One box, as a part. -/
def one : Layout Placed := lay six (.node "a" "" "")

-- Two parts in one room are not clear: `over` has no law of `Clear`, and this is why.
#guard decide (Layout.over one one).Fits
#guard !decide (Layout.over one one).Clear

/-- A box 40 wide in a room 10 wide: a part that does not fit. -/
def wide : Layout Placed :=
  Layout.leaf 10 48
    { key := "wide", x := 0, y := 0, w := 40, node := some ⟨"wide", "", "", false⟩ }

-- A part that does not fit breaks its neighbour: the second box starts at 10 + 16 = 26, inside
-- the first. `Clear.beside` asks that both parts fit, and this is why.
#guard !decide wide.Fits
#guard decide wide.Clear
#guard !decide (Layout.beside HGAP wide one).Clear

-- With no gap, two boxes that fit share an edge and no pixel: a box does not hold its last
-- edge.
#guard decide (Layout.beside 0 one one).Clear

end WhatwgTest.Svg.UseLayout
