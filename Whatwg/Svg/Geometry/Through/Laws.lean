import Whatwg.Svg.Geometry.Through
import Whatwg.Svg.Geometry.Grid

/-!
# Whatwg.Svg.Geometry.Through.Laws

Owner: the laws of a generator of curves (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Geometry/Through.lean` has a curve through a list of points as a value with four
laws. Here is what a caller gets from the four, for every generator at once, and what the two
kinds of generator of the kit are.

- **The old functions are the new ones at a form** (`through_cubics`, `areaCubics_through`,
  `line_through`, `link_through`, `area_through`, `Pen.curve_through`): `Shape.line c`,
  `Shape.link c`, `Shape.area c` and `Pen.curve` are the line, the link, the area and the pen of
  the generator `Curve.toThrough c`. An area of a form goes back along its flipped form. Each is
  true by definition, so no caller of the old ones changes.
- `monotoneX_cubics`, `monotoneY_cubics`: the pieces of the two monotone generators are
  `Curve.monotoneX` and `Curve.monotoneY`.
- `cubics_nil`: a generator has no piece for no point.
- **An area is a chain** (`chained_areaCubics`), and its pieces are the pieces of the top, the
  straight segment across and the pieces of the way back (`mem_areaCubics`).
- **Moved points** (`commutes`, `areaCubics_move`): a generator commutes with a move in the
  sense of `Whatwg/Svg/Scene/Moves.lean`, so a curve computed at one place stands for the curve
  at every other (`Commutes.stored`, `Commutes.from_origin`). The outline of an area between
  moved lines is the outline, moved.
- **The path as written** (`line_done`, `endPoint_line`, `endPoint_line_of`): the line of a
  generator is one subpath, and it ends at the last point, rounded once, where it draws
  anything.
- **A monotone area never leaves the band of its data** (`monotoneX_area_range`): where every
  point of the top and of the base is between `lo` and `hi` in height, so is every point of the
  outline. An area over the axis whose values are never negative never dips under the axis. No
  form of `Curve` has this law: a cardinal spline overshoots.

The laws of the monotone curve along `y` that are not laws of every generator are in
`Whatwg/Svg/Geometry/Monotone/Mirror.lean`. Its chain, its two ends and its move are the four
laws of the generator `Curve.Through.monotoneY`, with no proof of their own.

What this module does not claim: a law of the rounded coordinates of an area as written; that
the outline of an area does not cross itself, which is false of a top that goes under its base.
-/

namespace Whatwg.Svg.Value

namespace Curve

open Whatwg.Svg.Scene (Moves Commutes)

/-! ## The old functions are the new ones at a form -/

/-- The pieces of the generator of a form are the curve of the form. -/
theorem toThrough_cubics (c : Curve) : (toThrough c).cubics = c.cubics := rfl

/-- **The outline of an area of a form is the outline of its generator**, which goes back along
the flipped form. -/
theorem areaCubics_through (c : Curve) (top base : List Vec) :
    c.areaCubics top base = (toThrough c).areaCubics top base (toThrough c.flip) := rfl

/-- `Shape.line` is the line of the generator of the form. -/
theorem line_through (c : Curve) (points : List Vec) (places : Nat) :
    Shape.line c points places = (toThrough c).line points places := rfl

/-- `Shape.link` is the link of the generator of the form. -/
theorem link_through (c : Curve) (a b : Vec) (places : Nat) :
    Shape.link c a b places = (toThrough c).link a b places := rfl

/-- `Shape.area` is the area of the generator of the form, back along the flipped form. -/
theorem area_through (c : Curve) (top base : List Vec) (places : Nat) :
    Shape.area c top base places = (toThrough c).area top base places (toThrough c.flip) := rfl

/-- `Pen.curve` is the pen of the generator of the form. -/
theorem _root_.Whatwg.Svg.Value.Pen.curve_through (pen : Pen) (c : Curve) (points : List Vec)
    (places : Nat) : pen.curve c points places = pen.through (toThrough c) points places := rfl

namespace Through

/-- The pieces of the monotone generator along `x` are `Curve.monotoneX`. -/
theorem monotoneX_cubics : monotoneX.cubics = Curve.monotoneX := rfl

/-- The pieces of the monotone generator along `y` are `Curve.monotoneY`. -/
theorem monotoneY_cubics : monotoneY.cubics = Curve.monotoneY := rfl

/-! ## Every generator -/

/-- **A generator has no piece for no point**: a first piece would start at a first point. -/
theorem cubics_nil (g : Through) : g.cubics [] = [] := by
  cases h : g.cubics [] with
  | nil => rfl
  | cons c rest =>
    have e := g.starts [] c (congrArg List.head? h)
    cases e

/-- **The outline of an area is a chain**, whatever carries the way back. -/
theorem chained_areaCubics (g back : Through) (top base : List Vec) :
    Cubic.Chained (g.areaCubics top base back) = true :=
  chained_bridge (g.cubics top) (back.cubics base.reverse) top.getLast? base.getLast?
    (g.chained top) (back.chained base.reverse)
    (fun x hx => g.ends top x hx)
    (fun y hy => by
      have h := back.starts base.reverse y hy
      rw [List.head?_reverse] at h
      exact h)

/-- **The pieces of an area**: a piece of the top, the straight segment from the last point of
the top to the last point of the base, or a piece of the way back. -/
theorem mem_areaCubics {g back : Through} {top base : List Vec} {c : Cubic}
    (h : c ∈ g.areaCubics top base back) :
    c ∈ g.cubics top ∨
      (∃ t b, top.getLast? = some t ∧ base.getLast? = some b ∧ c = Cubic.line t b) ∨
      c ∈ back.cubics base.reverse := by
  unfold areaCubics at h
  rcases List.mem_append.mp h with h1 | h3
  · rcases List.mem_append.mp h1 with h1 | h2
    · exact Or.inl h1
    · cases ht : top.getLast? with
      | none =>
        rw [ht] at h2
        cases h2
      | some t =>
        cases hb : base.getLast? with
        | none =>
          rw [ht, hb] at h2
          cases h2
        | some b =>
          rw [ht, hb] at h2
          exact Or.inr (Or.inl ⟨t, b, rfl, rfl, List.mem_singleton.mp h2⟩)
  · exact Or.inr (Or.inr h3)

/-- **A generator commutes with a move**: its pieces through moved points are its pieces,
moved. It is the fourth law of a generator in the words of `Whatwg/Svg/Scene/Moves.lean`, so a
stored curve stands for the curve at a moved place (`Commutes.stored`). -/
theorem commutes (g : Through) : Commutes (δ := Vec) g.cubics := fun d points =>
  g.moved d points

/-- **The outline of an area between moved lines is the outline, moved.** -/
theorem areaCubics_move (g back : Through) (d : Vec) (top base : List Vec) :
    g.areaCubics (top.map fun p => p + d) (base.map fun p => p + d) back =
      (g.areaCubics top base back).map (Cubic.move d) := by
  unfold areaCubics
  rw [g.moved, ← List.map_reverse, back.moved, List.getLast?_map, List.getLast?_map,
    List.map_append, List.map_append]
  cases top.getLast? with
  | none => rfl
  | some t =>
    cases base.getLast? with
    | none => rfl
    | some b =>
      exact congrArg
        (fun m => List.map (Cubic.move d) (g.cubics top) ++ m ++
          List.map (Cubic.move d) (back.cubics base.reverse))
        (list_one (Cubic.move_line d t b).symm)

/-! ## The path as written -/

/-- **The line of a generator is one subpath**: its pieces are a chain. -/
theorem line_done (g : Through) (points : List Vec) (places : Nat) (pen : Pen)
    (h : Pen.ofCubics? (g.cubics points) places = some pen) : pen.done = [] :=
  Pen.done_ofCubics? (g.cubics points) places pen (g.chained points) h

/-- The line of a generator ends at the end of its last piece, as written. -/
theorem endPoint_line (g : Through) (points : List Vec) (places : Nat) :
    (g.line points places).endPoint =
      (g.cubics points).getLast?.map fun c => c.p3.round places :=
  Path.endPoint_ofCubics _ _

/-- **The line of a generator ends at the last point**, rounded once, where it draws
anything. -/
theorem endPoint_line_of (g : Through) (points : List Vec) (places : Nat) {c : Cubic}
    (h : (g.cubics points).getLast? = some c) :
    (g.line points places).endPoint = points.getLast?.map fun p => p.round places := by
  rw [endPoint_line, h, g.ends points c h]
  rfl

/-! ## The area under a monotone curve -/

/-- **A monotone area never leaves the band of its data.** Where every point of the top and
every point of the base is between `lo` and `hi` in height, so is every point of the outline:
of the top, of the straight segment across and of the way back. -/
theorem monotoneX_area_range (top base : List Vec) {lo hi : Rat}
    (ht : ∀ p ∈ top, lo ≤ p.y ∧ p.y ≤ hi) (hb : ∀ p ∈ base, lo ≤ p.y ∧ p.y ≤ hi) {c : Cubic}
    (hc : c ∈ monotoneX.areaCubics top base) {s : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    lo ≤ (c.pointAt s).y ∧ (c.pointAt s).y ≤ hi := by
  rcases mem_areaCubics hc with h | ⟨t, b, h1, h2, rfl⟩ | h
  · exact monotoneX_range top ht h hs0 hs1
  · have mt := ht t (List.mem_of_getLast? h1)
    have mb := hb b (List.mem_of_getLast? h2)
    rw [Cubic.line_pointAt]
    exact Box.step_mem mt.1 mt.2 mb.1 mb.2 hs0 hs1
  · exact monotoneX_range base.reverse (fun p hp => hb p (List.mem_reverse.mp hp)) h hs0 hs1

end Through

end Curve

end Whatwg.Svg.Value
