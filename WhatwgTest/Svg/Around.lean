import Whatwg.Svg.Geometry.Around

/-!
# WhatwgTest.Svg.Around

The two arcs of lean4-effect4's graph, written on `Cubic.around` of
`Whatwg/Svg/Geometry/Around.lean`.

**Source.** lean4-effect4 at commit `6ad8f7b8d`, `tools/Tools/View/Graph.lean`: the `back` case
and the `loop` case of `segments` (lines 414 to 434), with the numbers of
`tools/Tools/View/Grid.lean` (`CELL`, `ROWH`, `BACK_RISE`, `LOOP_REACH`, `LOOP_HALF`). The
consumer counts in whole pixels and divides with a quotient that rounds down. `backInt` and
`loopInt` below are its two cases as they are written there, and `back` and `loop` are the same
two on the kit. This file is a template for the consumer's port.

## What the port shows

- **The arc of a back edge is one call**, `Cubic.around p q lane`. Its control points are the
  consumer's before the consumer rounds: the consumer's abscissa is the kit's, rounded down
  (`backInt_is_back`, on a table of placements).
- **The law of the consumer's comment.** The comment in the consumer says "controls a third past
  the lane, so the arc's widest point reaches the lane". `back_in_lane` is the half of it that
  holds of every back edge: the arc never passes its lane. `back_reaches` is the other half, on
  its condition: the arc reaches the lane where the two sides it joins stand at one abscissa. A
  guard is a back edge between two boxes of different widths, whose arc stops three pixels short
  of its lane.
- **The loop is the same function**, with a swell of a half. `loop_reaches` reads off the kit's
  law what the consumer's numbers do not say: a loop goes one and a half of `LOOP_REACH` off the
  side of its box, since its control points stand at twice `LOOP_REACH`.
-/

namespace WhatwgTest.Svg.Around

open Whatwg.Svg.Value

/-! ## The consumer's numbers and its two cases, as written there -/

def CELL : Int := 8
def ROWH : Int := 24
def BACK_RISE : Int := 4
def LOOP_REACH : Int := 2 * CELL
def LOOP_HALF : Int := 8

/-- The fields of the consumer's `Placed` that its arcs read. `box` is its `node.isSome`: an
item is a box, or a point that an edge passes. -/
structure Placed where
  x : Int
  y : Int
  w : Int
  box : Bool := true

/-- A point of whole pixels, as the consumer has one. -/
abbrev Pt := Int × Int

/-- The consumer's `side`: a box's side at its middle row, and a point as its own side. -/
def side (p : Placed) (rise : Int) : Pt :=
  if p.box then (p.x + p.w, p.y + ROWH - rise) else (p.x + 2 * CELL, p.y)

/-- The abscissa of a lane: the consumer's `lx`. -/
def laneX (width : Int) (lane : Nat) : Int := width - CELL * (2 * lane + 1)

/-- The consumer's `back` case: the four points of its arc, in whole pixels. -/
def backInt (width : Int) (a b : Placed) (lane : Nat) : Pt × Pt × Pt × Pt :=
  let lx := laneX width lane
  let p : Pt := side a 0
  let q : Pt := side b BACK_RISE
  let cx := lx + (lx - max p.1 q.1) / 3
  (p, (cx, p.2), (cx, q.2), q)

/-- The consumer's `loop` case: the four points of its arc, in whole pixels. -/
def loopInt (a : Placed) : Pt × Pt × Pt × Pt :=
  let x := a.x + a.w
  let y := a.y + ROWH
  ((x, y - LOOP_HALF), (x + 2 * LOOP_REACH, y - 2 * LOOP_HALF),
    (x + 2 * LOOP_REACH, y + 2 * LOOP_HALF), (x, y + LOOP_HALF))

/-! ## The two cases on the kit -/

/-- **The arc of a back edge**, from the side of its source round its lane to the side of its
target. -/
def back (width : Int) (a b : Placed) (lane : Nat) : Cubic :=
  Cubic.around (Vec.ofPair (side a 0)) (Vec.ofPair (side b BACK_RISE)) (laneX width lane)

/-- **The loop of an edge from a box to itself**: an arc between two points of the box's right
side, with a swell of a half, round the line a `LOOP_REACH` and a half off the side. -/
def loop (a : Placed) : Cubic :=
  Cubic.around ⟨(a.x + a.w : Int), (a.y + ROWH - LOOP_HALF : Int)⟩
    ⟨(a.x + a.w : Int), (a.y + ROWH + LOOP_HALF : Int)⟩
    ((a.x + a.w : Int) + 3 * (LOOP_REACH : Int) / 2) (1 / 2)

/-- A point of the kit, each coordinate rounded down to a whole pixel. -/
def floor (v : Vec) : Pt := (v.x.floor, v.y.floor)

/-- The four points of a segment of the kit, each rounded down. -/
def floors (c : Cubic) : Pt × Pt × Pt × Pt := (floor c.p0, floor c.p1, floor c.p2, floor c.p3)

/-! ## The port against the consumer's code -/

/-- Placements with no pattern: boxes of several widths, a point, and several lanes. -/
def table : List (Int × Placed × Placed × Nat) :=
  [(400, ⟨24, 200, 120, true⟩, ⟨24, 56, 96, true⟩, 0),
    (400, ⟨24, 200, 96, true⟩, ⟨24, 56, 96, true⟩, 0),
    (431, ⟨40, 300, 71, true⟩, ⟨16, 8, 205, true⟩, 2),
    (512, ⟨24, 128, 64, false⟩, ⟨160, 32, 88, true⟩, 1),
    (300, ⟨200, 90, 77, true⟩, ⟨8, 40, 13, false⟩, 0)]

-- `backInt_is_back`: the consumer's four points are the kit's, each rounded down, on every row
-- of the table. Only the abscissa of the two control points is ever rounded: a third of a whole
-- number.
#guard table.all fun (width, a, b, lane) => backInt width a b lane == floors (back width a b lane)

-- A control of the rounding: in the first row the kit's control points stand at `474 + 2/3`,
-- and the consumer's at `474`.
#guard (back 400 ⟨24, 200, 120, true⟩ ⟨24, 56, 96, true⟩ 0).p1.x == 1424 / 3 &&
  (backInt 400 ⟨24, 200, 120, true⟩ ⟨24, 56, 96, true⟩ 0).2.1.1 == 474

-- The consumer's loop is the kit's, with nothing rounded.
#guard table.all fun (_, a, _, _) =>
  let c := loop a
  let i := loopInt a
  c == ⟨Vec.ofPair i.1, Vec.ofPair i.2.1, Vec.ofPair i.2.2.1, Vec.ofPair i.2.2.2⟩

/-! ## The laws, read at the port -/

/-- **A back edge never passes its lane**, where neither of the two sides it joins is past the
lane: `Cubic.around_x_le` at the consumer's arc. -/
theorem back_in_lane (width : Int) (a b : Placed) (lane : Nat)
    (h : max (Vec.ofPair (side a 0)).x (Vec.ofPair (side b BACK_RISE)).x ≤ (laneX width lane : Rat))
    {t : Rat} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((back width a b lane).pointAt t).x ≤ (laneX width lane : Rat) :=
  Cubic.around_x_le _ _ 0 h ht0 ht1

/-- **A back edge reaches its lane** where the two sides it joins stand at one abscissa:
`Cubic.around_touches` at the consumer's arc. -/
theorem back_reaches (width : Int) (a b : Placed) (lane : Nat)
    (h : (Vec.ofPair (side a 0)).x = (Vec.ofPair (side b BACK_RISE)).x) :
    ((back width a b lane).pointAt (1 / 2)).x = (laneX width lane : Rat) :=
  Cubic.around_touches _ _ _ 0 h

/-- **A loop goes a `LOOP_REACH` and a half off the side of its box**: `Cubic.around_touches`
at the consumer's loop, whose two ends stand on the side. -/
theorem loop_reaches (a : Placed) :
    ((loop a).pointAt (1 / 2)).x = ((a.x + a.w : Int) : Rat) + 3 * (LOOP_REACH : Int) / 2 :=
  Cubic.around_touches _ _ _ _ rfl

-- The second row of the table joins two boxes with one right side, and its arc reaches its
-- lane: the consumer's comment holds there.
#guard ((back 400 ⟨24, 200, 96, true⟩ ⟨24, 56, 96, true⟩ 0).pointAt (1 / 2)).x == 392

-- A control of `back_reaches`, which asks that the two sides stand at one abscissa. The first
-- row joins a box whose side stands at `144` to one whose side stands at `120`. Its arc is
-- widest at `389`, three pixels short of its lane at `392`: an eighth of the `24` between the
-- two sides.
#guard ((back 400 ⟨24, 200, 120, true⟩ ⟨24, 56, 96, true⟩ 0).pointAt (1 / 2)).x == 389 &&
  laneX 400 0 == 392

-- A control of `back_in_lane`, which asks that neither side is past the lane. A box whose side
-- stands at `420` is past a lane at `392`, and the arc starts past it.
#guard ((back 400 ⟨300, 200, 120, true⟩ ⟨24, 56, 96, true⟩ 0).pointAt 0).x == 420

-- What the consumer's rounding costs: with the two sides at one abscissa and a distance to the
-- lane that is no multiple of three, the consumer's arc, with its control points rounded down,
-- is widest half a pixel short of its lane. The kit's reaches it.
#guard
  let i := backInt 400 ⟨24, 200, 96, true⟩ ⟨24, 56, 96, true⟩ 0
  let c : Cubic := ⟨Vec.ofPair i.1, Vec.ofPair i.2.1, Vec.ofPair i.2.2.1, Vec.ofPair i.2.2.2⟩
  (c.pointAt (1 / 2)).x == 392 - 1 / 2 &&
    ((back 400 ⟨24, 200, 96, true⟩ ⟨24, 56, 96, true⟩ 0).pointAt (1 / 2)).x == 392

end WhatwgTest.Svg.Around
