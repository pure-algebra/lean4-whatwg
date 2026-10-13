import Whatwg.Svg.Geometry.Stack.Layers.Laws
import WhatwgTest.Svg.D3Through

/-!
# WhatwgTest.Svg.StackLayers

The stack tests of d3-shape, converted and run against `Stack` of
`Whatwg/Svg/Geometry/Stack/Layers.lean`, and the one level of lean4-effect4's queue, written on
it.

**Sources.**

- https://github.com/d3/d3-shape, the files `test/stack-test.js`, `test/offset/none-test.js`
  and `test/offset/diverging-test.js` at commit `a82254af78f0` of `main`. Copyright 2010-2022
  Mike Bostock, ISC licence. Every expected stack below that is marked as d3's is one of d3's
  test vectors, typed as the test has it.
- lean4-effect4's sketch of 2026-10-13, `docs/research/2026-10-13-living-quantities/sketch.html`
  in this repository, section "The run is one level": the Queue scene of capacity 2, nine steps.
  Its three paths are below as the sketch has them. The sketch says of itself that its values
  are the scene's and its placement is by hand.

## How a case of d3 is converted

d3's series are, for each layer, a pair `[y0, y1]` at each beat. A layer here is its values,
`y1 - y0` of d3's series before the offset is applied, and a band is its pairs.

- `stackOffsetNone(series, order)` with d3's own order is `Stack.pile floor layers`, with
  `floor` the `y0` of the first series. `stack()(data)` is `Stack.plain (Stack.layers data)`.
- `stackOffsetDiverging(series, order)` is `Stack.diverging layers`.
- `stackOrderReverse` is the list of layers reversed, and the bands reversed back.

## What was found

Of the 22 tests of the three files, 12 are of the stacking, and 9 of them are converted, each as
one guard that the kit's stack is d3's. Of the other 3, one is of `stackOffsetExpand`, which the
kit does not have, and two are of a value that is no number, which `Rat` does not have. The
other 10 tests are of d3's accessors and defaults, which are no part of a stack of numbers.

`Stack.signed` is d3's diverging stack wherever no value is zero. Two guards show where it
differs, on d3's own vector for zeros.

## The port: the one level of the queue

The sketch draws three counts of the queue at ten beats on one axis: the units held fill the
vessel from zero up to its brim at the capacity, the offers that wait press above the brim, and
the takers that wait are a deficit below zero. As a stack that is four layers: the takers, with
their sign; the units held; the room that is left in the vessel, which is not drawn; and the
offers. The kit's edges of the three layers that are drawn, at the sketch's scale, are the
sketch's three paths, each coordinate within a twentieth of a pixel (the sketch writes one
place), but for one control point: the sketch gives the last piece of an edge that ends on a
slope the slope of its chord, and d3's monotone curve, which the kit has, gives it `slope2`. So
the picture that was placed by hand is a fold of the counts, and the fold says where the hand
left d3's rule.
-/

namespace WhatwgTest.Svg.StackLayers

open Whatwg.Svg.Value
open WhatwgTest.Svg.D3Through (outline)

/-! ## stack-test.js -/

-- stack().keys([0, 1, 2, 3])([[1, 3, 5, 1], [2, 4, 2, 3], [1, 2, 4, 2]])
#guard Stack.plain (Stack.layers [[1, 3, 5, 1], [2, 4, 2, 3], [1, 2, 4, 2]]) ==
  [[(0, 1), (0, 2), (0, 1)], [(1, 4), (2, 6), (1, 3)], [(4, 9), (6, 8), (3, 7)],
    [(9, 10), (8, 11), (7, 9)]]

-- stack().keys([0, 1, 2, 3]).order(stackOrderReverse)(data)
#guard (Stack.plain (Stack.layers [[1, 3, 5, 1], [2, 4, 2, 3], [1, 2, 4, 2]]).reverse).reverse ==
  [[(9, 10), (9, 11), (8, 9)], [(6, 9), (5, 9), (6, 8)], [(1, 6), (3, 5), (2, 6)],
    [(0, 1), (0, 3), (0, 2)]]

-- The layers of d3's rows: the layer `i` is the value `i` of every row.
#guard Stack.layers [[1, 3, 5, 1], [2, 4, 2, 3], [1, 2, 4, 2]] ==
  [[1, 2, 1], [3, 4, 2], [5, 2, 4], [1, 3, 2]]

/-! ## offset/none-test.js -/

-- "stacks upon the first layer's existing positions"
-- stackOffsetNone([[[1, 2], [2, 4], [3, 4]], [[0, 3], [0, 4], [0, 2]], [[0, 5], [0, 2], [0, 4]]])
#guard Stack.pile [1, 2, 3] [[1, 2, 1], [3, 4, 2], [5, 2, 4]] ==
  [[(1, 2), (2, 4), (3, 4)], [(2, 5), (4, 8), (4, 6)], [(5, 10), (8, 10), (6, 10)]]

-- "observes the specified order": stackOrderReverse
#guard (Stack.plain ([[1, 2, 1], [3, 4, 2], [5, 2, 4]] : List (List Rat)).reverse).reverse ==
  [[(8, 9), (6, 8), (6, 7)], [(5, 8), (2, 6), (4, 6)], [(0, 5), (0, 2), (0, 4)]]

/-! ## offset/diverging-test.js -/

-- "applies a zero baseline, ignoring existing offsets"
#guard Stack.diverging [[1, 2, 1], [3, 4, 2], [5, 2, 4]] ==
  [[(0, 1), (0, 2), (0, 1)], [(1, 4), (2, 6), (1, 3)], [(4, 9), (6, 8), (3, 7)]]

-- "handles a single series"
#guard Stack.diverging [[1, 2, 1]] == [[(0, 1), (0, 2), (0, 1)]]

-- "observes the specified order": stackOrderReverse
#guard (Stack.diverging ([[1, 2, 1], [3, 4, 2], [5, 2, 4]] : List (List Rat)).reverse).reverse ==
  [[(8, 9), (6, 8), (6, 7)], [(5, 8), (2, 6), (4, 6)], [(0, 5), (0, 2), (0, 4)]]

-- "puts negative values below zero, in order"
#guard Stack.diverging [[1, -2, -1], [-3, -4, -2], [-5, -2, 4]] ==
  [[(0, 1), (-2, 0), (-1, 0)], [(-3, 0), (-6, -2), (-3, -1)], [(-8, -3), (-8, -6), (0, 4)]]

-- "puts zero values at zero, in order"
#guard Stack.diverging [[1, 2, -1], [3, 0, 0], [5, 2, 4]] ==
  [[(0, 1), (0, 2), (-1, 0)], [(1, 4), (0, 0), (0, 0)], [(4, 9), (2, 4), (0, 4)]]

/-! ## The signed stack beside d3's diverging stack -/

-- With no value of zero the signed stack has d3's edges: its baseline and its top are d3's
-- lower and upper edge, in the order that the sign of the value gives.
#guard (Stack.signed [[1, -2, -1], [-3, -4, -2], [-5, -2, 4]]).map (·.map Stack.span) ==
  Stack.diverging [[1, -2, -1], [-3, -4, -2], [-5, -2, 4]]

-- The top less the baseline is the value, with its sign: the first layer goes down by `2` at
-- its second beat.
#guard (Stack.signed [[1, -2, -1], [-3, -4, -2], [-5, -2, 4]]).map Stack.heights ==
  [[1, -2, -1], [-3, -4, -2], [-5, -2, 4]]

-- Where it differs: on d3's vector for zeros, the second layer is nothing at its second beat.
-- d3 puts it at zero. The signed stack puts it on the upper edge, at `2`, where the first
-- layer ends: the layer has no value below zero, so its side is the upper one.
#guard (Stack.signed [[1, 2, -1], [3, 0, 0], [5, 2, 4]]).map (·.map Stack.span) ==
  [[(0, 1), (0, 2), (-1, 0)], [(1, 4), (2, 2), (0, 0)], [(4, 9), (2, 4), (0, 4)]]

/-! ## The queue of the sketch: capacity 2, nine steps, ten beats -/

/-- The capacity of the queue. -/
def cap : Rat := 2

/-- The units held at each beat. -/
def held : List Rat := [0, 1, 2, 2, 2, 1, 0, 0, 1, 0]

/-- The offers that wait at each beat. -/
def offers : List Rat := [0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

/-- The takers that wait at each beat. -/
def takers : List Rat := [0, 0, 0, 0, 0, 0, 0, 1, 1, 0]

/-- The four layers of the one level: the takers with their sign, the units held, the room that
is left, and the offers. -/
def level : List (List Rat) :=
  [takers.map fun t => -t, held, held.map fun h => cap - h, offers]

/-- The abscissae of the ten beats in the sketch. -/
def beats : List Rat := (List.range 10).map fun (i : Nat) => 70 + 78 * (i : Rat)

/-- The sketch's scale: zero at `150`, and a unit `26` upward. -/
def scale (band : List (Rat × Rat)) : List (Rat × Rat) :=
  band.map fun e => (150 - 26 * e.1, 150 - 26 * e.2)

/-- The outer edge of the layer `i` of the level, at the sketch's scale, by the monotone
curve. -/
def edgeOf (i : Nat) : List Cubic :=
  Curve.monotoneX (Stack.edge beats (Stack.tops (scale ((Stack.signed level).getD i []))))

/-- The pieces that a path of the sketch draws, without its two segments of no length. -/
def drawn (path : String) : List Cubic := (outline path).filter fun c => c.p0 != c.p3

/-- Two numbers within a twentieth: one as the sketch writes it at one place. -/
def near (a b : Rat) : Bool := a - b ≤ 1 / 20 && b - a ≤ 1 / 20

/-- Two points within a twentieth along each axis. -/
def nearPoint (p q : Vec) : Bool := near p.x q.x && near p.y q.y

/-- The kit's pieces are the sketch's, each of the four points of each within a twentieth. -/
def sameAs (kit sketch : List Cubic) : Bool :=
  kit.length == sketch.length &&
    (kit.zip sketch).all fun (c, d) =>
      nearPoint c.p0 d.p0 && nearPoint c.p1 d.p1 && nearPoint c.p2 d.p2 && nearPoint c.p3 d.p3

-- The bands of the level: the takers hang from zero, the units held stand on zero, the room
-- stands on them and ends at the brim, and the offers stand on the brim.
#guard Stack.signed level ==
  [[(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, -1), (0, -1), (0, 0)],
    [(0, 0), (0, 1), (0, 2), (0, 2), (0, 2), (0, 1), (0, 0), (0, 0), (0, 1), (0, 0)],
    [(0, 2), (1, 2), (2, 2), (2, 2), (2, 2), (1, 2), (0, 2), (0, 2), (1, 2), (0, 2)],
    [(2, 2), (2, 2), (2, 2), (2, 3), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2)]]

/-- The sketch's path of the units held. -/
def sketchHeld : List Cubic := drawn
  "M70.0 150.0 L70.0 150.0 C96.0 141.3 122.0 132.7 148.0 124.0 C174.0 115.3 200.0 98.0 226.0 98.0 C252.0 98.0 278.0 98.0 304.0 98.0 C330.0 98.0 356.0 98.0 382.0 98.0 C408.0 98.0 434.0 115.3 460.0 124.0 C486.0 132.7 512.0 150.0 538.0 150.0 C564.0 150.0 590.0 150.0 616.0 150.0 C642.0 150.0 668.0 124.0 694.0 124.0 C720.0 124.0 746.0 141.3 772.0 150.0 L772.0 150.0 Z"

/-- The sketch's path of the offers that wait. -/
def sketchOffers : List Cubic := drawn
  "M70.0 98.0 L70.0 98.0 C96.0 98.0 122.0 98.0 148.0 98.0 C174.0 98.0 200.0 98.0 226.0 98.0 C252.0 98.0 278.0 72.0 304.0 72.0 C330.0 72.0 356.0 98.0 382.0 98.0 C408.0 98.0 434.0 98.0 460.0 98.0 C486.0 98.0 512.0 98.0 538.0 98.0 C564.0 98.0 590.0 98.0 616.0 98.0 C642.0 98.0 668.0 98.0 694.0 98.0 C720.0 98.0 746.0 98.0 772.0 98.0 L772.0 98.0 Z"

/-- The sketch's path of the takers that wait. -/
def sketchTakers : List Cubic := drawn
  "M70.0 150.0 L70.0 150.0 C96.0 150.0 122.0 150.0 148.0 150.0 C174.0 150.0 200.0 150.0 226.0 150.0 C252.0 150.0 278.0 150.0 304.0 150.0 C330.0 150.0 356.0 150.0 382.0 150.0 C408.0 150.0 434.0 150.0 460.0 150.0 C486.0 150.0 512.0 150.0 538.0 150.0 C564.0 150.0 590.0 176.0 616.0 176.0 C642.0 176.0 668.0 176.0 694.0 176.0 C720.0 176.0 746.0 158.7 772.0 150.0 L772.0 150.0 Z"

-- **The offers that wait**: the kit's edge is the sketch's path, all nine pieces. Its baseline
-- is the brim, which is the top of the room.
#guard sameAs (edgeOf 3) sketchOffers

-- **The units held**: the kit's edge is the sketch's path in its first eight pieces, and in
-- three of the four points of the ninth.
#guard sameAs (edgeOf 1).dropLast sketchHeld.dropLast

-- **The takers that wait**: the same, below zero.
#guard sameAs (edgeOf 0).dropLast sketchTakers.dropLast

-- Where the sketch is not d3's curve: the last piece of an edge that ends on a slope. d3 gives
-- the last point the slope `(3 s - t) / 2`, with `s` the slope of the chord and `t` the slope
-- at the point before (its `slope2`): here `1/2`, and the second control point at `137`. The
-- sketch, placed by hand, has the slope of the chord, `1/3`, and the control point at `141.3`.
-- The kit is d3's. Both stay between the two values.
#guard ((edgeOf 1).getLast?.map fun c => (c.p0, c.p1, c.p2, c.p3)) ==
    some (⟨694, 124⟩, ⟨720, 124⟩, ⟨746, 137⟩, ⟨772, 150⟩) &&
  (sketchHeld.getLast?.map fun c => (c.p0, c.p1, c.p2, c.p3)) ==
    some (⟨694, 124⟩, ⟨720, 124⟩, ⟨746, 1413 / 10⟩, ⟨772, 150⟩)
#guard ((edgeOf 0).getLast?.map fun c => c.p2) == some ⟨746, 163⟩ &&
  (sketchTakers.getLast?.map fun c => c.p2) == some ⟨746, 1587 / 10⟩

-- A control of the comparison: the edge of the units held is not the sketch's path of the
-- offers.
#guard !sameAs (edgeOf 1) sketchOffers

-- The area of a layer is one call. The area of the units held at the sketch's scale: nine
-- pieces along its top, the segment across at the last beat, and nine back along zero.
#guard (Curve.Through.monotoneX.between beats (scale ((Stack.signed level).getD 1 []))).length == 19

-- Why a value of zero stands on the edge of its side. With d3's rule the offers, which are
-- nothing at the third beat, stand at zero there, and their area from the third beat to the
-- fourth is drawn from zero across the units held. With the kit's rule they stand on the brim.
#guard ((Stack.diverging level).getD 3 []).getD 2 (9, 9) == (0, 0) &&
  ((Stack.signed level).getD 3 []).getD 2 (9, 9) == (2, 2)

/-! ## The laws, read at the queue -/

/-- **At every beat the height of each layer of the level is its count**, the takers' with
their sign: `Stack.heights_signed` at the queue. -/
theorem level_heights : (Stack.signed level).map Stack.heights = level :=
  Stack.heights_signed (takers.map fun t => -t) [held, held.map fun h => cap - h, offers]
    (by decide)

/-- The band of the offers that wait, as a layer upon the brim. -/
def pressure : List (Rat × Rat) :=
  List.zipWith (fun b v => (b, b + v)) (List.replicate 10 cap) offers

/-- The band of the units held, as a layer upon zero. -/
def vessel : List (Rat × Rat) :=
  List.zipWith (fun b v => (b, b + v)) (List.replicate 10 0) held

-- The two are the bands that the signed stack gives the offers and the units held: the offers
-- stand on the brim at every beat, and the units held on zero.
#guard (Stack.signed level).getD 3 [] == pressure && (Stack.signed level).getD 1 [] == vessel

/-- **The offers never go under the brim, at a beat or between two**: `Stack.first_over_level`
at the queue. Every point of the lower edge of their layer is at the capacity, and no point of
its upper edge is under it. -/
theorem pressure_over_brim {c d : Cubic}
    (hc : c ∈ Curve.monotoneX (Stack.edge beats (Stack.tops pressure)))
    (hd : d ∈ Curve.monotoneX (Stack.edge beats (Stack.bases pressure))) {s t : Rat}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (d.pointAt t).y = cap ∧ cap ≤ (c.pointAt s).y :=
  Stack.first_over_level beats 10 cap offers (by decide) hc hd hs0 hs1 ht0 ht1

/-- **The units held never go under zero, at a beat or between two.** -/
theorem vessel_over_zero {c d : Cubic}
    (hc : c ∈ Curve.monotoneX (Stack.edge beats (Stack.tops vessel)))
    (hd : d ∈ Curve.monotoneX (Stack.edge beats (Stack.bases vessel))) {s t : Rat}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (d.pointAt t).y = 0 ∧ 0 ≤ (c.pointAt s).y :=
  Stack.first_over_level beats 10 0 held (by decide) hc hd hs0 hs1 ht0 ht1

-- Neighbouring layers of the level share their edge at every beat: the room stands on the
-- units held, and the offers on the room, whose top is the brim at every beat.
#guard
  let bands := Stack.signed level
  Stack.bases (bands.getD 2 []) == Stack.tops (bands.getD 1 []) &&
    Stack.bases (bands.getD 3 []) == Stack.tops (bands.getD 2 []) &&
    Stack.tops (bands.getD 2 []) == List.replicate 10 cap

/-! ## Between two beats: two edges can cross -/

-- A control of what the monotone curve does not promise. Two layers at three beats, no value
-- negative. The lower layer rises steeply to the second beat and slowly after it, and the upper
-- layer is thin there: `101`, `1` and `0`. Each edge stays between its own two values from the
-- second beat to the third. A fifth of the way along, the upper edge is under the lower one:
-- the upper layer has a place with no thickness to give.
#guard
  let band := (Stack.plain [[0, 100, 110], [101, 1, 0]]).getD 1 []
  let upper := (Curve.monotoneX (Stack.edge [0, 1, 2] (Stack.tops band))).getD 1 default
  let lower := (Curve.monotoneX (Stack.edge [0, 1, 2] (Stack.bases band))).getD 1 default
  Stack.heights band == [101, 1, 0] &&
    (upper.pointAt (1 / 5)).x == (lower.pointAt (1 / 5)).x &&
    (upper.pointAt (1 / 5)).y < (lower.pointAt (1 / 5)).y &&
    101 ≤ (upper.pointAt (1 / 5)).y && (upper.pointAt (1 / 5)).y ≤ 110 &&
    100 ≤ (lower.pointAt (1 / 5)).y && (lower.pointAt (1 / 5)).y ≤ 110

-- A control of `Stack.apart`, which asks that the two values of the lower edge are no more
-- than the two values of the upper. They are not here: the lower edge ends at `110` and the
-- upper starts at `101`.
#guard
  let band := (Stack.plain [[0, 100, 110], [101, 1, 0]]).getD 1 []
  !(max ((Stack.bases band).getD 1 0) ((Stack.bases band).getD 2 0) ≤
    min ((Stack.tops band).getD 1 0) ((Stack.tops band).getD 2 0))

/-! ## At the beats nothing overlaps -/

/-- The three layers of the level that stand above zero, with the room as its ten counts. -/
def above : List (List Rat) := [held, [2, 1, 0, 0, 0, 1, 2, 2, 1, 2], offers]

-- They are the layers of the level after the takers.
#guard above == level.drop 1

/-- **No two of the layers above zero overlap at a beat**: `Stack.pile_apart` at the queue. It
is `stack_apart` of `Whatwg/Svg/Geometry/Stack.lean`, of the row of intervals at each beat. -/
theorem above_apart {b : Nat} (hb : b < 10) :
    (Stack.column (Stack.pile (List.replicate 10 0) above) b).Pairwise fun p q => p.2 ≤ q.1 :=
  Stack.pile_apart above (List.replicate 10 0) b 0
    (by rw [List.getElem?_replicate, if_pos hb]) (by decide) (by decide)

end WhatwgTest.Svg.StackLayers
