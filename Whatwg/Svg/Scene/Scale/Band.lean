
/-!
# Whatwg.Svg.Scene.Scale.Band

Owner: equal bands at equal steps (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A chart with a bar for each name, a grid of cells, the ranks of a layered graph, the columns of
a page: each puts things of one width at equal steps along a line. d3 calls it a band scale
(`d3-scale`, `src/band.js`). This module has it as a value in whole numbers, with the two ways
to make one and the way back from a place to its band, which d3 does not have.

- `Band`: the left edge of the first band, the step from one band to the next, the width of
  each band, and how many there are. The step is signed: a negative step runs the bands from
  right to left, as d3 does for a range that descends.
- `Band.at b i`: the left edge of the `i`-th band. `Band.span b i`: that edge with the width,
  in the form of `Row.spans`. `Band.mid b i`: the middle of the band, where an axis puts a tick.
  `Band.spans b`: all the bands in order, and `Band.edges b` their left edges.
- `Band.invert b x`: the band that holds the place `x`, and `none` between two bands, before
  the first and after the last.
- `Band.fit count lo hi padding`: **bands shared out over a range**, after d3's `band.js` with
  rounding. A `Padding` is d3's three numbers in thousandths: the part of a step left empty
  between two bands, the part left empty at the two ends, and where the room left over goes.
  With no padding it is a run of beats across a room: a band for each beat, and no gap.
- `Band.point count lo hi`: points and no bands, which is `fit` with an inner padding of the
  whole step, as in d3.
- `Band.ofGap start width gap count`: **bands with a whole gap between them**, for a caller
  that knows the width of a thing and not the range. `Band.fitting width gap length`: how many
  such bands a length has room for.
- `Band.Apart b`: no two bands share a unit. `Band.Inside b lo hi`: every band lies from `lo`
  to `hi`. Both are decided, so a program can test a band scale that it wrote by hand.

The laws are in `Whatwg/Svg/Scene/Scale/Band/Laws.lean`.

How `fit` differs from d3 (`d3-scale` at `d6904a4bde09`, `src/band.js`, the function
`rescale` with `round` set). The step and the width of a band are d3's: the step is rounded
down, and the width to the nearest whole number, a half going up. The start is not d3's. d3
shares out by the alignment the room left over *before* it rounds the width, and rounds the
start afterwards. This module shares out the whole units that are left over *after* the width
is rounded. The two agree on every value of d3's own tests. They differ in two ways, and each
is a law here that d3 does not have:

- d3's bands can leave the range by one unit where the alignment is not the middle. A range
  from `0` to `3` with one band, an inner padding of a half and the alignment `1` gives d3 the
  band from `2` to `4`. Here the bands are inside the range at every alignment
  (`Band.fit_inside`), and the alignments `0` and `1000` are flush with the two ends
  (`Band.fit_flush_left`, `Band.fit_flush_right`).
- Where the room left over is odd and the width was rounded down, d3 puts the odd unit after
  the last band and this module before the first. A range from `0` to `99` with three bands
  and an inner padding of `0.35` gives d3 the edges `0, 37, 74` and this module `1, 38, 75`.

Both d3 values are worked out by hand from `band.js`; no d3 code was run.

What this module does not claim: bands of different widths, which are a row
(`Whatwg/Svg/Scene/Row.lean`); a padding that is not a whole number of thousandths; a range
whose ends are fractions, since everything counts in whole units and d3's fractions are whole
numbers of a finer unit.

Every declaration here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- **Equal bands at equal steps.** -/
structure Band where
  /-- The left edge of the first band. -/
  start : Int
  /-- From the left edge of a band to the left edge of the next. A negative step runs the
  bands from right to left. -/
  step : Int
  /-- How wide each band is. -/
  width : Nat
  /-- How many bands there are. -/
  count : Nat
  deriving DecidableEq, Repr

/-- **The left edge of the `i`-th band**, the first being band `0`. -/
def Band.at (b : Band) (i : Nat) : Int := b.start + b.step * (i : Int)

namespace Band

/-- The `i`-th band as its left edge and its width: the form of `Row.spans`. -/
def span (b : Band) (i : Nat) : Int × Int := (Band.at b i, (b.width : Int))

/-- **The middle of the `i`-th band**, a half going up: where an axis puts the tick of a band,
as `center` of d3's `d3-axis/src/axis.js` does for a rounded scale. -/
def mid (b : Band) (i : Nat) : Int := Band.at b i + ((b.width + 1) / 2 : Nat)

/-- The `n` bands from the `i`-th on. -/
def spansFrom (b : Band) : Nat → Nat → List (Int × Int)
  | _, 0 => []
  | i, n + 1 => span b i :: spansFrom b (i + 1) n

/-- **All the bands in order**, each as its left edge and its width. -/
def spans (b : Band) : List (Int × Int) := spansFrom b 0 b.count

/-- The left edges of all the bands, in order. -/
def edges (b : Band) : List Int := (spans b).map Prod.fst

/-- **No two bands share a unit**: a band is no wider than a step is long. -/
def Apart (b : Band) : Prop := (b.width : Int) ≤ b.step ∨ (b.width : Int) ≤ -b.step

/-- Whether the bands are apart is decided. -/
instance (b : Band) : Decidable b.Apart := inferInstanceAs (Decidable (_ ∨ _))

/-- **Every band lies from `lo` to `hi`.** -/
def Inside (b : Band) (lo hi : Int) : Prop :=
  ∀ i, i < b.count → lo ≤ Band.at b i ∧ Band.at b i + (b.width : Int) ≤ hi

/-- Whether the bands lie in a range is decided. -/
instance (b : Band) (lo hi : Int) : Decidable (b.Inside lo hi) :=
  inferInstanceAs
    (Decidable (∀ i, i < b.count → lo ≤ Band.at b i ∧ Band.at b i + (b.width : Int) ≤ hi))

/-- **The band that holds a place**, and `none` for a place that no band holds: between two
bands, before the first or after the last. Where bands lie over each other, which `Apart`
rules out, it answers one of them. -/
def invert (b : Band) (x : Int) : Option Nat :=
  if 0 ≤ (x - b.start) / b.step ∧ (x - b.start) / b.step < (b.count : Int) ∧
      0 ≤ (x - b.start) % b.step ∧ (x - b.start) % b.step < (b.width : Int) then
    some ((x - b.start) / b.step).toNat
  else none

/-! ## Bands shared out over a range -/

/-- **How a range is shared out**: d3's `paddingInner`, `paddingOuter` and `align`, each in
thousandths. -/
structure Padding where
  /-- The part of a step that is left empty between two bands, per mille. More than the whole
  step counts as the whole step, as in d3. -/
  inner : Nat := 0
  /-- The part of a step that is left empty before the first band and after the last, per
  mille. It may be more than a whole step. -/
  outer : Nat := 0
  /-- The share of the room left over that goes before the first band, per mille: `0` puts the
  bands at the low end of the range, `500` in the middle and `1000` at the high end. More than
  `1000` counts as `1000`. -/
  align : Nat := 500
  deriving DecidableEq, Repr

/-- The step of `count` bands on a range `length` long, rounded down: d3's
`floor((stop - start) / max(1, n - paddingInner + paddingOuter * 2))`. -/
def stepOf (p : Padding) (count length : Nat) : Nat :=
  1000 * length / max 1000 (1000 * count + 2 * p.outer - min 1000 p.inner)

/-- The width of a band of a step, to the nearest whole number, a half going up: d3's
`round(step * (1 - paddingInner))`. -/
def widthOf (p : Padding) (step : Nat) : Nat :=
  (2 * (step * (1000 - min 1000 p.inner)) + 1000) / 2000

/-- The room left over: the length less the bands and the steps between them. -/
def slackOf (p : Padding) (count length : Nat) : Nat :=
  length - (stepOf p count length * (count - 1) + widthOf p (stepOf p count length))

/-- The part of the room left over that goes before the first band, to the nearest whole
number, a half going up. -/
def beforeOf (p : Padding) (count length : Nat) : Nat :=
  (2 * (slackOf p count length * min 1000 p.align) + 1000) / 2000

/-- **Bands shared out over a range.** `count` bands from `lo` to `hi`, after d3's band scale
with rounding. Where `hi` is less than `lo` the bands run from right to left, the first band
nearest `lo`, and the alignment still counts from the lesser end, as in d3. -/
def fit (count : Nat) (lo hi : Int) (p : Padding := {}) : Band :=
  if lo ≤ hi then
    ⟨lo + (beforeOf p count (hi - lo).natAbs : Nat), (stepOf p count (hi - lo).natAbs : Nat),
      widthOf p (stepOf p count (hi - lo).natAbs), count⟩
  else
    ⟨hi + (beforeOf p count (hi - lo).natAbs : Nat) +
        (stepOf p count (hi - lo).natAbs * (count - 1) : Nat),
      -(stepOf p count (hi - lo).natAbs : Nat), widthOf p (stepOf p count (hi - lo).natAbs), count⟩

/-- **Points shared out over a range**: bands of no width, a whole step apart. It is d3's point
scale, which is its band scale with an inner padding of `1`. -/
def point (count : Nat) (lo hi : Int) (outer : Nat := 0) (align : Nat := 500) : Band :=
  fit count lo hi ⟨1000, outer, align⟩

/-! ## Bands with a whole gap -/

/-- **Bands of one width with a whole gap between each two**, from a left edge. It is a row of
`Layout` whose parts are all as wide (`Band.row_ofGap` of the laws). -/
def ofGap (start : Int) (width gap count : Nat) : Band :=
  ⟨start, ((width + gap : Nat) : Int), width, count⟩

/-- **How many bands a length has room for**, each `width` wide with `gap` between each two. -/
def fitting (width gap length : Nat) : Nat := (length + gap) / (width + gap)

end Band

/-! ## Finite evaluations

The values of d3's own tests of the band scale and the point scale (`d3-scale` at
`d6904a4bde09`, `test/band-test.js` and `test/point-test.js`). Each comparison is exact. d3's
paddings `0.1`, `0.2`, `0.5` and `1` are `100`, `200`, `500` and `1000` per mille. Two of d3's
tests answer halves, without rounding (`7.5`, `82.5`): those are run here on a range twice as
long, which makes d3's own numbers whole. -/

-- "band(value) computes discrete bands in a continuous range".
#guard Band.edges (Band.fit 2 0 960) == [0, 480]
#guard Band.edges (Band.fit 3 0 120) == [0, 40, 80] && (Band.fit 3 0 120).width == 40
#guard Band.edges (Band.fit 3 0 240 ⟨200, 200, 500⟩) == [15, 90, 165] &&
  (Band.fit 3 0 240 ⟨200, 200, 500⟩).width == 60

-- "band.step() returns the distance between the starts of adjacent bands".
#guard [1, 2, 3].map (fun n => (Band.fit n 0 960).step) == [960, 480, 320]
#guard [1, 2].map (fun n => (Band.fit n 0 960 ⟨500, 500, 500⟩).step) == [640, 384]

-- "band.bandwidth() returns the width of the band".
#guard [0, 1, 2, 3].map (fun n => (Band.fit n 0 960).width) == [960, 960, 480, 320]
#guard [0, 1, 2].map (fun n => (Band.fit n 0 960 ⟨500, 500, 500⟩).width) == [480, 320, 192]

-- "band.domain([]) computes reasonable band and step values".
#guard [0, 500, 1000].map (fun p => ((Band.fit 0 0 960 ⟨p, p, 500⟩).step,
  (Band.fit 0 0 960 ⟨p, p, 500⟩).width)) == [(960, 960), (960, 480), (960, 0)]

-- "band.domain([value]) computes a reasonable singleton band, even with padding".
#guard [0, 500, 1000].map (fun p => (Band.at (Band.fit 1 0 960 ⟨p, p, 500⟩) 0,
  (Band.fit 1 0 960 ⟨p, p, 500⟩).step, (Band.fit 1 0 960 ⟨p, p, 500⟩).width)) ==
    [(0, 960, 960), (320, 640, 320), (480, 480, 0)]

-- "band.domain(values) recomputes the bands", and "band.round(true) computes discrete rounded
-- bands in a continuous range".
#guard Band.edges (Band.fit 3 0 100) == [1, 34, 67] && (Band.fit 3 0 100).width == 33
#guard Band.edges (Band.fit 4 0 100) == [0, 25, 50, 75] && (Band.fit 4 0 100).width == 25
#guard Band.edges (Band.fit 3 0 100 ⟨200, 200, 500⟩) == [7, 38, 69] &&
  (Band.fit 3 0 100 ⟨200, 200, 500⟩).width == 25

-- "band.range(values) can be descending".
#guard Band.edges (Band.fit 3 120 0) == [80, 40, 0] && (Band.fit 3 120 0).width == 40
#guard Band.edges (Band.fit 3 240 0 ⟨200, 200, 500⟩) == [165, 90, 15] &&
  (Band.fit 3 240 0 ⟨200, 200, 500⟩).width == 60

-- "band.paddingInner(p) specifies the inner padding p", with rounding.
#guard Band.edges (Band.fit 3 120 0 ⟨100, 0, 500⟩) == [83, 42, 1] &&
  (Band.fit 3 120 0 ⟨100, 0, 500⟩).width == 37
#guard Band.edges (Band.fit 3 120 0 ⟨200, 0, 500⟩) == [85, 43, 1] &&
  (Band.fit 3 120 0 ⟨200, 0, 500⟩).width == 34

-- "band.paddingOuter(p) specifies the outer padding p".
#guard Band.edges (Band.fit 3 120 0 ⟨200, 100, 500⟩) == [84, 44, 4] &&
  (Band.fit 3 120 0 ⟨200, 100, 500⟩).width == 32
#guard Band.edges (Band.fit 3 120 0 ⟨200, 1000, 500⟩) == [75, 50, 25] &&
  (Band.fit 3 120 0 ⟨200, 1000, 500⟩).width == 20

-- "band.copy() isolates changes to the domain", and to the range.
#guard Band.edges (Band.fit 2 0 2) == [0, 1] && Band.edges (Band.fit 2 3 5) == [3, 4] &&
  Band.edges (Band.fit 2 5 7) == [5, 6]

-- `test/point-test.js`: "scalePoint() is similar to scaleBand().paddingInner(1)", and
-- "point.padding(p) sets the band outer padding to p".
#guard Band.edges (Band.point 2 0 960) == [0, 960] && (Band.point 2 0 960).width == 0 &&
  (Band.point 2 0 960).step == 960
#guard Band.edges (Band.point 2 0 960 500) == [240, 720] && (Band.point 2 0 960 500).step == 480

-- Where this module leaves d3. One band on a range from `0` to `3`, an inner padding of a half
-- and everything left over before it: d3's band is from `2` to `4`, outside the range. Here it
-- is from `1` to `3`.
#guard Band.at (Band.fit 1 0 3 ⟨500, 0, 1000⟩) 0 == 1 && (Band.fit 1 0 3 ⟨500, 0, 1000⟩).width == 2
#guard decide ((Band.fit 1 0 3 ⟨500, 0, 1000⟩).Inside 0 3)
-- Three bands on a range from `0` to `99` with an inner padding of `0.35`: one unit is left
-- over, and it stands before the first band. d3 puts it after the last.
#guard Band.edges (Band.fit 3 0 99 ⟨350, 0, 500⟩) == [1, 38, 75] &&
  (Band.fit 3 0 99 ⟨350, 0, 500⟩).width == 24

-- The band under a place. Three bands `30` wide at steps of `37` from `8`: a place in a band
-- answers the band, and a place in a gap, before the first band or after the last answers
-- `none`.
#guard [8, 37, 45, 82, 111].map (Band.fit 3 0 120 ⟨200, 200, 500⟩).invert ==
  [some 0, some 0, some 1, some 2, some 2]
#guard [7, 38, 44, 112, 500, -3].map (Band.fit 3 0 120 ⟨200, 200, 500⟩).invert ==
  [none, none, none, none, none, none]
-- Bands that run from right to left answer in their own order.
#guard [0, 39, 40, 80, 119, 120].map (Band.fit 3 120 0).invert ==
  [some 2, some 2, some 1, some 0, some 0, none]

-- A control of `Band.Apart`: bands wider than their step lie over each other, and a place in
-- two bands answers one of them.
#guard !decide (Band.mk 0 10 15 3).Apart && (Band.mk 0 10 15 3).invert 12 == some 1
#guard decide (Band.fit 3 0 100 ⟨200, 200, 500⟩).Apart

-- Bands with a whole gap. The ranks of the consumer's graph: a rank every `72` units, each
-- `48` high. Its page: columns `8` wide from the left edge `24`, and a width of `1280` less two
-- margins of `24` has room for `154` of them.
#guard Band.edges (Band.ofGap 0 48 24 4) == [0, 72, 144, 216] &&
  Band.fitting 8 0 (1280 - 2 * 24) == 154
#guard Band.fitting 48 24 264 == 4 && Band.fitting 48 24 263 == 3

end Whatwg.Svg.Scene
