import Whatwg.Svg.Geometry.Shape.Laws
import Whatwg.Svg.Scene.Branch
import Whatwg.Svg.Geometry.Outline.Laws
import Whatwg.Svg.Geometry.Root.Laws
import Whatwg.Svg.Geometry.Stroke.Laws
import Whatwg.Html.Node.SvgDraw
import Whatwg.Html.Node.SvgPaint
import Whatwg.Html.Node.SvgKeyword
import Whatwg.Html.Node.SvgValid

/-!
# WhatwgTest.Html.SvgStroke

The geometry of lines of lean4-effect4 on the exact geometry of slice S11 of
`docs/SVG-PACKAGE-PLAN.md`: `tools/Tools/View/Organic.lean`, whole, and `straight`, `stepDown`,
`revealed` and `arrowhead` of `tools/Tools/View/Graph.lean`. The consumer is read at its
checkout `707b9a01`, and its look at `c7504d69`: since its slice D2 the default noise is zero,
and the look `organic` turns it on (`Organic.noisy` here). This module imports nothing of that
package, and restates its settings (`Organic`) and the forms of an edge (`Form`) under the
consumer's names.

**The check of a look's noise.** A width means a share, so a branch must not be drawn as wide
as its trunk. `Organic.refusal?` is the check that the consumer makes when it reads a look: the
noise is within `Branch.wobbleRoom` of the look's widths, or the refusal names the field.
`fork_apart` is what a look that passes is promised.

**What moved to the kit.** This port first wrote for itself what the kit did not have: the
noise, a smooth path with its end points twice, the samples of a line, the outline of a stroke
of varying width, a collar, a reveal and an arrowhead. None of that is the consumer's alone, so
it is now in the kit with its laws: `Whatwg/Svg/Geometry/Noise.lean`,
`Whatwg/Svg/Geometry/Stroke.lean` and `Whatwg/Svg/Geometry/Stroke/Laws.lean`. What is here is
what the consumer brings: its settings, its constants (`KAPPA`, the two lengths of an
arrowhead, the eight steps of a segment, the seven between the seeds of the two sides of a
stroke), da Vinci's split, the forms of an edge, the marks of a picture, and the numbers of
the guards.

| The consumer's | Here |
| --- | --- |
| `mix`, `cellValue` | `Noise.hash`, `Noise.cell` |
| `smooth`, `valueNoise` | `Noise.smooth`, `Noise.value` |
| `noise`, `seedOf` | `Noise.two`, `Noise.seedOf`, opened under the consumer's names |
| `envelope` | `Noise.envelope` |
| `halfWidth`, the half-width of `sidePoint` | `Stroke.organic` at the settings: `edge` |
| `through` | `Curve.through` at tension zero |
| `sampleAlong`, `samples`, `steps`, `runningLengths` | `Stroke.samples` |
| the point of `sidePoint` | `Stroke.side` |
| `outline` | `Stroke.outline` |
| `stroke` | `Stroke.stroke` with an `edge` for each side: `stroke` |
| `collar` | `Stroke.collar` at `KAPPA`: `collar` |
| `revealed` | `Cubic.revealed`, opened under the consumer's name |
| `arrowhead` | `Stroke.arrowhead` at the consumer's two lengths: `arrowhead` |
| `roundRect`, `ring` | `Cubic.roundRect`, `Cubic.ring` at `KAPPA` |
| `isqrt` | `sqrtDown` |
| `line`, `straight` | `Cubic.line` |
| `at_`, `dir` | `Cubic.pointAt`, `Cubic.direction` |
| `normal`, `dist`, `shift` | `Vec.normal`, `Vec.dist`, `+` |
| `segmentThrough`, `throughFrom` | `Curve.cardinalSegment (1 / 6)`, `Curve.windows` |

**The laws.** The consumer's are `noise_band`, `halfWidth_band`, `stroke_move` with its steps,
`stroke_organic`, and `move_back` with the step of its stroke cache that reads the move law
(`stroke_from_origin`). Each is here as a case of a law of the kit: `noise_band` of
`Noise.two_band`, `edge_band`, which is the consumer's `halfWidth_band` at its settings, of
`Stroke.organic_band`, and `stroke_move` of `Stroke.stroke_move`, whose steps are
`Stroke.samples_move`, `Stroke.side_move` and `Stroke.outline_move`. Exact arithmetic gives
more, which the consumer does not state:

- da Vinci's rule for every count of parts (`split_sq_le`, `lt_split_succ`), where the consumer
  checks six counts;
- the band of an edge of a stroke with no premise on the envelope and the noise (`edge_band`);
- every stroke is a chain that ends where it starts (`closed_stroke`), and so is a collar;
- a moved step down, a moved reveal, a moved arrowhead and a moved collar are the same, moved.

**How it differs from the consumer.**

- *Units.* A length is in logical pixels, a parameter runs from `0` to `1`, and a share is a
  number from `0` to `1`. The consumer counts thousandths and parts per mille.
- *Rounding.* The consumer rounds down at each division. Here the computation rounds at three
  roots and nowhere else: the distance between two samples (`Vec.dist`, at three places), the
  length of a direction under a normal (`Vec.normal`, at three places), and `split`
  (`sqrtDown`, at six places). A path is rounded once more where it is written, to the nearest
  thousandth.
- *A straight segment.* The consumer's has its controls on its ends, so its point at `t` is
  `3t² - 2t³` of the way along. `Cubic.line` has them at the thirds, so its point at `t` is
  `t` of the way along. Both draw the same line. The samples of a stroke along a straight
  segment are even here and crowd towards the ends there, and a reveal of part of a straight
  segment is that share of its length here.
- *The noise.* A cell is the floor of `s / wave`, and the place in the cell is exact. For a
  wave of zero every length is in the first cell, since `Rat` divides by zero to zero; the
  consumer makes such a wave one thousandth long. `Noise.smooth` is not clamped: it is proved
  to stay in `[0, 1]`.
- *No direction.* `Vec.normal` of the zero vector is zero, and the consumer's `normal` is
  `(1, 0)`. So the stroke of a line of no length has no area here.
- *The arrowhead* reads `Cubic.direction` at the end: three times the step from the second
  control to the end, and the chord where that is zero. The consumer reads the step alone,
  which is zero for its straight segments.

The guards at the end give the numbers: where no division rounds, the port's numbers are the
consumer's; a control of a round corner can differ by a thousandth; a knot of a stroke with
noise differs by a few thousandths along a curve.

What this battery does not claim: that a stroke here is the consumer's stroke. No theorem
relates this module to that package. The guards compare a few values, and each comment says
whether the consumer's number was worked by hand from its code or evaluated on a copy of its
integer definitions. No law bounds the distance of an edge from the centre line, since a
normal is of length one only nearly, and none says that an outline does not cross itself.
-/

namespace WhatwgTest.Html.SvgStroke

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Html.Schema (Exclusions)
open Whatwg.Svg.Value

-- Three definitions of the kit under the names the consumer has for them (`Grow.seedOf`,
-- `Grow.noise`, `Graph.revealed`). The guards read them under those names.
open Whatwg.Svg.Value.Noise (seedOf)
open Whatwg.Svg.Value.Noise renaming two → noise
open Whatwg.Svg.Value.Cubic (revealed)

/-! ## Integers -/

/-- **da Vinci's split** (`Grow.split`): the share of each of `n` parallel parts, `1/√n`,
rounded down at six places. The consumer's `isqrt` of a count of millionths squared is the
kit's `sqrtDown` at six places, and the two give the same number. -/
def split (n : Nat) : Rat := if n ≤ 1 then 1 else sqrtDown (1 / (n : Rat)) 6

/-- **da Vinci's rule, from below**: the squares of the shares of `n` parts sum to no more than
the whole. -/
theorem split_sq_le (n : Nat) (h : 2 ≤ n) : (n : Rat) * (split n * split n) ≤ 1 := by
  have hn : (0 : Rat) < (n : Rat) := Rat.natCast_pos.mpr (by omega)
  have hne : (n : Rat) ≠ 0 := Rat.ne_of_gt hn
  have hq : (0 : Rat) ≤ 1 / (n : Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  have hm := Rat.mul_le_mul_of_nonneg_left (sqrtDown_mul_self_le hq 6) (Rat.le_of_lt hn)
  have e : (n : Rat) * (1 / (n : Rat)) = 1 := by grind
  have h1 : ¬ n ≤ 1 := by omega
  rw [e] at hm
  rw [split, if_neg h1]
  exact hm

/-- **da Vinci's rule, from above**: with each share a millionth greater, the squares sum to
more than the whole. -/
theorem lt_split_succ (n : Nat) (h : 2 ≤ n) :
    1 < (n : Rat) * ((split n + 1 / (10 : Rat) ^ 6) * (split n + 1 / (10 : Rat) ^ 6)) := by
  have hn : (0 : Rat) < (n : Rat) := Rat.natCast_pos.mpr (by omega)
  have hne : (n : Rat) ≠ 0 := Rat.ne_of_gt hn
  have hm := Rat.mul_lt_mul_of_pos_left (lt_sqrtDown_succ (1 / (n : Rat)) 6) hn
  have e : (n : Rat) * (1 / (n : Rat)) = 1 := by grind
  have h1 : ¬ n ≤ 1 := by omega
  rw [e] at hm
  rw [split, if_neg h1]
  exact hm

/-! ## Settings, constants and outlines -/

/-- The settings of organic strokes (`Tools.View.Organic`): lengths in logical pixels, and the
noise as a share. A stroke reads `noise` and `wave`. -/
structure Organic where
  /-- the width of a line that carries all the work -/
  trunk : Rat := 2.4
  /-- the width of the thinnest line -/
  fine : Rat := 0.8
  /-- the radius of a collar where a line of the trunk's width meets a box or a bar -/
  flare : Rat := 6
  /-- how far the noise moves each edge of a line, as a share of its half-width. Zero by
  default, as in the consumer since its slice D2: the look `organic` turns it on -/
  noise : Rat := 0
  /-- the noise's wavelength along a line -/
  wave : Rat := 40
  deriving Repr, DecidableEq

/-- The look `organic` of the consumer (`tools/view/looks/organic.tokens.json`): the noise on,
the edges of a line inside a band of 35 per cent of its half-width. -/
def Organic.noisy : Organic := { noise := 0.35 }

/-- The room that a look's widths leave its noise, in per mille: that of a trunk and a branch
that carries half of what the trunk carries, at Leonardo's exponent (`Branch.wobbleRoom`). -/
def Organic.room (o : Organic) : Nat :=
  let trunk := (o.trunk * 1000).floor.toNat
  Whatwg.Svg.Scene.Branch.wobbleRoom (Whatwg.Svg.Scene.Share.width 2 trunk ⟨1, 2⟩) trunk

/-- **The check of a look's noise at its read** (the Effect4 coordinator's guidance 4, the
second check): the noise is within the room, or the refusal names the field. A look that passes
draws no branch of a fork of two as wide as its trunk (`fork_apart`). -/
def Organic.refusal? (o : Organic) : Option String :=
  if (o.noise * 1000).floor.toNat ≤ o.room then none
  else some ("organic.noise: " ++ toString (o.noise * 1000).floor ++
    " per mille is over the room of " ++ toString o.room ++
    " per mille that a trunk and a branch of half its share leave")

/-- **Within the room, a branch of a fork of two is narrower than its trunk at every point**: at
its widest the branch is no wider than the trunk at its narrowest, for a noise of `amp` per
mille that passes the check. The law is the kit's (`Branch.wobbleRoom_apart`). -/
theorem fork_apart (trunk amp : Nat)
    (h : amp ≤ Whatwg.Svg.Scene.Branch.wobbleRoom (Whatwg.Svg.Scene.Share.width 2 trunk ⟨1, 2⟩) trunk) :
    Whatwg.Svg.Scene.Share.width 2 trunk ⟨1, 2⟩ * (1000 + amp) ≤ trunk * (1000 - amp) := by
  have hc : (⟨1, 2⟩ : Whatwg.Svg.Scene.Share) ∈ Whatwg.Svg.Scene.Share.whole.split [1, 1] := by
    decide
  have hle := Whatwg.Svg.Scene.Share.width_split_le 2 trunk Whatwg.Svg.Scene.Share.whole [1, 1] hc
  rw [Whatwg.Svg.Scene.Share.width_whole 2 trunk (by decide)] at hle
  exact Whatwg.Svg.Scene.Branch.wobbleRoom_apart _ _ amp hle h

-- The default look has no noise and passes. The look `organic` has 350 per mille against a
-- room of 171, and is refused with the field's name.
#guard ({} : Organic).refusal? = none
#guard Organic.noisy.room = 171
#guard Organic.noisy.refusal? ==
  some ("organic.noise: 350 per mille is over the room of 171 per mille that a trunk and a " ++
    "branch of half its share leave")

/-- The circle constant of a quarter arc by one cubic, as the consumer has it (`Grow.KAPPA`).
The kit's own, `Cubic.kappa`, is `0.5523`. -/
def KAPPA : Rat := 552 / 1000

/-- **A rectangle with round corners** (`Grow.roundRect`), clockwise from the top left: the
kit's, at the consumer's roundness. -/
def roundRect (x y w h r : Rat) : List Cubic := Cubic.roundRect (Box.ofSize ⟨x, y⟩ w h) r KAPPA

/-- **A ring with round corners** (`Grow.ring`): the rectangle, and the rectangle `wt` inside
it. -/
def ring (x y w h r wt : Rat) : List (List Cubic) := Cubic.ring (Box.ofSize ⟨x, y⟩ w h) r wt KAPPA

/-- **A collar** where a line `w` wide meets a surface at `p` (`Grow.collar`): the kit's, at
the consumer's roundness. -/
def collar (p : Vec) (w R : Rat) (down : Bool) : List Cubic := Stroke.collar p w R down KAPPA

/-- The half-width of one edge of a stroke `w` wide (`Grow.halfWidth`, as `Grow.sidePoint`
calls it): the kit's half-width that wanders, at the settings' share of noise and wave. -/
def edge (seed : Nat) (o : Organic) (w : Rat) (tip : Bool) : Rat → Rat → Rat :=
  Stroke.organic seed (w / 2) o.noise o.wave tip

/-- **An organic stroke** along a centre line (`Grow.stroke`): the kit's stroke of varying
width, each segment at the consumer's eight steps. The two edges take two seeds, the second
seven on, as in the consumer. With `tip`, the line narrows to its last point. -/
def stroke (seed : Nat) (o : Organic) (w : Rat) (cs : List Cubic) (tip : Bool) : List Cubic :=
  Stroke.stroke cs (edge seed o w tip) (edge (seed + 7) o w tip) (n := 8)

/-! ## The laws of the band -/

/-- **The noise stays in its band** (`Grow.noise_band`): `[-1, 1]`, for every seed, wave and
length. It is the kit's law. -/
theorem noise_band (seed : Nat) (wave s : Rat) :
    -1 ≤ noise seed wave s ∧ noise seed wave s ≤ 1 :=
  Noise.two_band seed wave s

/-- **Each edge of a stroke stays in its band** (`Grow.halfWidth_band`): before the tip, the
half-width of an edge differs from `w / 2` by at most the settings' share of it, at every
seed, length of the line and place along it. The consumer states the band under premises on
the envelope and the noise; the kit proves both. -/
theorem edge_band (seed : Nat) (o : Organic) {w : Rat} (s whole : Rat) (hw0 : 0 ≤ w)
    (hn : 0 ≤ o.noise) :
    w / 2 * (1 - o.noise) ≤ edge seed o w false s whole ∧
      edge seed o w false s whole ≤ w / 2 * (1 + o.noise) :=
  Stroke.organic_band seed (by grind) hn o.wave s whole

/-! ## The move law of a stroke -/

/-- **The move law of a stroke** (`Grow.stroke_move`). The stroke of a centre line moved by `d`
is the stroke, moved by `d`: for every seed, organic settings, width, line and tip. The
consumer's moves a line by whole pixels and its stroke by a thousand times as many
thousandths; here both are one move. It is the kit's law for a stroke that is not snapped. -/
theorem stroke_move (seed : Nat) (o : Organic) (w : Rat) (cs : List Cubic) (tip : Bool) (d : Vec) :
    stroke seed o w (cs.map (Cubic.move d)) tip = (stroke seed o w cs tip).map (Cubic.move d) :=
  Stroke.stroke_move d id (fun _ => rfl) cs _ _ 8 3

/-- A stroke reads its organic settings' noise and wave alone (`Grow.stroke_organic`). -/
theorem stroke_organic (seed : Nat) {o o' : Organic} (hn : o.noise = o'.noise)
    (hw : o.wave = o'.wave) (w : Rat) (cs : List Cubic) (tip : Bool) :
    stroke seed o w cs tip = stroke seed o' w cs tip := by
  simp only [stroke, edge, hn, hw]

/-- A line moved to the origin by a point, and back, is the line (`move_back` of
`tools/Tools/View/Graph.lean`). -/
theorem move_back (cs : List Cubic) (p : Vec) :
    (cs.map (Cubic.move (-p))).map (Cubic.move p) = cs := by
  simp only [List.map_map, Function.comp_def, Cubic.move_move, Vec.neg_add_cancel,
    Cubic.move_zero, List.map_id']

/-- **A stroke kept at the origin and moved back is the stroke**: the step of the consumer's
stroke cache that reads the move law (`cachedStroke_eq`), for a move by any point. -/
theorem stroke_from_origin (seed : Nat) (o : Organic) (w : Rat) (cs : List Cubic) (tip : Bool)
    (p : Vec) :
    (stroke seed o w (cs.map (Cubic.move (-p))) tip).map (Cubic.move p) =
      stroke seed o w cs tip := by
  rw [← stroke_move, move_back]

/-! ## Closed outlines

The consumer does not state these. Each is a law of the kit. -/

/-- **Every stroke is a chain that ends where it starts**, for every seed, settings, width,
centre line and tip: the outline that `Path.ofLoops` asks for, where a list that is no chain is
written as several subpaths. -/
theorem closed_stroke (seed : Nat) (o : Organic) (w : Rat) (cs : List Cubic) (tip : Bool) :
    Cubic.Closed (stroke seed o w cs tip) = true :=
  Stroke.closed_stroke _ _ _ _ _ _

/-- A collar is a chain that ends where it starts. -/
theorem closed_collar (p : Vec) (w R : Rat) (down : Bool) :
    Cubic.Closed (collar p w R down) = true :=
  Stroke.closed_collar p w R down KAPPA

/-- The collar at a moved point is the collar, moved. -/
theorem collar_move (d p : Vec) (w R : Rat) (down : Bool) :
    collar (p + d) w R down = (collar p w R down).map (Cubic.move d) :=
  Stroke.collar_move d p w R down KAPPA

/-! ## The edges of a graph -/

/-- The form of an edge between two ranks, as the consumer's look names it
(`Tools.View.Curve`). Each is a form of the kit's `Curve`. -/
inductive Form where
  | bumpY | linear | stepY

/-- **A step down** from `a` to `b` in a form (`Graph.stepDown`). A `bumpY` step is one cubic,
vertical at both ends, each control the share `reach` of the drop from its end. A `stepY` step
turns at the middle of the drop, and between two ends in one column it is a straight step, as
it is in the consumer: the kit's `stepY` gives three segments there, the middle one of no
length. -/
def stepDown (form : Form) (reach : Rat) (a b : Vec) : List Cubic :=
  match form with
  | .bumpY => (Curve.bumpY reach).cubics [a, b]
  | .linear => Curve.linear.cubics [a, b]
  | .stepY => (if a.x = b.x then Curve.linear else Curve.stepY).cubics [a, b]

/-- A step down between two moved points is the step, moved (`Curve.cubics_move`). -/
theorem stepDown_move (form : Form) (reach : Rat) (a b d : Vec) :
    stepDown form reach (a + d) (b + d) = (stepDown form reach a b).map (Cubic.move d) := by
  cases form with
  | bumpY => exact Curve.cubics_move (.bumpY reach) d [a, b]
  | linear => exact Curve.cubics_move .linear d [a, b]
  | stepY =>
    have hx : ((a + d).x = (b + d).x) ↔ a.x = b.x := by
      simp only [Vec.add_def]
      grind
    by_cases h : a.x = b.x
    · simp only [stepDown, if_pos h, if_pos (hx.mpr h)]
      exact Curve.cubics_move _ d [a, b]
    · simp only [stepDown, if_neg h, if_neg (fun e => h (hx.mp e))]
      exact Curve.cubics_move _ d [a, b]

/-- The length of an arrowhead's two strokes along the segment, in logical pixels
(`Graph.HEAD_ALONG`). -/
def HEAD_ALONG : Rat := 6

/-- The reach of an arrowhead's two strokes across the segment (`Graph.HEAD_ACROSS`). -/
def HEAD_ACROSS : Rat := 4

/-- **An arrowhead** where a segment ends (`Graph.arrowhead`): the kit's, at the consumer's
two lengths. The consumer wraps each stroke in a call and moves it; this is the two
segments. -/
def arrowhead (c : Cubic) : List Cubic := Stroke.arrowhead c HEAD_ALONG HEAD_ACROSS

/-- The arrowhead of a moved segment is the arrowhead, moved. -/
theorem arrowhead_move (d : Vec) (c : Cubic) :
    arrowhead (c.move d) = (arrowhead c).map (Cubic.move d) :=
  Stroke.arrowhead_move d c HEAD_ALONG HEAD_ACROSS

/-! ## A stroke as a mark of a picture -/

/-- A filled shape of closed outlines in one `d`, by the even-odd rule: the consumer's
`.shape`, in the ink. -/
def shapeNode (ink : Rgb) (outlines : List (List Cubic)) (key : String) : SvgNode :=
  Svg.loops outlines
    ([.className "e4-fill-ink", .fillRule .evenodd, .fill ink] ++ SvgAttr.dataKey? key)

/-- **An organic stroke as a mark of a picture**: one closed path with a fill, as the consumer
draws the body of a forward edge. -/
def strokeNode (ink : Rgb) (seed : Nat) (o : Organic) (w : Rat) (cs : List Cubic) (tip : Bool)
    (key : String) : SvgNode :=
  shapeNode ink [stroke seed o w cs tip] key

/-- A shape passes where the marks of a picture stand, for every list of outlines, at every set
of HTML exclusions. -/
theorem shapeNode_ok (x : Exclusions) (ink : Rgb) (outlines : List (List Cubic)) (key : String) :
    (shapeNode ink outlines key).okAt (Pos.inSvg x) = true := by
  unfold shapeNode SvgAttr.dataKey?
  cases key.isEmpty <;> conv => lhs; whnf

/-- **A stroke passes where the marks of a picture stand**: for every seed, settings, width,
centre line, tip and key. The outline is not computed: the test of a shape reads no path. -/
theorem strokeNode_ok (x : Exclusions) (ink : Rgb) (seed : Nat) (o : Organic) (w : Rat)
    (cs : List Cubic) (tip : Bool) (key : String) :
    (strokeNode ink seed o w cs tip key).okAt (Pos.inSvg x) = true :=
  shapeNode_ok x ink [stroke seed o w cs tip] key

/-! ## The port beside the consumer

Each guard is a finite evaluation. A comment says what the consumer computes for the same
input, in its thousandths, and how that number was found. -/

/-- A point of whole thousandths, as the consumer counts. -/
def milli (x y : Int) : Vec := .fixed 3 x y

-- `split`. The consumer's `split 2`, `split 3`, `split 4` and `split 5` are 707106, 577350,
-- 500000 and 447213 millionths: the whole roots of 10^12 / n, by hand. The port's are the same.
#guard [split 2, split 3, split 4, split 5] =
  [707106 / 1000000, 577350 / 1000000, 500000 / 1000000, 447213 / 1000000]

-- The noise at seven lengths along a line, with seed 7 and a wave of 40 pixels. The
-- consumer's `noise 7 40000 s`, evaluated on a copy of its integer definitions, is -199, -155,
-- -45, 209, 658, 792 and 509 thousandths. It rounds down at each of its seven divisions; the
-- port's exact values are within two thousandths of them.
#guard (([0, 5, 10, 20, 33, 40, 57] : List Nat).zip
    ([-199, -155, -45, 209, 658, 792, 509] : List Int)).all fun x =>
  decide (-2 ≤ noise 7 40 x.1 * 1000 - x.2 ∧ noise 7 40 x.1 * 1000 - x.2 ≤ 2)

-- `roundRect`: a box 40 by 20 at (10, 20) with corners of radius 6. The consumer, by hand:
-- `r` is 6000 and `k` is 6000 * 552 / 1000 = 3312 with nothing rounded, so its first corner is
-- (44000, 20000) (47312, 20000) (50000, 22688) (50000, 26000), and so on round. The kit's
-- outline is the same eight segments at the same numbers. A side differs in its controls
-- only: the consumer's are on its ends.
#guard roundRect 10 20 40 20 6 =
  [Cubic.line (milli 16000 20000) (milli 44000 20000),
    ⟨milli 44000 20000, milli 47312 20000, milli 50000 22688, milli 50000 26000⟩,
    Cubic.line (milli 50000 26000) (milli 50000 34000),
    ⟨milli 50000 34000, milli 50000 37312, milli 47312 40000, milli 44000 40000⟩,
    Cubic.line (milli 44000 40000) (milli 16000 40000),
    ⟨milli 16000 40000, milli 12688 40000, milli 10000 37312, milli 10000 34000⟩,
    Cubic.line (milli 10000 34000) (milli 10000 26000),
    ⟨milli 10000 26000, milli 10000 22688, milli 12688 20000, milli 16000 20000⟩]

-- The same box with a radius of 6.001. The consumer, by hand: `k` is 6001 * 552 / 1000 = 3312,
-- rounded down from 3312.552, so its first corner is (43999, 20000) (47311, 20000)
-- (50000, 22689) (50000, 26001). The kit's controls are at 47.311552 and 22.688448, written
-- 47.312 and 22.688: each a thousandth from the consumer's.
#guard toString (Path.ofLoop (roundRect 10 20 40 20 6.001)) ==
  "M16.001,20H43.999C47.312,20 50,22.688 50,26.001V33.999C50,37.312 47.312,40 43.999,40" ++
  "H16.001C12.688,40 10,37.312 10,33.999V26.001C10,22.688 12.688,20 16.001,20Z"

-- `collar`: a line 2.4 wide leaves a surface at (10, 20) downward, with a radius of 6. The
-- consumer, by hand: `hw` is 1200 and `k` is 3312, and its two arcs are
-- (8800, 26000) (8800, 22688) (6112, 20000) (2800, 20000) and
-- (17200, 20000) (13888, 20000) (11200, 22688) (11200, 26000). The port's are the same.
#guard collar ⟨10, 20⟩ 2.4 6 true =
  [⟨milli 8800 26000, milli 8800 22688, milli 6112 20000, milli 2800 20000⟩,
    Cubic.line (milli 2800 20000) (milli 17200 20000),
    ⟨milli 17200 20000, milli 13888 20000, milli 11200 22688, milli 11200 26000⟩,
    Cubic.line (milli 11200 26000) (milli 8800 26000)]

-- A stroke 2 wide along a straight line 30 long, with no noise, as `Path.ofLoops` writes it:
-- one subpath, each straight segment a `V` or an `H`, and the line back across the start left
-- to the closepath. The consumer draws the same rectangle with eighteen `C` commands. Its
-- knots along each side are at 1.288, 4.687, 9.491, 15, 20.507, 25.312 and 28.71 (the first by
-- hand, the others evaluated on a copy of its definitions): its straight segment has its
-- controls on its ends, so its eight samples crowd towards the ends.
#guard toString (Path.ofLoops [stroke 0 { noise := 0 } 2 [Cubic.line ⟨0, 0⟩ ⟨0, 30⟩] false]) ==
  "M-1,0V3.75V7.5V11.25V15V18.75V22.5V26.25V30H1V26.25V22.5V18.75V15V11.25V7.5V3.75V0Z"

-- The first two segments of a stroke with noise, 2.4 wide, along one curved edge from (10, 20)
-- to (30, 46), seeded by the key `e1`. The consumer's, evaluated on a copy of its definitions:
-- (8800, 20000) (8956, 20799) (9172, 23369) (9741, 24794) and
-- (9741, 24794) (10310, 26219) (11245, 27432) (12218, 28553). Over the eighteen segments of
-- this outline no knot of the port is more than four thousandths from the consumer's.
#guard toString (Path.ofCubics
    ((stroke (seedOf "e1") Organic.noisy 2.4 [⟨⟨10, 20⟩, ⟨10, 33⟩, ⟨30, 33⟩, ⟨30, 46⟩⟩] false).take 2)) ==
  "M8.8,20C8.957,20.8 9.173,23.372 9.743,24.798C10.312,26.223 11.245,27.435 12.218,28.556"

-- A reveal of 12 of the 20 pixels of an edge of two straight segments, down 10 and across 10.
-- The port draws the first and 2 pixels of the second. The consumer, by hand: its part of the
-- second segment is `upTo 200`, and the rounding at each of its six steps brings the four
-- points to (0, 10): a segment of no length.
#guard toString (Path.ofCubics
    (revealed [Cubic.line ⟨0, 0⟩ ⟨0, 10⟩, Cubic.line ⟨0, 10⟩ ⟨10, 10⟩] 12)) == "M0,0V10H2"

-- `arrowhead` at the end of an arc that arrives leftwards. The consumer, by hand: the step
-- from the second control to the end is (-51, 0), so its two strokes start at (126, 226) and
-- (126, 234). The port's start at the same points.
#guard arrowhead ⟨⟨120, 40⟩, ⟨171, 40⟩, ⟨171, 230⟩, ⟨120, 230⟩⟩ =
  [Cubic.line ⟨126, 226⟩ ⟨120, 230⟩, Cubic.line ⟨126, 234⟩ ⟨120, 230⟩]

-- What the kit knows of these outlines and the consumer does not state. A rectangle with
-- round corners is a chain that ends where it starts, for every box, radius and roundness.
example (x y w h r : Rat) : Cubic.Closed (roundRect x y w h r) = true :=
  Cubic.closed_roundRect _ _ _

-- The rectangle at a moved corner is the rectangle, moved.
example (d : Vec) (x y w h r : Rat) :
    roundRect (x + d.x) (y + d.y) w h r = (roundRect x y w h r).map (Cubic.move d) := by
  have e : Box.ofSize ⟨x + d.x, y + d.y⟩ w h = (Box.ofSize ⟨x, y⟩ w h).move d :=
    Box.ofSize_move d ⟨x, y⟩ w h
  rw [roundRect, e, Cubic.roundRect_move]
  rfl

-- The part of a straight segment up to `t` is the straight segment to the point `t` of the
-- way along: a reveal of a straight edge is that share of its length.
example (a b : Vec) (t : Rat) : (Cubic.line a b).upTo t = Cubic.line a (a.lerp b t) := by
  rw [Cubic.upTo_eq_between, Cubic.line_between, Vec.lerp_zero]

end WhatwgTest.Html.SvgStroke
