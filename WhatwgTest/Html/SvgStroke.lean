import Whatwg.Svg.Geometry.Shape.Laws
import Whatwg.Svg.Geometry.Outline.Laws
import Whatwg.Svg.Geometry.Root.Laws
import Whatwg.Html.Node.SvgDraw
import Whatwg.Html.Node.SvgPaint
import Whatwg.Html.Node.SvgValid

/-!
# WhatwgTest.Html.SvgStroke

The geometry of lines of lean4-effect4 on the exact geometry of slice S11 of
`docs/SVG-PACKAGE-PLAN.md`: `tools/Tools/View/Organic.lean`, whole, and `straight`, `stepDown`,
`revealed` and `arrowhead` of `tools/Tools/View/Graph.lean`. The consumer is read at its
checkout `707b9a01`. This module imports nothing of that package, and restates its settings
(`Organic`) and the forms of an edge (`Form`) under the consumer's names.

**What is ported.** Every definition keeps the consumer's name and its order of steps.

- The noise: `mix` and `seedOf` as the consumer has them, on `Nat`; `cellValue`, `smooth`,
  `valueNoise` and `noise` in `Rat`, with a value in `[-1, 1]`.
- The width: `split`, `envelope`, `halfWidth`.
- The outlines: `roundRect`, `ring`, `collar`, and the stroke with its steps, `through`,
  `sampleAlong`, `samples`, `steps`, `runningLengths`, `sidePoint`, `outline`, `stroke`.
- The edges: `stepDown`, `revealed`, `arrowhead`.
- Ten of the consumer's definitions have none here, because the kit has them: `isqrt` is
  `sqrtDown`, `line` and `straight` are `Cubic.line`, `at_` is `Cubic.pointAt`, `dir` is
  `Cubic.direction`, `normal` is `Vec.normal`, `dist` is `Vec.dist`, `segmentThrough` is
  `Curve.cardinalSegment (1 / 6)`, `throughFrom` is `Curve.windows`, and `shift` is `+`.

**The laws.** The consumer's are `noise_band`, `halfWidth_band`, `stroke_move` with its steps,
`stroke_organic`, and `move_back` with the step of its stroke cache that reads the move law
(`stroke_from_origin`). Exact arithmetic gives more, which the consumer does not state:

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
  consumer makes such a wave one thousandth long. `smooth` is not clamped: it is proved to
  stay in `[0, 1]`.
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

/-! ## Noise -/

/-- A 32-bit mix of a seed and a cell (`Grow.mix`), as the consumer has it. -/
def mix (seed cell : Nat) : Nat :=
  let m := 4294967296
  let h := ((cell + 374761393) * 668265263 % m) ^^^ ((seed + 1442695041) * 2246822519 % m)
  let h := ((h ^^^ (h >>> 13)) * 1274126177) % m
  h ^^^ (h >>> 16)

/-- A cell's value, in `[-1, 1]` (`Grow.cellValue`): one of 2001 values a thousandth apart. -/
def cellValue (seed cell : Nat) : Rat := ((mix seed cell % 2001 : Nat) : Rat) / 1000 - 1

/-- Smoothstep (`Grow.smooth`): `t² (3 - 2t)`, which takes `[0, 1]` into `[0, 1]`
(`smooth_band`). -/
def smooth (t : Rat) : Rat := t * t * (3 - 2 * t)

/-- **Value noise** at `s` along a line, with cells `wave` long (`Grow.valueNoise`): between the
values of the cells around `s`, smoothly. The cell is the floor of `s / wave`. -/
def valueNoise (seed : Nat) (wave s : Rat) : Rat :=
  cellValue seed (s / wave).floor.toNat +
    smooth (s / wave - ((s / wave).floor : Rat)) *
      (cellValue seed ((s / wave).floor.toNat + 1) - cellValue seed (s / wave).floor.toNat)

/-- **The noise** at `s` (`Grow.noise`): two octaves, the second at half the wavelength and half
the weight. -/
def noise (seed : Nat) (wave s : Rat) : Rat :=
  (2 * valueNoise seed wave s + valueNoise (seed + 1) (wave / 2) s) / 3

/-- A key's seed (`Grow.seedOf`): FNV-1a over its characters' codes. -/
def seedOf (key : String) : Nat :=
  key.foldl (fun h c => ((h ^^^ c.toNat) * 16777619) % 4294967296) 2166136261

/-! ## The width of a line -/

/-- The envelope of the noise at `s` along a line `S` long (`Grow.envelope`): no noise at either
end, full beyond `ramp` from both. The `max 0` is the consumer's subtraction of natural
numbers, which stops at zero. -/
def envelope (ramp S s : Rat) : Rat :=
  if ramp = 0 then 1 else max 0 (min 1 (min (s / ramp) ((S - s) / ramp)))

/-- **A half-width** at a point of a line (`Grow.halfWidth`): `hw`, moved by the noise `v` at
most the share `amp`, and by the envelope `env`. -/
def halfWidth (hw amp env v : Rat) : Rat := hw + hw * amp * env * v

/-! ## Points and paths -/

/-- The settings of organic strokes (`Tools.View.Organic`): lengths in logical pixels, and the
noise as a share. A stroke reads `noise` and `wave`. -/
structure Organic where
  /-- the width of a line that carries all the work -/
  trunk : Rat := 2.4
  /-- the width of the thinnest line -/
  fine : Rat := 0.8
  /-- the radius of a collar where a line of the trunk's width meets a box or a bar -/
  flare : Rat := 6
  /-- how far the noise moves each edge of a line, as a share of its half-width -/
  noise : Rat := 0.35
  /-- the noise's wavelength along a line -/
  wave : Rat := 40
  deriving Repr, DecidableEq

/-- The circle constant of a quarter arc by one cubic, as the consumer has it (`Grow.KAPPA`).
The kit's own, `Cubic.kappa`, is `0.5523`. -/
def KAPPA : Rat := 552 / 1000

/-- **A rectangle with round corners** (`Grow.roundRect`), clockwise from the top left: the
kit's, at the consumer's roundness. -/
def roundRect (x y w h r : Rat) : List Cubic := Cubic.roundRect (Box.ofSize ⟨x, y⟩ w h) r KAPPA

/-- **A ring with round corners** (`Grow.ring`): the rectangle, and the rectangle `wt` inside
it. -/
def ring (x y w h r wt : Rat) : List (List Cubic) := Cubic.ring (Box.ofSize ⟨x, y⟩ w h) r wt KAPPA

/-- **A smooth path through points** (`Grow.through`): Catmull-Rom's spline, with the first
point before the first and the last point past the last. -/
def through (qs : List Vec) : List Cubic :=
  Curve.windows (Curve.cardinalSegment (1 / 6)) (Curve.doubled qs)

/-- The samples along one cubic at `n` steps (`Grow.sampleAlong`): each point and its
direction. A line's first cubic keeps its start; each later cubic drops it, the end of the one
before. -/
def sampleAlong (n : Nat) (c : Cubic) (first : Bool) : List (Vec × Vec) :=
  ((List.range (n + 1)).drop (if first then 0 else 1)).map fun (k : Nat) =>
    (c.pointAt ((k : Rat) / (n : Rat)), c.direction ((k : Rat) / (n : Rat)))

/-- The samples of a centre line (`Grow.samples`): each cubic at `n` steps. -/
def samples (n : Nat) (cs : List Cubic) : List (Vec × Vec) :=
  match cs with
  | [] => []
  | c :: rest => sampleAlong n c true ++ rest.flatMap fun c => sampleAlong n c false

/-- **A collar** where a line `w` wide meets a surface at `p` (`Grow.collar`): a quarter arc of
radius `R` on each side, from the line `R` away from the surface out along the surface. `down`
when the line leaves the surface downward. -/
def collar (p : Vec) (w R : Rat) (down : Bool) : List Cubic :=
  let s : Rat := if down then 1 else -1
  let hw := w / 2
  let l0 : Vec := ⟨p.x - hw, p.y + s * R⟩
  let l3 : Vec := ⟨p.x - hw - R, p.y⟩
  let r0 : Vec := ⟨p.x + hw + R, p.y⟩
  let r3 : Vec := ⟨p.x + hw, p.y + s * R⟩
  [Cubic.corner l0 ⟨p.x - hw, p.y⟩ l3 KAPPA, Cubic.line l3 r0,
    Cubic.corner r0 ⟨p.x + hw, p.y⟩ r3 KAPPA, Cubic.line r3 l0]

/-- The distance from each sample of a centre line to the next (`Grow.steps`), rounded down at
three places. -/
def steps (ss : List (Vec × Vec)) : List Rat :=
  (ss.zip (ss.drop 1)).map fun x => Vec.dist x.1.1 x.2.1

/-- The running lengths along a centre line's samples, from `0` (`Grow.runningLengths`): each
is the one before plus the step to the next sample. -/
def runningLengths (ss : List (Vec × Vec)) : List Rat :=
  ((steps ss).foldl (fun (acc : List Rat × Rat) d => ((acc.2 + d) :: acc.1, acc.2 + d))
    ([0], 0)).1.reverse

/-- One point of a stroke's side (`Grow.sidePoint`): the sample's point `x.1.1`, moved along the
normal of its direction `x.1.2` by the half-width at its running length `x.2`, of a line `S`
long. `sd` seeds the side's noise, and `sign` picks the side. With `tip` the half-width narrows
towards the end of the line, to a fifth of itself. -/
def sidePoint (seed : Nat) (o : Organic) (hw S : Rat) (tip : Bool) (sd : Nat) (sign : Rat)
    (x : (Vec × Vec) × Rat) : Vec :=
  let h := halfWidth hw o.noise (envelope (o.wave / 2) S x.2) (noise (seed + sd) o.wave x.2)
  let h := if tip = true ∧ 0 < S then h * min 1 ((S - x.2) * 3 / S + 1 / 5) else h
  x.1.1 + Vec.scale (sign * h) (Vec.normal x.1.2)

/-- **A stroke's closed outline** from its two sides, the right one turned (`Grow.outline`):
the left side's path, a line across the end, the right side's path, and a line back across the
start. An empty side has no outline. -/
def outline (left right : List Vec) : List Cubic :=
  match left.getLast?, right.head?, right.getLast?, left.head? with
  | some le, some rh, some rl, some lh =>
    through left ++ [Cubic.line le rh] ++ through right ++ [Cubic.line rl lh]
  | _, _, _, _ => []

/-- **An organic stroke** along a centre line (`Grow.stroke`): a closed outline whose
half-width is `w / 2` moved by the noise inside its band, the noise faded out at the ends. With
`tip`, the line narrows to its last point. An empty line has no sample, so no outline. -/
def stroke (seed : Nat) (o : Organic) (w : Rat) (cs : List Cubic) (tip : Bool) : List Cubic :=
  let ss := samples 8 cs
  let lens := runningLengths ss
  let S := lens.getLast?.getD 0
  let side (sd : Nat) (sign : Rat) : List Vec :=
    (ss.zip lens).map (sidePoint seed o (w / 2) S tip sd sign)
  outline (side 0 1) (side 7 (-1)).reverse

/-! ## The laws of the band -/

/-- A cell's value is in `[-1, 1]`. -/
theorem cellValue_band (seed cell : Nat) : -1 ≤ cellValue seed cell ∧ cellValue seed cell ≤ 1 := by
  unfold cellValue
  generalize mix seed cell = k
  have h0 : (0 : Rat) ≤ ((k % 2001 : Nat) : Rat) := Rat.natCast_nonneg
  have h1 : ((k % 2001 : Nat) : Rat) ≤ ((2000 : Nat) : Rat) :=
    Rat.natCast_le_natCast.mpr (by omega)
  have e : ((2000 : Nat) : Rat) = 2000 := Rat.natCast_ofNat
  rw [e] at h1
  generalize ((k % 2001 : Nat) : Rat) = q at h0 h1 ⊢
  constructor <;> grind

/-- Smoothstep takes `[0, 1]` into `[0, 1]`. The consumer clamps it; here it needs no clamp. -/
theorem smooth_band {t : Rat} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ smooth t ∧ smooth t ≤ 1 := by
  have a : 0 ≤ t * t * (3 - 2 * t) := Rat.mul_nonneg (rat_mul_self_nonneg t) (by grind)
  have b : 0 ≤ (1 - t) * (1 - t) * (1 + 2 * t) :=
    Rat.mul_nonneg (rat_mul_self_nonneg (1 - t)) (by grind)
  unfold smooth
  constructor <;> grind

-- kit: missing
/-- What a number is past its floor is in `[0, 1]`. -/
theorem fract_band (x : Rat) : 0 ≤ x - (x.floor : Rat) ∧ x - (x.floor : Rat) ≤ 1 := by
  have h0 := Rat.floor_le x
  have h1 := Rat.lt_floor_add_one x
  constructor <;> grind

/-- Value noise is in `[-1, 1]`: a step between the values of two cells (`Box.step_mem`). -/
theorem valueNoise_band (seed : Nat) (wave s : Rat) :
    -1 ≤ valueNoise seed wave s ∧ valueNoise seed wave s ≤ 1 := by
  have hf := fract_band (s / wave)
  have hu := smooth_band hf.1 hf.2
  have ha := cellValue_band seed (s / wave).floor.toNat
  have hb := cellValue_band seed ((s / wave).floor.toNat + 1)
  unfold valueNoise
  exact Box.step_mem ha.1 ha.2 hb.1 hb.2 hu.1 hu.2

/-- **The noise stays in its band** (`Grow.noise_band`): `[-1, 1]`, for every seed, wave and
length. -/
theorem noise_band (seed : Nat) (wave s : Rat) :
    -1 ≤ noise seed wave s ∧ noise seed wave s ≤ 1 := by
  have h1 := valueNoise_band seed wave s
  have h2 := valueNoise_band (seed + 1) (wave / 2) s
  unfold noise
  -- The two octaves are named before the arithmetic. Left as they stand, the search compares
  -- them by unfolding both down to the hash, whose 32-bit factors exhaust the memory.
  generalize valueNoise seed wave s = a at h1 ⊢
  generalize valueNoise (seed + 1) (wave / 2) s = b at h2 ⊢
  constructor <;> grind

/-- The envelope is in `[0, 1]`, for every ramp and every two lengths. -/
theorem envelope_band (ramp S s : Rat) : 0 ≤ envelope ramp S s ∧ envelope ramp S s ≤ 1 := by
  unfold envelope
  split <;> constructor <;> grind

/-- **The half-width stays in its band** (`Grow.halfWidth_band`): for a half-width and a share
that are not negative, an envelope in `[0, 1]` and a noise in `[-1, 1]`, the moved half-width
differs from `hw` by at most `hw` times the share. -/
theorem halfWidth_band {hw amp env v : Rat} (hw0 : 0 ≤ hw) (hamp : 0 ≤ amp)
    (henv : 0 ≤ env ∧ env ≤ 1) (hv : -1 ≤ v ∧ v ≤ 1) :
    hw - hw * amp ≤ halfWidth hw amp env v ∧ halfWidth hw amp env v ≤ hw + hw * amp := by
  have a : 0 ≤ hw * amp := Rat.mul_nonneg hw0 hamp
  have b0 : 0 ≤ hw * amp * env := Rat.mul_nonneg a henv.1
  have b1 : hw * amp * env ≤ hw * amp * 1 := Rat.mul_le_mul_of_nonneg_left henv.2 a
  have c1 : hw * amp * env * v ≤ hw * amp * env * 1 := Rat.mul_le_mul_of_nonneg_left hv.2 b0
  have c0 : hw * amp * env * (-1) ≤ hw * amp * env * v := Rat.mul_le_mul_of_nonneg_left hv.1 b0
  unfold halfWidth
  constructor <;> grind

/-- **Each edge of a stroke stays in its band**: the half-width that `sidePoint` computes before
the tip, at every seed, side, length of the line and place along it. The consumer states the
band of `halfWidth` under premises on the envelope and the noise; here both are proved. -/
theorem edge_band (seed sd : Nat) (o : Organic) {hw : Rat} (S s : Rat) (hw0 : 0 ≤ hw)
    (hn : 0 ≤ o.noise) :
    hw - hw * o.noise ≤
        halfWidth hw o.noise (envelope (o.wave / 2) S s) (noise (seed + sd) o.wave s) ∧
      halfWidth hw o.noise (envelope (o.wave / 2) S s) (noise (seed + sd) o.wave s) ≤
        hw + hw * o.noise :=
  halfWidth_band hw0 hn (envelope_band _ _ _) (noise_band _ _ _)

/-! ## The move law of a stroke

A stroke reads its centre line through its samples. A move of the line moves each sample's
point and keeps its direction (`samples_move`). Every later step reads a difference of two
points or adds an offset to a point. So the stroke of a moved line is the stroke, moved
(`stroke_move`). The consumer proves each step by hand on `Int`; here each is a law of the
kit. -/

/-- A sample moved by `d`: its point moved, its direction kept (`Grow.shiftSample`). -/
def shiftSample (d : Vec) (x : Vec × Vec) : Vec × Vec := (x.1 + d, x.2)

/-- A moved cubic's samples are the samples, moved (`Cubic.move_pointAt`,
`Cubic.move_direction`). -/
theorem sampleAlong_move (n : Nat) (c : Cubic) (first : Bool) (d : Vec) :
    sampleAlong n (c.move d) first = (sampleAlong n c first).map (shiftSample d) := by
  simp only [sampleAlong, List.map_map, Cubic.move_pointAt, Cubic.move_direction,
    Function.comp_def, shiftSample]

/-- **A moved line's samples are the samples, moved.** -/
theorem samples_move (n : Nat) (cs : List Cubic) (d : Vec) :
    samples n (cs.map (Cubic.move d)) = (samples n cs).map (shiftSample d) := by
  cases cs with
  | nil => rfl
  | cons c rest =>
    simp only [List.map_cons, samples, sampleAlong_move, List.map_append, List.flatMap_map,
      List.map_flatMap]

/-- Moved samples take the same steps (`Vec.dist_move`). -/
theorem steps_shift (d : Vec) (ss : List (Vec × Vec)) :
    steps (ss.map (shiftSample d)) = steps ss := by
  simp only [steps, ← List.map_drop, List.zip_map, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp, Prod.map, shiftSample, Vec.dist_move]

/-- Moved samples have the same running lengths. -/
theorem runningLengths_shift (d : Vec) (ss : List (Vec × Vec)) :
    runningLengths (ss.map (shiftSample d)) = runningLengths ss := by
  simp only [runningLengths, steps_shift]

-- kit: missing
/-- A sum of three points with its last two exchanged. -/
theorem vec_add_right_comm (p d q : Vec) : p + d + q = p + q + d := by
  rw [Vec.add_assoc, Vec.add_comm d q, ← Vec.add_assoc]

/-- A side's point at a moved sample is the point, moved. -/
theorem sidePoint_shift (seed : Nat) (o : Organic) (hw S : Rat) (tip : Bool) (sd : Nat)
    (sign : Rat) (d : Vec) (x : (Vec × Vec) × Rat) :
    sidePoint seed o hw S tip sd sign (shiftSample d x.1, x.2) =
      sidePoint seed o hw S tip sd sign x + d := by
  simp only [sidePoint, shiftSample]
  exact vec_add_right_comm _ _ _

/-- A side of moved samples is the side, moved. -/
theorem side_shift (seed : Nat) (o : Organic) (hw S : Rat) (tip : Bool) (sd : Nat)
    (sign : Rat) (d : Vec) (l : List ((Vec × Vec) × Rat)) :
    (l.map (Prod.map (shiftSample d) id)).map (sidePoint seed o hw S tip sd sign) =
      (l.map (sidePoint seed o hw S tip sd sign)).map (fun p => p + d) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  exact sidePoint_shift seed o hw S tip sd sign d x

-- kit: missing
/-- A smooth path through moved points is the path, moved (`Grow.through_shift`). -/
theorem through_move (d : Vec) (qs : List Vec) :
    through (qs.map fun p => p + d) = (through qs).map (Cubic.move d) := by
  unfold through
  rw [Curve.doubled_map]
  exact Curve.windows_map _ _ _ (Curve.cardinalSegment_move (1 / 6) d) _

/-- An outline of moved sides is the outline, moved (`Grow.outline_shift`). -/
theorem outline_move (d : Vec) (left right : List Vec) :
    outline (left.map fun p => p + d) (right.map fun p => p + d) =
      (outline left right).map (Cubic.move d) := by
  unfold outline
  rw [List.getLast?_map, List.head?_map, List.getLast?_map, List.head?_map]
  cases left.getLast? <;> cases right.head? <;> cases right.getLast? <;> cases left.head? <;>
    simp only [Option.map_none, Option.map_some, List.map_nil, List.map_append, List.map_cons,
      through_move, Cubic.move_line]

/-- **The move law of a stroke** (`Grow.stroke_move`). The stroke of a centre line moved by `d`
is the stroke, moved by `d`: for every seed, organic settings, width, line and tip. The
consumer's moves a line by whole pixels and its stroke by a thousand times as many
thousandths; here both are one move. -/
theorem stroke_move (seed : Nat) (o : Organic) (w : Rat) (cs : List Cubic) (tip : Bool) (d : Vec) :
    stroke seed o w (cs.map (Cubic.move d)) tip = (stroke seed o w cs tip).map (Cubic.move d) := by
  simp only [stroke, samples_move, runningLengths_shift, List.zip_map_left, side_shift]
  rw [← List.map_reverse, outline_move]

/-- A stroke reads its organic settings' noise and wave alone (`Grow.stroke_organic`). -/
theorem stroke_organic (seed : Nat) {o o' : Organic} (hn : o.noise = o'.noise)
    (hw : o.wave = o'.wave) (w : Rat) (cs : List Cubic) (tip : Bool) :
    stroke seed o w cs tip = stroke seed o' w cs tip := by
  have side : sidePoint seed o = sidePoint seed o' := by
    funext hw' S tip' sd sign x
    simp only [sidePoint, hn, hw]
  simp only [stroke, side]

/-- A line moved to the origin by a point, and back, is the line (`move_back` of
`tools/Tools/View/Graph.lean`). -/
theorem move_back (cs : List Cubic) (p : Vec) :
    (cs.map (Cubic.move (-p))).map (Cubic.move p) = cs := by
  -- kit: missing
  have e : -p + p = Vec.zero := by
    apply Vec.ext <;> simp only [Vec.add_def, Vec.neg_def, Vec.zero] <;> grind
  simp only [List.map_map, Function.comp_def, Cubic.move_move, e, Cubic.move_zero, List.map_id']

/-- **A stroke kept at the origin and moved back is the stroke**: the step of the consumer's
stroke cache that reads the move law (`cachedStroke_eq`), for a move by any point. -/
theorem stroke_from_origin (seed : Nat) (o : Organic) (w : Rat) (cs : List Cubic) (tip : Bool)
    (p : Vec) :
    (stroke seed o w (cs.map (Cubic.move (-p))) tip).map (Cubic.move p) =
      stroke seed o w cs tip := by
  rw [← stroke_move, move_back]

/-! ## A stroke is a closed outline

The consumer does not state it. The kit states it for its own curves (`Curve.chained_cubics`,
`Curve.cubics_getLast`, `Curve.cubics_head_of`), whose ends differ from the consumer's, so the
like of those laws are proved here for `through`. -/

-- kit: missing
/-- A smooth path through points is a chain. -/
theorem chained_through (qs : List Vec) : Cubic.Chained (through qs) = true :=
  Curve.chained_windows _ (Curve.cardinalSegment_join _) _

-- kit: missing
/-- The list of two points or more with each end twice. -/
theorem doubled_cons_cons (a b : Vec) (rest : List Vec) :
    ∃ l, Curve.doubled (a :: b :: rest) = a :: a :: b :: rest ++ [l] :=
  ⟨_, rfl⟩

-- kit: missing
/-- A smooth path starts a segment at every point but the last. -/
theorem through_starts (qs : List Vec) : (through qs).map (fun s => s.p0) = qs.dropLast := by
  unfold through
  rw [Curve.windows_cardinal_starts]
  match qs with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    obtain ⟨l, h⟩ := doubled_cons_cons a b rest
    rw [h]
    show ((a :: b :: rest) ++ [l]).dropLast.dropLast = (a :: b :: rest).dropLast
    rw [List.dropLast_concat]

-- kit: missing
/-- A smooth path ends a segment at every point but the first. -/
theorem through_ends (qs : List Vec) : (through qs).map (fun s => s.p3) = qs.tail := by
  unfold through
  rw [Curve.windows_cardinal_ends]
  match qs with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    obtain ⟨l, h⟩ := doubled_cons_cons a b rest
    rw [h]
    show ((b :: rest) ++ [l]).dropLast = b :: rest
    rw [List.dropLast_concat]

-- kit: missing
/-- The last segment of a smooth path ends at the last point of its list. -/
theorem through_getLast : ∀ (qs : List Vec) (x : Cubic),
    (through qs).getLast? = some x → qs.getLast? = some x.p3
  | [], _, h => by cases h
  | [_], _, h => by cases h
  | a :: b :: rest, x, h => by
    have e := congrArg List.getLast? (through_ends (a :: b :: rest))
    rw [List.getLast?_map, h] at e
    rw [List.getLast?_cons_cons]
    exact e.symm

-- kit: missing
/-- The first segment of a smooth path starts at the first point of its list. -/
theorem through_head_of : ∀ (qs : List Vec) (y : Cubic),
    (through qs).head? = some y → qs.head? = some y.p0
  | [], _, h => by cases h
  | [_], _, h => by cases h
  | a :: b :: rest, y, h => by
    have e := congrArg List.head? (through_starts (a :: b :: rest))
    rw [List.head?_map, h] at e
    exact e.symm

-- kit: missing
/-- A smooth path with no segment is through one point at most: its first is its last. -/
theorem through_eq_nil : ∀ (qs : List Vec) (a b : Vec),
    through qs = [] → qs.head? = some a → qs.getLast? = some b → a = b
  | [], _, _, _, ha, _ => by cases ha
  | [_], _, _, _, ha, hb => by
    cases ha
    cases hb
    rfl
  | a :: b :: rest, _, _, h, _, _ => by
    have e := through_ends (a :: b :: rest)
    rw [h] at e
    cases e

/-- **The outline of two sides is a chain that ends where it starts**, for every two lists of
points. -/
theorem closed_outline (left right : List Vec) : Cubic.Closed (outline left right) = true := by
  unfold outline
  cases hle : left.getLast? with
  | none => rfl
  | some le =>
    cases hrh : right.head? with
    | none => rfl
    | some rh =>
      cases hrl : right.getLast? with
      | none => rfl
      | some rl =>
        cases hlh : left.head? with
        | none => rfl
        | some lh =>
          have hmid :
              Cubic.Chained (through left ++ [Cubic.line le rh] ++ through right) = true := by
            have h := Curve.chained_bridge (through left) (through right) left.getLast? right.head?
              (chained_through left) (chained_through right) (through_getLast left)
              (through_head_of right)
            rw [hle, hrh] at h
            exact h
          have hall : Cubic.Chained
              (through left ++ [Cubic.line le rh] ++ through right ++ [Cubic.line rl lh]) =
                true := by
            refine Cubic.chained_append _ _ hmid rfl ?_
            intro x y hx hy
            cases hy
            cases hr : through right with
            | nil =>
              rw [hr, List.append_nil, List.getLast?_concat] at hx
              cases hx
              exact through_eq_nil right rh rl hr hrh hrl
            | cons s ss =>
              rw [hr, Curve.getLast?_append_cons] at hx
              have hx' := through_getLast right x (by rw [hr]; exact hx)
              rw [hrl] at hx'
              exact (Option.some.inj hx').symm
          refine Curve.closed_of _ hall ?_
          rw [List.getLast?_concat]
          cases hl : through left with
          | nil =>
            have e := through_eq_nil left lh le hl hlh hle
            rw [e]
            rfl
          | cons s ss =>
            have e := through_head_of left s (by rw [hl]; rfl)
            rw [hlh] at e
            exact e

/-- **Every stroke is a chain that ends where it starts**, for every seed, settings, width,
centre line and tip: the outline that `Path.ofLoops` asks for, where a list that is no chain is
written as several subpaths. -/
theorem closed_stroke (seed : Nat) (o : Organic) (w : Rat) (cs : List Cubic) (tip : Bool) :
    Cubic.Closed (stroke seed o w cs tip) = true :=
  closed_outline _ _

/-! ## A collar -/

/-- A collar is a chain that ends where it starts. -/
theorem closed_collar (p : Vec) (w R : Rat) (down : Bool) :
    Cubic.Closed (collar p w R down) = true := by
  simp only [collar, Cubic.Closed, Cubic.chained_cons, Cubic.chained_singleton, Cubic.line,
    Cubic.corner, List.getLast?_cons_cons, List.getLast?_singleton, Option.map_some, decide_true,
    Bool.and_self, beq_self_eq_true]

/-- The collar at a moved point is the collar, moved. -/
theorem collar_move (d p : Vec) (w R : Rat) (down : Bool) :
    collar (p + d) w R down = (collar p w R down).map (Cubic.move d) := by
  simp only [collar, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Cubic.ext <;> apply Vec.ext <;>
    simp only [Cubic.line, Cubic.corner, Cubic.move, Cubic.map, Vec.lerp, Vec.add_def] <;> grind

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

-- kit: missing
/-- Two points moved together are as far apart along the axes as they were. -/
theorem vec_taxi_move (d a b : Vec) : (a + d).taxi (b + d) = a.taxi b := by
  simp only [Vec.taxi, Vec.add_def]
  grind

-- kit: missing
/-- A moved segment has the size of the segment. -/
theorem taxi_move (d : Vec) (c : Cubic) : (c.move d).taxi = c.taxi := by
  simp only [Cubic.taxi, Cubic.move, Cubic.map, vec_taxi_move]

/-- **The segments revealed from their start for `budget` of size** (`Graph.revealed`): each
whole segment within the budget, then the part of the next one that the budget reaches. The
size of a segment is `Cubic.taxi`, and the part is exact: the consumer rounds its parameter
down to a part per mille, and each step of its split down to a pixel. -/
def revealed : List Cubic → Rat → List Cubic
  | [], _ => []
  | c :: rest, budget =>
    if budget ≤ 0 then []
    else if c.taxi ≤ budget then c :: revealed rest (budget - c.taxi)
    else [c.upTo (budget / c.taxi)]

/-- **A moved list is revealed as the list, moved.** The consumer reveals an edge where the
layout computed it and moves the result into place; by this law it may move first. -/
theorem revealed_move (d : Vec) : ∀ (cs : List Cubic) (budget : Rat),
    revealed (cs.map (Cubic.move d)) budget = (revealed cs budget).map (Cubic.move d)
  | [], _ => rfl
  | c :: rest, budget => by
    simp only [List.map_cons, revealed, taxi_move]
    split
    · rfl
    · split
      · rw [List.map_cons, revealed_move d rest]
      · rw [List.map_cons, List.map_nil, Cubic.move_upTo]

/-- The length of an arrowhead's two strokes along the segment, in logical pixels
(`Graph.HEAD_ALONG`). -/
def HEAD_ALONG : Rat := 6

/-- The reach of an arrowhead's two strokes across the segment (`Graph.HEAD_ACROSS`). -/
def HEAD_ACROSS : Rat := 4

/-- Where the two strokes of an arrowhead start, from the end of a segment that arrives along
`v`: back along the dominant axis of `v`, and to either side. `max a (-a)` is the size of a
number, for which the kit has no name. -/
def headBack (v : Vec) : Vec × Vec :=
  if max v.y (-v.y) ≤ max v.x (-v.x) then
    let s := if 0 ≤ v.x then -HEAD_ALONG else HEAD_ALONG
    (⟨s, -HEAD_ACROSS⟩, ⟨s, HEAD_ACROSS⟩)
  else
    let s := if 0 ≤ v.y then -HEAD_ALONG else HEAD_ALONG
    (⟨-HEAD_ACROSS, s⟩, ⟨HEAD_ACROSS, s⟩)

/-- **An arrowhead** where a segment ends (`Graph.arrowhead`): two short strokes back from its
end, along the dominant axis of its last direction. The consumer wraps each in a call and
moves it; this is the two segments. -/
def arrowhead (c : Cubic) : List Cubic :=
  [Cubic.line (c.p3 + (headBack (c.direction 1)).1) c.p3,
    Cubic.line (c.p3 + (headBack (c.direction 1)).2) c.p3]

/-- The arrowhead of a moved segment is the arrowhead, moved (`Cubic.move_direction`,
`Cubic.move_line`). -/
theorem arrowhead_move (d : Vec) (c : Cubic) :
    arrowhead (c.move d) = (arrowhead c).map (Cubic.move d) := by
  have e : (c.move d).p3 = c.p3 + d := rfl
  simp only [arrowhead, Cubic.move_direction, e, List.map_cons, List.map_nil, Cubic.move_line,
    vec_add_right_comm c.p3 d]

/-! ## A stroke as a mark of a picture -/

/-- A filled shape of closed outlines in one `d`, by the even-odd rule: the consumer's
`.shape`, in the ink. -/
def shapeNode (ink : Rgb) (outlines : List (List Cubic)) (key : String) : SvgNode :=
  Svg.loops outlines
    ([.className "e4-fill-ink", .fillRule true, .fill ink] ++ SvgAttr.dataKey? key)

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
    ((stroke (seedOf "e1") {} 2.4 [⟨⟨10, 20⟩, ⟨10, 33⟩, ⟨30, 33⟩, ⟨30, 46⟩⟩] false).take 2)) ==
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
  -- kit: missing
  have e : Box.ofSize ⟨x + d.x, y + d.y⟩ w h = (Box.ofSize ⟨x, y⟩ w h).move d := by
    simp only [Box.ofSize, Box.move, Box.mk.injEq]
    grind
  rw [roundRect, e, Cubic.roundRect_move]
  rfl

-- The part of a straight segment up to `t` is the straight segment to the point `t` of the
-- way along: a reveal of a straight edge is that share of its length.
example (a b : Vec) (t : Rat) : (Cubic.line a b).upTo t = Cubic.line a (a.lerp b t) := by
  rw [Cubic.upTo_eq_between, Cubic.line_between, Vec.lerp_zero]

end WhatwgTest.Html.SvgStroke
