import Whatwg.Svg.Scene.Moves
import Whatwg.Svg.Scene.Join

/-!
# Whatwg.Svg.Scene.Motion

Owner: motion as data (slice S12 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-62).

A step from one picture to the next is not a row of pictures. It is one picture, the next one,
and for each thing in it a *track*: what changes, from where to where, and when. A reader of
tracks draws the moments between: a browser reads them as CSS animations
(`Whatwg/Html/Node/SvgMotion.lean`), and a program reads them with `Track.at`.

Everything here counts in whole numbers, as lean4-effect4's `tools/Tools/View/Look.lean` and
`Motion.lean` do: a moment and a progress are in thousandths (per mille) of a step, and a
division rounds down. So this layer is under the strict ceiling. What each rounded number is
the floor of, in exact numbers, is said in `Whatwg/Svg/Geometry/Easing.lean`.

- `mix u v e`: the value `e` per mille of the way from `u` to `v`.
- `Easing`: a progress to an eased progress, in the two forms that CSS writes exactly.
  `stops` is `linear()` of CSS Easing Functions 2 with its stops evenly spaced: straight lines
  between the values. `cubic y1 y2` is `cubic-bezier(1/3, y1, 2/3, y2)`: with those two
  abscissae the curve's `x` is the progress itself, so the eased progress is a cubic polynomial
  of the progress, `3 y1 s (1 - s)² + 3 y2 s² (1 - s) + s³`, and no equation is solved.
- `Transition`: a delay, a duration and an easing. `Transition.at` is the timing of a CSS
  animation that fills both ways: the start before the delay, the end after the duration.
  Between them it reads the easing at the share of the duration that has passed
  (`Easing.of`, since slice S13 and ruling SV-67): the progress is not rounded to a thousandth
  first, so the reading is what a browser computes, rounded down once.
- `Pose`: what a track sets at a moment: a shift, a size, a part revealed, an opacity, a shape.
  `Change`: a pose at the start and a pose at the end, of one kind. `Change.morph` is a change
  of shape between two lists of segments of whole units (ruling SV-68): an edge between two
  things that move differently changes so, and stays joined to both.
- `Track`: a key, a change and a transition. `Motion`: a list of tracks.
- `Motion.within` holds every track inside a step of a thousand, and `Motion.delayed` starts
  each track later by its key.

The tracks of a join, what each kept, new and old thing does, are in
`Whatwg/Svg/Scene/Plan.lean`: `Motion.ofJoin` of a `Plan`.

The laws are in `Whatwg/Svg/Scene/Motion/Laws.lean`. The first is the end law: a track whose
transition is over stands at the end of its change (`Track.at_done`), so a step's last moment
is the next picture.
-/

namespace Whatwg.Svg.Scene

/-- The value `e` per mille of the way from `u` to `v`, rounded down: `u` at `0` and `v` at
`1000`. An `e` outside that range goes beyond them, as an easing that overshoots asks. -/
def mix (u v e : Int) : Int := v + (u - v) * (1000 - e) / 1000

/-! ## Easing -/

/-- An easing: a progress in per mille to an eased progress in per mille. -/
inductive Easing where
  /-- Straight lines between values at evenly spaced stops: the first at progress `0`, the
  last at `1000`. CSS writes it `linear(…)`. -/
  | stops (values : List Int)
  /-- The cubic polynomial `3 y1 s (1 - s)² + 3 y2 s² (1 - s) + s³` of the progress `s`, with
  the two heights in per mille. CSS writes it `cubic-bezier(1/3, y1, 2/3, y2)`. It starts at
  `0` with the slope `3 y1` and ends at `1` with the slope `3 (1 - y2)`. -/
  | cubic (y1 y2 : Int)
  deriving DecidableEq, Repr, Inhabited

namespace Easing

/-- The straight lines between `values` at evenly spaced stops, read at `p` per mille. Past the
last stop it is the last value. No value reads as `0`. -/
def stopsAt (values : List Int) (p : Nat) : Int :=
  let pieces := values.length - 1
  let last := values.getLast?.getD 0
  let i := p * pieces / 1000
  let a := values.getD i last
  let b := values.getD (i + 1) last
  a + (b - a) * ((p * pieces - 1000 * i : Nat) : Int) / 1000

/-- The cubic of the heights `y1` and `y2`, read at `p` per mille: one division, so it is the
exact value rounded down. -/
def cubicAt (y1 y2 : Int) (p : Nat) : Int :=
  let q : Int := p
  (3 * y1 * q * (1000 - q) ^ 2 + 3 * y2 * q ^ 2 * (1000 - q) + 1000 * q ^ 3) / 1000000000

/-- The progress itself. -/
def linear : Easing := .stops [0, 1000]

/-- Slow at first: the cube of the progress. -/
def cubicIn : Easing := .cubic 0 0

/-- Slow at last: one less the cube of what remains. -/
def cubicOut : Easing := .cubic 1000 1000

/-- Slow at last, after going a tenth past the end: the usual `back` easing, with the
overshoot `1.70158`. -/
def backOut : Easing := .cubic 1567 1000

/-- A function of the progress as stops: its values at `pieces + 1` evenly spaced moments. Any
easing that a program computes becomes one that CSS writes. -/
def sampled (f : Nat → Int) (pieces : Nat := 20) : Easing :=
  .stops ((List.range (pieces + 1)).map fun i => f (i * 1000 / pieces))

end Easing

/-- The eased progress at `p` per mille. -/
def Easing.at : Easing → Nat → Int
  | .stops values, p => Easing.stopsAt values p
  | .cubic y1 y2, p => Easing.cubicAt y1 y2 p

namespace Easing

/-- The straight lines between `values`, read at the share `num / den` of the progress, in per
mille: `stopsAt` with the progress as a fraction, so that no progress is rounded before the
reading. -/
def stopsOf (values : List Int) (num den : Nat) : Int :=
  let pieces := values.length - 1
  let last := values.getLast?.getD 0
  let i := num * pieces / den
  let a := values.getD i last
  let b := values.getD (i + 1) last
  a + (b - a) * ((num * pieces - den * i : Nat) : Int) / den

/-- The cubic of the heights `y1` and `y2`, read at the share `num / den` of the progress, in
per mille: one division, so it is the exact value rounded down. -/
def cubicOf (y1 y2 : Int) (num den : Nat) : Int :=
  let n : Int := num
  let d : Int := den
  (3 * y1 * n * (d - n) ^ 2 + 3 * y2 * n ^ 2 * (d - n) + 1000 * n ^ 3) / d ^ 3

end Easing

/-- **The eased progress at the share `num / den` of the progress**, in per mille. A transition
reads its easing so, at the share of its duration that has passed: the progress is not rounded
to a thousandth first, and the reading is the exact eased progress rounded down once. -/
def Easing.of : Easing → Nat → Nat → Int
  | .stops values, num, den => Easing.stopsOf values num den
  | .cubic y1 y2, num, den => Easing.cubicOf y1 y2 num den

/-- An easing that starts at `0` and ends at `1000`. A cubic always does. -/
def Easing.Proper (e : Easing) : Prop := e.at 0 = 0 ∧ e.at 1000 = 1000

instance (e : Easing) : Decidable e.Proper := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Transitions -/

/-- A transition: a delay, a duration and an easing. A program that counts in milliseconds
brings them to per mille of its step with `Transition.per`. -/
structure Transition where
  delay : Nat := 0
  duration : Nat := 1000
  ease : Easing := Easing.linear
  deriving DecidableEq, Repr, Inhabited

/-- The eased progress of a transition at the moment `t`: the easing's start until the delay
is over, its end once the duration is over, and between them the easing of the share of the
duration that has passed. -/
def Transition.at (tr : Transition) (t : Nat) : Int :=
  if tr.delay + tr.duration ≤ t then tr.ease.at 1000
  else if t ≤ tr.delay then tr.ease.at 0
  else tr.ease.of (t - tr.delay) tr.duration

namespace Transition

/-- A transition held inside a step of a thousand: it starts by the step's end and ends by
it. -/
def within (tr : Transition) : Transition :=
  { tr with delay := min tr.delay 1000, duration := min tr.duration (1000 - min tr.delay 1000) }

/-- A transition started `d` later, held inside its step. -/
def after (tr : Transition) (d : Nat) : Transition :=
  ({ tr with delay := tr.delay + d } : Transition).within

/-- A transition of milliseconds in per mille of a step of `step` milliseconds. -/
def per (step : Nat) (tr : Transition) : Transition :=
  { tr with delay := tr.delay * 1000 / step, duration := tr.duration * 1000 / step }

end Transition

/-! ## What a track sets -/

/-- What a track sets on a thing at a moment. -/
inductive Pose where
  /-- The thing stands off its place by a step. -/
  | shift (step : IVec)
  /-- The thing is drawn at `size` per mille of its size, about its middle. -/
  | grow (size : Int)
  /-- `part` per mille of the thing's line is drawn, from its start. -/
  | reveal (part : Int)
  /-- The thing is drawn at `shown` per mille of its opacity. -/
  | fade (shown : Int)
  /-- The thing is drawn with this shape, in whole units, in place of its own. -/
  | shape (segments : List ICubic)
  deriving DecidableEq, Repr, Inhabited

/-- A pose that changes nothing: no shift, the whole size, the whole line, the whole opacity.
A still picture has every thing at rest. -/
def Pose.AtRest : Pose → Prop
  | .shift step => step = 0
  | .grow size => size = 1000
  | .reveal part => part = 1000
  | .fade shown => shown = 1000
  | .shape _ => True

instance (p : Pose) : Decidable p.AtRest := by
  cases p <;> unfold Pose.AtRest <;> exact inferInstance

/-- A segment of whole units, each coordinate `e` per mille of the way from one to another. -/
def ICubic.mix (a b : ICubic) (e : Int) : ICubic :=
  let step (p q : IVec) : IVec := ⟨Scene.mix p.x q.x e, Scene.mix p.y q.y e⟩
  ⟨step a.p0 b.p0, step a.p1 b.p1, step a.p2 b.p2, step a.p3 b.p3⟩

/-- A change of one kind: the pose at its start and the pose at its end. -/
inductive Change where
  | shift (start stop : IVec)
  | grow (start stop : Int)
  | reveal (start stop : Int)
  | fade (start stop : Int)
  /-- The thing's shape changes from one list of segments to another, in whole units. Each
  segment goes to the segment at its place. An edge between two things that move differently
  changes so, and stays joined to both. Two lists of different lengths have no shape between
  them: the change is then a jump at the middle, as it is in CSS. -/
  | morph (start stop : List ICubic)
  deriving DecidableEq, Repr, Inhabited

namespace Change

/-- The pose at the start. -/
def start : Change → Pose
  | .shift a _ => .shift a
  | .grow a _ => .grow a
  | .reveal a _ => .reveal a
  | .fade a _ => .fade a
  | .morph a _ => .shape a

/-- The pose at the end. -/
def stop : Change → Pose
  | .shift _ b => .shift b
  | .grow _ b => .grow b
  | .reveal _ b => .reveal b
  | .fade _ b => .fade b
  | .morph _ b => .shape b

end Change

/-- The pose of a change at the eased progress `e` per mille. -/
def Change.at : Change → Int → Pose
  | .shift a b, e => .shift ⟨mix a.x b.x e, mix a.y b.y e⟩
  | .grow a b, e => .grow (mix a b e)
  | .reveal a b, e => .reveal (mix a b e)
  | .fade a b, e => .fade (mix a b e)
  | .morph a b, e =>
    if a.length = b.length then .shape (List.zipWith (fun x y => ICubic.mix x y e) a b)
    else if e < 500 then .shape a
    else .shape b

/-! ## Tracks -/

/-- A track: the thing with the key `key` changes by `change`, timed by `timing`. -/
structure Track (κ : Type) where
  key : κ
  change : Change
  timing : Transition := {}
  deriving Repr

/-- The pose of a track at the moment `t` of its step. -/
def Track.at {κ : Type} (tr : Track κ) (t : Nat) : Pose := tr.change.at (tr.timing.at t)

/-- A track is over at the moment `t`: its easing is proper and its transition has ended. -/
def Track.Done {κ : Type} (tr : Track κ) (t : Nat) : Prop :=
  tr.timing.ease.Proper ∧ tr.timing.delay + tr.timing.duration ≤ t

/-- A track that ends at rest: what it leaves is the still picture. -/
def Track.Settles {κ : Type} (tr : Track κ) : Prop := tr.change.stop.AtRest

/-- The motion of a step: its tracks. -/
abbrev Motion (κ : Type) : Type := List (Track κ)

namespace Motion

variable {κ : Type}

/-- Every key with its pose, track by track, at the moment `t`. -/
def poses (m : Motion κ) (t : Nat) : List (κ × Pose) := m.map fun tr => (tr.key, tr.at t)

/-- The poses of one key at the moment `t`. A key with no track has none, and is at rest. -/
def posesOf [BEq κ] (m : Motion κ) (key : κ) (t : Nat) : List Pose :=
  (m.filter fun tr => tr.key == key).map fun tr => tr.at t

/-- The motion with every transition held inside a step of a thousand. -/
def within (m : Motion κ) : Motion κ := m.map fun tr => { tr with timing := tr.timing.within }

/-- **The motion with each track started later**, by what `later` gives its key: things that
enter one after another, level by level or row by row. Hold the result in its step with
`within`. -/
def delayed (m : Motion κ) (later : κ → Nat) : Motion κ :=
  m.map fun tr => { tr with timing := { tr.timing with delay := tr.timing.delay + later tr.key } }

end Motion

end Whatwg.Svg.Scene
