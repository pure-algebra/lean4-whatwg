import Whatwg.Svg.Geometry.Shape
import Whatwg.Svg.Geometry.Root
import Whatwg.Svg.Geometry.Noise

/-!
# Whatwg.Svg.Geometry.Stroke

Owner: a line drawn as a filled outline, and what stands at its ends (slice S12 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-66). SVG strokes a path with
one width. A program that draws by hand wants a line whose width changes along it: thicker
where it carries more, narrower towards its tip, and not quite even. Such a line is no stroke
of SVG. It is a closed outline, filled.

How a stroke is built, each step a definition of its own:

- **The centre line** is a list of cubic segments, a chain.
- **Samples** (`Stroke.samples`): each segment is read at `n` steps. A sample is a point, the
  direction of travel there, and the length run so far, which is the sum of the distances
  between samples, each rounded down at `places`.
- **A side** (`Stroke.side`): each sample's point, moved along the normal of its direction by
  a half-width. The half-width is a function of the length run and the length of the whole
  line, so it can change along the line.
- **The outline** (`Stroke.outline`): a smooth path through one side, a straight segment
  across the end, a smooth path back through the other side, and a straight segment across
  the start. The smooth path is `Curve.through`, a cardinal spline with each end point twice.
- **`Stroke.stroke`** is these together, with a half-width for each side.

`Stroke.organic` is a half-width that wanders: a width moved by the noise of
`Whatwg/Svg/Geometry/Noise.lean` inside a band, with no noise at the two ends of the line.

Beside the stroke: `Stroke.collar`, where a line meets a surface; `Cubic.revealed`, the first
part of a chain, for a line that is drawn bit by bit; and `Stroke.arrowhead`.

Two things round, and nothing else: the distance between two samples and the length of a
direction under a normal, both square roots (`Whatwg/Svg/Geometry/Root.lean`), both at
`places`. A caller that wants its outline on a grid passes a `snap`, which is applied to each
point of a side.

The laws are in `Whatwg/Svg/Geometry/Stroke/Laws.lean`: every stroke and every collar is a
chain that ends where it starts; each of these figures, made of a moved line, is the figure,
moved; and `Stroke.organic` without a tip stays in its band.

What this module does not claim: that an outline does not cross itself, which it does where
the line turns more sharply than it is wide; that an edge is a given distance from the centre
line, since a normal is of length one only nearly, and a spline through the points of a side
is not the curve beside the line; the length of a curve, of which the length run is a bound
from below by chords; a join or a cap of the stroke properties of SVG.
-/

namespace Whatwg.Svg.Value

/-- **A smooth path through points**: the cardinal spline with each end point twice, so that
it starts at the first point and ends at the last (`Curve.through_starts`,
`Curve.through_ends` of the laws). At tension zero it is the Catmull-Rom spline. The curve
`Curve.cardinal` puts the neighbour of each end beyond it instead, as d3 does, and so leaves
its first point with a velocity of zero; this one leaves along the step to its second point.
No segment for fewer than two points. -/
def Curve.through (points : List Vec) (tension : Rat := 0) : List Cubic :=
  Curve.windows (Curve.cardinalSegment (Curve.cardinalScale tension)) (Curve.doubled points)

namespace Stroke

/-! ## The samples of a centre line -/

/-- A point of a centre line, the direction of travel there, and the length run from the
start of the line to the point. -/
structure Sample where
  /-- the point of the centre line -/
  point : Vec
  /-- the direction of travel at the point; its length says nothing -/
  direction : Vec
  /-- the length run so far, through the samples before this one -/
  along : Rat
  deriving DecidableEq, Repr, Inhabited

/-- The sample moved by `d`: its point moved, its direction and its length kept. -/
def Sample.move (d : Vec) (s : Sample) : Sample := ⟨s.point + d, s.direction, s.along⟩

/-- The points of one segment with their directions, at the parameters `k / n`. The first
segment of a line keeps its start; a later one drops it, since it is the end of the segment
before, which is kept with the direction in which that segment arrives. -/
def stationsOf (c : Cubic) (n : Nat) (first : Bool) : List (Vec × Vec) :=
  ((List.range (n + 1)).drop (if first then 0 else 1)).map fun (k : Nat) =>
    (c.pointAt ((k : Rat) / (n : Rat)), c.direction ((k : Rat) / (n : Rat)))

/-- The points of a line with their directions: each segment at `n` steps. For `n = 0` it is
the start of the line alone. -/
def stations (cs : List Cubic) (n : Nat) : List (Vec × Vec) :=
  match cs with
  | [] => []
  | c :: rest => stationsOf c n true ++ rest.flatMap fun c => stationsOf c n false

/-- The samples at a list of points with their directions, after the point `prev`, which was
reached at the length `run`: each is as far on as the distance from the point before it. -/
def measured (places : Nat) (run : Rat) (prev : Vec) : List (Vec × Vec) → List Sample
  | [] => []
  | x :: rest =>
    ⟨x.1, x.2, run + prev.dist x.1 places⟩ ::
      measured places (run + prev.dist x.1 places) x.1 rest

/-- **The samples of a centre line**: each segment at `n` steps, the first segment keeping its
start. The length run is `0` at the first sample, and at each later one it is the sum of the
distances between the samples so far, each rounded down at `places` (`Vec.dist`). No sample
for no segment. -/
def samples (cs : List Cubic) (n : Nat := 8) (places : Nat := 3) : List Sample :=
  match stations cs n with
  | [] => []
  | x :: rest => ⟨x.1, x.2, 0⟩ :: measured places 0 x.1 rest

/-- The length of the whole line, through its samples: the length run at the last one, and
zero for no sample. -/
def total (ss : List Sample) : Rat := (ss.getLast?.map fun s => s.along).getD 0

/-! ## A side, and the outline of two sides -/

/-- **One side of a stroke**: each sample's point, moved along the normal of its direction by
`sign` times the half-width there, and then put where `snap` puts it. The half-width
`half along whole` reads the length run at the sample and the length of the whole line. The
normal points to the right of the direction of travel on a screen (`Vec.normal`), so a `sign`
of `1` is the right side and `-1` the left. The length of a direction is rounded at
`places`. -/
def side (ss : List Sample) (half : Rat → Rat → Rat) (sign : Rat) (snap : Vec → Vec := id)
    (places : Nat := 3) : List Vec :=
  let whole := total ss
  ss.map fun s =>
    snap (s.point + Vec.scale (sign * half s.along whole) (s.direction.normal places))

/-- **The closed outline of two sides**: a smooth path through `ahead`, a straight segment
from its last point to the first of `back`, a smooth path through `back`, and a straight
segment from its last point to the first of `ahead`. `back` is given in the order in which
the outline runs it: for a stroke, from the end of the line to its start. No outline where a
side has no point. -/
def outline (ahead back : List Vec) (tension : Rat := 0) : List Cubic :=
  match ahead.getLast?, back.head?, back.getLast?, ahead.head? with
  | some aheadLast, some backFirst, some backLast, some aheadFirst =>
    Curve.through ahead tension ++ [Cubic.line aheadLast backFirst] ++
      Curve.through back tension ++ [Cubic.line backLast aheadFirst]
  | _, _, _, _ => []

/-- **A stroke of varying width**: the closed outline of the line `cs`, whose half-width at
the length `along` of a line `whole` long is `right along whole` on its right and
`left along whole` on its left. Right and left are those of the direction of travel on a
screen, where `y` grows downwards: a line that runs down the screen has its right side at the
lesser `x`. The outline runs out along the right side, across the end, back along the left
side and across the start. Each segment is read at `n` steps, each point of a side is put
where `snap` puts it, and the two roots are rounded at `places`. No outline for no segment. -/
def stroke (cs : List Cubic) (right left : Rat → Rat → Rat) (n : Nat := 8)
    (snap : Vec → Vec := id) (places : Nat := 3) : List Cubic :=
  let ss := samples cs n places
  outline (side ss right 1 snap places) (side ss left (-1) snap places).reverse

/-- **A half-width that wanders**, for a side of `stroke`: `hw`, moved by the noise of two
octaves at most the share `amp` of itself (`organic_band` of the laws). The noise has cells
`wave` long and fades out over half a wave at each end of the line (`Noise.envelope`), so the
line starts and ends at its width. With `tip` the half-width narrows over the last four
fifteenths of the line, to a fifth of itself at the end. Two sides of one line take two
seeds. -/
def organic (seed : Nat) (hw amp wave : Rat) (tip : Bool := false) : Rat → Rat → Rat :=
  fun along whole =>
    let h := hw + hw * amp * Noise.envelope (wave / 2) whole along * Noise.two seed wave along
    if tip = true ∧ 0 < whole then h * min 1 ((whole - along) * 3 / whole + 1 / 5) else h

/-! ## Where a line ends -/

/-- **A collar** where a line `w` wide meets a surface at `p`: a quarter turn of radius `r` on
each side, from the line `r` away from the surface out along the surface, and closed. The
surface runs along `x`. `down` when the line leaves the surface towards a greater `y`. `k` is
the roundness of a quarter turn (`Cubic.corner`). -/
def collar (p : Vec) (w r : Rat) (down : Bool) (k : Rat := Cubic.kappa) : List Cubic :=
  let s : Rat := if down then 1 else -1
  let hw := w / 2
  let l0 : Vec := ⟨p.x - hw, p.y + s * r⟩
  let l3 : Vec := ⟨p.x - hw - r, p.y⟩
  let r0 : Vec := ⟨p.x + hw + r, p.y⟩
  let r3 : Vec := ⟨p.x + hw, p.y + s * r⟩
  [Cubic.corner l0 ⟨p.x - hw, p.y⟩ l3 k, Cubic.line l3 r0,
    Cubic.corner r0 ⟨p.x + hw, p.y⟩ r3 k, Cubic.line r3 l0]

/-- Where the two strokes of an arrowhead start, from the end of a segment that arrives along
`v`: `along` back on the greater axis of `v`, and `across` to either side. -/
def headBack (v : Vec) (along across : Rat) : Vec × Vec :=
  if max v.y (-v.y) ≤ max v.x (-v.x) then
    let s := if 0 ≤ v.x then -along else along
    (⟨s, -across⟩, ⟨s, across⟩)
  else
    let s := if 0 ≤ v.y then -along else along
    (⟨-across, s⟩, ⟨across, s⟩)

/-- **An arrowhead** where a segment ends: two straight strokes to its end, each from `along`
back and `across` to one side. Back is along an axis, the one on which the segment's last
direction is the greater (`Cubic.direction` at `1`), so the head of a segment that arrives at
a slant is not turned with it. -/
def arrowhead (c : Cubic) (along across : Rat) : List Cubic :=
  [Cubic.line (c.p3 + (headBack (c.direction 1) along across).1) c.p3,
    Cubic.line (c.p3 + (headBack (c.direction 1) along across).2) c.p3]

end Stroke

/-- **The segments revealed from their start for `budget` of size**: each whole segment
within the budget, then the part of the next one that the budget reaches, and nothing for a
budget that is not positive. The size of a segment is `Cubic.taxi`, which needs no root, and
the part is exact (`Cubic.upTo`). A line drawn bit by bit is revealed for a growing budget. -/
def Cubic.revealed : List Cubic → Rat → List Cubic
  | [], _ => []
  | c :: rest, budget =>
    if budget ≤ 0 then []
    else if c.taxi ≤ budget then c :: revealed rest (budget - c.taxi)
    else [c.upTo (budget / c.taxi)]

end Whatwg.Svg.Value
