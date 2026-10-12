import Whatwg.Svg.Geometry.Cursor

/-!
# Whatwg.Svg.Geometry.Pen

Owner: a builder of path data (slice S10 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-44). A
program draws a path as it would on a canvas, one call after another, and the result is a
value of the typed `Path`:

```
Pen.begin p0 |>.lineTo p1 |>.curveTo c1 c2 p2 |>.close |>.d
```

A pen holds the subpaths that are finished, and the start and the commands of the one it is
drawing. It starts at a point, so a path that draws before it moves cannot be written. Every
command it writes is absolute, but those of `rect`, which are relative as the chapter's own
example of a rectangle is.

The result is a `Path`, so it prints and reads back by the law of the path grammar, with
nothing new to prove. `Pen.cursor` is the meaning of `Whatwg/Svg/Geometry/Cursor.lean` at the
pen's own subpath, and the laws of `Whatwg/Svg/Geometry/Pen/Laws.lean` say that it is the cursor
of the path the pen builds, and where each call leaves it.

What this module does not claim: an arc by its centre and its angles, or a corner by two
tangents. Both need a sine or a square root. `arcTo` is the chapter's own arc command, which
names the point it ends at, so a rounded corner is one call.
-/

namespace Whatwg.Svg.Value

/-- A path that is being drawn: the finished subpaths in order, each its start and its
commands, and the start and the commands of the current one. -/
structure Pen where
  /-- The subpaths that are finished, in order. -/
  done : List (Point × List Command)
  /-- The start of the current subpath. -/
  start : Point
  /-- The commands of the current subpath, in order. -/
  commands : List Command
  deriving DecidableEq, Repr, Inhabited

namespace Pen

/-- A pen at a point: the first moveto of the path. -/
def begin (p : Point) : Pen := ⟨[], p, []⟩

/-- One more command of the current subpath. -/
def push (pen : Pen) (c : Command) : Pen := { pen with commands := pen.commands ++ [c] }

/-- More commands of the current subpath. -/
def pushAll (pen : Pen) (cs : List Command) : Pen := { pen with commands := pen.commands ++ cs }

/-- A new subpath at a point. A subpath with no command is replaced: two movetos in a row
draw what the second draws. -/
def moveTo (pen : Pen) (p : Point) : Pen :=
  match pen.commands with
  | [] => { pen with start := p }
  | _ :: _ => ⟨pen.done ++ [(pen.start, pen.commands)], p, []⟩

/-- A straight segment to a point. -/
def lineTo (pen : Pen) (p : Point) : Pen := pen.push (.lineto false p [])

/-- A horizontal segment to an `x`. -/
def hTo (pen : Pen) (x : Decimal) : Pen := pen.push (.horizontalLineto false x [])

/-- A vertical segment to a `y`. -/
def vTo (pen : Pen) (y : Decimal) : Pen := pen.push (.verticalLineto false y [])

/-- A cubic Bézier segment by its two control points and its end. -/
def curveTo (pen : Pen) (c1 c2 p : Point) : Pen := pen.push (.curveto false (c1, c2, p) [])

/-- A cubic Bézier segment whose first control point reflects the last one. -/
def smoothTo (pen : Pen) (c2 p : Point) : Pen := pen.push (.smoothCurveto false (c2, p) [])

/-- A quadratic Bézier segment by its control point and its end. -/
def quadTo (pen : Pen) (c p : Point) : Pen := pen.push (.quadraticBezierCurveto false (c, p) [])

/-- An elliptical arc to a point: the chapter's arc command, by its two radii, its two flags
and its end. -/
def arcTo (pen : Pen) (rx ry : Magnitude) (largeArc sweep : Bool) (p : Point)
    (rotation : Magnitude := 0) : Pen :=
  pen.push (.ellipticalArc false ⟨rx, ry, rotation, largeArc, sweep, p⟩ [])

/-- Straight segments through a list of points, as one command; nothing for no point. -/
def linesTo (pen : Pen) : List Point → Pen
  | [] => pen
  | p :: rest => pen.push (.lineto false p rest)

/-- Cubic Bézier segments, each by its two control points and its end, as one command; nothing
for no segment. -/
def curvesTo (pen : Pen) : List (Point × Point × Point) → Pen
  | [] => pen
  | s :: rest => pen.push (.curveto false s rest)

/-- Close the current subpath: a straight segment back to its start. -/
def close (pen : Pen) : Pen := pen.push (.closepath false)

/-- A rectangle as a closed subpath of its own, by a corner, a width and a height: a moveto,
and then `h`, `v`, `h` and a closepath. -/
def rect (pen : Pen) (corner : Point) (width height : Decimal) : Pen :=
  (pen.moveTo corner).pushAll
    [.horizontalLineto true width [], .verticalLineto true height [],
      .horizontalLineto true (-width) [], .closepath false]

/-- The subpaths of the pen, in order: the finished ones and the current one. -/
def subpaths (pen : Pen) : List (Point × List Command) := pen.done ++ [(pen.start, pen.commands)]

/-- The path that the pen has drawn. -/
def path (pen : Pen) : Path := .ofSubpaths pen.subpaths

/-- The path of several pens, each after the one before: a shape of several closed parts in
one `d`. -/
def join (pens : List Pen) : Path := .ofSubpaths (pens.flatMap subpaths)

/-- The value of `d` that the pen has drawn. -/
def d (pen : Pen) : PathData := .path pen.path

/-- The two points of the path chapter at the pen: after the commands of its subpath. -/
def cursor (pen : Pen) : Cursor := (Cursor.mk pen.start pen.start).run pen.commands

/-- The current point of the pen. -/
def current (pen : Pen) : Point := pen.cursor.current

/-- The pen was handed no moveto as a command, so its subpath is the one that started at
`start`. Every call of the pen keeps this but `push` and `pushAll`, which take any command. -/
def Plain (pen : Pen) : Bool := pen.commands.all fun c => !c.isMoveto

end Pen

end Whatwg.Svg.Value
