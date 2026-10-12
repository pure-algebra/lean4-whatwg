import Whatwg.Svg.Value.Path
import Whatwg.Svg.Geometry.Arith

/-!
# Whatwg.Svg.Geometry.Cursor

Owner: what a path means for the point it has reached (slice S10 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-44). The authority is the chapter Paths of SVG 2, sealed
at `vendor/w3c-svgwg-47e645ef/master/paths.html`. It reads path data with two points in hand:

- the **current point**, where the next command starts;
- the **initial point of the current subpath**, which a moveto sets and a closepath returns
  to.

`Cursor` is that pair, and `Command.advance` is what one command does to it:

- a moveto sets both points; its further pairs are linetos;
- a closepath sets the current point to the initial point, and a command after it that is no
  moveto starts a subpath at that same point;
- every other command ends at its last pair, and an `H` or a `V` changes one coordinate;
- a relative command gives each pair from the current point at the start of its segment.

`Path.cursor` is the cursor after a whole path. Its first moveto is absolute even when it is
written `m`, as the chapter states; the pairs after it are relative then.

This is the meaning that the pen (`Whatwg/Svg/Geometry/Pen.lean`) and the curves
(`Whatwg/Svg/Geometry/Shape.lean`) are stated against: a law of theirs says where the path they
build ends by this function, and not by a field they keep themselves.

What this module does not claim: the shape that a path draws. No control point, radius or
flag is read here, and no bounding box, length or interior is defined.

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from
Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C
Document License, https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Svg.Value

/-- The two points that the path chapter keeps while it reads commands. -/
structure Cursor where
  /-- The current point: where the next command starts. -/
  current : Point
  /-- The initial point of the current subpath: where a closepath returns. -/
  start : Point
  deriving DecidableEq, Repr, Inhabited

namespace Cursor

/-- The end of a segment: the pair itself, or the current point moved by it. -/
def target (s : Cursor) (relative : Bool) (p : Point) : Point :=
  if relative then s.current + p else p

/-- A segment to a pair: the current point moves, and the subpath stays. -/
def lineTo (s : Cursor) (relative : Bool) (p : Point) : Cursor := ⟨s.target relative p, s.start⟩

/-- A horizontal segment: the `x` of the current point changes. -/
def hTo (s : Cursor) (relative : Bool) (x : Decimal) : Cursor :=
  ⟨⟨if relative then s.current.x + x else x, s.current.y⟩, s.start⟩

/-- A vertical segment: the `y` of the current point changes. -/
def vTo (s : Cursor) (relative : Bool) (y : Decimal) : Cursor :=
  ⟨⟨s.current.x, if relative then s.current.y + y else y⟩, s.start⟩

/-- A moveto: a new subpath starts at the pair. -/
def moveTo (s : Cursor) (relative : Bool) (p : Point) : Cursor :=
  ⟨s.target relative p, s.target relative p⟩

/-- A closepath: the current point returns to the initial point of the subpath. -/
def close (s : Cursor) : Cursor := ⟨s.start, s.start⟩

end Cursor

/-- What one command does to the two points. -/
def Command.advance (s : Cursor) : Command → Cursor
  | .moveto relative first rest =>
    rest.foldl (fun c p => c.lineTo relative p) (s.moveTo relative first)
  | .closepath _ => s.close
  | .lineto relative first rest => (first :: rest).foldl (fun c p => c.lineTo relative p) s
  | .horizontalLineto relative first rest =>
    (first :: rest).foldl (fun c x => c.hTo relative x) s
  | .verticalLineto relative first rest => (first :: rest).foldl (fun c y => c.vTo relative y) s
  | .curveto relative first rest => (first :: rest).foldl (fun c t => c.lineTo relative t.2.2) s
  | .smoothCurveto relative first rest =>
    (first :: rest).foldl (fun c t => c.lineTo relative t.2) s
  | .quadraticBezierCurveto relative first rest =>
    (first :: rest).foldl (fun c t => c.lineTo relative t.2) s
  | .smoothQuadraticBezierCurveto relative first rest =>
    (first :: rest).foldl (fun c p => c.lineTo relative p) s
  | .ellipticalArc relative first rest => (first :: rest).foldl (fun c a => c.lineTo relative a.to) s

/-- The command is a moveto: it starts a subpath. -/
def Command.isMoveto : Command → Bool
  | .moveto _ _ _ => true
  | _ => false

/-- The two points after a list of commands. -/
def Cursor.run (s : Cursor) (commands : List Command) : Cursor := commands.foldl Command.advance s

namespace Path

/-- The two points after a path, and none for the empty path. The first moveto is absolute
even when it is written `m`; the pairs after it are relative then. -/
def cursor : Path → Option Cursor
  | .empty => none
  | .moveto relative first rest commands =>
    some ((rest.foldl (fun c p => c.lineTo relative p) (Cursor.mk first first)).run commands)

/-- Where a path ends: its current point after its last command. -/
def endPoint (p : Path) : Option Point := p.cursor.map (·.current)

end Path

end Whatwg.Svg.Value
