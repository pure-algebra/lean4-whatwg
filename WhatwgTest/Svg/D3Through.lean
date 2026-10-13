import Whatwg.Svg.Geometry.Through
import WhatwgTest.Svg.D3Shape

/-!
# WhatwgTest.Svg.D3Through

The area tests of d3-shape for its monotone curves, run against the area of a generator
(`Curve.Through.areaCubics` of `Whatwg/Svg/Geometry/Through.lean`).

`WhatwgTest/Svg/D3Monotone.lean` converts the same ten assertions, and puts each area together
in the test: the curve of the top, a straight line, the curve of the base taken backwards. Here
no line of the test knows how an area is made. The kit's outline is one call,
`Curve.Through.monotoneX.areaCubics data (base data)`, and it is compared with d3's vector.

**Source.** https://github.com/d3/d3-shape, the files `test/curve/monotoneX-test.js` and
`test/curve/monotoneY-test.js` at commit `a82254af78f0` of `main`. Copyright 2010-2022 Mike
Bostock, ISC licence. Every expected path below is one of d3's test vectors, typed as the test
has it.

## How a case is compared

d3's vector is read as an outline (`outline`): an `M` sets the pen, an `L` is the straight
segment from the pen (`Cubic.line`), a `C` is the cubic from the pen with its two control points
and its end, and a `Z` draws nothing. The kit's outline and d3's are the same when they have as
many pieces and each piece has the same four points, every coordinate written at six places
(`sameOutline`, with `point` of `WhatwgTest/Svg/D3Shape.lean`).

This compares the curves and not the letters. d3 writes a level piece of a monotone curve as a
`C` whose control points stand at the thirds of the piece, and the straight segment between two
points as an `L`. Both are the segment `Cubic.line` of the kit, so the comparison holds them
equal, as it should: they draw the same points. `WhatwgTest/Svg/D3Monotone.lean` compares the
letters of the lines.

## What was found

All ten area assertions of the two files hold: 8 compare with d3's vector, and 2 are d3's `null`
for no point, which is no piece here. The area of one point is the straight segment from the
point to its base (`M0,1L0,0Z`), in d3 and in the kit. Two more guards are controls of the
comparison, and four say what the generator of a form of `Curve` gives.
-/

namespace WhatwgTest.Svg.D3Through

open Whatwg.Svg.Value
open WhatwgTest.Svg.D3Shape (point value)

/-! ## Reading d3's vector as an outline -/

/-- The path cut before each of its letters. -/
def cut : List Char → List (List Char)
  | [] => []
  | c :: rest =>
    match cut rest with
    | [] => [[c]]
    | g :: gs => if (g.head?.map Char.isAlpha).getD false then [c] :: g :: gs else (c :: g) :: gs

/-- The runs of a text between its commas and its spaces. -/
def fields : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
    match fields rest with
    | [] => [[c]]
    | f :: fs => if c == ',' || c == ' ' then [] :: f :: fs else (c :: f) :: fs

/-- The pieces that the commands draw from the point `pen`: a straight segment for an `L`, a
cubic for a `C`, and nothing for an `M` or a `Z`. -/
def pieces (pen : Vec) : List (List Char) → List Cubic
  | [] => []
  | g :: gs =>
    match g.head?, ((fields g.tail).filter fun f => !f.isEmpty).map value with
    | some 'M', [x, y] => pieces ⟨x, y⟩ gs
    | some 'L', [x, y] => Cubic.line pen ⟨x, y⟩ :: pieces ⟨x, y⟩ gs
    | some 'C', [x1, y1, x2, y2, x, y] => ⟨pen, ⟨x1, y1⟩, ⟨x2, y2⟩, ⟨x, y⟩⟩ :: pieces ⟨x, y⟩ gs
    | _, _ => pieces pen gs

/-- A path of d3 as the pieces it draws. -/
def outline (path : String) : List Cubic := pieces ⟨0, 0⟩ (cut path.toList)

/-- The four points of a piece, each coordinate at six places. -/
def spell (c : Cubic) : String :=
  point c.p0 ++ " " ++ point c.p1 ++ " " ++ point c.p2 ++ " " ++ point c.p3

/-- The kit's pieces are those of d3's path: as many, and each with the same four points at six
places. -/
def sameOutline (kit : List Cubic) (path : String) : Bool :=
  kit.map spell == (outline path).map spell

/-- The base of d3's area with its own `y0` of zero: the points at `y = 0`. -/
def base (data : List Vec) : List Vec := data.map fun p => ⟨p.x, 0⟩

/-- d3's `reflect`. -/
def reflect (data : List Vec) : List Vec := data.map Monotone.swap

/-- d3's `area().curve(curveMonotoneX)(data)`: one call of the kit. -/
def areaX (data : List Vec) : List Cubic := Curve.Through.monotoneX.areaCubics data (base data)

/-- d3's `area().curve(curveMonotoneY)(data)`: one call of the kit. -/
def areaY (data : List Vec) : List Cubic := Curve.Through.monotoneY.areaCubics data (base data)

/-! ## Controls of the comparison -/

-- The reading of a path: an `L` is a straight segment and a `C` a cubic, from where the pen is.
#guard outline "M0,1L1,3C1.5,3,2,0.25,3,-1Z" ==
  [Cubic.line ⟨0, 1⟩ ⟨1, 3⟩, ⟨⟨1, 3⟩, ⟨3 / 2, 3⟩, ⟨2, 1 / 4⟩, ⟨3, -1⟩⟩]

-- The comparison tells two curves apart: the area under the cardinal spline through the same
-- three points is not d3's monotone area.
#guard !sameOutline ((Curve.toThrough .catmullRom).areaCubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]
    (base [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]))
  "M0,1C0.333333,2,0.666667,3,1,3C1.333333,3,1.666667,2,2,1L2,0C1.666667,0,1.333333,0,1,0C0.666667,0,0.333333,0,0,0Z"

/-! ## monotoneX-test.js -/

-- area.curve(curveMonotoneX)([])
#guard areaX [] == []
-- area.curve(curveMonotoneX)([[0, 1]])
#guard sameOutline (areaX [⟨0, 1⟩]) "M0,1L0,0Z"
-- area.curve(curveMonotoneX)([[0, 1], [1, 3]])
#guard sameOutline (areaX [⟨0, 1⟩, ⟨1, 3⟩]) "M0,1L1,3L1,0L0,0Z"
-- area.curve(curveMonotoneX)([[0, 1], [1, 3], [2, 1]])
#guard sameOutline (areaX [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩])
  "M0,1C0.333333,2,0.666667,3,1,3C1.333333,3,1.666667,2,2,1L2,0C1.666667,0,1.333333,0,1,0C0.666667,0,0.333333,0,0,0Z"
-- area.curve(curveMonotoneX)([[0, 1], [1, 3], [2, 1], [3, 3]])
#guard sameOutline (areaX [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])
  "M0,1C0.333333,2,0.666667,3,1,3C1.333333,3,1.666667,1,2,1C2.333333,1,2.666667,2,3,3L3,0C2.666667,0,2.333333,0,2,0C1.666667,0,1.333333,0,1,0C0.666667,0,0.333333,0,0,0Z"

/-! ## monotoneY-test.js -/

-- area.curve(curveMonotoneY)([].map(reflect))
#guard areaY (reflect []) == []
-- area.curve(curveMonotoneY)([[0, 1]].map(reflect))
#guard sameOutline (areaY (reflect [⟨0, 1⟩])) "M1,0L1,0Z"
-- area.curve(curveMonotoneY)([[0, 1], [1, 3]].map(reflect))
#guard sameOutline (areaY (reflect [⟨0, 1⟩, ⟨1, 3⟩])) "M1,0L3,1L3,0L1,0Z"
-- area.curve(curveMonotoneY)([[0, 1], [1, 3], [2, 1]].map(reflect))
#guard sameOutline (areaY (reflect [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]))
  "M1,0C2,0.333333,3,0.666667,3,1C3,1.333333,2,1.666667,1,2L1,0C1,0,3,0,3,0C3,0,1,0,1,0Z"
-- area.curve(curveMonotoneY)([[0, 1], [1, 3], [2, 1], [3, 3]].map(reflect))
#guard sameOutline (areaY (reflect [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]))
  "M1,0C2,0.333333,3,0.666667,3,1C3,1.333333,1,1.666667,1,2C1,2.333333,2,2.666667,3,3L3,0C3,0,1,0,1,0C1,0,3,0,3,0C3,0,1,0,1,0Z"

/-! ## The generator of a form of `Curve` -/

-- The area of a form is the area of its generator, back along the flipped form: the two give
-- the same pieces for a form whose steps turn round on the way back.
#guard Curve.stepBefore.areaCubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩] (base [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) ==
  (Curve.toThrough .stepBefore).areaCubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩] (base [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩])
    (Curve.toThrough .stepAfter)
-- A control of the way back: with the form itself on the way back the outline is another one.
#guard Curve.stepBefore.areaCubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩] (base [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) !=
  (Curve.toThrough .stepBefore).areaCubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩] (base [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩])

-- `Curve.Through.under` at a form: the bump along `y` is the bump along `x` under the exchange
-- of the two axes, on these points.
#guard (Curve.toThrough (.bumpY (1 / 2))).cubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩] ==
  ((Curve.toThrough (.bumpX (1 / 2))).under Monotone.swap (fun _ => rfl) (fun _ _ => rfl)).cubics
    [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]

-- A control of what a generator does not owe: two points that are one point give the monotone
-- curve no piece, and a form of `Curve` a piece of no length.
#guard Curve.Through.monotoneX.cubics [⟨1, 1⟩, ⟨1, 1⟩] == [] &&
  (Curve.toThrough .linear).cubics [⟨1, 1⟩, ⟨1, 1⟩] == [Cubic.line ⟨1, 1⟩ ⟨1, 1⟩]

end WhatwgTest.Svg.D3Through
