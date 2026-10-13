import Whatwg.Svg.Geometry.Shape

/-!
# WhatwgTest.Svg.D3Shape

The curve tests of d3-shape, converted and run against the curves of
`Whatwg/Svg/Geometry/Shape.lean`. Those curves are d3's algorithms. This module checks them with
d3's own test vectors, by running, and reads nothing of d3's source.

**Source.** https://github.com/d3/d3-shape, the files `test/curve/*-test.js` and
`test/asserts.js` at commit `a82254af78f08799c71d7ab25df557c4872a3c51` of `main`. Copyright
2010-2022 Mike Bostock, ISC licence. Every expected path below that is marked as d3's is one of
d3's test vectors, typed as the test has it.

## How a case is converted

There is one `#guard` for one assertion of d3, under the name of its test file, with d3's call
in the comment above it.

- A curve of d3 is the form of that name: `curveLinear` is `Curve.linear`, `curveStep` is
  `Curve.stepX`, `curveStepBefore` is `Curve.stepBefore`, `curveStepAfter` is
  `Curve.stepAfter`, `curveBumpX` and `curveBumpY` are `Curve.bumpX` and `Curve.bumpY` at their
  own reach of a half, `curveBasis` is `Curve.basis`, `curveCardinal` is `Curve.cardinal` at its
  own tension of zero, `curveCardinal.tension(t)` is `Curve.cardinal t`, and
  `curveCatmullRom.alpha(0)` is `Curve.catmullRom`.
- `line().curve(c)(data)` is `Curve.cubics`. For d3's `Open` curve of that name it is
  `Curve.cubicsOpen`, and for its `Closed` curve `Curve.cubicsClosed`.
- `area().curve(c)(data)` has d3's own `y0` of zero, so the base of the area is its points at
  `y = 0` (`base`) and its outline is `Curve.areaCubics` (`area`). The kit has an area for
  `Curve.cubics` alone, so for d3's `Open` and `Closed` curves this module puts the two curves
  together as d3 does (`areaOpen`, `areaClosed`).
- The segments are written as d3 writes a path (`d3`, `d3Closed`): d3 computes in floating
  point and the kit in `Rat`, and each number of the kit is rounded once, where it is written.
- `assert.strictEqual(path, null)`: d3 gives `null` for a path of no command. The guard compares
  with the empty text.
- `assertPathEqual(path, expected)` is `pathEqual`. d3's `assertPathEqual` writes every number
  of both paths again and compares the texts. At this commit it writes a number at three places,
  and a number within a millionth of a whole number as that whole number. `pathEqual` writes a
  number at six places, the places of d3's vectors, which is the finer comparison: two paths
  that it holds equal have the same numbers, so d3's `assertPathEqual` holds them equal too.
- `assert.strictEqual(a, b)` of two paths is `==` of two texts.

## What was found

d3's `test/curve/` has 237 assertions, and 130 of them are converted here. Each guard is of one
of three kinds.

**Kind 1, 82 guards: the kit's text is d3's.** 42 compare with d3's vector, 34 with the empty
text for d3's `null`, and 6 compare two texts of the kit where d3 compares two of its paths.

**Kind 2, 46 guards: the same outline, written with other commands.** The comment above the
guard names the difference and gives d3's vector where the guard does not compare with it.

- *dot*, 10 guards. For one point, and for the three points of an open spline, d3 writes a
  closed subpath of no length, such as `M0,1Z`. The kit has no segment there and writes nothing.
  `Whatwg/Svg/Geometry/Shape.lean` says so.
- *no length*, 5 guards. A closed curve through one point is a dot in d3 and in the kit. d3
  writes `M0,1Z`, and the kit's ring is one straight segment of no length, `M0,1L0,1Z`.
- *start*, 15 guards. d3 starts a closed spline at its second point, or near it for a basis
  spline, and the kit at its first. The guard takes the kit's ring from its second segment on
  (`fromSecond`), and in 12 of the 15 the text is then d3's vector, which the guard compares
  with. The other 3 are also *flat*.
- *flat*, 17 guards with those 3. d3 writes every piece of a spline or of a bump as a `C`, also
  where its four points are on one line in order, as they are along the base of an area at
  `y = 0`. The writer here asks the segment (`Cubic.isStraight`) and writes an `L`. Each `C` of
  d3 that is an `L` here has its two control points on `y = 0` between its ends.
- *collinear*, 2 guards. `Curve.stepX` passes through every point, so it writes two `L` along
  one line, to the point and on, where `curveStep` writes one.

**Kind 3, 2 guards, marked `DIFFERS`: another outline.** `area().curve(curveBasisOpen)` and
`area().curve(curveCardinalOpen)` of three points. d3 has one point for each of the two open
curves and joins them: a straight line from the top to the base and back, such as `M1,3L1,0Z`,
which holds no area. `Curve.cubicsOpen` has no segment for three points, so `areaOpen` has no
point to join and writes nothing. This is the *dot* again, seen through an area.

In all 130, every coordinate that the kit's text and d3's vector both write is the same number
at six places.

One difference is not seen at the level of segments: d3 ends a closed spline of three points or
more where it started and writes no `Z`, and `Shape.loop` writes one.

## Not covered

The 42 assertions of `monotoneX-test.js` and `monotoneY-test.js` are converted in
`WhatwgTest/Svg/D3Monotone.lean`. 65 assertions of `test/curve/` have no form in the kit and
are left out:

- `curveNatural` and `curveBundle`: the 13 assertions of `natural-test.js` and
  `bundle-test.js`;
- `curveCatmullRom` with a positive `alpha`, which is also its own `alpha` of a half: 46
  assertions of `catmullRom-test.js`, `catmullRomClosed-test.js` and `catmullRomOpen-test.js`;
- a tension given as the string `"0.5"`: 6 assertions of the three cardinal files. A tension
  here is a `Rat`.

`curveBumpRadial` and the radial generators have no test under `test/curve/`.
-/

namespace WhatwgTest.Svg.D3Shape

open Whatwg.Svg.Value

/-! ## Writing segments as d3 writes a path -/

/-- A number as d3's vectors write one: at six places at most (`Decimal.ofRat`, a half going
up), with no zero at the end of its fraction and no exponent. The kit's own spelling of a
decimal writes a millionth as `1e-6`, so the digits are written here from the mantissa and the
exponent. -/
def num (q : Rat) : String :=
  let d := Decimal.ofRat q 6
  let places := (-d.exponent).toNat
  let digits := toString (d.mantissa.natAbs % 10 ^ places)
  (if d.mantissa < 0 then "-" else "") ++ toString (d.mantissa.natAbs / 10 ^ places) ++
    (if places = 0 then "" else ("." : String).pushn '0' (places - digits.length) ++ digits)

/-- A point as d3 writes one. -/
def point (p : Vec) : String := num p.x ++ "," ++ num p.y

/-- The segments as d3 writes an open path: `M` at the start of the first segment, and again
wherever a segment does not start at `pen`, the end of the one before it; `L` for a segment that
draws a straight line (`Cubic.isStraight`) and `C` for any other. A straight segment of no
length is written, as d3 writes one. No segment is the empty text, which is d3's `null`. -/
def d3 (segments : List Cubic) (pen : Option Vec := none) : String :=
  match segments with
  | [] => ""
  | c :: rest =>
    (if pen = some c.p0 then "" else "M" ++ point c.p0) ++
      (if c.isStraight then "L" ++ point c.p3
        else "C" ++ point c.p1 ++ "," ++ point c.p2 ++ "," ++ point c.p3) ++
      d3 rest (some c.p3)

/-- The segments as d3 writes a closed path, with a `Z`. A last straight segment back to the
start is left to the `Z`, which draws that line: the kit's own writer leaves it so
(`Pen.withoutReturn`). -/
def d3Closed (segments : List Cubic) : String :=
  if segments.isEmpty then "" else d3 (Pen.withoutReturn segments) ++ "Z"

/-! ## Comparing as d3's test compares -/

/-- The number that a run of digits writes, with a sign before it or none, and a point in it or
none. -/
def value (token : List Char) : Rat :=
  let digits : Nat := (token.filter Char.isDigit).foldl (fun n c => 10 * n + (c.toNat - 48)) 0
  (if token.head? = some '-' then -1 else 1) * (digits : Rat) /
    (10 : Rat) ^ ((token.dropWhile (· != '.')).length - 1)

/-- A path with every number in it written again by `num`, so that `0.500000` is `0.5`. `token`
holds the number that is being read. No vector of the converted files has an exponent, and none
is read here. -/
def respell (text : List Char) (token : List Char := []) : String :=
  match text with
  | [] => if token.isEmpty then "" else num (value token)
  | c :: rest =>
    if c.isDigit || c == '.' || c == '-' then respell rest (token ++ [c])
    else (if token.isEmpty then "" else num (value token)) ++ c.toString ++ respell rest

/-- d3's `assertPathEqual`: the two paths are one text when every number of both is written
again. -/
def pathEqual (actual expected : String) : Bool := respell actual.toList == respell expected.toList

/-! ## d3's area, and where d3 starts a ring -/

/-- The base of d3's area with its own `y0` of zero: the points at `y = 0`, in the order of the
top. -/
def base (points : List Vec) : List Vec := points.map fun p => ⟨p.x, 0⟩

/-- d3's `area().curve(c)(data)`: the kit's outline between the points and their base. -/
def area (c : Curve) (points : List Vec) : List Cubic := c.areaCubics points (base points)

/-- d3's area for an `Open` curve: the open curve of the top, straight to the open curve of the
base taken backwards. Where either has no segment there is no point to join, and no outline. -/
def areaOpen (c : Curve) (points : List Vec) : List Cubic :=
  match (c.cubicsOpen points).getLast?, (c.flip.cubicsOpen (base points).reverse).head? with
  | some top, some back =>
    c.cubicsOpen points ++ [Cubic.line top.p3 back.p0] ++ c.flip.cubicsOpen (base points).reverse
  | _, _ => []

/-- d3's area for a `Closed` curve: two rings, the closed curve of the top and that of the base
taken backwards, each written by `write`. -/
def areaClosed (write : List Cubic → String) (c : Curve) (points : List Vec) : String :=
  write (c.cubicsClosed points) ++ write (c.flip.cubicsClosed (base points).reverse)

/-- A ring from its second segment on: the same closed outline from another start. d3 starts a
closed spline there. -/
def fromSecond (ring : List Cubic) : List Cubic := ring.rotateLeft 1

/-! ## basis-test.js -/

-- line.curve(curveBasis)([])
#guard d3 (Curve.basis.cubics []) == ""
-- line.curve(curveBasis)([[0, 1]])
-- Kind 2 (dot): d3 has "M0,1Z".
#guard d3 (Curve.basis.cubics [⟨0, 1⟩]) == ""
-- line.curve(curveBasis)([[0, 1], [1, 3]])
#guard pathEqual (d3 (Curve.basis.cubics [⟨0, 1⟩, ⟨1, 3⟩])) "M0,1L1,3"
-- line.curve(curveBasis)([[0, 1], [1, 3], [2, 1]])
#guard pathEqual (d3 (Curve.basis.cubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]))
  "M0,1L0.166667,1.333333C0.333333,1.666667,0.666667,2.333333,1,2.333333C1.333333,2.333333,1.666667,1.666667,1.833333,1.333333L2,1"
-- area.curve(curveBasis)([])
#guard d3Closed (area .basis []) == ""
-- area.curve(curveBasis)([[0, 1]])
#guard pathEqual (d3Closed (area .basis [⟨0, 1⟩])) "M0,1L0,0Z"
-- area.curve(curveBasis)([[0, 1], [1, 3]])
#guard pathEqual (d3Closed (area .basis [⟨0, 1⟩, ⟨1, 3⟩])) "M0,1L1,3L1,0L0,0Z"
-- area.curve(curveBasis)([[0, 1], [1, 3], [2, 1]])
-- Kind 2 (flat): d3 has
-- "M0,1L0.166667,1.333333C0.333333,1.666667,0.666667,2.333333,1,2.333333C1.333333,2.333333,1.666667,1.666667,1.833333,1.333333L2,1L2,0L1.833333,0C1.666667,0,1.333333,0,1,0C0.666667,0,0.333333,0,0.166667,0L0,0Z"
#guard d3Closed (area .basis [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) ==
  "M0,1L0.166667,1.333333C0.333333,1.666667,0.666667,2.333333,1,2.333333C1.333333,2.333333,1.666667,1.666667,1.833333,1.333333L2,1L2,0L1.833333,0L1,0L0.166667,0L0,0Z"

/-! ## basisClosed-test.js -/

-- line.curve(curveBasisClosed)([])
#guard d3Closed (Curve.basis.cubicsClosed []) == ""
-- line.curve(curveBasisClosed)([[0, 0]])
-- Kind 2 (no length): d3 has "M0,0Z".
#guard d3Closed (Curve.basis.cubicsClosed [⟨0, 0⟩]) == "M0,0L0,0Z"
-- line.curve(curveBasisClosed)([[0, 0], [0, 10]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual (d3Closed (fromSecond (Curve.basis.cubicsClosed [⟨0, 0⟩, ⟨0, 10⟩])))
  "M0,6.666667L0,3.333333Z"
-- line.curve(curveBasisClosed)([[0, 0], [0, 10], [10, 10]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual (d3 (fromSecond (Curve.basis.cubicsClosed [⟨0, 0⟩, ⟨0, 10⟩, ⟨10, 10⟩])))
  "M1.666667,8.333333C3.333333,10,6.666667,10,6.666667,8.333333C6.666667,6.666667,3.333333,3.333333,1.666667,3.333333C0,3.333333,0,6.666667,1.666667,8.333333"
-- line.curve(curveBasisClosed)([[0, 0], [0, 10], [10, 10], [10, 0]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual
  (d3 (fromSecond (Curve.basis.cubicsClosed [⟨0, 0⟩, ⟨0, 10⟩, ⟨10, 10⟩, ⟨10, 0⟩])))
  "M1.666667,8.333333C3.333333,10,6.666667,10,8.333333,8.333333C10,6.666667,10,3.333333,8.333333,1.666667C6.666667,0,3.333333,0,1.666667,1.666667C0,3.333333,0,6.666667,1.666667,8.333333"
-- line.curve(curveBasisClosed)([[0, 0], [0, 10], [10, 10], [10, 0], [0, 0]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual
  (d3 (fromSecond (Curve.basis.cubicsClosed [⟨0, 0⟩, ⟨0, 10⟩, ⟨10, 10⟩, ⟨10, 0⟩, ⟨0, 0⟩])))
  "M1.666667,8.333333C3.333333,10,6.666667,10,8.333333,8.333333C10,6.666667,10,3.333333,8.333333,1.666667C6.666667,0,3.333333,0,1.666667,0C0,0,0,0,0,1.666667C0,3.333333,0,6.666667,1.666667,8.333333"

/-! ## basisOpen-test.js -/

-- line.curve(curveBasisOpen)([])
#guard d3 (Curve.basis.cubicsOpen []) == ""
-- line.curve(curveBasisOpen)([[0, 0]])
#guard d3 (Curve.basis.cubicsOpen [⟨0, 0⟩]) == ""
-- line.curve(curveBasisOpen)([[0, 0], [0, 10]])
#guard d3 (Curve.basis.cubicsOpen [⟨0, 0⟩, ⟨0, 10⟩]) == ""
-- line.curve(curveBasisOpen)([[0, 0], [0, 10], [10, 10]])
-- Kind 2 (dot): d3 has "M1.666667,8.333333Z".
#guard d3 (Curve.basis.cubicsOpen [⟨0, 0⟩, ⟨0, 10⟩, ⟨10, 10⟩]) == ""
-- line.curve(curveBasisOpen)([[0, 0], [0, 10], [10, 10], [10, 0]])
#guard pathEqual (d3 (Curve.basis.cubicsOpen [⟨0, 0⟩, ⟨0, 10⟩, ⟨10, 10⟩, ⟨10, 0⟩]))
  "M1.666667,8.333333C3.333333,10,6.666667,10,8.333333,8.333333"
-- line.curve(curveBasisOpen)([[0, 0], [0, 10], [10, 10], [10, 0], [0, 0]])
#guard pathEqual (d3 (Curve.basis.cubicsOpen [⟨0, 0⟩, ⟨0, 10⟩, ⟨10, 10⟩, ⟨10, 0⟩, ⟨0, 0⟩]))
  "M1.666667,8.333333C3.333333,10,6.666667,10,8.333333,8.333333C10,6.666667,10,3.333333,8.333333,1.666667"
-- area.curve(curveBasisOpen)([])
#guard d3Closed (areaOpen .basis []) == ""
-- area.curve(curveBasisOpen)([[0, 1]])
#guard d3Closed (areaOpen .basis [⟨0, 1⟩]) == ""
-- area.curve(curveBasisOpen)([[0, 1], [1, 3]])
#guard d3Closed (areaOpen .basis [⟨0, 1⟩, ⟨1, 3⟩]) == ""
-- area.curve(curveBasisOpen)([[0, 0], [0, 10], [10, 10]])
-- DIFFERS: d3 has "M1.666667,8.333333L1.666667,0Z", the straight line from (1.666667, 8.333333)
-- to (1.666667, 0) and back, which holds no area. The kit has no segment for either open curve
-- of three points, and nothing is written.
#guard d3Closed (areaOpen .basis [⟨0, 0⟩, ⟨0, 10⟩, ⟨10, 10⟩]) == ""
-- area.curve(curveBasisOpen)([[0, 0], [0, 10], [10, 10], [10, 0]])
-- Kind 2 (flat): d3 has
-- "M1.666667,8.333333C3.333333,10,6.666667,10,8.333333,8.333333L8.333333,0C6.666667,0,3.333333,0,1.666667,0Z"
#guard d3Closed (areaOpen .basis [⟨0, 0⟩, ⟨0, 10⟩, ⟨10, 10⟩, ⟨10, 0⟩]) ==
  "M1.666667,8.333333C3.333333,10,6.666667,10,8.333333,8.333333L8.333333,0L1.666667,0Z"
-- area.curve(curveBasisOpen)([[0, 0], [0, 10], [10, 10], [10, 0], [0, 0]])
-- Kind 2 (flat): d3 has
-- "M1.666667,8.333333C3.333333,10,6.666667,10,8.333333,8.333333C10,6.666667,10,3.333333,8.333333,1.666667L8.333333,0C10,0,10,0,8.333333,0C6.666667,0,3.333333,0,1.666667,0Z"
-- The first `C` of the base runs past its end to (10, 0) and back, and is a `C` here too.
#guard d3Closed (areaOpen .basis [⟨0, 0⟩, ⟨0, 10⟩, ⟨10, 10⟩, ⟨10, 0⟩, ⟨0, 0⟩]) ==
  "M1.666667,8.333333C3.333333,10,6.666667,10,8.333333,8.333333C10,6.666667,10,3.333333,8.333333,1.666667L8.333333,0C10,0,10,0,8.333333,0L1.666667,0Z"

/-! ## bumpX-test.js -/

-- line.curve(curveBumpX)([])
#guard d3 (Curve.bumpX.cubics []) == ""
-- line.curve(curveBumpX)([[0, 1]])
-- Kind 2 (dot): d3 has "M0,1Z".
#guard d3 (Curve.bumpX.cubics [⟨0, 1⟩]) == ""
-- line.curve(curveBumpX)([[0, 1], [1, 3]])
#guard pathEqual (d3 (Curve.bumpX.cubics [⟨0, 1⟩, ⟨1, 3⟩])) "M0,1C0.500000,1,0.500000,3,1,3"
-- line.curve(curveBumpX)([[0, 1], [1, 3], [2, 1]])
#guard pathEqual (d3 (Curve.bumpX.cubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]))
  "M0,1C0.500000,1,0.500000,3,1,3C1.500000,3,1.500000,1,2,1"
-- area.curve(curveBumpX)([])
#guard d3Closed (area .bumpX []) == ""
-- area.curve(curveBumpX)([[0, 1]])
#guard pathEqual (d3Closed (area .bumpX [⟨0, 1⟩])) "M0,1L0,0Z"
-- area.curve(curveBumpX)([[0, 1], [1, 3]])
-- Kind 2 (flat): d3 has "M0,1C0.500000,1,0.500000,3,1,3L1,0C0.500000,0,0.500000,0,0,0Z".
#guard d3Closed (area .bumpX [⟨0, 1⟩, ⟨1, 3⟩]) == "M0,1C0.5,1,0.5,3,1,3L1,0L0,0Z"
-- area.curve(curveBumpX)([[0, 1], [1, 3], [2, 1]])
-- Kind 2 (flat): d3 has
-- "M0,1C0.500000,1,0.500000,3,1,3C1.500000,3,1.500000,1,2,1L2,0C1.500000,0,1.500000,0,1,0C0.500000,0,0.500000,0,0,0Z"
#guard d3Closed (area .bumpX [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) ==
  "M0,1C0.5,1,0.5,3,1,3C1.5,3,1.5,1,2,1L2,0L1,0L0,0Z"

/-! ## bumpY-test.js -/

-- line.curve(curveBumpY)([])
#guard d3 (Curve.bumpY.cubics []) == ""
-- line.curve(curveBumpY)([[0, 1]])
-- Kind 2 (dot): d3 has "M0,1Z".
#guard d3 (Curve.bumpY.cubics [⟨0, 1⟩]) == ""
-- line.curve(curveBumpY)([[0, 1], [1, 3]])
#guard pathEqual (d3 (Curve.bumpY.cubics [⟨0, 1⟩, ⟨1, 3⟩])) "M0,1C0,2,1,2,1,3"
-- line.curve(curveBumpY)([[0, 1], [1, 3], [2, 1]])
#guard pathEqual (d3 (Curve.bumpY.cubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩])) "M0,1C0,2,1,2,1,3C1,2,2,2,2,1"
-- area.curve(curveBumpY)([])
#guard d3Closed (area .bumpY []) == ""
-- area.curve(curveBumpY)([[0, 1]])
#guard pathEqual (d3Closed (area .bumpY [⟨0, 1⟩])) "M0,1L0,0Z"
-- area.curve(curveBumpY)([[0, 1], [1, 3]])
-- Kind 2 (flat): d3 has "M0,1C0,2,1,2,1,3L1,0C1,0,0,0,0,0Z".
#guard d3Closed (area .bumpY [⟨0, 1⟩, ⟨1, 3⟩]) == "M0,1C0,2,1,2,1,3L1,0L0,0Z"
-- area.curve(curveBumpY)([[0, 1], [1, 3], [2, 1]])
-- Kind 2 (flat): d3 has "M0,1C0,2,1,2,1,3C1,2,2,2,2,1L2,0C2,0,1,0,1,0C1,0,0,0,0,0Z".
#guard d3Closed (area .bumpY [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) ==
  "M0,1C0,2,1,2,1,3C1,2,2,2,2,1L2,0L1,0L0,0Z"

/-! ## cardinal-test.js -/

-- line.curve(curveCardinal)([])
#guard d3 (Curve.cardinal.cubics []) == ""
-- line.curve(curveCardinal)([[0, 1]])
-- Kind 2 (dot): d3 has "M0,1Z".
#guard d3 (Curve.cardinal.cubics [⟨0, 1⟩]) == ""
-- line.curve(curveCardinal)([[0, 1], [1, 3]])
#guard pathEqual (d3 (Curve.cardinal.cubics [⟨0, 1⟩, ⟨1, 3⟩])) "M0,1L1,3"
-- line.curve(curveCardinal)([[0, 1], [1, 3], [2, 1]])
#guard pathEqual (d3 (Curve.cardinal.cubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]))
  "M0,1C0,1,0.666667,3,1,3C1.333333,3,2,1,2,1"
-- line.curve(curveCardinal)([[0, 1], [1, 3], [2, 1], [3, 3]])
#guard pathEqual (d3 (Curve.cardinal.cubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]))
  "M0,1C0,1,0.666667,3,1,3C1.333333,3,1.666667,1,2,1C2.333333,1,3,3,3,3"
-- line.curve(curveCardinal)(data) is line.curve(curveCardinal.tension(0))(data),
-- for data = [[0, 1], [1, 3], [2, 1], [3, 3]]
#guard d3 (Curve.cardinal.cubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) ==
  d3 ((Curve.cardinal 0).cubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])
-- line.curve(curveCardinal.tension(0.5))([[0, 1], [1, 3], [2, 1], [3, 3]])
#guard pathEqual (d3 ((Curve.cardinal 0.5).cubics [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]))
  "M0,1C0,1,0.833333,3,1,3C1.166667,3,1.833333,1,2,1C2.166667,1,3,3,3,3"
-- area.curve(curveCardinal)([])
#guard d3Closed (area .cardinal []) == ""
-- area.curve(curveCardinal)([[0, 1]])
#guard pathEqual (d3Closed (area .cardinal [⟨0, 1⟩])) "M0,1L0,0Z"
-- area.curve(curveCardinal)([[0, 1], [1, 3]])
#guard pathEqual (d3Closed (area .cardinal [⟨0, 1⟩, ⟨1, 3⟩])) "M0,1L1,3L1,0L0,0Z"
-- area.curve(curveCardinal)([[0, 1], [1, 3], [2, 1]])
-- Kind 2 (flat): d3 has
-- "M0,1C0,1,0.666667,3,1,3C1.333333,3,2,1,2,1L2,0C2,0,1.333333,0,1,0C0.666667,0,0,0,0,0Z"
#guard d3Closed (area .cardinal [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) ==
  "M0,1C0,1,0.666667,3,1,3C1.333333,3,2,1,2,1L2,0L1,0L0,0Z"
-- area.curve(curveCardinal)([[0, 1], [1, 3], [2, 1], [3, 3]])
-- Kind 2 (flat): d3 has
-- "M0,1C0,1,0.666667,3,1,3C1.333333,3,1.666667,1,2,1C2.333333,1,3,3,3,3L3,0C3,0,2.333333,0,2,0C1.666667,0,1.333333,0,1,0C0.666667,0,0,0,0,0Z"
#guard d3Closed (area .cardinal [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) ==
  "M0,1C0,1,0.666667,3,1,3C1.333333,3,1.666667,1,2,1C2.333333,1,3,3,3,3L3,0L2,0L1,0L0,0Z"
-- area.curve(curveCardinal)(data) is area.curve(curveCardinal.tension(0))(data),
-- for data = [[0, 1], [1, 3], [2, 1], [3, 3]]
#guard d3Closed (area .cardinal [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) ==
  d3Closed (area (.cardinal 0) [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])
-- area.curve(curveCardinal.tension(0.5))([[0, 1], [1, 3], [2, 1], [3, 3]])
-- Kind 2 (flat): d3 has
-- "M0,1C0,1,0.833333,3,1,3C1.166667,3,1.833333,1,2,1C2.166667,1,3,3,3,3L3,0C3,0,2.166667,0,2,0C1.833333,0,1.166667,0,1,0C0.833333,0,0,0,0,0Z"
#guard d3Closed (area (.cardinal 0.5) [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) ==
  "M0,1C0,1,0.833333,3,1,3C1.166667,3,1.833333,1,2,1C2.166667,1,3,3,3,3L3,0L2,0L1,0L0,0Z"

/-! ## cardinalClosed-test.js -/

-- line.curve(curveCardinalClosed)([])
#guard d3Closed (Curve.cardinal.cubicsClosed []) == ""
-- line.curve(curveCardinalClosed)([[0, 1]])
-- Kind 2 (no length): d3 has "M0,1Z".
#guard d3Closed (Curve.cardinal.cubicsClosed [⟨0, 1⟩]) == "M0,1L0,1Z"
-- line.curve(curveCardinalClosed)([[0, 1], [1, 3]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual (d3Closed (fromSecond (Curve.cardinal.cubicsClosed [⟨0, 1⟩, ⟨1, 3⟩])))
  "M1,3L0,1Z"
-- line.curve(curveCardinalClosed)([[0, 1], [1, 3], [2, 1]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual (d3 (fromSecond (Curve.cardinal.cubicsClosed [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩])))
  "M1,3C1.333333,3,2.166667,1.333333,2,1C1.833333,0.666667,0.166667,0.666667,0,1C-0.166667,1.333333,0.666667,3,1,3"
-- line.curve(curveCardinalClosed)([[0, 1], [1, 3], [2, 1], [3, 3]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual
  (d3 (fromSecond (Curve.cardinal.cubicsClosed [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])))
  "M1,3C1.333333,3,1.666667,1,2,1C2.333333,1,3.333333,3,3,3C2.666667,3,0.333333,1,0,1C-0.333333,1,0.666667,3,1,3"
-- line.curve(curveCardinalClosed)(data) is line.curve(curveCardinalClosed.tension(0))(data),
-- for data = [[0, 1], [1, 3], [2, 1], [3, 3]]
#guard d3 (Curve.cardinal.cubicsClosed [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) ==
  d3 ((Curve.cardinal 0).cubicsClosed [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])
-- line.curve(curveCardinalClosed.tension(0.5))([[0, 1], [1, 3], [2, 1], [3, 3]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual
  (d3 (fromSecond ((Curve.cardinal 0.5).cubicsClosed [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])))
  "M1,3C1.166667,3,1.833333,1,2,1C2.166667,1,3.166667,3,3,3C2.833333,3,0.166667,1,0,1C-0.166667,1,0.833333,3,1,3"
-- area.curve(curveCardinalClosed)([])
#guard areaClosed d3Closed .cardinal [] == ""
-- area.curve(curveCardinalClosed)([[0, 1]])
-- Kind 2 (no length): d3 has "M0,1ZM0,0Z".
#guard areaClosed d3Closed .cardinal [⟨0, 1⟩] == "M0,1L0,1ZM0,0L0,0Z"
-- area.curve(curveCardinalClosed)([[0, 1], [1, 3]])
-- Kind 2 (start): compared from the second segment of each ring of the kit.
#guard areaClosed (d3Closed ∘ fromSecond) .cardinal [⟨0, 1⟩, ⟨1, 3⟩] == "M1,3L0,1ZM0,0L1,0Z"
-- area.curve(curveCardinalClosed)([[0, 1], [1, 3], [2, 1]])
-- Kind 2 (start, flat): from the second segment of each ring of the kit. d3 has
-- "M1,3C1.333333,3,2.166667,1.333333,2,1C1.833333,0.666667,0.166667,0.666667,0,1C-0.166667,1.333333,0.666667,3,1,3M1,0C0.666667,0,-0.166667,0,0,0C0.166667,0,1.833333,0,2,0C2.166667,0,1.333333,0,1,0"
-- The two `C` of the base that run past an end are `C` here too.
#guard areaClosed (d3 ∘ fromSecond) .cardinal [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩] ==
  "M1,3C1.333333,3,2.166667,1.333333,2,1C1.833333,0.666667,0.166667,0.666667,0,1C-0.166667,1.333333,0.666667,3,1,3M1,0C0.666667,0,-0.166667,0,0,0L2,0C2.166667,0,1.333333,0,1,0"
-- area.curve(curveCardinalClosed)([[0, 1], [1, 3], [2, 1], [3, 3]])
-- Kind 2 (start, flat): from the second segment of each ring of the kit. d3 has
-- "M1,3C1.333333,3,1.666667,1,2,1C2.333333,1,3.333333,3,3,3C2.666667,3,0.333333,1,0,1C-0.333333,1,0.666667,3,1,3M2,0C1.666667,0,1.333333,0,1,0C0.666667,0,-0.333333,0,0,0C0.333333,0,2.666667,0,3,0C3.333333,0,2.333333,0,2,0"
#guard areaClosed (d3 ∘ fromSecond) .cardinal [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩] ==
  "M1,3C1.333333,3,1.666667,1,2,1C2.333333,1,3.333333,3,3,3C2.666667,3,0.333333,1,0,1C-0.333333,1,0.666667,3,1,3M2,0L1,0C0.666667,0,-0.333333,0,0,0L3,0C3.333333,0,2.333333,0,2,0"
-- area.curve(curveCardinalClosed)(data) is area.curve(curveCardinalClosed.tension(0))(data),
-- for data = [[0, 1], [1, 3], [2, 1], [3, 3]]
#guard areaClosed d3 .cardinal [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩] ==
  areaClosed d3 (.cardinal 0) [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]
-- area.curve(curveCardinalClosed.tension(0.5))([[0, 1], [1, 3], [2, 1], [3, 3]])
-- Kind 2 (start, flat): from the second segment of each ring of the kit. d3 has
-- "M1,3C1.166667,3,1.833333,1,2,1C2.166667,1,3.166667,3,3,3C2.833333,3,0.166667,1,0,1C-0.166667,1,0.833333,3,1,3M2,0C1.833333,0,1.166667,0,1,0C0.833333,0,-0.166667,0,0,0C0.166667,0,2.833333,0,3,0C3.166667,0,2.166667,0,2,0"
#guard areaClosed (d3 ∘ fromSecond) (.cardinal 0.5) [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩] ==
  "M1,3C1.166667,3,1.833333,1,2,1C2.166667,1,3.166667,3,3,3C2.833333,3,0.166667,1,0,1C-0.166667,1,0.833333,3,1,3M2,0L1,0C0.833333,0,-0.166667,0,0,0L3,0C3.166667,0,2.166667,0,2,0"

/-! ## cardinalOpen-test.js -/

-- line.curve(curveCardinalOpen)([])
#guard d3 (Curve.cardinal.cubicsOpen []) == ""
-- line.curve(curveCardinalOpen)([[0, 1]])
#guard d3 (Curve.cardinal.cubicsOpen [⟨0, 1⟩]) == ""
-- line.curve(curveCardinalOpen)([[0, 1], [1, 3]])
#guard d3 (Curve.cardinal.cubicsOpen [⟨0, 1⟩, ⟨1, 3⟩]) == ""
-- line.curve(curveCardinalOpen)([[0, 1], [1, 3], [2, 1]])
-- Kind 2 (dot): d3 has "M1,3Z".
#guard d3 (Curve.cardinal.cubicsOpen [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) == ""
-- line.curve(curveCardinalOpen)([[0, 1], [1, 3], [2, 1], [3, 3]])
#guard pathEqual (d3 (Curve.cardinal.cubicsOpen [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]))
  "M1,3C1.333333,3,1.666667,1,2,1"
-- line.curve(curveCardinalOpen)(data) is line.curve(curveCardinalOpen.tension(0))(data),
-- for data = [[0, 1], [1, 3], [2, 1], [3, 3]]
#guard d3 (Curve.cardinal.cubicsOpen [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) ==
  d3 ((Curve.cardinal 0).cubicsOpen [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])
-- line.curve(curveCardinalOpen.tension(0.5))([[0, 1], [1, 3], [2, 1], [3, 3]])
#guard pathEqual (d3 ((Curve.cardinal 0.5).cubicsOpen [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]))
  "M1,3C1.166667,3,1.833333,1,2,1"
-- area.curve(curveCardinalOpen)([])
#guard d3Closed (areaOpen .cardinal []) == ""
-- area.curve(curveCardinalOpen)([[0, 1]])
#guard d3Closed (areaOpen .cardinal [⟨0, 1⟩]) == ""
-- area.curve(curveCardinalOpen)([[0, 1], [1, 3]])
#guard d3Closed (areaOpen .cardinal [⟨0, 1⟩, ⟨1, 3⟩]) == ""
-- area.curve(curveCardinalOpen)([[0, 1], [1, 3], [2, 1]])
-- DIFFERS: d3 has "M1,3L1,0Z", the straight line from (1, 3) to (1, 0) and back, which holds no
-- area. The kit has no segment for either open curve of three points, and nothing is written.
#guard d3Closed (areaOpen .cardinal [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) == ""
-- area.curve(curveCardinalOpen)([[0, 1], [1, 3], [2, 1], [3, 3]])
-- Kind 2 (flat): d3 has "M1,3C1.333333,3,1.666667,1,2,1L2,0C1.666667,0,1.333333,0,1,0Z".
#guard d3Closed (areaOpen .cardinal [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) ==
  "M1,3C1.333333,3,1.666667,1,2,1L2,0L1,0Z"
-- area.curve(curveCardinalOpen)(data) is area.curve(curveCardinalOpen.tension(0))(data),
-- for data = [[0, 1], [1, 3], [2, 1], [3, 3]]
#guard d3Closed (areaOpen .cardinal [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) ==
  d3Closed (areaOpen (.cardinal 0) [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])
-- area.curve(curveCardinalOpen.tension(0.5))([[0, 1], [1, 3], [2, 1], [3, 3]])
-- Kind 2 (flat): d3 has "M1,3C1.166667,3,1.833333,1,2,1L2,0C1.833333,0,1.166667,0,1,0Z".
#guard d3Closed (areaOpen (.cardinal 0.5) [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) ==
  "M1,3C1.166667,3,1.833333,1,2,1L2,0L1,0Z"

/-! ## catmullRom-test.js

Only `curveCatmullRom.alpha(0)`, the uniform spline. -/

-- area.curve(curveCatmullRom.alpha(0))([])
#guard d3Closed (area Curve.catmullRom []) == ""
-- area.curve(curveCatmullRom.alpha(0))([[0, 1]])
#guard pathEqual (d3Closed (area Curve.catmullRom [⟨0, 1⟩])) "M0,1L0,0Z"
-- area.curve(curveCatmullRom.alpha(0))([[0, 1], [1, 3]])
#guard pathEqual (d3Closed (area Curve.catmullRom [⟨0, 1⟩, ⟨1, 3⟩])) "M0,1L1,3L1,0L0,0Z"
-- area.curve(curveCatmullRom.alpha(0))([[0, 1], [1, 3], [2, 1]])
-- Kind 2 (flat): d3 has
-- "M0,1C0,1,0.666667,3,1,3C1.333333,3,2,1,2,1L2,0C2,0,1.333333,0,1,0C0.666667,0,0,0,0,0Z"
#guard d3Closed (area Curve.catmullRom [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) ==
  "M0,1C0,1,0.666667,3,1,3C1.333333,3,2,1,2,1L2,0L1,0L0,0Z"
-- area.curve(curveCatmullRom.alpha(0))([[0, 1], [1, 3], [2, 1], [3, 3]])
-- Kind 2 (flat): d3 has
-- "M0,1C0,1,0.666667,3,1,3C1.333333,3,1.666667,1,2,1C2.333333,1,3,3,3,3L3,0C3,0,2.333333,0,2,0C1.666667,0,1.333333,0,1,0C0.666667,0,0,0,0,0Z"
#guard d3Closed (area Curve.catmullRom [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) ==
  "M0,1C0,1,0.666667,3,1,3C1.333333,3,1.666667,1,2,1C2.333333,1,3,3,3,3L3,0L2,0L1,0L0,0Z"

/-! ## catmullRomClosed-test.js

Only `curveCatmullRomClosed.alpha(0)`. -/

-- line.curve(curveCatmullRomClosed.alpha(0))([])
#guard d3Closed (Curve.catmullRom.cubicsClosed []) == ""
-- line.curve(curveCatmullRomClosed.alpha(0))([[0, 1]])
-- Kind 2 (no length): d3 has "M0,1Z".
#guard d3Closed (Curve.catmullRom.cubicsClosed [⟨0, 1⟩]) == "M0,1L0,1Z"
-- line.curve(curveCatmullRomClosed.alpha(0))([[0, 1], [1, 3]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual (d3Closed (fromSecond (Curve.catmullRom.cubicsClosed [⟨0, 1⟩, ⟨1, 3⟩])))
  "M1,3L0,1Z"
-- line.curve(curveCatmullRomClosed.alpha(0))([[0, 1], [1, 3], [2, 1]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual (d3 (fromSecond (Curve.catmullRom.cubicsClosed [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩])))
  "M1,3C1.333333,3,2.166667,1.333333,2,1C1.833333,0.666667,0.166667,0.666667,0,1C-0.166667,1.333333,0.666667,3,1,3"
-- line.curve(curveCatmullRomClosed.alpha(0))([[0, 1], [1, 3], [2, 1], [3, 3]])
-- Kind 2 (start): compared from the second segment of the kit's ring.
#guard pathEqual
  (d3 (fromSecond (Curve.catmullRom.cubicsClosed [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])))
  "M1,3C1.333333,3,1.666667,1,2,1C2.333333,1,3.333333,3,3,3C2.666667,3,0.333333,1,0,1C-0.333333,1,0.666667,3,1,3"

/-! ## linear-test.js -/

-- line.curve(curveLinear)([])
#guard d3 (Curve.linear.cubics []) == ""
-- line.curve(curveLinear)([[0, 1]])
-- Kind 2 (dot): d3 has "M0,1Z".
#guard d3 (Curve.linear.cubics [⟨0, 1⟩]) == ""
-- line.curve(curveLinear)([[0, 1], [2, 3]])
#guard pathEqual (d3 (Curve.linear.cubics [⟨0, 1⟩, ⟨2, 3⟩])) "M0,1L2,3"
-- line.curve(curveLinear)([[0, 1], [2, 3], [4, 5]])
#guard pathEqual (d3 (Curve.linear.cubics [⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩])) "M0,1L2,3L4,5"
-- area.curve(curveLinear)([])
#guard d3Closed (area .linear []) == ""
-- area.curve(curveLinear)([[0, 1]])
#guard pathEqual (d3Closed (area .linear [⟨0, 1⟩])) "M0,1L0,0Z"
-- area.curve(curveLinear)([[0, 1], [2, 3]])
#guard pathEqual (d3Closed (area .linear [⟨0, 1⟩, ⟨2, 3⟩])) "M0,1L2,3L2,0L0,0Z"
-- area.curve(curveLinear)([[0, 1], [2, 3], [4, 5]])
#guard pathEqual (d3Closed (area .linear [⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩])) "M0,1L2,3L4,5L4,0L2,0L0,0Z"

/-! ## linearClosed-test.js -/

-- line.curve(curveLinearClosed)([])
#guard d3Closed (Curve.linear.cubicsClosed []) == ""
-- line.curve(curveLinearClosed)([[0, 1]])
-- Kind 2 (no length): d3 has "M0,1Z".
#guard d3Closed (Curve.linear.cubicsClosed [⟨0, 1⟩]) == "M0,1L0,1Z"
-- line.curve(curveLinearClosed)([[0, 1], [2, 3]])
#guard pathEqual (d3Closed (Curve.linear.cubicsClosed [⟨0, 1⟩, ⟨2, 3⟩])) "M0,1L2,3Z"
-- line.curve(curveLinearClosed)([[0, 1], [2, 3], [4, 5]])
#guard pathEqual (d3Closed (Curve.linear.cubicsClosed [⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩])) "M0,1L2,3L4,5Z"

/-! ## step-test.js -/

-- line.curve(curveStep)([])
#guard d3 (Curve.stepX.cubics []) == ""
-- line.curve(curveStep)([[0, 1]])
-- Kind 2 (dot): d3 has "M0,1Z".
#guard d3 (Curve.stepX.cubics [⟨0, 1⟩]) == ""
-- line.curve(curveStep)([[0, 1], [2, 3]])
#guard pathEqual (d3 (Curve.stepX.cubics [⟨0, 1⟩, ⟨2, 3⟩])) "M0,1L1,1L1,3L2,3"
-- line.curve(curveStep)([[0, 1], [2, 3], [4, 5]])
-- Kind 2 (collinear): d3 has "M0,1L1,1L1,3L3,3L3,5L4,5". The kit stops at (2, 3) on the way from
-- (1, 3) to (3, 3).
#guard d3 (Curve.stepX.cubics [⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩]) == "M0,1L1,1L1,3L2,3L3,3L3,5L4,5"
-- area.curve(curveStep)([])
#guard d3Closed (area .stepX []) == ""
-- area.curve(curveStep)([[0, 1]])
#guard pathEqual (d3Closed (area .stepX [⟨0, 1⟩])) "M0,1L0,0Z"
-- area.curve(curveStep)([[0, 1], [2, 3]])
#guard pathEqual (d3Closed (area .stepX [⟨0, 1⟩, ⟨2, 3⟩])) "M0,1L1,1L1,3L2,3L2,0L1,0L1,0L0,0Z"
-- area.curve(curveStep)([[0, 1], [2, 3], [4, 5]])
-- Kind 2 (collinear): d3 has "M0,1L1,1L1,3L3,3L3,5L4,5L4,0L3,0L3,0L1,0L1,0L0,0Z". The kit stops
-- at (2, 3) on the way from (1, 3) to (3, 3), and at (2, 0) on the way from (3, 0) to (1, 0).
#guard d3Closed (area .stepX [⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩]) ==
  "M0,1L1,1L1,3L2,3L3,3L3,5L4,5L4,0L3,0L3,0L2,0L1,0L1,0L0,0Z"

/-! ## stepAfter-test.js -/

-- line.curve(curveStepAfter)([])
#guard d3 (Curve.stepAfter.cubics []) == ""
-- line.curve(curveStepAfter)([[0, 1]])
-- Kind 2 (dot): d3 has "M0,1Z".
#guard d3 (Curve.stepAfter.cubics [⟨0, 1⟩]) == ""
-- line.curve(curveStepAfter)([[0, 1], [2, 3]])
#guard pathEqual (d3 (Curve.stepAfter.cubics [⟨0, 1⟩, ⟨2, 3⟩])) "M0,1L2,1L2,3"
-- line.curve(curveStepAfter)([[0, 1], [2, 3], [4, 5]])
#guard pathEqual (d3 (Curve.stepAfter.cubics [⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩])) "M0,1L2,1L2,3L4,3L4,5"
-- area.curve(curveStepAfter)([])
#guard d3Closed (area .stepAfter []) == ""
-- area.curve(curveStepAfter)([[0, 1]])
#guard pathEqual (d3Closed (area .stepAfter [⟨0, 1⟩])) "M0,1L0,0Z"
-- area.curve(curveStepAfter)([[0, 1], [2, 3]])
#guard pathEqual (d3Closed (area .stepAfter [⟨0, 1⟩, ⟨2, 3⟩])) "M0,1L2,1L2,3L2,0L2,0L0,0Z"
-- area.curve(curveStepAfter)([[0, 1], [2, 3], [4, 5]])
#guard pathEqual (d3Closed (area .stepAfter [⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩]))
  "M0,1L2,1L2,3L4,3L4,5L4,0L4,0L2,0L2,0L0,0Z"

/-! ## stepBefore-test.js -/

-- line.curve(curveStepBefore)([])
#guard d3 (Curve.stepBefore.cubics []) == ""
-- line.curve(curveStepBefore)([[0, 1]])
-- Kind 2 (dot): d3 has "M0,1Z".
#guard d3 (Curve.stepBefore.cubics [⟨0, 1⟩]) == ""
-- line.curve(curveStepBefore)([[0, 1], [2, 3]])
#guard pathEqual (d3 (Curve.stepBefore.cubics [⟨0, 1⟩, ⟨2, 3⟩])) "M0,1L0,3L2,3"
-- line.curve(curveStepBefore)([[0, 1], [2, 3], [4, 5]])
#guard pathEqual (d3 (Curve.stepBefore.cubics [⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩])) "M0,1L0,3L2,3L2,5L4,5"
-- area.curve(curveStepBefore)([])
#guard d3Closed (area .stepBefore []) == ""
-- area.curve(curveStepBefore)([[0, 1]])
#guard pathEqual (d3Closed (area .stepBefore [⟨0, 1⟩])) "M0,1L0,0Z"
-- area.curve(curveStepBefore)([[0, 1], [2, 3]])
#guard pathEqual (d3Closed (area .stepBefore [⟨0, 1⟩, ⟨2, 3⟩])) "M0,1L0,3L2,3L2,0L0,0L0,0Z"
-- area.curve(curveStepBefore)([[0, 1], [2, 3], [4, 5]])
#guard pathEqual (d3Closed (area .stepBefore [⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩]))
  "M0,1L0,3L2,3L2,5L4,5L4,0L2,0L2,0L0,0L0,0Z"

end WhatwgTest.Svg.D3Shape
