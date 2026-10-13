import Whatwg.Svg.Geometry.Monotone
import WhatwgTest.Svg.D3Shape

/-!
# WhatwgTest.Svg.D3Monotone

The tests of d3-shape for its monotone curves, converted and run against `Curve.monotoneX` and
`Curve.monotoneY` of `Whatwg/Svg/Geometry/Monotone.lean`.

**Source.** https://github.com/d3/d3-shape, the files `test/curve/monotoneX-test.js` and
`test/curve/monotoneY-test.js` at commit `a82254af78f0` of `main`. Copyright 2010-2022 Mike
Bostock, ISC licence. Every expected path below is one of d3's test vectors, typed as the test
has it.

## How a case is converted

As in `WhatwgTest/Svg/D3Shape.lean`, whose writer of numbers and whose comparison this module
uses (`point`, `pathEqual`): one `#guard` for one assertion of d3, with d3's call above it.

- `line().curve(curveMonotoneX)(data)` is `Curve.monotoneX data`, written by `line`. d3 writes
  every piece of a monotone curve as a `C`, also a level one, and the straight segment between
  two points as an `L`. `line` writes so: a `C` for each piece where three points or more are
  left, and an `L` for two.
- `area().curve(curveMonotoneX)(data)` has d3's own `y0` of zero. The kit has no area for this
  curve, so `area` puts the outline together as d3 does: the curve of the top, a straight line
  to the last point of the base, the curve of the base taken backwards, and a `Z`.
- `curveMonotoneY` is `Curve.monotoneY`, and d3's `reflect` is `Monotone.swap`.

## What was found

d3 has 42 assertions in the two files, and all are converted. In 40 the kit's text is d3's:
26 compare with d3's vector, 4 compare with the empty text for d3's `null`, and 10 compare two
texts of the kit where d3 compares two of its paths. In 2, marked *dot*, d3 writes a closed
subpath of no length for one point (`M0,1Z`) and the kit has no segment and writes nothing, as
for every curve of `WhatwgTest/Svg/D3Shape.lean`. One more guard is a control of this module.

Every vector with a repeated abscissa, where d3 divides by zero and reads an endless slope, is
among the 26: the exact cases of `Monotone.slope3` give d3's path there.
-/

namespace WhatwgTest.Svg.D3Monotone

open Whatwg.Svg.Value
open WhatwgTest.Svg.D3Shape (point pathEqual)

/-- The pieces as d3 writes the pieces of a monotone curve: a `C` for each. -/
def curves (pieces : List Cubic) : String :=
  String.join (pieces.map fun c => "C" ++ point c.p1 ++ "," ++ point c.p2 ++ "," ++ point c.p3)

/-- The pieces of a monotone curve through `data` after its start: an `L` where two points are
left, and a `C` for each piece otherwise. -/
def after (data : List Vec) (pieces : List Cubic) : String :=
  match Monotone.distinct data, pieces with
  | [_, _], [c] => "L" ++ point c.p3
  | _, cs => curves cs

/-- d3's `line().curve(curveMonotoneX)(data)`, or the same along `y` for `alongX = false`. No
piece is the empty text. -/
def line (data : List Vec) (alongX : Bool := true) : String :=
  let pieces := if alongX then Curve.monotoneX data else Curve.monotoneY data
  match pieces with
  | [] => ""
  | c :: rest =>
    "M" ++ point c.p0 ++ after (if alongX then data else data.map Monotone.swap) (c :: rest)

/-- d3's `area().curve(curveMonotoneX)(data)` with its own `y0` of zero, or the same along `y`:
the curve of the top, a straight line to the last point of the base, the curve of the base
taken backwards, and a `Z`. -/
def area (data : List Vec) (alongX : Bool := true) : String :=
  let base : List Vec := (data.map fun p => (⟨p.x, 0⟩ : Vec)).reverse
  let gen (ps : List Vec) : List Cubic := if alongX then Curve.monotoneX ps else Curve.monotoneY ps
  let key (ps : List Vec) : List Vec := if alongX then ps else ps.map Monotone.swap
  match data.head?, base.head? with
  | some a, some b =>
    "M" ++ point a ++ after (key data) (gen data) ++ "L" ++ point b ++
      after (key base) (gen base) ++ "Z"
  | _, _ => ""

/-- d3's `reflect`. -/
def reflect (data : List Vec) : List Vec := data.map Monotone.swap

/-! ## monotoneX-test.js -/

-- line.curve(curveMonotoneX)([])
#guard line [] == ""
-- line.curve(curveMonotoneX)([[0, 1]])
-- dot: d3 has "M0,1Z".
#guard line [⟨0, 1⟩] == ""
-- line.curve(curveMonotoneX)([[0, 1], [1, 3]])
#guard pathEqual (line [⟨0, 1⟩, ⟨1, 3⟩]) "M0,1L1,3"
-- line.curve(curveMonotoneX)([[0, 1], [1, 3], [2, 1]])
#guard pathEqual (line [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩])
  "M0,1C0.333333,2,0.666667,3,1,3C1.333333,3,1.666667,2,2,1"
-- line.curve(curveMonotoneX)([[0, 1], [1, 3], [2, 1], [3, 3]])
#guard pathEqual (line [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])
  "M0,1C0.333333,2,0.666667,3,1,3C1.333333,3,1.666667,1,2,1C2.333333,1,2.666667,2,3,3"

-- "preserves monotonicity in y"
-- line.curve(curveMonotoneX)([[0, 200], [100, 100], [200, 100], [300, 300], [400, 300]])
#guard pathEqual (line [⟨0, 200⟩, ⟨100, 100⟩, ⟨200, 100⟩, ⟨300, 300⟩, ⟨400, 300⟩])
  "M0,200C33.333333,150,66.666667,100,100,100C133.333333,100,166.666667,100,200,100C233.333333,100,266.666667,300,300,300C333.333333,300,366.666667,300,400,300"

-- "handles duplicate x-values"
-- line.curve(curveMonotoneX)([[0, 200], [0, 100], [100, 100], [200, 0]])
#guard pathEqual (line [⟨0, 200⟩, ⟨0, 100⟩, ⟨100, 100⟩, ⟨200, 0⟩])
  "M0,200C0,200,0,100,0,100C33.333333,100,66.666667,100,100,100C133.333333,100,166.666667,50,200,0"
-- line.curve(curveMonotoneX)([[0, 200], [100, 100], [100, 0], [200, 0]])
#guard pathEqual (line [⟨0, 200⟩, ⟨100, 100⟩, ⟨100, 0⟩, ⟨200, 0⟩])
  "M0,200C33.333333,183.333333,66.666667,166.666667,100,100C100,100,100,0,100,0C133.333333,0,166.666667,0,200,0"
-- line.curve(curveMonotoneX)([[0, 200], [100, 100], [200, 100], [200, 0]])
#guard pathEqual (line [⟨0, 200⟩, ⟨100, 100⟩, ⟨200, 100⟩, ⟨200, 0⟩])
  "M0,200C33.333333,150,66.666667,100,100,100C133.333333,100,166.666667,100,200,100C200,100,200,0,200,0"

-- "handles segments of infinite slope"
-- line.curve(curveMonotoneX)([[0, 200], [100, 150], [100, 50], [200, 0]])
#guard pathEqual (line [⟨0, 200⟩, ⟨100, 150⟩, ⟨100, 50⟩, ⟨200, 0⟩])
  "M0,200C33.333333,191.666667,66.666667,183.333333,100,150C100,150,100,50,100,50C133.333333,16.666667,166.666667,8.333333,200,0"
-- line.curve(curveMonotoneX)([[200, 0], [100, 50], [100, 150], [0, 200]])
#guard pathEqual (line [⟨200, 0⟩, ⟨100, 50⟩, ⟨100, 150⟩, ⟨0, 200⟩])
  "M200,0C166.666667,8.333333,133.333333,16.666667,100,50C100,50,100,150,100,150C66.666667,183.333333,33.333333,191.666667,0,200"

/-- The path d3's test of coincident points compares five others with. -/
def plain : List Vec := [⟨0, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨200, 0⟩]

-- "ignores coincident points": each is strictEqual to line(plain)
#guard line [⟨0, 200⟩, ⟨0, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨200, 0⟩] == line plain
#guard line [⟨0, 200⟩, ⟨50, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨200, 0⟩] == line plain
#guard line [⟨0, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨200, 0⟩] == line plain
#guard line [⟨0, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨150, 0⟩, ⟨200, 0⟩] == line plain
#guard line [⟨0, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨200, 0⟩, ⟨200, 0⟩] == line plain
-- A control of the five: the path they are compared with is a curve of four pieces.
#guard (Curve.monotoneX plain).length == 4

-- area.curve(curveMonotoneX)([])
#guard area [] == ""
-- area.curve(curveMonotoneX)([[0, 1]])
#guard pathEqual (area [⟨0, 1⟩]) "M0,1L0,0Z"
-- area.curve(curveMonotoneX)([[0, 1], [1, 3]])
#guard pathEqual (area [⟨0, 1⟩, ⟨1, 3⟩]) "M0,1L1,3L1,0L0,0Z"
-- area.curve(curveMonotoneX)([[0, 1], [1, 3], [2, 1]])
#guard pathEqual (area [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩])
  "M0,1C0.333333,2,0.666667,3,1,3C1.333333,3,1.666667,2,2,1L2,0C1.666667,0,1.333333,0,1,0C0.666667,0,0.333333,0,0,0Z"
-- area.curve(curveMonotoneX)([[0, 1], [1, 3], [2, 1], [3, 3]])
#guard pathEqual (area [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])
  "M0,1C0.333333,2,0.666667,3,1,3C1.333333,3,1.666667,1,2,1C2.333333,1,2.666667,2,3,3L3,0C2.666667,0,2.333333,0,2,0C1.666667,0,1.333333,0,1,0C0.666667,0,0.333333,0,0,0Z"

/-! ## monotoneY-test.js -/

-- line.curve(curveMonotoneY)([].map(reflect))
#guard line (reflect []) false == ""
-- line.curve(curveMonotoneY)([[0, 1]].map(reflect))
-- dot: d3 has "M1,0Z".
#guard line (reflect [⟨0, 1⟩]) false == ""
-- line.curve(curveMonotoneY)([[0, 1], [1, 3]].map(reflect))
#guard pathEqual (line (reflect [⟨0, 1⟩, ⟨1, 3⟩]) false) "M1,0L3,1"
-- line.curve(curveMonotoneY)([[0, 1], [1, 3], [2, 1]].map(reflect))
#guard pathEqual (line (reflect [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) false)
  "M1,0C2,0.333333,3,0.666667,3,1C3,1.333333,2,1.666667,1,2"
-- line.curve(curveMonotoneY)([[0, 1], [1, 3], [2, 1], [3, 3]].map(reflect))
#guard pathEqual (line (reflect [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) false)
  "M1,0C2,0.333333,3,0.666667,3,1C3,1.333333,1,1.666667,1,2C1,2.333333,2,2.666667,3,3"

-- "preserves monotonicity in y"
#guard pathEqual
  (line (reflect [⟨0, 200⟩, ⟨100, 100⟩, ⟨200, 100⟩, ⟨300, 300⟩, ⟨400, 300⟩]) false)
  "M200,0C150,33.333333,100,66.666667,100,100C100,133.333333,100,166.666667,100,200C100,233.333333,300,266.666667,300,300C300,333.333333,300,366.666667,300,400"

-- "handles duplicate x-values"
#guard pathEqual (line (reflect [⟨0, 200⟩, ⟨0, 100⟩, ⟨100, 100⟩, ⟨200, 0⟩]) false)
  "M200,0C200,0,100,0,100,0C100,33.333333,100,66.666667,100,100C100,133.333333,50,166.666667,0,200"
#guard pathEqual (line (reflect [⟨0, 200⟩, ⟨100, 100⟩, ⟨100, 0⟩, ⟨200, 0⟩]) false)
  "M200,0C183.333333,33.333333,166.666667,66.666667,100,100C100,100,0,100,0,100C0,133.333333,0,166.666667,0,200"
#guard pathEqual (line (reflect [⟨0, 200⟩, ⟨100, 100⟩, ⟨200, 100⟩, ⟨200, 0⟩]) false)
  "M200,0C150,33.333333,100,66.666667,100,100C100,133.333333,100,166.666667,100,200C100,200,0,200,0,200"

-- "handles segments of infinite slope"
#guard pathEqual (line (reflect [⟨0, 200⟩, ⟨100, 150⟩, ⟨100, 50⟩, ⟨200, 0⟩]) false)
  "M200,0C191.666667,33.333333,183.333333,66.666667,150,100C150,100,50,100,50,100C16.666667,133.333333,8.333333,166.666667,0,200"
#guard pathEqual (line (reflect [⟨200, 0⟩, ⟨100, 50⟩, ⟨100, 150⟩, ⟨0, 200⟩]) false)
  "M0,200C8.333333,166.666667,16.666667,133.333333,50,100C50,100,150,100,150,100C183.333333,66.666667,191.666667,33.333333,200,0"

-- "ignores coincident points": each is strictEqual to the path of `plain`, reflected
#guard line (reflect [⟨0, 200⟩, ⟨0, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨200, 0⟩]) false ==
  line (reflect plain) false
#guard line (reflect [⟨0, 200⟩, ⟨50, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨200, 0⟩]) false ==
  line (reflect plain) false
#guard line (reflect [⟨0, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨200, 0⟩]) false ==
  line (reflect plain) false
#guard line (reflect [⟨0, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨150, 0⟩, ⟨200, 0⟩]) false ==
  line (reflect plain) false
#guard line (reflect [⟨0, 200⟩, ⟨50, 200⟩, ⟨100, 100⟩, ⟨150, 0⟩, ⟨200, 0⟩, ⟨200, 0⟩]) false ==
  line (reflect plain) false

-- area.curve(curveMonotoneY)([].map(reflect))
#guard area (reflect []) false == ""
-- area.curve(curveMonotoneY)([[0, 1]].map(reflect))
#guard pathEqual (area (reflect [⟨0, 1⟩]) false) "M1,0L1,0Z"
-- area.curve(curveMonotoneY)([[0, 1], [1, 3]].map(reflect))
#guard pathEqual (area (reflect [⟨0, 1⟩, ⟨1, 3⟩]) false) "M1,0L3,1L3,0L1,0Z"
-- area.curve(curveMonotoneY)([[0, 1], [1, 3], [2, 1]].map(reflect))
#guard pathEqual (area (reflect [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]) false)
  "M1,0C2,0.333333,3,0.666667,3,1C3,1.333333,2,1.666667,1,2L1,0C1,0,3,0,3,0C3,0,1,0,1,0Z"
-- area.curve(curveMonotoneY)([[0, 1], [1, 3], [2, 1], [3, 3]].map(reflect))
#guard pathEqual (area (reflect [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩]) false)
  "M1,0C2,0.333333,3,0.666667,3,1C3,1.333333,1,1.666667,1,2C1,2.333333,2,2.666667,3,3L3,0C3,0,1,0,1,0C1,0,3,0,3,0C3,0,1,0,1,0Z"

end WhatwgTest.Svg.D3Monotone
