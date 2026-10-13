import Whatwg.Svg.Geometry.Nearest

/-!
# WhatwgTest.Svg.Nearest

lean4-effect4's nearest cubic Bézier, written on `Easing.nearestCubic` of
`Whatwg/Svg/Scene/Nearest.lean`.

**Source.** lean4-effect4 at commit `6ad8f7b8d`, `tools/Tools/View/Look.lean`: `Ease`, its two
tables, `tableAt`, `Ease.at`, `Ease.points`, `roundDiv` and `Ease.bezier` (lines 38 to 112).
They are in the namespace `Consumer` below as they are written there. This file is a template
for the consumer's port: its `Ease.bezier e` is `Easing.nearestCubic e.points`, and with its
easings as easings of the kit it is `Easing.nearest`.

## What the port shows

- **The kit's function is the consumer's** on the twenty-one points of each of its seven
  easings: the same two whole numbers. The consumer's sums run over twenty pieces with each
  term scaled by `20³`, and the kit's over any number of pieces.
- **What comes back.** The consumer's doc says that its cubic easings "come back to within the
  rounding of their points". The evaluations say how near: its `in_` and its `out` come back
  exactly, and its `outBack` as `(1565, 999)`. The kit's own cubics, read at twenty-one stops
  and rounded down there, come back within one per mille of their heights.
- **A trap that the kit's function for an easing avoids.** The easing `linear` of the kit has
  two stops. Two stops are too few for two equations, and `nearestCubic` of them reads `(0, 0)`,
  which is the easing that is slow at first. `Easing.nearest` reads the points of the easing,
  twenty-one of them, and gives the heights a third and two thirds.
-/

namespace WhatwgTest.Svg.Nearest

open Whatwg.Svg.Scene

/-! ## The consumer's code, as written there -/

namespace Consumer

inductive Ease where
  | linear | in_ | out | inOut | outBack | settle | spring
deriving Repr, DecidableEq

def settleTable : List Int :=
  [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992, 995, 998, 1000]

def springTable : List Int :=
  [0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045, 1041, 1034, 1026, 1019, 1012, 1007, 1003, 1000]

def tableAt (t : List Int) (p : Nat) : Int :=
  let a := t.getD (p / 50) 1000
  let b := t.getD (p / 50 + 1) 1000
  a + (b - a) * ((p % 50 : Nat) : Int) / 50

def Ease.at : Ease → Nat → Int
  | .linear, p => p
  | .in_, p => (p : Int) ^ 3 / 1000000
  | .out, p => 1000 - (1000 - (p : Int)) ^ 3 / 1000000
  | .inOut, p =>
    if p < 500 then 4 * (p : Int) ^ 3 / 1000000 else 1000 - (2 * (1000 - (p : Int))) ^ 3 / 2000000
  | .outBack, p =>
    let q : Int := (p : Int) - 1000
    1000 + 2702 * q ^ 3 / 1000000000 + 1702 * q ^ 2 / 1000000
  | .settle, p => tableAt settleTable p
  | .spring, p => tableAt springTable p

def Ease.all : List Ease := [.linear, .in_, .out, .inOut, .outBack, .settle, .spring]

def Ease.points (e : Ease) : List Int := (List.range 21).map fun i => e.at (i * 50)

def roundDiv (a b : Int) : Int := (2 * a + b) / (2 * b)

def Ease.bezier (e : Ease) : Int × Int :=
  let pts := e.points.zipIdx
  let b1 (i : Nat) : Int := 3 * (i : Int) * (20 - (i : Int)) ^ 2
  let b2 (i : Nat) : Int := 3 * (i : Int) ^ 2 * (20 - (i : Int))
  let res (v : Int) (i : Nat) : Int := 8 * v - (i : Int) ^ 3
  let sum (f : Int → Nat → Int) : Int := pts.foldl (fun s (v, i) => s + f v i) 0
  let a11 := sum fun _ i => b1 i * b1 i
  let a12 := sum fun _ i => b1 i * b2 i
  let a22 := sum fun _ i => b2 i * b2 i
  let r1 := sum fun v i => b1 i * res v i
  let r2 := sum fun v i => b2 i * res v i
  let det := a11 * a22 - a12 * a12
  (roundDiv (1000 * (r1 * a22 - r2 * a12)) det, roundDiv (1000 * (a11 * r2 - a12 * r1)) det)

end Consumer

/-! ## The port -/

/-- The consumer's `Ease.bezier`, on the kit: one call. -/
def bezier (e : Consumer.Ease) : Int × Int := Easing.nearestCubic e.points

/-- The consumer's easings as easings of the kit: its cubics as cubics, and the others as the
stops of their twenty-one points. -/
def easing : Consumer.Ease → Easing
  | .linear => Easing.linear
  | .in_ => Easing.cubicIn
  | .out => Easing.cubicOut
  | e => .stops e.points

-- The kit's function is the consumer's, on each of its seven easings.
#guard Consumer.Ease.all.all fun e => bezier e == e.bezier

-- What the seven are: the progress itself is the cubic of the heights a third and two thirds,
-- and the two cubics come back exactly.
#guard Consumer.Ease.all.map bezier ==
  [(333, 667), (0, 0), (1000, 1000), (-314, 1314), (1565, 999), (911, 1066), (1198, 1116)]

-- With the consumer's easings as easings of the kit, `Easing.nearest` gives the same heights
-- for six of the seven. The seventh is the consumer's `outBack`: as stops of its points it
-- gives the consumer's heights, which the guard above has.
#guard (Consumer.Ease.all.filter (· != .outBack)).all fun e =>
  (easing e).nearest == .cubic (bezier e).1 (bezier e).2

/-! ## What comes back from a cubic -/

-- The kit's cubics, read at twenty-one stops and rounded down there, within one per mille.
#guard Easing.cubicIn.nearest == Easing.cubicIn && Easing.cubicOut.nearest == Easing.cubicOut
#guard Easing.backOut == .cubic 1567 1000 && Easing.backOut.nearest == .cubic 1566 1000
#guard Easing.backIn == .cubic 0 (-567) && Easing.backIn.nearest == .cubic (-1) (-568)

-- `Easing.nearestCubic_of_cubic` at real stops. At ten pieces the cubic of the heights `2000`
-- and `-1000` reads a whole number of per mille at every stop, so its stops stand on it and it
-- comes back with nothing rounded away.
#guard Easing.nearestCubic ((Easing.cubic 2000 (-1000)).values 10) == (2000, -1000)

-- A control of that law, which asks that the stops stand on the cubic. The stops of `backOut`
-- at ten pieces are rounded down, and what comes back is not `1567`.
#guard Easing.nearestCubic (Easing.backOut.values 10) != (1567, 1000) &&
  Easing.nearestCubic (Easing.backOut.values 10) == (1566, 1000)

/-! ## The premise of the laws, and the trap -/

-- `Sums.det` is more than `0` at twenty-one stops, and at four. It reads the number of stops
-- and not their values.
#guard 0 < (Easing.Sums.of (Easing.nearestRows (Easing.linear.points 20))).det &&
  0 < (Easing.Sums.of (Easing.nearestRows [0, 300, 600, 1000])).det

-- A control of the premise: with three stops, and with two, the two equations are one, `det`
-- is `0`, and both heights read `0`.
#guard (Easing.Sums.of (Easing.nearestRows [0, 500, 1000])).det == 0 &&
  Easing.nearestCubic [0, 500, 1000] == (0, 0) && Easing.nearestCubic [0, 1000] == (0, 0)

-- The trap: the stops of `linear` are two, and its points are twenty-one. `nearest` reads the
-- points.
#guard Easing.linear.values == [0, 1000] && (Easing.linear.points).length == 21 &&
  Easing.linear.nearest == .cubic 333 667

/-! ## The exact heights -/

-- The exact heights of the progress itself are a third and two thirds of a thousand, and the
-- whole-number answer is each to the nearest whole number.
#guard Easing.nearestExact (Easing.linear.points 20) == (1000 / 3, 2000 / 3)

-- What `Easing.nearestExact_least` is about: the exact heights of the consumer's spring are no
-- whole numbers, and the whole-number heights are a little further from its points.
#guard
  let pts := Consumer.Ease.spring.points
  let exact := Easing.nearestExact pts
  Easing.distance pts exact.1 exact.2 < Easing.distance pts 1198 1116 &&
    exact != (1198, 1116)

end WhatwgTest.Svg.Nearest
