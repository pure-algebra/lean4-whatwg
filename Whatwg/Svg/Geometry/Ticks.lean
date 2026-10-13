import Whatwg.Svg.Geometry.Rational

/-!
# Whatwg.Svg.Geometry.Ticks

Owner: the round numbers of an axis (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

An axis names a few values of its range, and a reader takes the rest from them. The values
are round: multiples of `1`, `2` or `5` times a power of ten. d3 finds them in
`d3-array/src/ticks.js` and moves the ends of a range out to them in `d3-array/src/nice.js`.
This module has both in exact numbers.

It is in the exact layer, since a tick is a decimal number and the whole-number layer of
`Whatwg/Svg/Scene/` has no fraction. A step is a `Decimal` whose mantissa is `1`, `2` or `5`,
and a tick is a `Decimal` with the step's exponent. So the ticks of one axis are written with
one count of places, which is what d3's `tickFormat` works out from the step afterwards.

- `Ticks.exponent q`: the power of ten at or below a number that is more than zero.
- `Ticks.nearest q`: the number of `1, 2, 5, 10, 20, 50, ...` that is nearest `q` in ratio.
- `Ticks.step start stop count`: the step of the ticks of a range, for about `count` gaps. It
  is d3's `tickStep`.
- `Ticks.ticks start stop count`: the ticks, each a multiple of the step, in the order of the
  range. It is d3's `ticks`. `Ticks.values` is the same as numbers, and `Ticks.between` the
  multiples of any step in a range.
- `Ticks.nice start stop count`: the range moved out to round numbers, so that its ends are
  ticks. It is d3's `nice`. `Ticks.Settled` says that the ends of a range are multiples of the
  range's own step.

The laws are beside this module, under `Whatwg/Svg/Geometry/Ticks/`: `Laws.lean` for the step
and the ticks, `Count.lean` for how many ticks there are, `Nice.lean` for a range moved out, and
`Axis.lean` for the ticks on a `Scale` of the whole-number layer.

How this differs from d3 (`d3-array` at `be0ae0d2b36a`), which computes in floating point:

- d3 picks the digit of a step by comparing with `Math.sqrt(50)`, `Math.sqrt(10)` and
  `Math.sqrt(2)`, each rounded to a float. Here the comparison is of squares, and is exact. No
  rational number is one of those three roots, so the exact comparison never meets the case
  that d3's rounding decides.
- d3 keeps a step below one as its reciprocal with a minus sign, so that a tick is an integer
  divided by an integer and `0.1 + 0.2` is never formed. An exact number needs no such guard:
  the step is the number itself.
- d3 rounds a quotient to the nearest integer and then moves it by one where the rounding went
  past the range. That is the ceiling and the floor of the quotient, which is what is taken
  here.
- The count is a whole number. d3 takes a fraction too, and for a count below two that gives
  no tick it takes twice the count. Here that is done for the count `1`.
- A range of one value has no step, and has no ticks here. d3 answers the value itself. A
  number that is not a number and an endless one do not exist here.
- **`nice` can fail to settle, and says so.** d3's `nice` moves the ends out until the step
  stops changing. With the count `1`, on a range with zero inside it, the step need not stop:
  `(-1, 1)` goes to `(-2, 2)`, `(-5, 5)`, `(-10, 10)` and on, each round asking for a wider
  step. By a reading of their sources, d3-array loops until its number overflows, and d3-scale
  gives up after ten rounds and leaves the range as it was. Here `nice` makes a stated count
  of rounds, and answers the range as it was where the step has not stopped by then. A control
  below has the case.

What this module does not claim: ticks on a scale that is not a straight line; a format with a
prefix or a percent sign; that `nice` settles within its rounds for every count of two or more.
That held of each of the 26 840 cases of a grid tried in a probe (low ends from `-3` to `3` and
widths from `0.1` to `28`, in tenths, with the counts from `2` to `12`), each within three
rounds, and it is not proved.
-/

namespace Whatwg.Svg.Value

namespace Ticks

/-! ## The power of ten at or below a number -/

/-- The count of digits of a whole number, less one: for `n` of one or more, the `k` with
`10 ^ k ≤ n < 10 ^ (k + 1)`. -/
def magnitude (n : Nat) : Nat := if n < 10 then 0 else magnitude (n / 10) + 1

/-- **The power of ten at or below a number**: for `q` more than zero, the whole `e` with
`10 ^ e ≤ q < 10 ^ (e + 1)`. It is the floor of the logarithm to the base ten, found by
counting digits. -/
def exponent (q : Rat) : Int :=
  if 1 ≤ q then (magnitude q.floor.toNat : Int)
  else -((magnitude ((1 / q).ceil.toNat - 1) : Int) + 1)

/-- A number over the power of ten at or below it: from one to less than ten. -/
def lead (q : Rat) : Rat := q / (10 : Rat) ^ exponent q

/-- **The round number nearest a number, in ratio.** The round numbers are `1`, `2` and `5`
times a power of ten. Between two of them the choice changes at their geometric mean, so the
squares are compared: `50` is `5 * 10`, `10` is `2 * 5`, and `2` is `1 * 2`. -/
def nearest (q : Rat) : Decimal :=
  if 50 ≤ lead q * lead q then ⟨1, exponent q + 1⟩
  else if 10 ≤ lead q * lead q then ⟨5, exponent q⟩
  else if 2 ≤ lead q * lead q then ⟨2, exponent q⟩
  else ⟨1, exponent q⟩

/-! ## The multiples of a step in a range -/

/-- `k` times a step, written with the step's exponent. -/
def times (s : Decimal) (k : Int) : Decimal := ⟨k * s.mantissa, s.exponent⟩

/-- The first multiple of a step that is no less than a number, as its multiplier. -/
def low (start : Rat) (s : Decimal) : Int := (start / s.toRat).ceil

/-- The last multiple of a step that is no more than a number, as its multiplier. -/
def high (stop : Rat) (s : Decimal) : Int := (stop / s.toRat).floor

/-- **The multiples of a step from `start` to `stop`**, in rising order. -/
def between (start stop : Rat) (s : Decimal) : List Decimal :=
  (List.range (high stop s - low start s + 1).toNat).map fun (k : Nat) =>
    times s (low start s + (k : Int))

/-! ## The step and the ticks of a range -/

/-- The round number nearest the range shared out over `count` gaps. -/
def plain (start stop : Rat) (count : Nat) : Decimal := nearest ((stop - start) / (count : Rat))

/-- **The step of the ticks of a range**, for about `count` gaps, where `start` is less than
`stop` and `count` is not zero. For the count `1`, where the step of one gap has no multiple in
the range, it is the step of two gaps, as in d3. -/
def step (start stop : Rat) (count : Nat) : Decimal :=
  if count = 1 ∧ high stop (plain start stop 1) < low start (plain start stop 1) then
    plain start stop 2
  else plain start stop count

/-- **The ticks of a range**: the multiples of its step that lie in it, each written with the
step's exponent. They rise where `start` is less than `stop` and fall where it is more. A count
of zero and a range of one value have none. -/
def ticks (start stop : Rat) (count : Nat) : List Decimal :=
  if count = 0 ∨ start = stop then []
  else if start < stop then between start stop (step start stop count)
  else (between stop start (step stop start count)).reverse

/-- The ticks of a range as numbers. -/
def values (start stop : Rat) (count : Nat) : List Rat := (ticks start stop count).map Decimal.toRat

/-! ## A range moved out to round numbers -/

/-- A range moved out to the multiples of a step: the low end down and the high end up. -/
def widen (start stop : Rat) (s : Decimal) : Rat × Rat :=
  ((start / s.toRat).floor * s.toRat, (stop / s.toRat).ceil * s.toRat)

/-- **The ends of a range are multiples of its own step.** Then the first tick of the range is
its low end and the last is its high end. -/
def Settled (start stop : Rat) (count : Nat) : Prop :=
  widen start stop (step start stop count) = (start, stop)

/-- Whether a range is settled is decided. -/
instance (start stop : Rat) (count : Nat) : Decidable (Settled start stop count) :=
  inferInstanceAs (Decidable (_ = _))

/-- Rounds of moving a range out, until the step is the step of the round before. `none` where
the rounds end first. -/
def settle (count : Nat) : Nat → Decimal → Rat → Rat → Option (Rat × Rat)
  | 0, _, _, _ => none
  | rounds + 1, before, start, stop =>
    if step start stop count = before then some (start, stop)
    else
      settle count rounds (step start stop count) (widen start stop (step start stop count)).1
        (widen start stop (step start stop count)).2

/-- **A range moved out to round numbers**, so that its ends are ticks of it. Where the step
does not stop changing within `rounds` rounds, and for a count of zero or a range of one
value, the range is answered as it was. A range that falls is answered falling. -/
def nice (start stop : Rat) (count : Nat) (rounds : Nat := 32) : Rat × Rat :=
  if count = 0 ∨ start = stop then (start, stop)
  else if start < stop then
    (settle count rounds (step start stop count) (widen start stop (step start stop count)).1
      (widen start stop (step start stop count)).2).getD (start, stop)
  else
    ((settle count rounds (step stop start count) (widen stop start (step stop start count)).1
      (widen stop start (step stop start count)).2).map fun p => (p.2, p.1)).getD (start, stop)

end Ticks

/-! ## Finite evaluations

The values of d3's own tests (`d3-array` at `be0ae0d2b36a`, `test/tickStep-test.js`,
`test/tickIncrement-test.js`, `test/ticks-test.js` and `test/nice-test.js`; `d3-scale` at
`d6904a4bde09`, `test/linear-test.js`). d3 asserts each with strict equality, and each is
compared here as an exact number: a decimal literal such as `0.1` is the rational number one
tenth. The tests of a number that is not a number, of an endless one, of a negative zero and
of a count that is a fraction have nothing to convert. -/

-- "tickStep(start, stop, count) returns approximately count + 1 tickStep when start < stop":
-- the counts from ten down to one. `tickIncrement` has the same thirty values, written as
-- reciprocals where they are below one.
#guard (List.range 10).map (fun i => (Ticks.step 0 1 (10 - i)).toRat) ==
  [0.1, 0.1, 0.1, 0.2, 0.2, 0.2, 0.2, 0.5, 0.5, 1]
#guard (List.range 10).map (fun i => (Ticks.step 0 10 (10 - i)).toRat) ==
  [1, 1, 1, 2, 2, 2, 2, 5, 5, 10]
#guard (List.range 10).map (fun i => (Ticks.step (-10) 10 (10 - i)).toRat) ==
  [2, 2, 2, 2, 5, 5, 5, 5, 10, 20]

-- "ticks(start, stop, count) remains within the domain".
#guard Ticks.values 0 2.2 3 == [0, 1, 2]

-- "ticks(start, stop, count) returns approximately count + 1 ticks when start < stop".
#guard [10, 9, 8].all fun n =>
  Ticks.values 0 1 n == [0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1]
#guard [7, 6, 5, 4].all fun n => Ticks.values 0 1 n == [0, 0.2, 0.4, 0.6, 0.8, 1]
#guard [3, 2].all fun n => Ticks.values 0 1 n == [0, 0.5, 1]
#guard Ticks.values 0 1 1 == [0, 1]
#guard [10, 9, 8].all fun n => Ticks.values 0 10 n == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#guard [7, 6, 5, 4].all fun n => Ticks.values 0 10 n == [0, 2, 4, 6, 8, 10]
#guard [3, 2].all fun n => Ticks.values 0 10 n == [0, 5, 10]
#guard Ticks.values 0 10 1 == [0, 10]
#guard [10, 9, 8, 7].all fun n =>
  Ticks.values (-10) 10 n == [-10, -8, -6, -4, -2, 0, 2, 4, 6, 8, 10]
#guard [6, 5, 4, 3].all fun n => Ticks.values (-10) 10 n == [-10, -5, 0, 5, 10]
#guard Ticks.values (-10) 10 2 == [-10, 0, 10] && Ticks.values (-10) 10 1 == [0]

-- "ticks(start, stop, count) returns the reverse of ticks(stop, start, count)": the thirty
-- pairs of d3's test.
#guard (List.range 10).all fun i =>
  Ticks.values 1 0 (i + 1) == (Ticks.values 0 1 (i + 1)).reverse &&
    Ticks.values 10 0 (i + 1) == (Ticks.values 0 10 (i + 1)).reverse &&
    Ticks.values 10 (-10) (i + 1) == (Ticks.values (-10) 10 (i + 1)).reverse

-- "ticks(start, stop, count) handles precision problems". In exact numbers there is none.
#guard Ticks.values 0.98 1.14 10 == [0.98, 1, 1.02, 1.04, 1.06, 1.08, 1.1, 1.12, 1.14]

-- "ticks(start, stop, count) tries to return at least one tick if count >= 0.5": the two of
-- its cases with a whole count.
#guard Ticks.values 1 364 1 == [200] && Ticks.values 1 499 1 == [200, 400]

-- The ticks of one axis are written with one count of places: what d3's `tickFormat` gives.
#guard (Ticks.ticks 0 1 5).map toString == ["0.0", "0.2", "0.4", "0.6", "0.8", "1.0"]
#guard (Ticks.ticks 0.98 1.14 10).map toString ==
  ["0.98", "1.00", "1.02", "1.04", "1.06", "1.08", "1.10", "1.12", "1.14"]
#guard (Ticks.ticks (-10) 10 3).map toString == ["-10", "-5", "0", "5", "10"]

-- `test/nice-test.js`, "nice(start, stop, count) returns the expected values".
#guard [1000, 100, 30, 10, 6, 5, 1].map (Ticks.nice 0.132 0.876) ==
  [(0.132, 0.876), (0.13, 0.88), (0.12, 0.88), (0.1, 0.9), (0.1, 0.9), (0, 1), (0, 1)]
#guard [1000, 100, 30, 10, 6, 5, 1].map (Ticks.nice 132 876) ==
  [(132, 876), (130, 880), (120, 880), (100, 900), (100, 900), (0, 1000), (0, 1000)]
-- "nice(start, stop, count) returns [start, stop] if start === stop", and "if count is not
-- positive".
#guard Ticks.nice 1 1 10 == (1, 1) && Ticks.nice 0 1 0 == (0, 1)

-- `d3-scale`, `test/linear-test.js`, "linear.nice(count) extends the domain to match the
-- desired ticks" and "nices the domain, extending it to round numbers".
#guard Ticks.nice 0 0.96 10 == (0, 1) && Ticks.nice 0 96 10 == (0, 100) &&
  Ticks.nice 0.96 0 10 == (1, 0) && Ticks.nice 96 0 10 == (100, 0) &&
  Ticks.nice 0 (-0.96) 10 == (0, -1) && Ticks.nice 0 (-96) 10 == (0, -100) &&
  Ticks.nice (-0.96) 0 10 == (-1, 0) && Ticks.nice (-96) 0 10 == (-100, 0) &&
  Ticks.nice (-0.1) 51.1 8 == (-10, 60)
#guard Ticks.nice 1.1 10.9 10 == (1, 11) && Ticks.nice 10.9 1.1 10 == (11, 1) &&
  Ticks.nice 0.7 11.001 10 == (0, 12) && Ticks.nice 123.1 6.7 10 == (130, 0) &&
  Ticks.nice 0 0.49 10 == (0, 0.5) && Ticks.nice 0 14.1 5 == (0, 20) &&
  Ticks.nice 0 15 5 == (0, 20)
-- "linear.nice(count) accepts a tick count to control nicing step".
#guard [5, 10, 100].map (Ticks.nice 12 87) == [(0, 100), (10, 90), (12, 87)]

-- "linear.ticks(X) spans linear.nice(X).domain()": the seventeen ranges of d3's test. The
-- first and the last tick of the nice range are its ends.
#guard ([(1, 9, 2), (1, 9, 3), (1, 9, 4), (8, 9, 2), (8, 9, 3), (8, 9, 4)] ++
    (List.range 11).map fun k => (((k + 1 : Nat) : Rat), (21 : Rat), 2)).all fun (a, b, n) =>
  let r := Ticks.nice a b n
  (Ticks.values r.1 r.2 n).head? == some r.1 && (Ticks.values r.1 r.2 n).getLast? == some r.2 &&
    decide (Ticks.Settled r.1 r.2 n)

-- A control: a range that does not settle. With the count `1` and zero inside the range, each
-- round asks for a wider step, so `nice` answers the range as it was. Two gaps settle at once.
#guard Ticks.nice (-1) 1 1 == (-1, 1) && !decide (Ticks.Settled (-1) 1 1)
#guard Ticks.settle 1 4 (Ticks.step (-1) 1 1) (-2) 2 == none
#guard Ticks.nice (-1) 1 2 == (-1, 1) && decide (Ticks.Settled (-1) 1 2)
-- With the count `1` and zero outside the range, the walk is long and ends: ten rounds from
-- `(999, 1001.5)`, each a wider step, to `(0, 2000)`. With nine rounds the range is answered as
-- it was. d3-scale's `linear.nice` allows itself ten computations of the step, which is nine
-- rounds here, so by a reading of `linear.js` it leaves this range as it was; it was not run.
#guard Ticks.nice 999 1001.5 1 == (0, 2000) && Ticks.nice 999 1001.5 1 10 == (0, 2000) &&
  Ticks.nice 999 1001.5 1 9 == (999, 1001.5)

end Whatwg.Svg.Value
