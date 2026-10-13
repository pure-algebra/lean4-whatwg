import Whatwg.Svg.Geometry.Spring.Laws

/-!
# WhatwgTest.Html.SvgSpring

The two springs of lean4-effect4 on the kit's spring as exact data (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`). The consumer is read at its checkout `14222463`: the section
"Easing" of `tools/Tools/View/Look.lean`, last changed at `2d32a911`, which has `settleTable` and
`springTable` as twenty-one numbers each, typed by hand from the textbook's formulas. This module
imports nothing of that package.

**What a real port copies.** Two definitions and one line each.

1. `settle` and `spring`: the consumer's two springs as three rational numbers each. The numbers
   are the textbook's, to five places: the consumer's own comments give `ω = 7.4` for the first,
   and `ζ = 0.7` with `ω = 7.5` for the second, over a step of twenty pieces.
2. `settle.easing` and `spring.easing` are the consumer's two tables, stop for stop (the first
   two guards). A port writes `settle.easing` where it has `.stops settleTable`.

**What the port gets that a table does not give.**

- `settle_bounded`: the easing of `settle` passes `Easing.bounded` for every number of pieces,
  by `Spring.critical_easing_bounded`. For the table that was one evaluation of twenty-one
  numbers. `settle_in_range` is what it buys: a transition with that easing reads from `0` to
  `1000` at every moment.
- `settle_proper`, `settle_rising`, `settle_settled`: it ends at `1000`, its stops never fall,
  and what is left of the way from a piece on is a number that a caller evaluates.
- `spring_envelope`: the response of `spring` is within `1.41 rⁱ`, by
  `Spring.under_response_bound`.
- A step that is interrupted. `resumedFrom` is the easing of a thing that is seen moving when
  its target moves, and `nextOffset` is the one line of arithmetic that a caller writes for it.
  Three things with the consumer's numbers: one whose target goes on (`chased_calm`,
  `chased_bounded`), one whose target turns back while it moves fast, which is not calm, and
  one whose target turns back while it moves slowly (`late_calm`, `late_bounded`, `late_near`).
  `turned_inside` and `apart` are the laws of three pictures at the same numbers: the thing that
  is not calm stays between its three places, and two things keep their gap, each with its own
  momentum.
  The guards beside them are the speed of each thing after the cut: with the consumer's table
  from standing it jumps, and with the resumed easing it does not.

**The controls.** Each is a spring or a thing with numbers where a premise fails and the
conclusion with it: a spring that swings, a critical spring with a rest of more than `1`, one
with `c` less than `0`, a thing that moves toward its target faster than `r` a piece, a thing
that moves away from its new target, and stops that are rounded down.

What this module does not do. It writes no step: `resumedFrom` is an easing, and the plan that
gives it to `settle` of `Plan.resume` is not here. The pieces of the step before and of the
resumed step are of one length here, so a speed in units a piece is the same number in both.

Every guard is a finite evaluation by the compiler, and no theorem. Every theorem of this module
depends on `propext`, `Quot.sound` and `Classical.choice` at most.
-/

namespace WhatwgTest.Html.SvgSpring

open Whatwg.Svg.Scene

/-! ## The consumer's two tables -/

/-- The consumer's critically damped spring, in per mille at every twentieth of the step:
`settleTable` of `tools/Tools/View/Look.lean` of lean4-effect4. -/
def settleTable : List Int :=
  [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992, 995,
    998, 1000]

/-- The consumer's underdamped spring, in per mille at every twentieth of the step:
`springTable` of `tools/Tools/View/Look.lean` of lean4-effect4. -/
def springTable : List Int :=
  [0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045, 1041, 1034, 1026, 1019,
    1012, 1007, 1003, 1000]

/-! ## The two springs -/

/-- **The consumer's `settle` as a spring.** Its comment gives `ω = 7.4` over one step, and a
step has twenty pieces. So `c` is `ωh = 37/100`, and `r` stands for `e^(-37/100)`, which is
`0.69073` to five places. -/
def settle : Spring := Spring.critical (69073 / 100000) (37 / 100)

/-- **The consumer's `spring` as a spring.** Its comment gives `ζ = 0.7` and `ω = 7.5` over one
step. One piece decays by `e^(-0.2625)` and turns by the angle `0.2678`. To five places the
decay is `0.76913`, the cosine of the angle `0.96435`, and `c`, which is the sine times
`ζ / √(1 - ζ²)`, is `0.25937`. -/
def spring : Spring := Spring.under (76913 / 100000) (96435 / 100000) (25937 / 100000)

-- The port: the easing of each spring is the consumer's table, stop for stop.
#guard settle.easing = .stops settleTable
#guard spring.easing = .stops springTable

/-! ## What a spring gives that a table does not -/

/-- **The consumer's `settle` stays in range for every number of pieces.** -/
theorem settle_bounded (pieces : Nat) : (settle.easing pieces).bounded = true :=
  Spring.critical_easing_bounded _ _ (by grind) (by grind) (by grind) pieces

/-- The consumer's `settle` is proper for every number of pieces but none. -/
theorem settle_proper {pieces : Nat} (h : 0 < pieces) : (settle.easing pieces).Proper :=
  Spring.critical_easing_proper _ _ (by grind) (by grind) (by grind) h

/-- The stops of the consumer's `settle` never fall, for every number of pieces. -/
theorem settle_rising (pieces : Nat) :
    ((List.range (pieces + 1)).map (settle.stop 1 settle.rest pieces)).Pairwise (· ≤ ·) :=
  Spring.critical_easing_rising _ _ (by grind) (by grind) (by grind) pieces

/-- **What the premise buys.** A transition with the easing of `settle` reads from `0` to `1000`
at every moment, whatever its delay, its duration and the number of pieces. It is the premise of
the kit's laws of a step. -/
theorem settle_in_range (pieces delay duration t : Nat) :
    0 ≤ ({ delay, duration, ease := settle.easing pieces } : Transition).at t ∧
      ({ delay, duration, ease := settle.easing pieces } : Transition).at t ≤ 1000 :=
  Transition.bounded_at _ t (settle_bounded pieces)

/-- **How near `settle` is, from a piece on**: at most `(1 + 37/100 n) rⁿ` of the way is
left. -/
theorem settle_settled {n i : Nat} (h : n ≤ i) :
    settle.response i ≤ (1 + 37 / 100 * (n : Rat)) * (69073 / 100000) ^ n :=
  Spring.critical_settled _ _ (by grind) (by grind) (by grind) h

-- At the last of twenty pieces less than six thousandths of the way are left. The easing takes
-- them away so as to end at `1000`.
#guard (1 + 37 / 100 * ((20 : Nat) : Rat)) * (69073 / 100000 : Rat) ^ 20 < 6 / 1000
#guard 5 / 1000 < settle.response 20

/-- **The consumer's `spring` swings inside a bound that shrinks**: its response is within
`1.41 rⁱ`. The textbook's bound is `1 / √(1 - ζ²)`, which is `1.4003`. -/
theorem spring_envelope (i : Nat) :
    -(141 / 100 * (76913 / 100000) ^ i) ≤ spring.response i ∧
      spring.response i ≤ 141 / 100 * (76913 / 100000) ^ i :=
  Spring.under_response_bound _ _ _ _ (by grind) (by grind) (by grind) (by grind) i

/-! ## Controls -/

-- A spring that swings passes its end: the consumer's `spring` fails the test, by 45 per mille.
#guard spring.easing.bounded = false
#guard spring.easing.over = 45

-- `Spring.critical_easing_bounded` needs a rest of `1` at most. With `r = 9/10` and `c = 1/5`
-- the rest is `27/25`: one piece after it is let go the thing is further from its target than
-- it was, and the first stop of its easing is `-204`.
#guard (Spring.critical (9 / 10) (1 / 5)).rest = 27 / 25
#guard 1 < (Spring.critical (9 / 10) (1 / 5)).response 1
#guard (Spring.critical (9 / 10) (1 / 5)).stop 1 (27 / 25) 20 1 = -204
#guard (Spring.critical (9 / 10) (1 / 5)).easing.bounded = false

-- `Spring.critical_easing_proper` needs a piece, and a rest of less than `1`. With no piece the
-- easing is one stop, `0`. With `r = 1/2` and `c = 1` the rest is `1`: after one piece the
-- thing has not moved, so an easing of one piece has no way to share out and ends at `0`.
#guard settle.easing 0 = .stops [0]
#guard ¬(settle.easing 0).Proper
#guard (Spring.critical (1 / 2) 1).rest = 1
#guard (Spring.critical (1 / 2) 1).easing 1 = .stops [0, 0]
#guard ¬((Spring.critical (1 / 2) 1).easing 1).Proper

-- It needs `0 ≤ c` too. With `c = -1/5` the response is `(1 - i/5) rⁱ`, which is less than `0`
-- from the sixth piece on: the thing passes its target, and the easing passes its end by 32.
#guard (Spring.critical (7 / 10) (-1 / 5)).response 6 < 0
#guard (Spring.critical (7 / 10) (-1 / 5)).easing.over = 32

-- `Spring.critical_resumed_bounded` needs a calm thing. A thing at the offset `1` that would be
-- at `1/2` one piece later moves toward its target faster than `r = 0.69073` a piece. It passes
-- the target at the fourth piece, and its resumed easing passes its end by 68.
#guard ¬Spring.Calm (69073 / 100000) 1 (1 / 2)
#guard settle.run 1 (1 / 2) 3 > 0 ∧ settle.run 1 (1 / 2) 4 < 0
#guard (settle.resumed 1 (1 / 2)).over = 68

/-- The stops of a spring's easing, rounded down in place of to the nearest. -/
def downStops (s : Spring) (pieces : Nat := 20) : List Int :=
  (List.range (pieces + 1)).map fun i => (1000 * s.share 1 s.rest pieces i).floor

/-- At which stops two tables differ, and by how much. -/
def differences (a b : List Int) : List (Nat × Int) :=
  ((a.zip b).zipIdx.filter fun x => x.1.1 != x.1.2).map fun x => (x.2, x.1.2 - x.1.1)

-- Why `Easing.mille` rounds to the nearest. The consumer's tables are rounded so. Rounded down,
-- the same two springs are one per mille under the consumer's tables at ten stops and at
-- eleven.
#guard differences (downStops settle) settleTable =
  [(1, 1), (2, 1), (4, 1), (5, 1), (6, 1), (8, 1), (12, 1), (13, 1), (15, 1), (17, 1)]
#guard differences (downStops spring) springTable =
  [(1, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (12, 1), (13, 1), (16, 1), (18, 1), (19, 1)]

/-! ## A step that is interrupted

A thing goes from `0` to `400` with the consumer's `settle`, and the kit reads its place in whole
units at each of twenty pieces. At the sixth piece it is seen at `261` and would be at `293` one
piece later: it moves `32` a piece. At the twelfth it is seen at `376` and moves `7` a piece.
Then its target moves. -/

/-- The place of the thing at the piece `i` of the step before, as the kit reads it. -/
def before (i : Nat) : Int := mix 0 400 ((Easing.stops settleTable).at (50 * i))

#guard (List.range 21).map before =
  [0, 21, 68, 122, 175, 222, 261, 293, 319, 339, 355, 367, 376, 383, 388, 392, 394, 396, 398,
    399, 400]

/-- **The next offset of a thing whose target moves.** The thing would be at `next` one piece
later, and its target is now at `target`, `moved` further than it was. The thing keeps its
momentum: its next offset is `next - target` and the first piece of a fresh spring over the way
`moved` (`Spring.moved_next`). -/
def nextOffset (next target moved : Rat) : Rat := next - target + moved * (1 - settle.rest)

/-- **The easing of a thing that is seen moving when its target moves.** The thing is seen at
`seen` and would be at `next` one piece later. -/
def resumedFrom (seen next target moved : Rat) (pieces : Nat := 20) : Easing :=
  settle.resumed (seen - target) (nextOffset next target moved) pieces

/-- The places of a thing from `seen` to `target` with an easing, at each of twenty pieces. -/
def places (seen target : Int) (e : Easing) : List Int :=
  (List.range 21).map fun i => mix seen target (e.at (50 * i))

/-- The number that `nextOffset` is, with the rest of `settle` written out. -/
theorem nextOffset_eq (next target moved : Rat) :
    nextOffset next target moved =
      next - target + moved * (1 - (1 + 37 / 100) * (69073 / 100000)) := rfl

/-! ### The target goes on

The thing is seen at `261` on its way to `400`, and the target moves to `600`. -/

/-- The thing is calm: it is moving toward its new target, and no faster than `r` a piece. -/
theorem chased_calm : Spring.Calm (69073 / 100000) (261 - 600) (nextOffset 293 600 200) := by
  rw [nextOffset_eq]
  exact Or.inr ⟨by grind, by grind, by grind⟩

/-- So its resumed easing stays in range, for every number of pieces, and the kit's laws of a
step hold of it. -/
theorem chased_bounded (pieces : Nat) : (resumedFrom 261 293 600 200 pieces).bounded = true :=
  Spring.critical_resumed_bounded _ _ (by grind) chased_calm pieces

-- The speed. The thing was moving 32 a piece. With the consumer's table from standing it moves
-- 18 in the first piece after the cut: it slows down, though its target went further the same
-- way. With the resumed easing it moves 43: the 32 it had, and the first piece of a fresh spring
-- over the 200 that the target moved, which is 10.74.
#guard before 7 - before 6 = 32
#guard (places 261 600 (.stops settleTable)).take 3 = [261, 279, 318]
#guard (places 261 600 (resumedFrom 261 293 600 200)).take 3 = [261, 304, 352]
#guard (200 : Rat) * (1 - settle.rest) = 1073998 / 100000

/-! ### The target turns back

The target moves from `400` to `100` while the thing is on its way right. -/

-- Early, the thing is not calm, and its resumed easing fails the test: it starts below `0`,
-- since a thing that keeps its speed goes on away from its new target before it turns. With the
-- consumer's table the thing turns at once, from 32 a piece to the right to 9 to the left. With
-- the resumed easing it goes on 15 to the right, and then turns.
#guard ¬Spring.Calm (69073 / 100000) (261 - 100) (nextOffset 293 100 (-300))
#guard (resumedFrom 261 293 100 (-300)).bounded = false
#guard (places 261 100 (.stops settleTable)).take 4 = [261, 252, 233, 211]
#guard (places 261 100 (resumedFrom 261 293 100 (-300))).take 4 = [261, 276, 267, 246]

/-- How far whole places are from exact ones, at most, piece by piece: in thousandths of a unit,
rounded up. -/
def far (reads : List Int) (exact : Nat → Rat) : Int :=
  (reads.zipIdx.map fun x =>
    let read := ((x.1 : Int) : Rat)
    (1000 * (if exact x.2 ≤ read then read - exact x.2 else exact x.2 - read)).ceil).foldl max 0

-- How near that easing is to the spring, where no law of the kit says it. Over the twenty-one
-- stops the kit's whole-number place is within 2.18 units of the place of the run. The last
-- offset of the run is 1.26, which the easing takes away so as to end on the target, and each
-- reading rounds down once.
#guard far (places 261 100 (resumedFrom 261 293 100 (-300)))
  (fun i => 100 + settle.run (261 - 100) (nextOffset 293 100 (-300)) i) = 2171
#guard (1000 * settle.run (261 - 100) (nextOffset 293 100 (-300)) 20).floor = 1260

/-- **The thing that turns back stays between its three places.** It stood at `0`, was let go
toward `400`, and is sent on toward `100`. It goes on to the right for a while after the cut,
and it never leaves the room from `0` to `400`, whenever the cut comes. Its resumed easing
fails the test of an easing in range, and this law does not ask for it. -/
theorem turned_inside (k i : Nat) :
    0 ≤ settle.interrupted 0 400 100 k i ∧ settle.interrupted 0 400 100 k i ≤ 400 :=
  Spring.critical_interrupted_mem _ _ (by grind) (by grind) (by grind) 0 400 _ _ _ (by grind)
    (by grind) (by grind) k i

-- The kit's whole-number places with the resumed easing are within 2.16 units of that exact
-- place, cut at the sixth piece. The easing starts from the whole place 261, and the exact
-- place at the cut is 260.11.
#guard far (places 261 100 (resumedFrom 261 293 100 (-300))) (settle.interrupted 0 400 100 6) =
  2158
#guard (100 * settle.interrupted 0 400 100 6 0).floor = 26011

/-! ### Two things, three pictures

A second thing goes from `16` to `500` and is sent on to `116` at the same cut. The two are `16`
apart in the first picture and in the last, and `100` apart in the second. -/

/-- **The two things keep their gap through the interruption**, whenever the cut comes. Each
takes the momentum it has, so the two have two resumed easings, and the kit's law of one easing
for the kept things does not reach them. This law does. -/
theorem apart (k i : Nat) :
    settle.interrupted 0 400 100 k i + 16 ≤ settle.interrupted 16 500 116 k i :=
  Spring.critical_interrupted_gap _ _ (by grind) (by grind) (by grind) _ _ _ _ _ _ 16
    (by grind) (by grind) (by grind) k i

-- The kit's whole-number places of the two, each with its own resumed easing: the second thing
-- is seen at 332 and would be at 371. Over the twenty-one stops their least gap is 16.
#guard before 6 = 261 ∧ mix 16 500 ((Easing.stops settleTable).at 300) = 332 ∧
  mix 16 500 ((Easing.stops settleTable).at 350) = 371
#guard (((places 261 100 (resumedFrom 261 293 100 (-300))).zip
  (places 332 116 (resumedFrom 332 371 116 (-384)))).map fun x => x.2 - x.1).foldl min 1000 = 16

-- `Spring.critical_interrupted_gap` needs a response that never rises. The consumer's `spring`
-- swings. Cut at its twentieth piece, the same two things are less than 16 apart twelve pieces
-- later: the second thing has passed its place by more than the first has.
#guard ¬(spring.interrupted 0 400 100 20 12 + 16 ≤ spring.interrupted 16 500 116 20 12)

#guard before 12 = 376 ∧ before 13 = 383

/-- Late, the thing moves `7` a piece, which is less than the first piece of the fresh spring,
`16.11`. A target that turns back then leaves the thing calm. -/
theorem late_calm : Spring.Calm (69073 / 100000) (376 - 100) (nextOffset 383 100 (-300)) := by
  rw [nextOffset_eq]
  exact Or.inl ⟨by grind, by grind, by grind⟩

/-- So its resumed easing stays in range, for every number of pieces. -/
theorem late_bounded (pieces : Nat) : (resumedFrom 376 383 100 (-300) pieces).bounded = true :=
  Spring.critical_resumed_bounded _ _ (by grind) late_calm pieces

/-- **How near that easing is to the spring**, by the law: at the stop of each of twenty pieces,
the place read in exact numbers is no more than the last offset of the run and `0.138` below
the place of the run, and no more than `0.138` above it. -/
theorem late_near {i : Nat} (hi : i ≤ 20) :
    100 + settle.run 276 (nextOffset 383 100 (-300)) i -
          settle.run 276 (nextOffset 383 100 (-300)) 20 - 276 / 2000 ≤
        mixExact (100 + 276) 100
          (((settle.stop 276 (nextOffset 383 100 (-300)) 20 i : Int) : Rat) / 1000) ∧
      mixExact (100 + 276) 100
          (((settle.stop 276 (nextOffset 383 100 (-300)) 20 i : Int) : Rat) / 1000) ≤
        100 + settle.run 276 (nextOffset 383 100 (-300)) i + 276 / 2000 := by
  have e := nextOffset_eq 383 100 (-300)
  exact Spring.critical_mixExact_stop_near _ _ (by grind) 100 276 _ (by grind)
    (by rw [e]; grind) (by rw [e]; grind) (by rw [e]; grind) (by decide) hi

-- The last offset of that run, which the law's lower side gives away: 1.52 units.
#guard (1000 * settle.run 276 (nextOffset 383 100 (-300)) 20).floor = 1518

end WhatwgTest.Html.SvgSpring