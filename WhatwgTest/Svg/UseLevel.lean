import Whatwg.Svg.Scene.Scale.Band.Laws
import Whatwg.Svg.Scene.Scale.Linear

/-!
# WhatwgTest.Svg.UseLevel

The "one level" of the living-quantities sketch, drawn on the scales of
`Whatwg/Svg/Scene/Scale/` (slice S22; ask W16 of
`docs/research/2026-10-12-whatwg-requests.md`). The sketch is
`docs/research/2026-10-13-living-quantities/sketch.html`, section 3, "The run is one level":
the Queue scene with a capacity of two over nine steps. The sketch places every number by
hand. Here the same numbers come from two scales and the counts.

**What is drawn, and from what.**

| In the sketch, by hand | Here |
| --- | --- |
| ten bar lines at `70, 148, ..., 772`, one for each moment of nine steps | `beats`, nine bands across the room: `Band.fit 9 70 772`; `moment` |
| the arrows of the commands at `109, 187, ...`, the middle of each beat | `Band.mid beats` |
| zero at the ordinate `150`, the brim of the vessel at `98`, a pressure of one at `72` and a deficit of one at `176` | `level`, a `Scale.linear` from `-1` to `3` down the screen; `Scale.baseline` |
| the knots of the three curves: the held units, the pressure above the brim, the deficit below zero | `knots`, the mark of each count at the bar line of its moment |
| the centres of the units at `137` and `111`, of a waiting offer at `85` and of a waiting taker at `163` | `slots`, one band for each unit of the axis: `Band.fit 4 176 72`; `Band.mid slots` |
| the vessel from the ordinate `98` to the ordinate `150` | from the mark of the capacity to the baseline |

The counts are read from the sketch's own curves, at the ten moments: units held, offers
waiting and takers waiting.

**What the laws say of this picture**, which the sketch cannot say of itself:

- the nine beats tile the room and fill it, with nothing left over (`beats_tile`,
  `beats_fill`), and every beat lies in the room (`beats_inside`);
- **a layer's height at a beat is its value on the scale** (`level_height`): a count `v`
  stands `26 * v` above the baseline, and a deficit below it, with no rounding. It is the law
  that the note asks of W19;
- zero stands at `150` (`level_baseline`), a count is never drawn below it and a deficit never
  above it (`held_above`, `deficit_below`);
- the beat and the slot under a pointer are `Band.invert` (the guards at the foot), and the
  level under an ordinate is `Scale.invert`.

What this module does not draw: the curve through the knots, which is the monotone curve of
`Whatwg/Svg/Geometry/`; the channels of section 2 of the sketch; the hull of the vessel.

The guards are finite evaluations against the sketch's own numbers, each named in the comment
above it, and two controls of a room that is not a multiple of its beats.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UseLevel

open Whatwg.Svg.Scene

/-! ## The run: the Queue scene, capacity two, nine steps -/

/-- The capacity of the queue. -/
def capacity : Int := 2

/-- The units held at each of the ten moments of the run. -/
def held : List Int := [0, 1, 2, 2, 2, 1, 0, 0, 1, 0]

/-- The offers waiting at each moment: one, when the queue is full. -/
def offers : List Int := [0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

/-- The takers waiting at each moment. At the ninth a taker is woken and not yet gone, while a
unit is held: the one moment where one signed level does not say all three counts. -/
def takers : List Int := [0, 0, 0, 0, 0, 0, 0, 1, 1, 0]

/-! ## The two scales -/

/-- **The beats of the run**: nine bands across the room, from `70` to `772`. -/
def beats : Band := Band.fit 9 70 772

/-- **The level**: counts from a deficit of one to a pressure of one above the brim, down the
screen from the ordinate `176` to the ordinate `72`. -/
def level : Scale := .linear (-1) 3 176 72

/-- One slot for each unit of the axis, from the deficit upward. -/
def slots : Band := Band.fit 4 176 72

/-- The bar line of a moment: the left edge of the beat that begins there. -/
def moment (i : Nat) : Int := Band.at beats i

/-- **The knots of a layer**: for each moment, its bar line and the mark of its count. -/
def knots (counts : List Int) : List (Int × Int) :=
  counts.zipIdx.map fun p => (moment p.2, level.at p.1)

/-! ## What the laws say of the picture -/

/-- The nine beats tile: each starts where the one before it ends. -/
theorem beats_tile : Row.Tiles beats.spans := Band.fit_plain_tiles (by decide) rfl 9

/-- The nine beats fill the room, with nothing left over: `702` is nine times `78`. -/
theorem beats_fill : beats.start = 70 ∧ Band.at beats 8 + (beats.width : Int) = 772 :=
  Band.fit_plain_exact (by decide) rfl rfl rfl (by decide) (by decide)

/-- Every beat lies in the room. -/
theorem beats_inside : beats.Inside 70 772 := Band.fit_inside 9 70 772 {}

/-- The level falls: more is drawn higher on the screen. -/
theorem level_falling : level.Falling := by decide

/-- Zero stands at the ordinate `150`. -/
theorem level_baseline : level.baseline = 150 := rfl

/-- **A layer's height at a beat is its value on the scale**: a count `v` stands `26 * v` above
the baseline, and a deficit below it, with no rounding. -/
theorem level_height {v : Int} (h1 : -1 ≤ v) (h2 : v ≤ 3) :
    level.baseline - level.at v = 26 * v := by
  have h := Scale.linear_height (-1) 3 176 72 (-26) (by decide) (by decide) (by decide)
    (by decide) h1 h2
  have h' : level.at v - level.baseline = -26 * v := h
  omega

/-- A count that is not negative is never drawn below the baseline. -/
theorem held_above {v : Int} (h : 0 ≤ v) : level.at v ≤ level.baseline :=
  Scale.at_le_baseline_of_falling level level_falling h

/-- A deficit is never drawn above the baseline. -/
theorem deficit_below {v : Int} (h : v ≤ 0) : level.baseline ≤ level.at v :=
  Scale.baseline_le_at_of_falling level level_falling h

/-! ## Finite evaluations: the sketch's own numbers -/

-- The ten bar lines of the sketch (`<line x1=...>`, ten of them), and the width of a beat.
#guard (List.range 10).map moment == [70, 148, 226, 304, 382, 460, 538, 616, 694, 772]
#guard beats.width == 78 && beats.step == 78
-- The arrows of the eight commands that carry a value, at the middle of their beats. The
-- seventh beat has none: its taker waits.
#guard [0, 1, 2, 3, 4, 5, 7, 8].map (Band.mid beats) == [109, 187, 265, 343, 421, 499, 655, 733]

-- The level: the deficit, zero, one unit, the brim and the pressure, as the sketch has them.
#guard [-1, 0, 1, capacity, capacity + 1].map level.at == [176, 150, 124, 98, 72]
-- The vessel of the sketch is `52` high, from the brim to the baseline.
#guard level.baseline - level.at capacity == 52

-- The knots of the filled area: the units held (the first `path` of the sketch's figure).
#guard knots held == [(70, 150), (148, 124), (226, 98), (304, 98), (382, 98), (460, 124),
  (538, 150), (616, 150), (694, 124), (772, 150)]
-- The knots of the pressure above the brim (the second `path`): the brim, and one offer waiting
-- at the fourth moment.
#guard (knots (offers.map (capacity + ·))).map Prod.snd ==
  [98, 98, 98, 72, 98, 98, 98, 98, 98, 98]
-- The knots of the deficit below zero (the third `path`): one taker waiting at the eighth and
-- the ninth moment.
#guard (knots (takers.map (- ·))).map Prod.snd ==
  [150, 150, 150, 150, 150, 150, 150, 176, 176, 150]

-- The slots: a waiting taker at `163`, the two units at `137` and `111`, a waiting offer at
-- `85` (the centres of the sketch's circles and boxes).
#guard [0, 1, 2, 3].map (Band.mid slots) == [163, 137, 111, 85]

-- The way back. The beat under a pointer, the slot under a pointer, and the level under an
-- ordinate: on this scale every mark gives back its count.
#guard [70, 300, 771, 772, 69].map beats.invert == [some 0, some 2, some 8, none, none]
#guard [163, 137, 111, 85].map slots.invert == [some 0, some 1, some 2, some 3]
#guard [176, 150, 124, 98, 72].map level.invert == [-1, 0, 1, 2, 3]
-- Between two marks the ordinate answers the count whose mark is the nearest above it on the
-- screen: the law of a falling scale.
#guard [149, 125, 124, 123].map level.invert == [1, 1, 1, 2]

-- Controls: a room that is not a multiple of its beats. Nine beats in a room of `700` are `77`
-- wide and leave `7` over: `4` before the first and `3` after the last. In a room of `701`
-- they leave `8`: `4` and `4`.
#guard (Band.fit 9 70 770).width == 77 && (Band.fit 9 70 770).start == 74 &&
  Band.at (Band.fit 9 70 770) 8 + 77 == 767
#guard (Band.fit 9 70 771).start == 74 && Band.at (Band.fit 9 70 771) 8 + 77 == 767

end WhatwgTest.Svg.UseLevel
