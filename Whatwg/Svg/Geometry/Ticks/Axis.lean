import Whatwg.Svg.Geometry.Ticks.Laws
import Whatwg.Svg.Scene.Scale

/-!
# Whatwg.Svg.Geometry.Ticks.Axis

Owner: where the ticks of an axis stand (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

The ticks are decimal numbers of the exact layer, and a `Scale` of `Whatwg/Svg/Scene/` counts
in whole numbers of the caller's own unit. This module is where the two meet. The whole-number
layer does not call the exact one: a module there reaches no rational number. A program asks
here for the ticks with their marks, and hands the whole numbers on.

- `Ticks.whole places q`: a number in whole units of `10 ^ -places`, rounded down. A scale
  whose data is in thousandths reads a number with `places` three.
- `Ticks.marks s places start stop count`: the ticks of a range, each with the length that the
  scale `s` gives it. The first of a pair is what an axis writes, and the second where it
  writes it.

What the laws say:

- `whole_of_places`: a tick with no more places than the unit has is read with no rounding.
- `whole_mono`: a greater number is read as no less.
- **The marks of an axis never run backwards** (`marks_rise`): on a scale that rises, along the
  ticks of a range that rises, no mark is less than the one before. Two ticks can share a mark
  where the scale is short, and `Scale.ties` lists them.
- `marks_ticks`: what the marks write is the ticks.

What this module does not claim: a line for the axis, a length for a tick or a place for a
label, which a caller draws; marks on a band scale, whose ticks are its bands
(`Band.mid` of `Whatwg/Svg/Scene/Scale/Band.lean`).
-/

namespace Whatwg.Svg.Value

namespace Ticks

open Whatwg.Svg.Scene (Scale)

/-- **A number in whole units of `10 ^ -places`**, rounded down. -/
def whole (places : Nat) (q : Rat) : Int := (q * (10 : Rat) ^ places).floor

/-- **The ticks of an axis, each with its mark**: the tick as it is written, and the length
that the scale gives its number in whole units of `10 ^ -places`. -/
def marks (s : Scale) (places : Nat) (start stop : Rat) (count : Nat) : List (Decimal × Int) :=
  (ticks start stop count).map fun t => (t, s.at (whole places t.toRat))

/-- A greater number is read as no less. -/
theorem whole_mono (places : Nat) {a b : Rat} (h : a ≤ b) : whole places a ≤ whole places b :=
  Rat.le_floor_iff.mpr (Rat.le_trans (Rat.floor_le _)
    (Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Decimal.ratTen_pow_pos places))))

/-- **A tick with no more places than the unit has is read with no rounding.** -/
theorem whole_of_places (d : Decimal) (places : Nat) (h : -d.exponent ≤ (places : Int)) :
    whole places d.toRat = d.mantissaAt (-(places : Int)) := by
  unfold whole
  rw [Decimal.toRat_eq_div_pow d places h, Rat.div_mul_cancel (Decimal.ratTen_pow_ne places),
    Rat.floor_intCast]

/-- What the marks write is the ticks. -/
theorem marks_ticks (s : Scale) (places : Nat) (start stop : Rat) (count : Nat) :
    (marks s places start stop count).map Prod.fst = ticks start stop count := by
  unfold marks
  rw [List.map_map]
  exact List.map_id' _

/-- **The marks of an axis never run backwards**: on a scale that rises, along the ticks of a
range that rises, no mark is less than the one before. -/
theorem marks_rise (s : Scale) (hr : s.Rising) (places : Nat) {start stop : Rat} (h : start < stop)
    (count : Nat) : ((marks s places start stop count).map Prod.snd).Pairwise (· ≤ ·) := by
  have hv := ticks_rising h count
  unfold values at hv
  rw [List.pairwise_map] at hv
  unfold marks
  rw [List.map_map, List.pairwise_map]
  exact List.Pairwise.imp (fun {a b} hab =>
    Scale.at_mono s hr (whole_mono places (Rat.le_of_lt hab))) hv

end Ticks

/-! ## Finite evaluations -/

-- An axis from nothing to one, with data in thousandths, on two hundred units of length: six
-- ticks, each written with one place, forty units apart.
#guard (Ticks.marks (.linear 0 1000 0 200) 3 0 1 5).map (fun p => (toString p.1, p.2)) ==
  [("0.0", 0), ("0.2", 40), ("0.4", 80), ("0.6", 120), ("0.8", 160), ("1.0", 200)]

-- The same axis down a screen, from the ordinate `200` to the ordinate `0`: a scale that
-- falls. A control of `marks_rise`, which asks for a scale that rises.
#guard (Ticks.marks (.linear 0 1000 200 0) 3 0 1 2).map Prod.snd == [200, 100, 0]

-- A control of `whole_of_places`: a tick with two places read in whole tenths is rounded down.
#guard Ticks.whole 1 (0.98 : Rat) == 9 && Ticks.whole 2 (0.98 : Rat) == 98

-- A short scale: eleven ticks on five units of length share their marks two by two.
#guard (Ticks.marks (.linear 0 10 0 5) 0 0 10 10).map Prod.snd == [0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5]

end Whatwg.Svg.Value
