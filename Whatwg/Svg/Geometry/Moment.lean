import Whatwg.Svg.Geometry.Easing
import Whatwg.Svg.Scene.Between
import Whatwg.Svg.Scene.Motion.Laws

/-!
# Whatwg.Svg.Geometry.Moment

Owner: a motion at every time, in exact numbers (slice S15 of `docs/SVG-PACKAGE-PLAN.md`; ruling
SV-82).

`Whatwg/Svg/Scene/Motion.lean` reads a motion in whole numbers. A moment is a whole thousandth
of a step, and every reading rounds down once. `Whatwg/Svg/Scene/Between.lean` proves that a gap
of both pictures is a gap at every such moment. A browser draws the times between two
thousandths too, and it does not round to a thousandth. This module says the same things in
exact rational numbers at every rational time, and it says how far the whole-number reading is
from the exact one.

- The exact readings. `Easing.exact` is the eased progress at an exact progress, with `1` for
  the whole. For a cubic it is the polynomial `Easing.cubicExact` of
  `Whatwg/Svg/Geometry/Easing.lean`, and for stops the straight line between two stops
  (`Easing.stopsExact`). `Transition.exact` is the eased progress of a transition at a rational
  time, with the three branches of `Transition.at`. `mixExact u v e` is the value the share `e`
  of the way from `u` to `v`. It is each coordinate of `Vec.lerp` (`lerp_eq_mixExact`).
- The whole-number reading is the exact one, rounded down: an easing at a share
  (`Easing.of_eq_floor`), an easing in per mille (`Easing.at_eq_floor`), a transition at a whole
  moment (`Transition.at_eq_floor`) and a mix (`mix_eq_floor_exact`). No law of the four has a
  premise. A denominator of zero and a duration of zero read the same on both sides.
- The two ends. At the progress `0` and at `1` nothing is rounded (`Easing.exact_zero`,
  `Easing.exact_one`), so a proper easing reads `0` and `1` there (`Easing.exact_proper`). A
  transition reads the start of its easing up to its delay (`Transition.exact_before`), the end
  from its end on (`Transition.exact_done`), and between the two its easing at the share of its
  duration that has passed (`Transition.exact_between`).
- In range. An easing that passes the test `Easing.bounded` reads from `0` to `1` at every
  exact progress from `0` to `1` (`Easing.exact_mem`). A transition with such an easing reads
  from `0` to `1` at every rational time (`Transition.exact_mem`). An easing goes past its end
  by `Easing.over` at most (`Easing.exact_le_over`, `Transition.exact_le_over`).
- Mixing. A gap at both ends is a gap at every share in range (`mixExact_gap`), and a strict
  gap is a strict one (`mixExact_gap_lt`). A bound at both ends is a bound on the way
  (`mixExact_le`, `le_mixExact`, `mixExact_mem`). A fixed step at both ends is that step at
  every share (`mixExact_add_right`).
- **The law of the module** is `Transition.exact_gap`. Two values take one transition, and its
  easing passes the test. They keep at every rational time each gap that both pictures have.
  `KeptExact R` says that every share of the way between two pictures that have `R` has `R`,
  over the points of the kit. "Left of", "above" and "the fixed step from" are kept. So is a gap
  along any direction (`KeptExact.along`), which whole numbers lose off the two axes.
  `KeptExact.moment` is the law for a kept relation at every rational time.
- How near. With `x` the exact value at a whole moment on the way from `u` to `v`, the
  whole-number reading is more than `x - 1 - max (v - u) 0 / 1000` and no more than
  `x + max (u - v) 0 / 1000` (`Transition.mix_near`). Two roundings down make the distance.

The motion proof graph has the open item "a moment is a whole thousandth of a step". These are
the laws it asks for: what `Between.lean` says of a gap, a bound and a kept relation at the
whole moments holds at every rational time between them.

What this module does not claim. A time is a rational number here, and no law speaks of a
limit. A browser computes in floating point, and what it draws is an observation of that host:
the laws are of the exact reading. `Easing.bounded` is a test that suffices, as in
`Between.lean`. `Transition.mix_near` is a law of one value. It says nothing of a change of
shape between two lists of different lengths, which jumps at the middle. The spans that grow
past their size (`grow_apart` of `Between.lean`) have no exact form here.


Every law here depends on `propext`, `Quot.sound` and `Classical.choice` at most.
-/

namespace Whatwg.Svg.Value

/-- What is left of a count after a smaller count is, as a rational number, the difference of
the two. -/
theorem rat_natCast_sub {m n : Nat} (h : m ≤ n) :
    ((n - m : Nat) : Rat) = (n : Rat) - (m : Rat) := by
  rw [← Rat.intCast_natCast, Int.natCast_sub h, Rat.intCast_sub, Rat.intCast_natCast,
    Rat.intCast_natCast]

/-- What is left of a number that is not negative after the count of its floor is from `0` to
`1`, and never `1`. -/
theorem rat_sub_floor_toNat_mem {x : Rat} (h : 0 ≤ x) :
    0 ≤ x - ((x.floor.toNat : Nat) : Rat) ∧ x - ((x.floor.toNat : Nat) : Rat) < 1 := by
  have hf : 0 ≤ x.floor := Rat.le_floor_iff.mpr h
  have e : ((x.floor.toNat : Nat) : Rat) = (x.floor : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hf]
  have h1 := Rat.floor_le x
  have h2 := Rat.lt_floor_add_one x
  simp only [Rat.intCast_add, Rat.intCast_ofNat] at h2
  rw [e]
  constructor <;> grind

/-- A thousand times a thousandth of a number is the number. -/
theorem rat_thousand_mul_div (x : Rat) : 1000 * (x / 1000) = x := by grind

/-- A share of no count is `0`: a quotient by zero is `0`. -/
theorem rat_div_natCast_zero (x : Rat) : x / ((0 : Nat) : Rat) = 0 := by
  show x / 0 = 0
  rw [Rat.div_def, Rat.inv_zero, Rat.mul_zero]

/-- A part of a whole that is more than zero is a share of it from `0` to `1`. -/
theorem rat_div_mem {x d : Rat} (hd : 0 < d) (h0 : 0 ≤ x) (h1 : x ≤ d) :
    0 ≤ x / d ∧ x / d ≤ 1 := by
  have hne : d ≠ 0 := Rat.ne_of_gt hd
  have a := Decimal.rat_div_le_div hd h0
  have b := Decimal.rat_div_le_div hd h1
  have e0 : (0 : Rat) / d = 0 := by grind
  have e1 : d / d = 1 := by grind
  rw [e0] at a
  rw [e1] at b
  exact ⟨a, b⟩

end Whatwg.Svg.Value

namespace Whatwg.Svg.Scene

open Whatwg.Svg.Value

/-! ## The exact readings -/

/-- The straight lines between `values` at evenly spaced stops, at the exact progress `s`: the
whole is `1`. It is `Easing.stopsOf` with nothing rounded. Past the last stop it is the last
value, and no value reads as `0`. -/
def Easing.stopsExact (values : List Int) (s : Rat) : Rat :=
  let pieces := values.length - 1
  let last := values.getLast?.getD 0
  let i := (s * (pieces : Rat)).floor.toNat
  let a := values.getD i last
  let b := values.getD (i + 1) last
  ((a : Rat) + ((b : Rat) - (a : Rat)) * (s * (pieces : Rat) - (i : Rat))) / 1000

/-- The eased progress at the exact progress `s`: the whole is `1`. -/
def Easing.exact : Easing → Rat → Rat
  | .stops values, s => Easing.stopsExact values s
  | .cubic y1 y2, s => Easing.cubicExact y1 y2 s

/-- The eased progress of a transition at the exact time `τ`. The time is in thousandths of
the step, as a moment is, and the whole of the progress is `1`. The branches are those of
`Transition.at`: the end comes first, so a transition with a duration of zero reads its end
from its delay on. -/
def Transition.exact (tr : Transition) (τ : Rat) : Rat :=
  if ((tr.delay + tr.duration : Nat) : Rat) ≤ τ then tr.ease.exact 1
  else if τ ≤ (tr.delay : Rat) then tr.ease.exact 0
  else tr.ease.exact ((τ - (tr.delay : Rat)) / (tr.duration : Rat))

/-- The value the share `e` of the way from `u` to `v`, in exact numbers: `u` at `0` and `v` at
`1`. A share outside that range goes beyond them. -/
def mixExact (u v e : Rat) : Rat := u + (v - u) * e

/-! ## Mixing in exact numbers -/

/-- At the start of the way the mixed value is the first one. -/
theorem mixExact_zero (u v : Rat) : mixExact u v 0 = u := by
  simp only [mixExact]
  grind

/-- At the end of the way the mixed value is the second one. -/
theorem mixExact_one (u v : Rat) : mixExact u v 1 = v := by
  simp only [mixExact]
  grind

/-- A value mixed with itself is that value, at every share. -/
theorem mixExact_self (u e : Rat) : mixExact u u e = u := by
  simp only [mixExact]
  grind

/-- A thing that grows from nothing to its whole size has the share as its size. -/
theorem mixExact_grow (e : Rat) : mixExact 0 1 e = e := by
  simp only [mixExact]
  grind

/-- **A fixed step at both ends is that step at every share**, in range or not. -/
theorem mixExact_add_right (u v c e : Rat) : mixExact (u + c) (v + c) e = mixExact u v e + c := by
  simp only [mixExact]
  grind

/-- **A gap at both ends is a gap at every share in range.** Where the second value is `g` or
more past the first at both ends, it is `g` or more past it at every share from `0` to `1`. A
negative `g` is an overlap, and it never grows.

The mixed value is `u` times `1 - e` and `v` times `e`. Neither weight is negative, and they
sum to `1`. Both premises on `e` are needed, as for `mix_gap`. -/
theorem mixExact_gap (u₁ v₁ u₂ v₂ g e : Rat) (h0 : 0 ≤ e) (h1 : e ≤ 1) (hu : u₁ + g ≤ u₂)
    (hv : v₁ + g ≤ v₂) : mixExact u₁ v₁ e + g ≤ mixExact u₂ v₂ e := by
  have p : 0 ≤ (u₂ - u₁ - g) * (1 - e) := Rat.mul_nonneg (by grind) (by grind)
  have q : 0 ≤ (v₂ - v₁ - g) * e := Rat.mul_nonneg (by grind) h0
  simp only [mixExact]
  grind

/-- **A strict gap at both ends is a strict gap at every share in range.** Two things that do
not touch at either end do not touch on the way. Whole numbers say this with a gap of `1`. -/
theorem mixExact_gap_lt (u₁ v₁ u₂ v₂ g e : Rat) (h0 : 0 ≤ e) (h1 : e ≤ 1) (hu : u₁ + g < u₂)
    (hv : v₁ + g < v₂) : mixExact u₁ v₁ e + g < mixExact u₂ v₂ e := by
  have p : 0 ≤ (u₂ - u₁ - g) * (1 - e) := Rat.mul_nonneg (by grind) (by grind)
  rcases Rat.le_iff_lt_or_eq.mp h0 with h | h
  · have q : 0 < (v₂ - v₁ - g) * e := Rat.mul_pos (by grind) h
    simp only [mixExact]
    grind
  · subst h
    simp only [mixExact]
    grind

/-- A value that is no more than `hi` at both ends is no more than `hi` on the way. -/
theorem mixExact_le (hi u v e : Rat) (h0 : 0 ≤ e) (h1 : e ≤ 1) (hu : u ≤ hi) (hv : v ≤ hi) :
    mixExact u v e ≤ hi := by
  have h := mixExact_gap u v hi hi 0 e h0 h1 (by grind) (by grind)
  rw [mixExact_self, Rat.add_zero] at h
  exact h

/-- A value that is no less than `lo` at both ends is no less than `lo` on the way. -/
theorem le_mixExact (lo u v e : Rat) (h0 : 0 ≤ e) (h1 : e ≤ 1) (hu : lo ≤ u) (hv : lo ≤ v) :
    lo ≤ mixExact u v e := by
  have h := mixExact_gap lo lo u v 0 e h0 h1 (by grind) (by grind)
  rw [mixExact_self, Rat.add_zero] at h
  exact h

/-- **A value between `lo` and `hi` at both ends is between them on the way.** A thing inside a
room in both pictures does not leave it. -/
theorem mixExact_mem (lo hi u v e : Rat) (h0 : 0 ≤ e) (h1 : e ≤ 1) (hu : lo ≤ u ∧ u ≤ hi)
    (hv : lo ≤ v ∧ v ≤ hi) : lo ≤ mixExact u v e ∧ mixExact u v e ≤ hi :=
  ⟨le_mixExact lo u v e h0 h1 hu.1 hv.1, mixExact_le hi u v e h0 h1 hu.2 hv.2⟩

/-- The step of the kit between two points is the mix of each coordinate. -/
theorem lerp_eq_mixExact (a b : Vec) (e : Rat) :
    a.lerp b e = ⟨mixExact a.x b.x e, mixExact a.y b.y e⟩ :=
  Vec.ext (congrArg (a.x + ·) (Rat.mul_comm _ _)) (congrArg (a.y + ·) (Rat.mul_comm _ _))

/-- **The whole-number `mix` is the exact mix, rounded down**: at `e` per mille it is the floor
of the exact value at the share `e / 1000`. -/
theorem mix_eq_floor_exact (u v e : Int) :
    mix u v e = (mixExact (u : Rat) (v : Rat) ((e : Rat) / 1000)).floor := by
  rw [mix_eq_floor]
  congr 1
  simp only [mixExact]
  grind

/-! ## Easings in exact numbers -/

namespace Easing

/-- Stops at the exact progress `s`, with a name for the piece that `s` falls in: the count of
the floor of `s` times the number of pieces. -/
theorem stopsExact_piece (values : List Int) (s : Rat) (i : Nat)
    (hi : (s * ((values.length - 1 : Nat) : Rat)).floor.toNat = i) :
    stopsExact values s =
      (((values.getD i (values.getLast?.getD 0) : Int) : Rat) +
        (((values.getD (i + 1) (values.getLast?.getD 0) : Int) : Rat) -
            ((values.getD i (values.getLast?.getD 0) : Int) : Rat)) *
          (s * ((values.length - 1 : Nat) : Rat) - (i : Rat))) / 1000 := by
  subst hi
  rfl

/-- At the start stops read their first value over a thousand, and `0` where there is no
value. -/
theorem stopsExact_zero (values : List Int) :
    stopsExact values 0 = ((values.getD 0 (values.getLast?.getD 0) : Int) : Rat) / 1000 := by
  have hi : ((0 : Rat) * ((values.length - 1 : Nat) : Rat)).floor.toNat = 0 := by
    rw [Rat.zero_mul]
    rfl
  have z : ((0 : Nat) : Rat) = 0 := rfl
  rw [stopsExact_piece values 0 0 hi, z]
  generalize ((values.getD 0 (values.getLast?.getD 0) : Int) : Rat) = a
  generalize ((values.getD (0 + 1) (values.getLast?.getD 0) : Int) : Rat) = b
  grind

/-- The first value of stops, over a thousand, is their exact reading at the start. -/
theorem stopsExact_first (v : Int) (rest : List Int) :
    stopsExact (v :: rest) 0 = (v : Rat) / 1000 :=
  stopsExact_zero (v :: rest)

/-- At the end stops read their last value over a thousand, and `0` where there is no value. -/
theorem stopsExact_one (values : List Int) :
    stopsExact values 1 = ((values.getLast?.getD 0 : Int) : Rat) / 1000 := by
  have hi : ((1 : Rat) * ((values.length - 1 : Nat) : Rat)).floor.toNat = values.length - 1 := by
    rw [Rat.one_mul, ← Rat.intCast_natCast, Rat.floor_intCast, Int.toNat_natCast]
  rw [stopsExact_piece values 1 _ hi, getD_last]
  generalize ((values.getLast?.getD 0 : Int) : Rat) = a
  generalize ((values.getD (values.length - 1 + 1) (values.getLast?.getD 0) : Int) : Rat) = b
  grind

/-! ### The whole-number reading is the exact one, rounded down -/

/-- With the denominator `0` stops read their first value: every division gives `0`. -/
theorem stopsOf_den_zero (values : List Int) (num : Nat) :
    stopsOf values num 0 = values.getD 0 (values.getLast?.getD 0) := by
  show values.getD (num * (values.length - 1) / 0) (values.getLast?.getD 0) +
    (values.getD (num * (values.length - 1) / 0 + 1) (values.getLast?.getD 0) -
      values.getD (num * (values.length - 1) / 0) (values.getLast?.getD 0)) *
      ((num * (values.length - 1) - 0 * (num * (values.length - 1) / 0) : Nat) : Int) /
        ((0 : Nat) : Int) =
    values.getD 0 (values.getLast?.getD 0)
  rw [Nat.div_zero, Int.natCast_zero, Int.ediv_zero, Int.add_zero]

/-- With the denominator `0` a cubic reads `0`: its one division gives `0`. -/
theorem cubicOf_den_zero (y1 y2 : Int) (num : Nat) : cubicOf y1 y2 num 0 = 0 := by
  have h : ((0 : Nat) : Int) ^ 3 = 0 := rfl
  show (3 * y1 * (num : Int) * (((0 : Nat) : Int) - (num : Int)) ^ 2 +
    3 * y2 * (num : Int) ^ 2 * (((0 : Nat) : Int) - (num : Int)) + 1000 * (num : Int) ^ 3) /
      ((0 : Nat) : Int) ^ 3 = 0
  rw [h, Int.ediv_zero]

/-- **The reading of stops at a share is the exact one, rounded down**: the floor of a
thousand times the straight line at the share `num / den`. It has no premise on the
denominator: with `0` both sides read the first value. -/
theorem stopsOf_eq_floor_exact (values : List Int) (num den : Nat) :
    stopsOf values num den =
      (1000 * stopsExact values ((num : Rat) / (den : Rat))).floor := by
  rcases Nat.eq_zero_or_pos den with hd | hd
  · subst hd
    rw [stopsOf_den_zero, rat_div_natCast_zero, stopsExact_zero, rat_thousand_mul_div,
      Rat.floor_intCast]
  · have hD : (den : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hd)
    have hi : ((num : Rat) / (den : Rat) * ((values.length - 1 : Nat) : Rat)).floor.toNat =
        num * (values.length - 1) / den := by
      have e : (num : Rat) / (den : Rat) * ((values.length - 1 : Nat) : Rat) =
          (((num * (values.length - 1) : Nat) : Int) : Rat) / (((den : Nat) : Int) : Rat) := by
        rw [Rat.intCast_natCast, Rat.intCast_natCast, Rat.natCast_mul]
        grind
      rw [e, rat_floor_intCast_div _ (Int.natCast_pos.mpr hd), ← Int.natCast_ediv,
        Int.toNat_natCast]
    have hn :
        ((num * (values.length - 1) - den * (num * (values.length - 1) / den) : Nat) : Rat) +
          (den : Rat) * ((num * (values.length - 1) / den : Nat) : Rat) =
        (num : Rat) * ((values.length - 1 : Nat) : Rat) := by
      rw [← Rat.natCast_mul den, ← Rat.natCast_add, Nat.sub_add_cancel (Nat.mul_div_le _ _),
        Rat.natCast_mul]
    rw [stopsOf_eq_floor values num den hd, stopsExact_piece values _ _ hi]
    congr 1
    generalize ((values.getD (num * (values.length - 1) / den) (values.getLast?.getD 0) : Int) :
      Rat) = a
    generalize ((values.getD (num * (values.length - 1) / den + 1) (values.getLast?.getD 0) :
      Int) : Rat) = b
    generalize ((num * (values.length - 1) - den * (num * (values.length - 1) / den) : Nat) :
      Rat) = n at hn ⊢
    generalize ((num * (values.length - 1) / den : Nat) : Rat) = i at hn ⊢
    generalize ((values.length - 1 : Nat) : Rat) = p at hn ⊢
    generalize (num : Rat) = N at hn ⊢
    generalize (den : Rat) = d at hD hn ⊢
    grind

/-- **The reading of a cubic at a share is the exact one, rounded down**, with no premise on
the denominator: with `0` both sides are `0`. -/
theorem cubicOf_eq_floor_exact (y1 y2 : Int) (num den : Nat) :
    cubicOf y1 y2 num den = (1000 * cubicExact y1 y2 ((num : Rat) / (den : Rat))).floor := by
  rcases Nat.eq_zero_or_pos den with hd | hd
  · subst hd
    rw [cubicOf_den_zero, rat_div_natCast_zero, cubicExact_zero, Rat.mul_zero]
    rfl
  · exact cubicOf_eq_floor y1 y2 num den hd

/-- **The reading of an easing at a share is the exact one, rounded down**: `e.of num den` is
the floor of a thousand times the exact eased progress at `num / den`. It holds for every
denominator. -/
theorem of_eq_floor (e : Easing) (num den : Nat) :
    e.of num den = (1000 * e.exact ((num : Rat) / (den : Rat))).floor := by
  cases e with
  | stops values => exact stopsOf_eq_floor_exact values num den
  | cubic y1 y2 => exact cubicOf_eq_floor_exact y1 y2 num den

/-- **The reading of an easing in per mille is the exact one, rounded down.** -/
theorem at_eq_floor (e : Easing) (p : Nat) :
    e.at p = (1000 * e.exact ((p : Rat) / 1000)).floor := by
  rw [← of_thousand, of_eq_floor]
  rfl

/-! ### The two ends -/

/-- **At the start the exact reading is the whole-number one**, as a share of the whole:
nothing is rounded there. For a cubic it is `0`, and for stops the first value over a
thousand. -/
theorem exact_zero (e : Easing) : e.exact 0 = ((e.at 0 : Int) : Rat) / 1000 := by
  cases e with
  | stops values =>
    show stopsExact values 0 = ((stopsAt values 0 : Int) : Rat) / 1000
    rw [stopsAt_on values 0 0 (Nat.zero_mul _)]
    exact stopsExact_zero values
  | cubic y1 y2 =>
    show cubicExact y1 y2 0 = ((cubicAt y1 y2 0 : Int) : Rat) / 1000
    rw [cubicExact_zero, cubicAt_zero]
    show (0 : Rat) = 0 / 1000
    grind

/-- **At the end the exact reading is the whole-number one**, as a share of the whole. For a
cubic it is `1`, and for stops the last value over a thousand. -/
theorem exact_one (e : Easing) : e.exact 1 = ((e.at 1000 : Int) : Rat) / 1000 := by
  cases e with
  | stops values =>
    show stopsExact values 1 = ((stopsAt values 1000 : Int) : Rat) / 1000
    rw [stopsAt_end]
    exact stopsExact_one values
  | cubic y1 y2 =>
    show cubicExact y1 y2 1 = ((cubicAt y1 y2 1000 : Int) : Rat) / 1000
    rw [cubicExact_one, cubicAt_end]
    show (1 : Rat) = 1000 / 1000
    grind

end Easing

/-- No per mille is no share. -/
private theorem mille_zero : ((0 : Int) : Rat) / 1000 = 0 := by
  show (0 : Rat) / 1000 = 0
  grind

/-- A thousand per mille is the whole. -/
private theorem mille_one : ((1000 : Int) : Rat) / 1000 = 1 := by
  show (1000 : Rat) / 1000 = 1
  grind

/-- **A proper easing starts at nothing and ends at the whole, in exact numbers.** Every cubic
is proper (`Easing.proper_cubic`). -/
theorem Easing.exact_proper (e : Easing) (h : e.Proper) : e.exact 0 = 0 ∧ e.exact 1 = 1 := by
  rw [Easing.exact_zero, Easing.exact_one, h.1, h.2]
  exact ⟨mille_zero, mille_one⟩

/-! ## Easings that stay in range, in exact numbers -/


/-- Per mille in order are shares in order. -/
private theorem mille_le {a b : Int} (h : a ≤ b) : (a : Rat) / 1000 ≤ (b : Rat) / 1000 :=
  Decimal.rat_div_le_div (by decide) (Rat.intCast_le_intCast.mpr h)

/-- The whole and what a number of per mille is past a thousand are that number as a share. -/
private theorem over_eq (m : Int) (h : 1000 ≤ m) :
    (1 : Rat) + (((m - 1000).toNat : Nat) : Rat) / 1000 = (m : Rat) / 1000 := by
  rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (Int.sub_nonneg_of_le h), Rat.intCast_sub,
    Rat.intCast_ofNat]
  grind

/-- The four weights of a cubic at a progress from `0` to `1` are not negative: `(1 - s)³`,
`s (1 - s)²`, `s² (1 - s)` and `s³`. -/
private theorem weights_nonneg (s : Rat) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ (1 - s) * (1 - s) * (1 - s) ∧ 0 ≤ s * (1 - s) * (1 - s) ∧ 0 ≤ s * s * (1 - s) ∧
      0 ≤ s * s * s := by
  have hr : 0 ≤ 1 - s := by grind
  exact ⟨Rat.mul_nonneg (Rat.mul_nonneg hr hr) hr, Rat.mul_nonneg (Rat.mul_nonneg hs0 hr) hr,
    Rat.mul_nonneg (Rat.mul_nonneg hs0 hs0) hr, Rat.mul_nonneg (Rat.mul_nonneg hs0 hs0) hs0⟩

namespace Easing

/-- **Stops read no more than what `0` and every value are no more than**, at every exact
progress that is not negative. The reading is a point of the straight line between two values,
and a missing value reads as `0`. Past the last stop it is the last value, so the progress has
no upper bound here. -/
theorem stopsExact_le (hi : Int) (values : List Int) (s : Rat) (hhi : 0 ≤ hi)
    (h : ∀ v ∈ values, v ≤ hi) (hs : 0 ≤ s) : stopsExact values s ≤ (hi : Rat) / 1000 := by
  have hlast : values.getLast?.getD 0 ≤ hi := last_of_all (· ≤ hi) values 0 hhi h
  have hget : ∀ i, values.getD i (values.getLast?.getD 0) ≤ hi := fun i =>
    getD_of_all (· ≤ hi) values i _ hlast h
  have hf := rat_sub_floor_toNat_mem
    (Rat.mul_nonneg hs (Rat.natCast_nonneg (a := values.length - 1)))
  have m := mixExact_le (hi : Rat) _ _ _ hf.1 (Rat.le_of_lt hf.2)
    (Rat.intCast_le_intCast.mpr (hget (s * ((values.length - 1 : Nat) : Rat)).floor.toNat))
    (Rat.intCast_le_intCast.mpr (hget ((s * ((values.length - 1 : Nat) : Rat)).floor.toNat + 1)))
  rw [stopsExact_piece values s _ rfl]
  exact Decimal.rat_div_le_div (by decide) m

/-- **Stops read no less than what `0` and every value are no less than**, at every exact
progress that is not negative. -/
theorem le_stopsExact (lo : Int) (values : List Int) (s : Rat) (hlo : lo ≤ 0)
    (h : ∀ v ∈ values, lo ≤ v) (hs : 0 ≤ s) : (lo : Rat) / 1000 ≤ stopsExact values s := by
  have hlast : lo ≤ values.getLast?.getD 0 := last_of_all (lo ≤ ·) values 0 hlo h
  have hget : ∀ i, lo ≤ values.getD i (values.getLast?.getD 0) := fun i =>
    getD_of_all (lo ≤ ·) values i _ hlast h
  have hf := rat_sub_floor_toNat_mem
    (Rat.mul_nonneg hs (Rat.natCast_nonneg (a := values.length - 1)))
  have m := le_mixExact (lo : Rat) _ _ _ hf.1 (Rat.le_of_lt hf.2)
    (Rat.intCast_le_intCast.mpr (hget (s * ((values.length - 1 : Nat) : Rat)).floor.toNat))
    (Rat.intCast_le_intCast.mpr (hget ((s * ((values.length - 1 : Nat) : Rat)).floor.toNat + 1)))
  rw [stopsExact_piece values s _ rfl]
  exact Decimal.rat_div_le_div (by decide) m

/-- **A cubic reads no more than what `1` and its two heights are no more than**, at every
exact progress from `0` to `1`. It shares `0`, its two heights and `1` by the four weights
`(1 - s)³`, `3 s (1 - s)²`, `3 s² (1 - s)` and `s³`. No weight is negative, and they sum to
`1`. -/
theorem cubicExact_le (hi : Rat) (y1 y2 : Int) (s : Rat) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hhi : 1 ≤ hi) (h1 : (y1 : Rat) / 1000 ≤ hi) (h2 : (y2 : Rat) / 1000 ≤ hi) :
    cubicExact y1 y2 s ≤ hi := by
  obtain ⟨w0, w1, w2, w3⟩ := weights_nonneg s hs0 hs1
  simp only [cubicExact]
  generalize (y1 : Rat) / 1000 = a at h1 ⊢
  generalize (y2 : Rat) / 1000 = b at h2 ⊢
  have p0 := Rat.mul_nonneg (show 0 ≤ hi - 0 by grind) w0
  have p1 := Rat.mul_nonneg (show 0 ≤ hi - a by grind) w1
  have p2 := Rat.mul_nonneg (show 0 ≤ hi - b by grind) w2
  have p3 := Rat.mul_nonneg (show 0 ≤ hi - 1 by grind) w3
  grind

/-- **A cubic reads no less than what `0` and its two heights are no less than**, at every
exact progress from `0` to `1`. -/
theorem le_cubicExact (lo : Rat) (y1 y2 : Int) (s : Rat) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hlo : lo ≤ 0) (h1 : lo ≤ (y1 : Rat) / 1000) (h2 : lo ≤ (y2 : Rat) / 1000) :
    lo ≤ cubicExact y1 y2 s := by
  obtain ⟨w0, w1, w2, w3⟩ := weights_nonneg s hs0 hs1
  simp only [cubicExact]
  generalize (y1 : Rat) / 1000 = a at h1 ⊢
  generalize (y2 : Rat) / 1000 = b at h2 ⊢
  have p0 := Rat.mul_nonneg (show 0 ≤ 0 - lo by grind) w0
  have p1 := Rat.mul_nonneg (show 0 ≤ a - lo by grind) w1
  have p2 := Rat.mul_nonneg (show 0 ≤ b - lo by grind) w2
  have p3 := Rat.mul_nonneg (show 0 ≤ 1 - lo by grind) w3
  grind

/-- **An easing that passes the test stays in range at every exact progress** from `0` to `1`.
It is `Easing.bounded_of` in exact numbers: at every rational share, and not at the shares of
whole numbers only. Stops ask for `0 ≤ s` alone, and a cubic for both bounds, as the controls
of this file show. -/
theorem exact_mem (e : Easing) (s : Rat) (h : e.bounded = true) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    0 ≤ e.exact s ∧ e.exact s ≤ 1 := by
  cases e with
  | stops values =>
    have hv : ∀ v ∈ values, (0 : Int) ≤ v ∧ v ≤ 1000 := fun v hm => by
      have hb := List.all_eq_true.mp h v hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact hb
    have lo := le_stopsExact 0 values s (Int.le_refl 0) (fun v hm => (hv v hm).1) h0
    have hi := stopsExact_le 1000 values s (by decide) (fun v hm => (hv v hm).2) h0
    rw [mille_zero] at lo
    rw [mille_one] at hi
    exact ⟨lo, hi⟩
  | cubic y1 y2 =>
    simp only [bounded, Bool.and_eq_true, decide_eq_true_eq] at h
    have a0 := mille_le h.1.1.1
    have a1 := mille_le h.1.1.2
    have b0 := mille_le h.1.2
    have b1 := mille_le h.2
    rw [mille_zero] at a0 b0
    rw [mille_one] at a1 b1
    exact ⟨le_cubicExact 0 y1 y2 s h0 h1 Rat.le_refl a0 b0,
      cubicExact_le 1 y1 y2 s h0 h1 Rat.le_refl a1 b1⟩

/-- **An easing goes past its end by `over` at most, at every exact progress** from `0` to
`1`: `Easing.of_le_over` in exact numbers. A size that takes the easing is no more than
`1 + over / 1000` of itself at every time. -/
theorem exact_le_over (e : Easing) (s : Rat) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    e.exact s ≤ 1 + (e.over : Rat) / 1000 := by
  cases e with
  | stops values =>
    obtain ⟨hm, hall⟩ := le_foldl_max values 1000
    show stopsExact values s ≤ 1 + (((values.foldl max 1000 - 1000).toNat : Nat) : Rat) / 1000
    rw [over_eq _ hm]
    exact stopsExact_le _ values s (Int.le_trans (by decide) hm) hall h0
  | cubic y1 y2 =>
    have hm : (1000 : Int) ≤ max 1000 (max y1 y2) := Int.le_max_left _ _
    have t := mille_le hm
    rw [mille_one] at t
    show cubicExact y1 y2 s ≤ 1 + (((max 1000 (max y1 y2) - 1000).toNat : Nat) : Rat) / 1000
    rw [over_eq _ hm]
    exact cubicExact_le _ y1 y2 s h0 h1 t
      (mille_le (Int.le_trans (Int.le_max_left y1 y2) (Int.le_max_right 1000 _)))
      (mille_le (Int.le_trans (Int.le_max_right y1 y2) (Int.le_max_right 1000 _)))

end Easing

/-! ## A transition at every time -/

namespace Transition

/-- From its end on, a transition reads the end of its easing. -/
theorem exact_done (tr : Transition) (τ : Rat)
    (h : ((tr.delay + tr.duration : Nat) : Rat) ≤ τ) : tr.exact τ = tr.ease.exact 1 := by
  rw [Transition.exact, if_pos h]

/-- Up to its delay, a transition that has not ended reads the start of its easing. -/
theorem exact_before (tr : Transition) (τ : Rat) (h1 : τ ≤ (tr.delay : Rat))
    (h2 : τ < ((tr.delay + tr.duration : Nat) : Rat)) : tr.exact τ = tr.ease.exact 0 := by
  rw [Transition.exact, if_neg (Rat.not_le.mpr h2), if_pos h1]

/-- Between its delay and its end, a transition reads its easing at the share of its duration
that has passed. -/
theorem exact_between (tr : Transition) (τ : Rat) (h1 : (tr.delay : Rat) < τ)
    (h2 : τ < ((tr.delay + tr.duration : Nat) : Rat)) :
    tr.exact τ = tr.ease.exact ((τ - (tr.delay : Rat)) / (tr.duration : Rat)) := by
  rw [Transition.exact, if_neg (Rat.not_le.mpr h2), if_neg (Rat.not_le.mpr h1)]

/-- From its end on, a transition with a proper easing reads the whole. A value that takes it
stands at its place in the next picture (`mixExact_one`). -/
theorem exact_done_proper (tr : Transition) (τ : Rat) (hp : tr.ease.Proper)
    (h : ((tr.delay + tr.duration : Nat) : Rat) ≤ τ) : tr.exact τ = 1 :=
  (exact_done tr τ h).trans (Easing.exact_proper tr.ease hp).2

/-- Up to its delay, a transition with a proper easing that has not ended reads nothing. A
value that takes it stands at its place in the first picture (`mixExact_zero`). -/
theorem exact_before_proper (tr : Transition) (τ : Rat) (hp : tr.ease.Proper)
    (h1 : τ ≤ (tr.delay : Rat)) (h2 : τ < ((tr.delay + tr.duration : Nat) : Rat)) :
    tr.exact τ = 0 :=
  (exact_before tr τ h1 h2).trans (Easing.exact_proper tr.ease hp).1

/-- **At every time a transition reads its easing at a share from `0` to `1`**: none up to the
delay, the whole from the end on, and between the two the share of the duration that has
passed. A duration of zero leaves no time between the two, so nothing is divided by zero. -/
theorem exact_share (tr : Transition) (τ : Rat) :
    ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ tr.exact τ = tr.ease.exact s := by
  by_cases h2 : ((tr.delay + tr.duration : Nat) : Rat) ≤ τ
  · exact ⟨1, by decide, Rat.le_refl, exact_done tr τ h2⟩
  · have h2' := Rat.not_le.mp h2
    by_cases h1 : τ ≤ (tr.delay : Rat)
    · exact ⟨0, Rat.le_refl, by decide, exact_before tr τ h1 h2'⟩
    · have h1' := Rat.not_le.mp h1
      have h3 := h2'
      rw [Rat.natCast_add] at h3
      have m := rat_div_mem (x := τ - (tr.delay : Rat)) (d := (tr.duration : Rat)) (by grind)
        (by grind) (by grind)
      exact ⟨_, m.1, m.2, exact_between tr τ h1' h2'⟩

/-- **A transition whose easing passes the test reads in range at every time**: before its
delay, between its delay and its end, and after its end. -/
theorem exact_mem (tr : Transition) (τ : Rat) (h : tr.ease.bounded = true) :
    0 ≤ tr.exact τ ∧ tr.exact τ ≤ 1 := by
  obtain ⟨s, hs0, hs1, he⟩ := exact_share tr τ
  rw [he]
  exact Easing.exact_mem tr.ease s h hs0 hs1

/-- **A transition goes past the end by the `over` of its easing at most, at every time.** -/
theorem exact_le_over (tr : Transition) (τ : Rat) :
    tr.exact τ ≤ 1 + (tr.ease.over : Rat) / 1000 := by
  obtain ⟨s, hs0, hs1, he⟩ := exact_share tr τ
  rw [he]
  exact Easing.exact_le_over tr.ease s hs0 hs1

/-- **The whole-number reading of a transition is the exact one, rounded down**, at every whole
moment. It has no premise. A duration of zero leaves no moment between the delay and the end,
and the two readings take the same branch at every moment: the end comes first in both. -/
theorem at_eq_floor (tr : Transition) (t : Nat) :
    tr.at t = (1000 * tr.exact (t : Rat)).floor := by
  rcases Nat.lt_or_ge t (tr.delay + tr.duration) with h2 | h2
  · rcases Nat.lt_or_ge tr.delay t with h1 | h1
    · rw [at_between tr t h1 h2,
        exact_between tr t (Rat.natCast_lt_natCast.mpr h1) (Rat.natCast_lt_natCast.mpr h2),
        Easing.of_eq_floor, rat_natCast_sub (Nat.le_of_lt h1)]
    · rw [at_before tr t h1 h2,
        exact_before tr t (Rat.natCast_le_natCast.mpr h1) (Rat.natCast_lt_natCast.mpr h2),
        Easing.exact_zero, rat_thousand_mul_div, Rat.floor_intCast]
  · rw [at_done tr t h2, exact_done tr t (Rat.natCast_le_natCast.mpr h2), Easing.exact_one,
      rat_thousand_mul_div, Rat.floor_intCast]

/-- **A gap of both pictures is a gap at every time.** Two values take one transition, and its
easing passes the test. Where the second is `g` or more past the first in both pictures, it is
`g` or more past it at every rational time `τ`: before the delay, between two thousandths of
the step, and after the end. Nothing is rounded. -/
theorem exact_gap (tr : Transition) (τ : Rat) (h : tr.ease.bounded = true)
    (u₁ v₁ u₂ v₂ g : Rat) (hu : u₁ + g ≤ u₂) (hv : v₁ + g ≤ v₂) :
    mixExact u₁ v₁ (tr.exact τ) + g ≤ mixExact u₂ v₂ (tr.exact τ) :=
  mixExact_gap u₁ v₁ u₂ v₂ g _ (exact_mem tr τ h).1 (exact_mem tr τ h).2 hu hv

/-- A strict gap of both pictures is a strict gap at every time: two things that do not touch
in either picture never touch. -/
theorem exact_gap_lt (tr : Transition) (τ : Rat) (h : tr.ease.bounded = true)
    (u₁ v₁ u₂ v₂ g : Rat) (hu : u₁ + g < u₂) (hv : v₁ + g < v₂) :
    mixExact u₁ v₁ (tr.exact τ) + g < mixExact u₂ v₂ (tr.exact τ) :=
  mixExact_gap_lt u₁ v₁ u₂ v₂ g _ (exact_mem tr τ h).1 (exact_mem tr τ h).2 hu hv

/-- A value between `lo` and `hi` in both pictures is between them at every time. -/
theorem exact_within (tr : Transition) (τ : Rat) (h : tr.ease.bounded = true) (lo hi u v : Rat)
    (hu : lo ≤ u ∧ u ≤ hi) (hv : lo ≤ v ∧ v ≤ hi) :
    lo ≤ mixExact u v (tr.exact τ) ∧ mixExact u v (tr.exact τ) ≤ hi :=
  mixExact_mem lo hi u v _ (exact_mem tr τ h).1 (exact_mem tr τ h).2 hu hv

end Transition

/-! ## Relations that every time keeps -/

/-- A relation of two exact places that every share of the way between two pictures keeps.
Where `a` and `b` have it in one picture and `a'` and `b'` in the next, the two places on the
straight way have it at every share from `0` to `1`. The two things take one share. It is
`Kept` of `Whatwg/Svg/Scene/Between.lean` in exact numbers, over the points of the kit. -/
def KeptExact (R : Vec → Vec → Prop) : Prop :=
  ∀ {a a' b b' : Vec} {e : Rat}, 0 ≤ e → e ≤ 1 → R a b → R a' b' →
    R (a.lerp a' e) (b.lerp b' e)

/-- "Left of, by `g`" is kept: a gap along the first axis. -/
theorem KeptExact.leftOf (g : Rat) : KeptExact (fun a b => a.x + g ≤ b.x) := by
  intro a a' b b' e h0 h1 h h'
  show (a.lerp a' e).x + g ≤ (b.lerp b' e).x
  rw [lerp_eq_mixExact, lerp_eq_mixExact]
  exact mixExact_gap a.x a'.x b.x b'.x g e h0 h1 h h'

/-- "Above, by `g`" is kept: a gap along the second axis. -/
theorem KeptExact.above (g : Rat) : KeptExact (fun a b => a.y + g ≤ b.y) := by
  intro a a' b b' e h0 h1 h h'
  show (a.lerp a' e).y + g ≤ (b.lerp b' e).y
  rw [lerp_eq_mixExact, lerp_eq_mixExact]
  exact mixExact_gap a.y a'.y b.y b'.y g e h0 h1 h h'

/-- "The fixed step `d` from" is kept: the end of a line on its box, a label on its mark. -/
theorem KeptExact.step (d : Vec) : KeptExact (fun a b => b = a + d) := by
  intro a a' b b' e _ _ h h'
  subst h
  subst h'
  exact Vec.lerp_add a a' d e

/-- Two kept relations together are kept. -/
theorem KeptExact.and {R S : Vec → Vec → Prop} (hR : KeptExact R) (hS : KeptExact S) :
    KeptExact (fun a b => R a b ∧ S a b) := by
  intro a a' b b' e h0 h1 h h'
  exact ⟨hR h0 h1 h.1 h'.1, hS h0 h1 h.2 h'.2⟩

/-- **How far one thing is past another along a direction, on the way, is the mix of how far it
is in the two pictures.** The direction `n` is any vector, and "how far" is the scalar product
with it. It holds at every share, in range or not. -/
theorem dot_lerp_sub (a a' b b' n : Vec) (e : Rat) :
    (b.lerp b' e - a.lerp a' e).dot n = mixExact ((b - a).dot n) ((b' - a').dot n) e := by
  simp only [Vec.lerp, Vec.dot, Vec.sub_def, mixExact]
  grind

/-- **A gap along any direction is kept**: a half-plane. Where the second thing is `g` or more
past the first along `n` in both pictures, it is so at every share in range. Whole numbers
keep a gap along the two axes only. Off them each coordinate is rounded down by itself, and
the gap is lost, as a control of this file shows. -/
theorem KeptExact.along (n : Vec) (g : Rat) : KeptExact (fun a b => g ≤ (b - a).dot n) := by
  intro a a' b b' e h0 h1 h h'
  show g ≤ (b.lerp b' e - a.lerp a' e).dot n
  rw [dot_lerp_sub]
  exact le_mixExact g _ _ e h0 h1 h h'

/-- **A kept relation of two pictures holds at every time of a step.** Two things take one
transition, and its easing passes the test. Where their places have a kept relation in both
pictures, their places at the rational time `τ` have it, whatever `τ` is. It is `Kept.moment`
at every time, with nothing rounded. -/
theorem KeptExact.moment {R : Vec → Vec → Prop} (hR : KeptExact R) (tr : Transition) (τ : Rat)
    (h : tr.ease.bounded = true) {a a' b b' : Vec} (hab : R a b) (hab' : R a' b') :
    R (a.lerp a' (tr.exact τ)) (b.lerp b' (tr.exact τ)) :=
  hR (tr.exact_mem τ h).1 (tr.exact_mem τ h).2 hab hab'

/-! ## How near the whole-number reading is -/

/-- **The whole-number mix at a rounded share is near the exact mix.** The share `x` is rounded
down to a thousandth, and the mix is rounded down to a whole unit. On the way up, from `u` to a
greater `v`, both roundings go down. The reading is then no more than the exact value, and less
than one unit and a thousandth of the way below it. On the way down the first rounding goes up.
The reading is then less than one unit below the exact value, and no more than a thousandth of
the way above it. -/
theorem mix_floor_near (u v : Int) (x : Rat) :
    mixExact u v x - ((max (v - u) 0 : Int) : Rat) / 1000 - 1 <
        ((mix u v (1000 * x).floor : Int) : Rat) ∧
      ((mix u v (1000 * x).floor : Int) : Rat) ≤
        mixExact u v x + ((max (u - v) 0 : Int) : Rat) / 1000 := by
  have e1 := Rat.floor_le (1000 * x)
  have e2 := Rat.lt_floor_add_one (1000 * x)
  rw [mix_eq_floor_exact]
  have m1 := Rat.floor_le (mixExact u v (((1000 * x).floor : Rat) / 1000))
  have m2 := Rat.lt_floor_add_one (mixExact u v (((1000 * x).floor : Rat) / 1000))
  simp only [Rat.intCast_add, Rat.intCast_ofNat] at e2 m2
  generalize ((mixExact u v (((1000 * x).floor : Rat) / 1000)).floor : Rat) = m at m1 m2 ⊢
  generalize (((1000 * x).floor : Int) : Rat) = e at e1 e2 m1 m2 ⊢
  simp only [mixExact] at m1 m2 ⊢
  rcases Int.le_total u v with h | h
  · have hmax1 : max (v - u) 0 = v - u := by omega
    have hmax2 : max (u - v) 0 = 0 := by omega
    have huv := Rat.intCast_le_intCast.mpr h
    rw [hmax1, hmax2, Rat.intCast_sub]
    generalize (u : Rat) = U at huv m1 m2 ⊢
    generalize (v : Rat) = V at huv m1 m2 ⊢
    have p1 := Rat.mul_nonneg (show 0 ≤ V - U by grind) (show 0 ≤ x - e / 1000 by grind)
    have p2 := Rat.mul_nonneg (show 0 ≤ V - U by grind)
      (show 0 ≤ 1 / 1000 - (x - e / 1000) by grind)
    constructor <;> grind
  · have hmax1 : max (v - u) 0 = 0 := by omega
    have hmax2 : max (u - v) 0 = u - v := by omega
    have huv := Rat.intCast_le_intCast.mpr h
    rw [hmax1, hmax2, Rat.intCast_sub]
    generalize (u : Rat) = U at huv m1 m2 ⊢
    generalize (v : Rat) = V at huv m1 m2 ⊢
    have p1 := Rat.mul_nonneg (show 0 ≤ U - V by grind) (show 0 ≤ x - e / 1000 by grind)
    have p2 := Rat.mul_nonneg (show 0 ≤ U - V by grind)
      (show 0 ≤ 1 / 1000 - (x - e / 1000) by grind)
    constructor <;> grind

/-- **The reading of an easing at a share, mixed in whole numbers, is near the exact mix.** -/
theorem Easing.mix_near (e : Easing) (num den : Nat) (u v : Int) :
    mixExact u v (e.exact ((num : Rat) / (den : Rat))) - ((max (v - u) 0 : Int) : Rat) / 1000 -
          1 <
        ((mix u v (e.of num den) : Int) : Rat) ∧
      ((mix u v (e.of num den) : Int) : Rat) ≤
        mixExact u v (e.exact ((num : Rat) / (den : Rat))) +
          ((max (u - v) 0 : Int) : Rat) / 1000 := by
  rw [e.of_eq_floor num den]
  exact mix_floor_near u v _

/-- **What a program reads at a whole moment is near the exact value there.** With `x` the
exact value at the moment `t` on the way from `u` to `v`, the whole-number reading
`mix u v (tr.at t)` is more than `x - 1 - max (v - u) 0 / 1000` and no more than
`x + max (u - v) 0 / 1000`. Two roundings down make the distance: the easing's, to a thousandth
of the way, and the mix's, to a whole unit. Each side is nearly reached, as the last evaluations
of this file show. -/
theorem Transition.mix_near (tr : Transition) (t : Nat) (u v : Int) :
    mixExact u v (tr.exact (t : Rat)) - ((max (v - u) 0 : Int) : Rat) / 1000 - 1 <
        ((mix u v (tr.at t) : Int) : Rat) ∧
      ((mix u v (tr.at t) : Int) : Rat) ≤
        mixExact u v (tr.exact (t : Rat)) + ((max (u - v) 0 : Int) : Rat) / 1000 := by
  rw [tr.at_eq_floor t]
  exact mix_floor_near u v _

/-! ## Controls and finite evaluations

Each control is a picture with numbers where a premise fails and the conclusion with it. The
times of a transition are between two thousandths of the step, where the whole-number reading
says nothing. -/

-- `mixExact_gap` needs `0 ≤ e`. Two things stand at `0`, and the second goes to `10`: they do
-- not overlap before or after. At the share `-1/10` the second stands at `-1`, behind the
-- first.
#guard mixExact 0 10 (-1 / 10) = -1
#guard ¬(mixExact 0 0 (-1 / 10) + 0 ≤ mixExact 0 10 (-1 / 10))

-- `mixExact_gap` needs `e ≤ 1`, and `Transition.exact_gap` an easing that passes the test. A
-- thing goes from `0` to `100` and another stays at `116`, so both pictures have a gap of `16`.
-- `Easing.backOut` fails the test. At the time `700 + 1/2` it reads more than `1`, the first
-- thing stands past `108`, and the gap is less than `8`.
#guard Easing.backOut.bounded = false
#guard (0 : Rat) + 16 ≤ 116 ∧ (100 : Rat) + 16 ≤ 116
#guard 1 < ({ ease := Easing.backOut } : Transition).exact (1401 / 2)
#guard 108 < mixExact 0 100 (({ ease := Easing.backOut } : Transition).exact (1401 / 2))
#guard ¬(mixExact 0 100 (({ ease := Easing.backOut } : Transition).exact (1401 / 2)) + 16 ≤
  mixExact 116 116 (({ ease := Easing.backOut } : Transition).exact (1401 / 2)))

-- `KeptExact.moment` needs one transition for the two things. Two things go `100` to the right
-- and are `16` apart in both pictures, by one easing that passes the test. The first starts at
-- once and the second waits. At the time `499 + 1/2` the first stands at `99 + 9/10` and the
-- second still at `16`.
#guard Easing.linear.bounded = true
#guard (0 : Rat) + 16 ≤ 16 ∧ (100 : Rat) + 16 ≤ 116
#guard mixExact 0 100 (({ delay := 0, duration := 500 } : Transition).exact (999 / 2)) = 999 / 10
#guard mixExact 16 116 (({ delay := 500, duration := 500 } : Transition).exact (999 / 2)) = 16
#guard ¬(mixExact 0 100 (({ delay := 0, duration := 500 } : Transition).exact (999 / 2)) + 16 ≤
  mixExact 16 116 (({ delay := 500, duration := 500 } : Transition).exact (999 / 2)))

-- `Easing.exact_mem` needs the progress in range. Stops go on along their first line before
-- the start, and stand at their last value past the end. A cubic goes on at both sides.
#guard Easing.linear.exact (-1 / 2) = -1 / 2
#guard Easing.linear.exact 2 = 1
#guard Easing.cubicIn.exact (-1) = -1
#guard Easing.cubicIn.exact 2 = 8

-- `KeptExact.along` has no whole-number form off the axes. A thing stays at the origin, and
-- another goes from `(1, 0)` to `(0, 1)`: it is `1` past the first along `(1, 1)` in both
-- pictures. Half way the exact place is `(1/2, 1/2)`, still `1` along. The whole-number place
-- is the origin: each coordinate is rounded down by itself.
#guard ((⟨1, 0⟩ : Vec) - ⟨0, 0⟩).dot ⟨1, 1⟩ = 1 ∧ ((⟨0, 1⟩ : Vec) - ⟨0, 0⟩).dot ⟨1, 1⟩ = 1
#guard (((⟨1, 0⟩ : Vec).lerp ⟨0, 1⟩ (1 / 2)) - (⟨0, 0⟩ : Vec).lerp ⟨0, 0⟩ (1 / 2)).dot ⟨1, 1⟩ = 1
#guard (⟨mix 1 0 500, mix 0 1 500⟩ : IVec) = ⟨0, 0⟩

-- "Beside or above" is not kept in exact numbers either. A thing stays at the origin. Another
-- is `10` to its right before and `10` below it after. Half way it is `5` to the right and `5`
-- below, and neither axis holds the two `10` apart.
#guard (⟨10, 0⟩ : Vec).lerp ⟨0, 10⟩ (1 / 2) = ⟨5, 5⟩

-- `Transition.mix_near`, the low side. A value goes up from `0` to `999` in a step of a
-- million. At the moment `1999` the exact value is `1997001 / 1000000`. The easing reads `1`
-- per mille, and the mix reads `0`. The bound is `1999 / 1000000` below that.
#guard mix 0 999 (({ duration := 1000000 } : Transition).at 1999) = 0
#guard mixExact 0 999 (({ duration := 1000000 } : Transition).exact 1999) = 1997001 / 1000000
#guard mixExact 0 999 (({ duration := 1000000 } : Transition).exact 1999) - 999 / 1000 - 1 =
  -1999 / 1000000

-- `Transition.mix_near`, the high side. A value goes down from `1000` to `0` in the same step.
-- At the moment `999` the exact value is `999001 / 1000`. The easing reads `0` per mille, and
-- the mix reads `1000`. The bound is `1 / 1000` above that.
#guard mix 1000 0 (({ duration := 1000000 } : Transition).at 999) = 1000
#guard mixExact 1000 0 (({ duration := 1000000 } : Transition).exact 999) = 999001 / 1000
#guard mixExact 1000 0 (({ duration := 1000000 } : Transition).exact 999) + 1000 / 1000 =
  1000001 / 1000

end Whatwg.Svg.Scene
