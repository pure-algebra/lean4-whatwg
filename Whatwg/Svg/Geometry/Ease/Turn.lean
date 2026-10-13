import Whatwg.Svg.Geometry.Ease

/-!
# Whatwg.Svg.Geometry.Ease.Turn

Owner: the turn of an easing in exact numbers, for every easing (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Geometry/Ease.lean` proves of a cubic that its turn reads what is left of the whole
after the cubic at `1 - s` (`Easing.exact_out_cubic`), and says of stops that the same holds at
each stop by definition and is not proved between two stops. This module proves it between two
stops, and so of every easing.

- **The turn of stops** (`Easing.stopsExact_turned`): at every exact progress from `0` to `1`,
  the turned stops read what is left of the whole after the stops at `1 - s`. The turned stops
  are the same broken line read from its other end. The proof has two cases. Where the progress
  falls on a stop, both sides read one value. Where it falls between two stops, the two stops
  around `1 - s` are the two around `s` in the other order, and the two lines are one.
- **The turn of an easing** (`Easing.exact_out`): `e.out.exact s = 1 - e.exact (1 - s)`, for
  every easing but stops with no value. It is d3's `t => 1 - easeIn(1 - t)` (d3-ease
  `test/generic.js`, commit `4099c6d715f5`; BSD 3-Clause licence, Copyright 2010-2021 Mike
  Bostock, 2001 Robert Penner), as a law of the data of an easing and not of one function.
- **Played backwards** (`Easing.backward`): a value on its way from `u` to `v` under an easing,
  read at `1 - s`, is the value on its way from `v` to `u` under the turned easing at `s`. An
  exit that is an entrance played backwards is the opposite change with the turned easing,
  whatever the easing is.
- `Easing.exact_out_out`: an easing turned twice reads as the easing (`Easing.out_out`).

What this module does not claim: the same in whole numbers, where the two sides differ by the
rounding, one per mille at the most, since one rounds down what the other rounds up; anything
for stops with no value, whose turn has no value either and reads `0` on both sides, so that
the law fails there; a progress outside `0` to `1`, where stops stand still past their end and
go on along their first line before their start, which the turn exchanges.

Every law here depends on `propext`, `Quot.sound` and `Classical.choice` at most.
-/

namespace Whatwg.Svg.Scene

open Whatwg.Svg.Value

namespace Easing

/-! ## A value of a turned list -/

/-- **A value of a turned list is what is left of a thousand after the value at the same place
from the other end.** The place is inside the list, so neither side reads the value that stands
for a place past the end. -/
theorem getD_turned (vs : List Int) {j : Nat} (hj : j < vs.length) (d d' : Int) :
    (turned vs).getD j d' = 1000 - vs.getD (vs.length - 1 - j) d := by
  have hlen : j < (vs.map fun v => 1000 - v).length := by
    rw [List.length_map]
    exact hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  unfold turned
  rw [List.getElem?_reverse hlen, List.length_map, List.getElem?_map]
  cases h : vs[vs.length - 1 - j]? with
  | none =>
    have := List.getElem?_eq_none_iff.mp h
    omega
  | some v => rfl

/-- A number that is not negative, from a count up to the next, has that count as the count of
its floor. -/
theorem floor_toNat_eq {x : Rat} {k : Nat} (h1 : (k : Rat) ≤ x) (h2 : x < (k : Rat) + 1) :
    x.floor.toNat = k := by
  have e : x.floor = (k : Int) := by
    apply Decimal.rat_floor_eq
    · rw [Rat.intCast_natCast]
      exact h1
    · rw [Rat.intCast_natCast]
      exact h2
  rw [e]
  exact Int.toNat_natCast k

/-! ## The turn of stops -/

/-- **The turned stops read what is left of the whole after the stops at `1 - s`**, at every
exact progress from `0` to `1`: on a stop and between two. The stops have a value. -/
theorem stopsExact_turned (vs : List Int) (hv : vs ≠ []) {s : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    stopsExact (turned vs) s = 1 - stopsExact vs (1 - s) := by
  obtain ⟨n, hn⟩ : ∃ n, vs.length = n + 1 := by
    cases vs with
    | nil => exact absurd rfl hv
    | cons a rest => exact ⟨rest.length, rfl⟩
  have hn1 : vs.length - 1 = n := by omega
  have hN : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
  have hx0 : 0 ≤ s * (n : Rat) := Rat.mul_nonneg hs0 hN
  have hx1 : s * (n : Rat) ≤ (n : Rat) := by
    have p := Rat.mul_nonneg (show 0 ≤ 1 - s by grind) hN
    grind
  have fl := rat_sub_floor_toNat_mem hx0
  have hlenT : (turned vs).length - 1 = n := by
    rw [length_turned]
    exact hn1
  have hiT : (s * (((turned vs).length - 1 : Nat) : Rat)).floor.toNat =
      (s * (n : Rat)).floor.toNat := by rw [hlenT]
  have e1 : (1 - s) * ((vs.length - 1 : Nat) : Rat) = (n : Rat) - s * (n : Rat) := by
    rw [hn1]
    grind
  rw [stopsExact_piece (turned vs) s _ hiT, hlenT]
  generalize hi : (s * (n : Rat)).floor.toNat = i at fl ⊢
  have hin : i ≤ n := by
    have h : (i : Rat) ≤ (n : Rat) := by grind
    exact Rat.natCast_le_natCast.mp h
  by_cases hw : s * (n : Rat) = (i : Rat)
  · -- the progress falls on a stop
    have hj : ((1 - s) * ((vs.length - 1 : Nat) : Rat)).floor.toNat = n - i := by
      rw [e1]
      apply floor_toNat_eq
      · rw [rat_natCast_sub hin]
        grind
      · rw [rat_natCast_sub hin]
        grind
    rw [stopsExact_piece vs (1 - s) _ hj, e1, hw, rat_natCast_sub hin,
      getD_turned vs (show i < vs.length by omega) (vs.getLast?.getD 0), hn, Rat.intCast_sub,
      Rat.intCast_ofNat]
    have ei : n + 1 - 1 - i = n - i := by omega
    rw [ei]
    grind
  · -- the progress falls between two stops
    have hlt : (i : Rat) < s * (n : Rat) := by grind
    have hi1 : i + 1 ≤ n := by
      have h : (i : Rat) < (n : Rat) := by grind
      have := Rat.natCast_lt_natCast.mp h
      omega
    have hc : ((n - (i + 1) : Nat) : Rat) = (n : Rat) - (i : Rat) - 1 := by
      rw [rat_natCast_sub hi1, Rat.natCast_add]
      grind
    have hj : ((1 - s) * ((vs.length - 1 : Nat) : Rat)).floor.toNat = n - (i + 1) := by
      rw [e1]
      apply floor_toNat_eq
      · rw [hc]
        grind
      · rw [hc]
        grind
    have ea : n + 1 - 1 - i = n - i := by omega
    have eb : n + 1 - 1 - (i + 1) = n - (i + 1) := by omega
    have ec : n - (i + 1) + 1 = n - i := by omega
    rw [stopsExact_piece vs (1 - s) _ hj, e1, hc,
      getD_turned vs (show i < vs.length by omega) (vs.getLast?.getD 0),
      getD_turned vs (show i + 1 < vs.length by omega) (vs.getLast?.getD 0), hn, ea, eb, ec,
      Rat.intCast_sub, Rat.intCast_sub, Rat.intCast_ofNat]
    grind

/-! ## The turn of every easing -/

/-- **The turn of an easing, in exact numbers**: at every exact progress from `0` to `1`, the
turned easing reads what is left of the whole after the easing at `1 - s`. It holds of every
easing but stops with no value. -/
theorem exact_out (e : Easing) (he : e ≠ stops []) {s : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    e.out.exact s = 1 - e.exact (1 - s) := by
  cases e with
  | stops vs => exact stopsExact_turned vs (fun h => he (congrArg stops h)) hs0 hs1
  | cubic y1 y2 => exact exact_out_cubic y1 y2 s

/-- **A change played backwards is the opposite change under the turned easing**, whatever the
easing. The value on its way from `u` to `v`, at the progress `1 - s`, is the value on its way
from `v` to `u` under the turned easing at `s`. -/
theorem backward (e : Easing) (he : e ≠ stops []) (u v : Rat) {s : Rat} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : mixExact u v (e.exact (1 - s)) = mixExact v u (e.out.exact s) := by
  rw [exact_out e he hs0 hs1]
  simp only [mixExact]
  grind

/-- An easing turned twice reads as the easing. -/
theorem exact_out_out (e : Easing) (s : Rat) : e.out.out.exact s = e.exact s := by
  rw [out_out]

end Easing

/-! ## Controls

Each is a case where a premise of `Easing.exact_out` fails, and the law with it. -/

-- The law asks that the stops have a value. With none, the turned stops have none either:
-- both read `0`, and what is left of the whole after `0` is `1`.
#guard (Easing.stops []).out.exact (1 / 2) = 0 ∧ 1 - (Easing.stops []).exact (1 - 1 / 2) = 1

-- The law asks for a progress from `0` to `1`. Past the end the turned stops stand at their
-- last value, and the stops, read before their start, go on along their first line.
#guard (Easing.stops [0, 500, 1000]).out.exact 2 = 1 ∧
  1 - (Easing.stops [0, 500, 1000]).exact (1 - 2) = 2

-- Between two stops, where the law is new: stops that rise fast and then slowly, turned, at a
-- quarter of the progress, which is on no stop of four values. The turned stops read `3/40`
-- there, and the stops read `37/40` at three quarters.
#guard (Easing.stops [0, 700, 900, 1000]).out = Easing.stops [0, 100, 300, 1000] ∧
  (Easing.stops [0, 700, 900, 1000]).out.exact (1 / 4) = 3 / 40 ∧
  (Easing.stops [0, 700, 900, 1000]).exact (3 / 4) = 37 / 40

end Whatwg.Svg.Scene
