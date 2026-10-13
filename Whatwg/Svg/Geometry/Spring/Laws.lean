import Whatwg.Svg.Geometry.Spring
import Whatwg.Svg.Geometry.Moment

/-!
# Whatwg.Svg.Geometry.Spring.Laws

Owner: the laws of the two kinds of spring and of the easings made from them (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Geometry/Spring.lean` has a spring as three rational numbers, with the laws of every
spring. This module says what a spring of each kind does, and what the easing made from it is
known to be, for every number of pieces.

- The stops. `Easing.mille` rounds a share to the nearest per mille: it keeps the order, it is
  exact at `0` and at `1`, and it is within a half per mille of the share (`mille_mono`,
  `mille_zero`, `mille_one`, `mille_near`). A resumed easing starts at `0`, ends at `1000` where
  the run has moved at all (`resumed_proper`), and reads its stop at the moment of each piece
  (`resumed_at_stop`). It is the same for a thing left of its target and for its mirror image
  (`resumed_neg`), and for the same motion counted in another unit (`resumed_scale`).
- **What the easing draws.** A change from the place where a thing is seen to its target, read
  at the exact share of the piece `i`, is the target and the offset of the run there
  (`mixExact_run`). The easing ends at `1000` exactly, so its shares are of the way to where the
  run stands at the last piece: that takes away the last offset times the share
  (`mixExact_share`). Rounding a share to a per mille moves the place by the first offset over
  two thousand at most (`mixExact_stop`, `mixExact_stop_near`), and the whole-number reading
  rounds down once more (`mix_stop_near`).
- **A critical spring.** Its offsets are `(a + b i) rⁱ` (`critical_run_succ`,
  `critical_response`, `critical_kick`), and how fast it closes on the place it is drawn to
  falls by `r` each piece (`critical_drift`). **No overshoot**: a thing that is not moving away
  from its target, nor toward it faster than `r` a piece, never passes the target and never
  turns back (`critical_calm`, `critical_run_le`). `Spring.Calm` says that of a thing on either
  side of its target, and a calm thing stays calm (`critical_stays_calm`). The response is the
  run of a calm thing (`critical_rest_calm`), so it is positive, at most `1` and never rises
  (`critical_response_pos`, `critical_response_le_one`, `critical_response_le`). **Settling**:
  the response is at most `restⁱ` (`critical_response_le_pow`), and from the piece `n` on at
  most `(1 + c n) rⁿ` (`critical_settled`).
- **The easing of a critical spring** passes `Easing.bounded`, its stops never fall and it is
  proper, for every number of pieces (`critical_easing_bounded`, `critical_easing_rising`,
  `critical_easing_proper`). So does the resumed easing of a calm thing
  (`critical_resumed_bounded`, `critical_resumed_rising`, `critical_resumed_proper`), and it is
  within the last offset and a two-thousandth of the first of the spring it stands for
  (`critical_mixExact_stop_near`). The premise of `Motion.together` of
  `Whatwg/Svg/Scene/Together.lean` is then known from what a spring is, and not from reading a
  table.
- **A step that is interrupted.** Two things on one critical spring, each let go at rest and
  both sent on at one cut, keep at every piece each gap that their three pictures have
  (`critical_interrupted_gap`), and a thing stays inside a room that holds its three places
  (`critical_interrupted_mem`). No easing is asked to stay in range: the place of each thing is
  a mean of its three places.
- **A spring that swings.** Where `p² < 4 q`, the square of every offset is under a bound that
  each piece multiplies by `q` (`swing_sq_le`). For `Spring.under r k c` that is a bound
  `B * rⁱ` on the offset itself (`under_bound`, `under_response_bound`).

What this module does not claim. The laws of an easing are of its stops, and of its readings at
the moments of the pieces. That an easing whose stops never fall reads values that never fall
between them is not proved here. `Spring.Calm` suffices for an easing in range and is not shown
to be needed. A thing that moves toward its target faster than `r` a piece passes it once, and a
thing that moves away from it goes further before it turns: the controls of
`WhatwgTest/Html/SvgSpring.lean` have one of each, and the resumed easing of neither passes
`Easing.bounded`. So a thing that keeps its speed keeps the gaps of `Motion.together` only where
it is calm, and a caller that needs both tests `Spring.Calm`. `under_bound` is a bound and not
the least one: a rational `B` stands where the textbook has a square root. No law says that a
spring that swings fails `Easing.bounded`, though the one tried does. `mixExact_stop_near` is of
a thing right of its target, and the mirror image is not stated.

Every law here depends on `propext`, `Quot.sound` and `Classical.choice` at most.
-/

namespace Whatwg.Svg.Value

/-- The floor keeps the order. -/
theorem rat_floor_mono {x y : Rat} (h : x ≤ y) : x.floor ≤ y.floor :=
  Rat.le_floor_iff.mpr (Rat.le_trans (Rat.floor_le x) h)

/-- A quotient by zero is zero. -/
theorem rat_div_zero (x : Rat) : x / 0 = 0 := by
  rw [Rat.div_def, Rat.inv_zero, Rat.mul_zero]

/-- The inverse of a number that is not negative is not negative. -/
theorem rat_inv_nonneg {c : Rat} (hc : 0 ≤ c) : 0 ≤ c⁻¹ := by
  rcases Rat.le_iff_lt_or_eq.mp hc with h | h
  · exact Rat.le_of_lt (Rat.inv_pos.mpr h)
  · rw [← h, Rat.inv_zero]
    exact Rat.le_refl

/-- Dividing both sides by a number that is not negative keeps `≤`: by zero too, where both
quotients are zero. -/
theorem rat_div_le_div_of_nonneg {a b c : Rat} (hc : 0 ≤ c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right h (rat_inv_nonneg hc)

/-- A part of a whole is a share of it from `0` to `1`: of a whole of nothing too, where the
share is `0`. -/
theorem rat_div_mem_of_le {x d : Rat} (h0 : 0 ≤ x) (h1 : x ≤ d) : 0 ≤ x / d ∧ x / d ≤ 1 := by
  rcases Rat.le_iff_lt_or_eq.mp (Rat.le_trans h0 h1) with h | h
  · exact rat_div_mem h h0 h1
  · rw [← h, rat_div_zero]
    exact ⟨Rat.le_refl, by decide⟩

/-- A number whose square is no more than the square of `b` is from `-b` to `b`. -/
theorem rat_abs_le_of_mul_self_le {x b : Rat} (hb : 0 ≤ b) (h : x * x ≤ b * b) :
    -b ≤ x ∧ x ≤ b := by
  refine ⟨Rat.not_lt.mp fun hlt => ?_, Rat.not_lt.mp fun hlt => ?_⟩
  · have p : 0 < (-x - b) * (-x + b) := Rat.mul_pos (by grind) (by grind)
    grind
  · have p : 0 < (x - b) * (x + b) := Rat.mul_pos (by grind) (by grind)
    grind

/-- A power of a square is the square of the power. -/
theorem rat_mul_self_pow (r : Rat) (i : Nat) : (r * r) ^ i = r ^ i * r ^ i := by
  induction i with
  | zero => rw [Rat.pow_zero, Rat.pow_zero, Rat.mul_one]
  | succ i ih =>
    rw [Rat.pow_succ, Rat.pow_succ, ih]
    grind

/-- The count after a count is one more, as a rational number. -/
theorem rat_natCast_succ (i : Nat) : ((i + 1 : Nat) : Rat) = (i : Rat) + 1 := by
  rw [Rat.natCast_add]
  rfl

end Whatwg.Svg.Value

namespace Whatwg.Svg.Scene

open Whatwg.Svg.Value

/-! ## Per mille, to the nearest -/

namespace Easing

/-- No share is no per mille. -/
theorem mille_zero : mille 0 = 0 :=
  Decimal.rat_floor_eq (k := 0) (show (0 : Rat) ≤ 1000 * 0 + 1 / 2 by grind)
    (show (1000 : Rat) * 0 + 1 / 2 < 0 + 1 by grind)

/-- The whole is a thousand per mille. -/
theorem mille_one : mille 1 = 1000 :=
  Decimal.rat_floor_eq (k := 1000) (show (1000 : Rat) ≤ 1000 * 1 + 1 / 2 by grind)
    (show (1000 : Rat) * 1 + 1 / 2 < 1000 + 1 by grind)

/-- Rounding keeps the order of two shares. -/
theorem mille_mono {x y : Rat} (h : x ≤ y) : mille x ≤ mille y :=
  rat_floor_mono (by grind)

/-- **A share and its per mille are within a half per mille**: the rounded value is more than
the share less a two-thousandth, and no more than the share and a two-thousandth. -/
theorem mille_near (x : Rat) :
    x - 1 / 2000 < ((mille x : Int) : Rat) / 1000 ∧
      ((mille x : Int) : Rat) / 1000 ≤ x + 1 / 2000 := by
  have h1 := Rat.floor_le (1000 * x + 1 / 2)
  have h2 := Rat.lt_floor_add_one (1000 * x + 1 / 2)
  simp only [Rat.intCast_add, Rat.intCast_ofNat] at h2
  show x - 1 / 2000 < (((1000 * x + 1 / 2).floor : Int) : Rat) / 1000 ∧
    (((1000 * x + 1 / 2).floor : Int) : Rat) / 1000 ≤ x + 1 / 2000
  generalize (((1000 * x + 1 / 2).floor : Int) : Rat) = m at h1 h2 ⊢
  constructor <;> grind

/-- A share from `0` to `1` is from `0` to `1000` per mille. -/
theorem mille_mem {x : Rat} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ mille x ∧ mille x ≤ 1000 := by
  have a := mille_mono h0
  have b := mille_mono h1
  rw [mille_zero] at a
  rw [mille_one] at b
  exact ⟨a, b⟩

end Easing

namespace Spring

/-! ## The stops of a resumed easing -/

/-- At the first piece nothing of the way is gone. -/
theorem share_zero (s : Spring) (x0 x1 : Rat) (n : Nat) : s.share x0 x1 n 0 = 0 := by
  have e : x0 - x0 = 0 := by grind
  show (x0 - x0) / (x0 - s.run x0 x1 n) = 0
  rw [e, Rat.div_def, Rat.zero_mul]

/-- At the last piece the whole way is gone, where the run has moved at all. -/
theorem share_last (s : Spring) (x0 x1 : Rat) (n : Nat) (h : s.run x0 x1 n ≠ x0) :
    s.share x0 x1 n n = 1 := by
  show (x0 - s.run x0 x1 n) / (x0 - s.run x0 x1 n) = 1
  generalize s.run x0 x1 n = y at h ⊢
  grind

/-- The first stop is `0`. -/
theorem stop_zero (s : Spring) (x0 x1 : Rat) (n : Nat) : s.stop x0 x1 n 0 = 0 := by
  rw [stop, share_zero]
  exact Easing.mille_zero

/-- The last stop is `1000`, where the run has moved at all. -/
theorem stop_last (s : Spring) (x0 x1 : Rat) (n : Nat) (h : s.run x0 x1 n ≠ x0) :
    s.stop x0 x1 n n = 1000 := by
  rw [stop, share_last s x0 x1 n h]
  exact Easing.mille_one

/-- **A stop is within a half per mille of the share it rounds.** -/
theorem stop_near (s : Spring) (x0 x1 : Rat) (n i : Nat) :
    s.share x0 x1 n i - 1 / 2000 < ((s.stop x0 x1 n i : Int) : Rat) / 1000 ∧
      ((s.stop x0 x1 n i : Int) : Rat) / 1000 ≤ s.share x0 x1 n i + 1 / 2000 :=
  Easing.mille_near _

/-- **A resumed easing is proper**, where the run has moved at all by its last piece: it starts
at `0` and ends at `1000`, so a change that takes it ends on the target. -/
theorem resumed_proper (s : Spring) (x0 x1 : Rat) (n : Nat) (h : s.run x0 x1 n ≠ x0) :
    (s.resumed x0 x1 n).Proper := by
  rw [resumed_stops]
  apply Easing.proper_stops
  · rw [List.head?_map, List.head?_range, if_neg (Nat.succ_ne_zero n)]
    exact congrArg some (s.stop_zero x0 x1 n)
  · rw [List.getLast?_map, List.getLast?_range, if_neg (Nat.succ_ne_zero n)]
    exact congrArg some (s.stop_last x0 x1 n h)

/-- **The easing of a spring is proper**, where the response has moved at all by its last
piece. -/
theorem easing_proper (s : Spring) (n : Nat) (h : s.response n ≠ 1) : (s.easing n).Proper :=
  s.resumed_proper 1 s.rest n h

/-- **At the moment of a piece a resumed easing reads the stop of that piece.** The moment `p`
is the piece `i` of `n`, in per mille. -/
theorem resumed_at_stop (s : Spring) (x0 x1 : Rat) (n i p : Nat) (hi : i ≤ n)
    (hp : p * n = 1000 * i) : (s.resumed x0 x1 n).at p = s.stop x0 x1 n i := by
  have hl : ((List.range (n + 1)).map (s.stop x0 x1 n)).length = n + 1 := by
    rw [List.length_map, List.length_range]
  rw [resumed_stops]
  show Easing.stopsAt ((List.range (n + 1)).map (s.stop x0 x1 n)) p = s.stop x0 x1 n i
  rw [Easing.stopsAt_stop _ i p (by rw [hl]; omega) (by rw [hl, Nat.add_sub_cancel]; exact hp),
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- The share of the way is the same for offsets that are `l` times as far, where `l` is not
`0`. -/
theorem share_scale (s : Spring) (l x0 x1 : Rat) (n i : Nat) (hl : l ≠ 0) :
    s.share (l * x0) (l * x1) n i = s.share x0 x1 n i := by
  show (l * x0 - s.run (l * x0) (l * x1) i) / (l * x0 - s.run (l * x0) (l * x1) n) =
    (x0 - s.run x0 x1 i) / (x0 - s.run x0 x1 n)
  rw [run_scale, run_scale]
  generalize s.run x0 x1 i = a
  generalize s.run x0 x1 n = b
  by_cases h : x0 - b = 0
  · have e : l * x0 - l * b = 0 := by grind
    rw [h, e, rat_div_zero, rat_div_zero]
  · have e : l * x0 - l * b ≠ 0 := by grind
    grind

/-- **A resumed easing is the same for a thing and for its mirror image**, and for the same
motion counted in another unit: only the share of the second offset in the first matters. -/
theorem resumed_scale (s : Spring) (l x0 x1 : Rat) (n : Nat) (hl : l ≠ 0) :
    s.resumed (l * x0) (l * x1) n = s.resumed x0 x1 n := by
  rw [resumed_stops, resumed_stops]
  exact congrArg Easing.stops
    (List.map_congr_left fun i _ => congrArg Easing.mille (s.share_scale l x0 x1 n i hl))

/-- The share of the way is the same for the mirror image. -/
theorem share_neg (s : Spring) (x0 x1 : Rat) (n i : Nat) :
    s.share (-x0) (-x1) n i = s.share x0 x1 n i := by
  have e0 : -x0 = -1 * x0 := by grind
  have e1 : -x1 = -1 * x1 := by grind
  rw [e0, e1]
  exact s.share_scale (-1) x0 x1 n i (by grind)

/-- **A thing left of its target and its mirror image right of it have one resumed easing.** -/
theorem resumed_neg (s : Spring) (x0 x1 : Rat) (n : Nat) :
    s.resumed (-x0) (-x1) n = s.resumed x0 x1 n := by
  rw [resumed_stops, resumed_stops]
  exact congrArg Easing.stops
    (List.map_congr_left fun i _ => congrArg Easing.mille (s.share_neg x0 x1 n i))

/-! ## What the easing draws -/

/-- **A change from where a thing is seen to its target follows the run.** The thing is seen at
`target + x0`. At the exact share `1 - x i / x0`, the place on the straight way to the target is
the target and the offset `x i` of the run. This is the share before it is scaled to end at `1`
and before it is rounded. -/
theorem mixExact_run (s : Spring) (target x0 x1 : Rat) (i : Nat) (h : x0 ≠ 0) :
    mixExact (target + x0) target (1 - s.run x0 x1 i / x0) = target + s.run x0 x1 i := by
  simp only [mixExact]
  generalize s.run x0 x1 i = y
  grind

/-- **What the scaling adds.** The shares of a resumed easing are of the way to where the run
stands at its last piece, so that the easing ends at `1` exactly. The place at the share of the
piece `i` is then the place of the run, less the last offset times that share: nothing at the
first piece, and the whole of the last offset at the last one, where the thing stands on its
target. -/
theorem mixExact_share (s : Spring) (target x0 x1 : Rat) (n i : Nat) (h : s.run x0 x1 n ≠ x0) :
    mixExact (target + x0) target (s.share x0 x1 n i) =
      target + s.run x0 x1 i - s.run x0 x1 n * s.share x0 x1 n i := by
  simp only [mixExact, share]
  generalize s.run x0 x1 i = y
  generalize s.run x0 x1 n = z at h ⊢
  grind

/-- **What the rounding adds.** The place at the stop of the piece `i`, read in exact numbers,
is the place at the share and the first offset times what the rounding took from the share. -/
theorem mixExact_stop (s : Spring) (target x0 x1 : Rat) (n i : Nat) (h : s.run x0 x1 n ≠ x0) :
    mixExact (target + x0) target (((s.stop x0 x1 n i : Int) : Rat) / 1000) =
      target + s.run x0 x1 i - s.run x0 x1 n * s.share x0 x1 n i +
        x0 * (s.share x0 x1 n i - ((s.stop x0 x1 n i : Int) : Rat) / 1000) := by
  have m := s.mixExact_share target x0 x1 n i h
  simp only [mixExact] at m ⊢
  grind

/-- **How near the easing is to the spring, at the stop of a piece.** The thing is seen at
`target + x0` with `x0` not negative, the run has not passed its target at the last piece, and
the share of the piece is from `0` to `1`. Then the place read at the stop is no more than the
last offset and a two-thousandth of the first below the place of the run, and no more than a
two-thousandth of the first above it. -/
theorem mixExact_stop_near (s : Spring) (target x0 x1 : Rat) (n i : Nat)
    (h : s.run x0 x1 n ≠ x0) (hx : 0 ≤ x0) (hn : 0 ≤ s.run x0 x1 n)
    (h0 : 0 ≤ s.share x0 x1 n i) (h1 : s.share x0 x1 n i ≤ 1) :
    target + s.run x0 x1 i - s.run x0 x1 n - x0 / 2000 ≤
        mixExact (target + x0) target (((s.stop x0 x1 n i : Int) : Rat) / 1000) ∧
      mixExact (target + x0) target (((s.stop x0 x1 n i : Int) : Rat) / 1000) ≤
        target + s.run x0 x1 i + x0 / 2000 := by
  rw [s.mixExact_stop target x0 x1 n i h]
  obtain ⟨n1, n2⟩ := s.stop_near x0 x1 n i
  generalize ((s.stop x0 x1 n i : Int) : Rat) / 1000 = e at n1 n2 ⊢
  generalize s.share x0 x1 n i = sh at h0 h1 n1 n2 ⊢
  generalize s.run x0 x1 i = y
  generalize s.run x0 x1 n = z at hn
  have p1 := Rat.mul_nonneg hx (show 0 ≤ sh - e + 1 / 2000 by grind)
  have p2 := Rat.mul_nonneg hx (show 0 ≤ 1 / 2000 - (sh - e) by grind)
  have p3 := Rat.mul_nonneg hn h0
  have p4 := Rat.mul_nonneg hn (show 0 ≤ 1 - sh by grind)
  constructor <;> grind

/-- **How near the whole-number reading is.** A thing is seen at the whole place `seen` and
goes to the whole place `target`. The kit's `mix` at the stop of the piece `i` rounds down once
more, so it is less than one unit further below the place of the run. -/
theorem mix_stop_near (s : Spring) (seen target : Int) (x1 : Rat) (n i : Nat)
    (h : s.run ((seen : Rat) - (target : Rat)) x1 n ≠ (seen : Rat) - (target : Rat))
    (hx : 0 ≤ (seen : Rat) - (target : Rat))
    (hn : 0 ≤ s.run ((seen : Rat) - (target : Rat)) x1 n)
    (h0 : 0 ≤ s.share ((seen : Rat) - (target : Rat)) x1 n i)
    (h1 : s.share ((seen : Rat) - (target : Rat)) x1 n i ≤ 1) :
    (target : Rat) + s.run ((seen : Rat) - (target : Rat)) x1 i -
          s.run ((seen : Rat) - (target : Rat)) x1 n - ((seen : Rat) - (target : Rat)) / 2000 - 1 <
        ((mix seen target (s.stop ((seen : Rat) - (target : Rat)) x1 n i) : Int) : Rat) ∧
      ((mix seen target (s.stop ((seen : Rat) - (target : Rat)) x1 n i) : Int) : Rat) ≤
        (target : Rat) + s.run ((seen : Rat) - (target : Rat)) x1 i +
          ((seen : Rat) - (target : Rat)) / 2000 := by
  obtain ⟨b1, b2⟩ := s.mixExact_stop_near (target : Rat) _ x1 n i h hx hn h0 h1
  have e : (target : Rat) + ((seen : Rat) - (target : Rat)) = (seen : Rat) := by grind
  rw [e] at b1 b2
  rw [mix_eq_floor_exact]
  have f1 := Rat.floor_le (mixExact (seen : Rat) (target : Rat)
    (((s.stop ((seen : Rat) - (target : Rat)) x1 n i : Int) : Rat) / 1000))
  have f2 := Rat.lt_floor_add_one (mixExact (seen : Rat) (target : Rat)
    (((s.stop ((seen : Rat) - (target : Rat)) x1 n i : Int) : Rat) / 1000))
  simp only [Rat.intCast_add, Rat.intCast_ofNat] at f2
  constructor <;> grind

/-! ## A critical spring -/

/-- **How fast a critical spring closes falls by `r` each piece.** The offset one piece later,
less `r` times the offset now, is what a thing with no speed of its own would not have: it is
`rⁱ` times what it was at the start. -/
theorem critical_drift (r c x0 x1 : Rat) (i : Nat) :
    (critical r c).run x0 x1 (i + 1) - r * (critical r c).run x0 x1 i = r ^ i * (x1 - r * x0) := by
  induction i generalizing x0 x1 with
  | zero =>
    show x1 - r * x0 = r ^ 0 * (x1 - r * x0)
    rw [Rat.pow_zero, Rat.one_mul]
  | succ i ih =>
    have e := ih x1 (2 * r * x1 - r * r * x0)
    rw [Rat.pow_succ]
    show (critical r c).run x1 (2 * r * x1 - r * r * x0) (i + 1) -
      r * (critical r c).run x1 (2 * r * x1 - r * r * x0) i = r ^ i * r * (x1 - r * x0)
    rw [e]
    grind

/-- **The offsets of a critical spring, in closed form**: from the second one on they are
`(x1 + (x1 - r x0) i) rⁱ`. -/
theorem critical_run_succ (r c x0 x1 : Rat) (i : Nat) :
    (critical r c).run x0 x1 (i + 1) = (x1 + (x1 - r * x0) * (i : Rat)) * r ^ i := by
  induction i with
  | zero =>
    have z : ((0 : Nat) : Rat) = 0 := rfl
    show x1 = (x1 + (x1 - r * x0) * ((0 : Nat) : Rat)) * r ^ 0
    rw [z, Rat.pow_zero]
    grind
  | succ i ih =>
    have d := critical_drift r c x0 x1 (i + 1)
    rw [ih, Rat.pow_succ] at d
    rw [rat_natCast_succ, Rat.pow_succ]
    generalize (critical r c).run x0 x1 (i + 1 + 1) = y at d ⊢
    generalize r ^ i = R at d ⊢
    grind

/-- **The response of a critical spring is `(1 + c i) rⁱ`.** -/
theorem critical_response (r c : Rat) (i : Nat) :
    (critical r c).response i = (1 + c * (i : Rat)) * r ^ i := by
  cases i with
  | zero =>
    have z : ((0 : Nat) : Rat) = 0 := rfl
    show (1 : Rat) = (1 + c * ((0 : Nat) : Rat)) * r ^ 0
    rw [z, Rat.pow_zero]
    grind
  | succ i =>
    show (critical r c).run 1 ((1 + c) * r) (i + 1) = (1 + c * ((i + 1 : Nat) : Rat)) * r ^ (i + 1)
    rw [critical_run_succ, rat_natCast_succ, Rat.pow_succ]
    grind

/-- The kick of a critical spring, from its second offset on: `(i + 1) rⁱ`. -/
theorem critical_kick_succ (r c : Rat) (i : Nat) :
    (critical r c).kick (i + 1) = ((i : Rat) + 1) * r ^ i := by
  show (critical r c).run 0 1 (i + 1) = ((i : Rat) + 1) * r ^ i
  rw [critical_run_succ]
  grind

/-- **The kick of a critical spring is `i rⁱ⁻¹`.** -/
theorem critical_kick (r c : Rat) (i : Nat) :
    (critical r c).kick i = (i : Rat) * r ^ (i - 1) := by
  cases i with
  | zero =>
    have z : ((0 : Nat) : Rat) = 0 := rfl
    show (0 : Rat) = ((0 : Nat) : Rat) * r ^ (0 - 1)
    rw [z, Rat.zero_mul]
  | succ i => rw [critical_kick_succ, rat_natCast_succ, Nat.add_sub_cancel]

/-- **No overshoot.** A thing on a critical spring is calm where it is not past its target, is
not moving away from it, and is not moving toward it faster than `r` a piece:
`r * x0 ≤ x1 ≤ x0`. A calm thing stays calm. So at every piece it has not passed its target, and
it is no further from it than a piece before. -/
theorem critical_calm (r c : Rat) (hr : 0 ≤ r) (x0 x1 : Rat) (h0 : 0 ≤ x0) (h1 : r * x0 ≤ x1)
    (h2 : x1 ≤ x0) (i : Nat) :
    0 ≤ (critical r c).run x0 x1 i ∧
      r * (critical r c).run x0 x1 i ≤ (critical r c).run x0 x1 (i + 1) ∧
      (critical r c).run x0 x1 (i + 1) ≤ (critical r c).run x0 x1 i := by
  induction i generalizing x0 x1 with
  | zero => exact ⟨h0, h1, h2⟩
  | succ i ih =>
    have a0 := Rat.mul_nonneg hr h0
    have a1 : 0 ≤ x1 := Rat.le_trans a0 h1
    have a2 := Rat.mul_nonneg hr (show 0 ≤ x1 - r * x0 by grind)
    have a3 := Rat.mul_nonneg (rat_mul_self_nonneg r) (show 0 ≤ x0 - x1 by grind)
    have a4 := Rat.mul_nonneg a1 (rat_mul_self_nonneg (1 - r))
    exact ih x1 (2 * r * x1 - r * r * x0) a1 (by grind) (by grind)

/-- **A calm thing on a critical spring never turns back**: it is no further from its target
at a later piece than at an earlier one. -/
theorem critical_run_le (r c : Rat) (hr : 0 ≤ r) (x0 x1 : Rat) (h0 : 0 ≤ x0) (h1 : r * x0 ≤ x1)
    (h2 : x1 ≤ x0) {i j : Nat} (hij : i ≤ j) :
    (critical r c).run x0 x1 j ≤ (critical r c).run x0 x1 i := by
  induction hij with
  | refl => exact Rat.le_refl
  | step _ ih => exact Rat.le_trans (critical_calm r c hr x0 x1 h0 h1 h2 _).2.2 ih

/-- A calm thing that is moving at all has left its place by every later piece. -/
theorem critical_moved (r c : Rat) (hr : 0 ≤ r) (x0 x1 : Rat) (h0 : 0 ≤ x0) (h1 : r * x0 ≤ x1)
    (h2 : x1 ≤ x0) (hne : x1 ≠ x0) {n : Nat} (hn : 0 < n) : (critical r c).run x0 x1 n ≠ x0 := by
  intro e
  have m := critical_run_le r c hr x0 x1 h0 h1 h2 (i := 1) (j := n) hn
  rw [e, run_one] at m
  exact hne (by grind)

/-- The response of a critical spring is a calm run, where `0 ≤ r`, `0 ≤ c` and the rest is at
most `1`. -/
theorem critical_response_calm (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1)
    (i : Nat) :
    0 ≤ (critical r c).response i ∧
      r * (critical r c).response i ≤ (critical r c).response (i + 1) ∧
      (critical r c).response (i + 1) ≤ (critical r c).response i := by
  have a := Rat.mul_nonneg hc hr
  exact critical_calm r c hr 1 ((1 + c) * r) (by decide) (by grind) h i

/-- **The response of a critical spring never rises.** -/
theorem critical_response_le (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1)
    {i j : Nat} (hij : i ≤ j) : (critical r c).response j ≤ (critical r c).response i := by
  have a := Rat.mul_nonneg hc hr
  exact critical_run_le r c hr 1 ((1 + c) * r) (by decide) (by grind) h hij

/-- **The response of a critical spring is at most `1`**: the thing never goes back past where
it was let go. -/
theorem critical_response_le_one (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1)
    (i : Nat) : (critical r c).response i ≤ 1 :=
  critical_response_le r c hr hc h (Nat.zero_le i)

/-- **The response of a critical spring is positive**: the thing never reaches its target, and
never passes it. -/
theorem critical_response_pos (r c : Rat) (hr : 0 < r) (hc : 0 ≤ c) (i : Nat) :
    0 < (critical r c).response i := by
  have a := Rat.mul_nonneg hc (Rat.natCast_nonneg (a := i))
  rw [critical_response]
  exact Rat.mul_pos (by grind) (Rat.pow_pos hr)

/-- **Settling, by a fixed share.** The response of a critical spring is at most `restⁱ`: what
is left falls at least as fast as the rest of one piece, each piece. -/
theorem critical_response_le_pow (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (i : Nat) :
    (critical r c).response i ≤ ((1 + c) * r) ^ i := by
  induction i with
  | zero =>
    rw [Rat.pow_zero]
    exact Rat.le_refl
  | succ i ih =>
    have hi := Rat.mul_nonneg hc (Rat.natCast_nonneg (a := i))
    have hR : 0 ≤ r ^ i := Rat.pow_nonneg hr
    have hrest : 0 ≤ (1 + c) * r := Rat.mul_nonneg (by grind) hr
    have b := Rat.mul_le_mul_of_nonneg_left ih hrest
    have a := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hc hi) hr) hR
    rw [critical_response] at b ⊢
    rw [rat_natCast_succ, Rat.pow_succ, Rat.pow_succ]
    generalize ((1 + c) * r) ^ i = P at b ⊢
    generalize r ^ i = R at a b ⊢
    generalize (i : Rat) = n at a b ⊢
    grind

/-- **Settling, from a piece on.** From the piece `n` on, the response of a critical spring is
at most `(1 + c n) rⁿ`: a caller evaluates that number to know how near the thing is. -/
theorem critical_settled (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1)
    {n i : Nat} (hni : n ≤ i) : (critical r c).response i ≤ (1 + c * (n : Rat)) * r ^ n := by
  rw [← critical_response]
  exact critical_response_le r c hr hc h hni

/-! ## A calm thing, on either side of its target -/

/-- The mirror image of a calm thing is calm. -/
theorem Calm.neg {r x0 x1 : Rat} (h : Calm r x0 x1) : Calm r (-x0) (-x1) := by
  rcases h with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · exact Or.inr ⟨by grind, by grind, by grind⟩
  · exact Or.inl ⟨by grind, by grind, by grind⟩

/-- **A calm thing stays calm**, on either side of its target. At every piece of its run on a
critical spring it has not passed its target, it is not moving away, and it is not moving toward
the target faster than `r` a piece. -/
theorem critical_stays_calm (r c : Rat) (hr : 0 ≤ r) {x0 x1 : Rat} (h : Calm r x0 x1) (i : Nat) :
    Calm r ((critical r c).run x0 x1 i) ((critical r c).run x0 x1 (i + 1)) := by
  rcases h with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · exact Or.inl (critical_calm r c hr x0 x1 a b d i)
  · have m := critical_calm r c hr (-x0) (-x1) (by grind) (by grind) (by grind) i
    rw [run_neg, run_neg] at m
    exact Or.inr ⟨by grind, by grind, by grind⟩

/-- The response of a critical spring is the run of a calm thing, where `0 ≤ r`, `0 ≤ c` and
the rest is at most `1`. -/
theorem critical_rest_calm (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1) :
    Calm r 1 ((1 + c) * r) := by
  have a := Rat.mul_nonneg hc hr
  exact Or.inl ⟨by decide, by grind, h⟩

/-! ## A step that is interrupted, on a critical spring -/

/-- **A gap of three pictures is a gap at every piece of an interrupted step.** Two things take
one critical spring. Each was let go at rest from its place in the first picture toward its
place in the second, and both were sent on toward the third at one cut, each with the place and
the momentum it had. Where the second thing is `g` or more past the first in all three
pictures, it is `g` or more past it at every piece after the cut, whenever the cut came. So the
order and the gaps of kept things outlast an interruption, and no easing is asked to stay in
range. -/
theorem critical_interrupted_gap (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1)
    (p0 p1 p2 q0 q1 q2 g : Rat) (h0 : p0 + g ≤ q0) (h1 : p1 + g ≤ q1) (h2 : p2 + g ≤ q2)
    (k i : Nat) :
    (critical r c).interrupted p0 p1 p2 k i + g ≤ (critical r c).interrupted q0 q1 q2 k i := by
  have w0 := (critical_response_calm r c hr hc h (k + i)).1
  have w1 := critical_response_le r c hr hc h (Nat.le_add_left i k)
  have w2 := critical_response_le_one r c hr hc h i
  rw [interrupted_mean, interrupted_mean]
  generalize (critical r c).response (k + i) = a at w0 w1 ⊢
  generalize (critical r c).response i = b at w1 w2 ⊢
  have m0 := Rat.mul_nonneg (show 0 ≤ q0 - p0 - g by grind) w0
  have m1 := Rat.mul_nonneg (show 0 ≤ q1 - p1 - g by grind) (show 0 ≤ b - a by grind)
  have m2 := Rat.mul_nonneg (show 0 ≤ q2 - p2 - g by grind) (show 0 ≤ 1 - b by grind)
  grind

/-- **A thing inside a room in three pictures does not leave it when its step is
interrupted.** It may go on away from its new target for a while, and it never goes past the
furthest of its three places. -/
theorem critical_interrupted_mem (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1)
    (lo hi p0 p1 p2 : Rat) (h0 : lo ≤ p0 ∧ p0 ≤ hi) (h1 : lo ≤ p1 ∧ p1 ≤ hi)
    (h2 : lo ≤ p2 ∧ p2 ≤ hi) (k i : Nat) :
    lo ≤ (critical r c).interrupted p0 p1 p2 k i ∧
      (critical r c).interrupted p0 p1 p2 k i ≤ hi := by
  have a := critical_interrupted_gap r c hr hc h lo lo lo p0 p1 p2 0 (by grind) (by grind)
    (by grind) k i
  have b := critical_interrupted_gap r c hr hc h p0 p1 p2 hi hi hi 0 (by grind) (by grind)
    (by grind) k i
  have e : ∀ x : Rat, (critical r c).interrupted x x x k i = x := by
    intro x
    rw [interrupted_mean]
    grind
  rw [e lo] at a
  rw [e hi] at b
  constructor <;> grind

/-! ## The easing of a critical spring -/

/-- **The share of each piece of a calm thing is from `0` to `1`.** -/
theorem critical_share_mem (r c : Rat) (hr : 0 ≤ r) {x0 x1 : Rat} (h : Calm r x0 x1)
    {n i : Nat} (hi : i ≤ n) :
    0 ≤ (critical r c).share x0 x1 n i ∧ (critical r c).share x0 x1 n i ≤ 1 := by
  have key : ∀ y0 y1 : Rat, 0 ≤ y0 → r * y0 ≤ y1 → y1 ≤ y0 →
      0 ≤ (critical r c).share y0 y1 n i ∧ (critical r c).share y0 y1 n i ≤ 1 := by
    intro y0 y1 h0 h1 h2
    have a := critical_run_le r c hr y0 y1 h0 h1 h2 (Nat.zero_le i)
    have b := critical_run_le r c hr y0 y1 h0 h1 h2 hi
    rw [run_zero] at a
    exact rat_div_mem_of_le (x := y0 - (critical r c).run y0 y1 i)
      (d := y0 - (critical r c).run y0 y1 n) (by grind) (by grind)
  rcases h with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · exact key x0 x1 a b d
  · rw [← share_neg]
    exact key (-x0) (-x1) (by grind) (by grind) (by grind)

/-- **The share of a later piece of a calm thing is no less than that of an earlier one.** -/
theorem critical_share_mono (r c : Rat) (hr : 0 ≤ r) {x0 x1 : Rat} (h : Calm r x0 x1) (n : Nat)
    {i j : Nat} (hij : i ≤ j) :
    (critical r c).share x0 x1 n i ≤ (critical r c).share x0 x1 n j := by
  have key : ∀ y0 y1 : Rat, 0 ≤ y0 → r * y0 ≤ y1 → y1 ≤ y0 →
      (critical r c).share y0 y1 n i ≤ (critical r c).share y0 y1 n j := by
    intro y0 y1 h0 h1 h2
    have a := critical_run_le r c hr y0 y1 h0 h1 h2 (Nat.zero_le n)
    have b := critical_run_le r c hr y0 y1 h0 h1 h2 hij
    rw [run_zero] at a
    exact rat_div_le_div_of_nonneg (c := y0 - (critical r c).run y0 y1 n) (by grind) (by grind)
  rcases h with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · exact key x0 x1 a b d
  · rw [← share_neg (critical r c) x0 x1 n i, ← share_neg (critical r c) x0 x1 n j]
    exact key (-x0) (-x1) (by grind) (by grind) (by grind)

/-- **The resumed easing of a calm thing on a critical spring stays in range**: it passes
`Easing.bounded`, for every number of pieces. It is the premise of the kit's laws of a step:
kept things that take one such easing keep their gaps and their order at every moment. -/
theorem critical_resumed_bounded (r c : Rat) (hr : 0 ≤ r) {x0 x1 : Rat} (h : Calm r x0 x1)
    (n : Nat) : ((critical r c).resumed x0 x1 n).bounded = true := by
  rw [resumed_stops]
  show ((List.range (n + 1)).map ((critical r c).stop x0 x1 n)).all
    (fun v => decide (0 ≤ v) && decide (v ≤ 1000)) = true
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  have m := critical_share_mem r c hr h (Nat.le_of_lt_succ (List.mem_range.mp hi))
  have k := Easing.mille_mem m.1 m.2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact k

/-- **The stops of the resumed easing of a calm thing never fall.** -/
theorem critical_resumed_rising (r c : Rat) (hr : 0 ≤ r) {x0 x1 : Rat} (h : Calm r x0 x1)
    (n : Nat) : ((List.range (n + 1)).map ((critical r c).stop x0 x1 n)).Pairwise (· ≤ ·) :=
  List.pairwise_map.mpr (List.Pairwise.imp
    (fun hlt => Easing.mille_mono (critical_share_mono r c hr h n (Nat.le_of_lt hlt)))
    List.pairwise_lt_range)

/-- **The resumed easing of a calm thing is proper**, where the thing is moving at all and the
easing has a piece. -/
theorem critical_resumed_proper (r c : Rat) (hr : 0 ≤ r) {x0 x1 : Rat} (h : Calm r x0 x1)
    (hne : x1 ≠ x0) {n : Nat} (hn : 0 < n) : ((critical r c).resumed x0 x1 n).Proper := by
  rcases h with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · exact resumed_proper _ x0 x1 n (critical_moved r c hr x0 x1 a b d hne hn)
  · rw [← resumed_neg]
    exact resumed_proper _ (-x0) (-x1) n
      (critical_moved r c hr (-x0) (-x1) (by grind) (by grind) (by grind) (by grind) hn)

/-- **How near the easing of a calm thing is to its spring**, at the stop of each piece. The
thing is right of its target, at `target + x0`. In exact numbers, the place read at the stop of
the piece `i` is no more than the last offset and a two-thousandth of the first below the place
of the run, and no more than a two-thousandth of the first above it. The last offset is what the
easing takes away so as to end on the target. -/
theorem critical_mixExact_stop_near (r c : Rat) (hr : 0 ≤ r) (target x0 x1 : Rat) (h0 : 0 ≤ x0)
    (h1 : r * x0 ≤ x1) (h2 : x1 ≤ x0) (hne : x1 ≠ x0) {n i : Nat} (hn : 0 < n) (hi : i ≤ n) :
    target + (critical r c).run x0 x1 i - (critical r c).run x0 x1 n - x0 / 2000 ≤
        mixExact (target + x0) target ((((critical r c).stop x0 x1 n i : Int) : Rat) / 1000) ∧
      mixExact (target + x0) target ((((critical r c).stop x0 x1 n i : Int) : Rat) / 1000) ≤
        target + (critical r c).run x0 x1 i + x0 / 2000 := by
  have m := critical_share_mem r c hr (Or.inl ⟨h0, h1, h2⟩) hi
  exact mixExact_stop_near _ target x0 x1 n i (critical_moved r c hr x0 x1 h0 h1 h2 hne hn) h0
    (critical_calm r c hr x0 x1 h0 h1 h2 n).1 m.1 m.2

/-- **The easing of a critical spring stays in range**, for every number of pieces, where
`0 ≤ r`, `0 ≤ c` and the rest is at most `1`. That its stops are from `0` to `1000` is known
from what the spring is, and no table is read. -/
theorem critical_easing_bounded (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1)
    (n : Nat) : ((critical r c).easing n).bounded = true :=
  critical_resumed_bounded r c hr (critical_rest_calm r c hr hc h) n

/-- **The stops of the easing of a critical spring never fall.** -/
theorem critical_easing_rising (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1)
    (n : Nat) :
    ((List.range (n + 1)).map ((critical r c).stop 1 ((1 + c) * r) n)).Pairwise (· ≤ ·) :=
  critical_resumed_rising r c hr (critical_rest_calm r c hr hc h) n

/-- **The easing of a critical spring is proper**, where it has a piece and the rest is less
than `1`. -/
theorem critical_easing_proper (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r < 1)
    {n : Nat} (hn : 0 < n) : ((critical r c).easing n).Proper :=
  critical_resumed_proper r c hr (critical_rest_calm r c hr hc (Rat.le_of_lt h))
    (Rat.ne_of_lt h) hn

/-! ## A spring that swings -/

/-- The square form of any spring is a square and `q - p² / 4` times the square of the first
offset, here four times over. -/
theorem energy_eq (s : Spring) (a b : Rat) :
    4 * s.energy a b = (2 * b - s.p * a) * (2 * b - s.p * a) + (4 * s.q - s.p * s.p) * (a * a) := by
  simp only [energy]
  grind

/-- **A spring that swings stays under a bound that shrinks.** For every spring,
`4 q - p²` times the square of an offset is at most four times the square form, which each
piece multiplies by `q`. Where `p² < 4 q` that bounds the offset. -/
theorem swing_sq_le (s : Spring) (x0 x1 : Rat) (i : Nat) :
    (4 * s.q - s.p * s.p) * (s.run x0 x1 i * s.run x0 x1 i) ≤ 4 * (s.q ^ i * s.energy x0 x1) := by
  have e := s.energy_run x0 x1 i
  have f := s.energy_eq (s.run x0 x1 i) (s.run x0 x1 (i + 1))
  have p := rat_mul_self_nonneg (2 * s.run x0 x1 (i + 1) - s.p * s.run x0 x1 i)
  rw [e] at f
  grind

/-- With `k = 1` a spring that swings is the critical one. -/
theorem under_one (r c : Rat) : under r 1 c = critical r c := by
  show (⟨2 * r * 1, r * r, (1 + c) * r⟩ : Spring) = ⟨2 * r, r * r, (1 + c) * r⟩
  rw [Rat.mul_one]

/-- **The offsets of a spring that swings are within `B rⁱ`.** `B` is any number that is not
negative with `energy x0 x1 ≤ (1 - k²) r² B²`: a rational number stands where the textbook has a
square root. -/
theorem under_bound (r k c x0 x1 B : Rat) (hr : 0 < r) (hk : k * k < 1) (hB : 0 ≤ B)
    (hE : (under r k c).energy x0 x1 ≤ (1 - k * k) * (r * r) * (B * B)) (i : Nat) :
    -(B * r ^ i) ≤ (under r k c).run x0 x1 i ∧ (under r k c).run x0 x1 i ≤ B * r ^ i := by
  have hw : 0 < (1 - k * k) * (r * r) := Rat.mul_pos (by grind) (Rat.mul_pos hr hr)
  have hR : 0 ≤ r ^ i * r ^ i := rat_mul_self_nonneg _
  have hP : 0 ≤ r ^ i := Rat.pow_nonneg (Rat.le_of_lt hr)
  have h1 := swing_sq_le (under r k c) x0 x1 i
  have h2 := Rat.mul_le_mul_of_nonneg_left hE hR
  have hq : (under r k c).q = r * r := rfl
  have hp : (under r k c).p = 2 * r * k := rfl
  rw [hq, hp, rat_mul_self_pow] at h1
  generalize (under r k c).energy x0 x1 = E at h1 h2
  generalize (under r k c).run x0 x1 i = x at h1 ⊢
  generalize r ^ i = R at h1 h2 hR hP ⊢
  have h3 : x * x * ((1 - k * k) * (r * r)) ≤ B * R * (B * R) * ((1 - k * k) * (r * r)) := by
    grind
  exact rat_abs_le_of_mul_self_le (Rat.mul_nonneg hB hP)
    ((Decimal.rat_mul_le_mul_right hw).mp h3)

/-- **The response of a spring that swings is within `B rⁱ`**, for any `B` that is not negative
with `1 - k² + c² ≤ (1 - k²) B²`. With the textbook's numbers that is its envelope. -/
theorem under_response_bound (r k c B : Rat) (hr : 0 < r) (hk : k * k < 1) (hB : 0 ≤ B)
    (hc : 1 - k * k + c * c ≤ (1 - k * k) * (B * B)) (i : Nat) :
    -(B * r ^ i) ≤ (under r k c).response i ∧ (under r k c).response i ≤ B * r ^ i := by
  refine under_bound r k c 1 ((k + c) * r) B hr hk hB ?_ i
  have a := Rat.mul_le_mul_of_nonneg_left hc (rat_mul_self_nonneg r)
  simp only [energy, under]
  grind

end Spring

end Whatwg.Svg.Scene
