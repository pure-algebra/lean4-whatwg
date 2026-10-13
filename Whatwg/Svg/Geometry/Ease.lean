import Whatwg.Svg.Scene.Ease
import Whatwg.Svg.Geometry.Monotone.Laws
import Whatwg.Svg.Geometry.Moment

/-!
# Whatwg.Svg.Geometry.Ease

Owner: what the family of an easing means in exact numbers, and the easings that never go back
(slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Ease.lean` turns an easing and tests whether it rises, on its data. This
module says what the two mean for the readings, in the exact numbers of
`Whatwg/Svg/Geometry/Moment.lean` and then in the whole numbers that a transition reads.

- **The turn of a cubic** (`Easing.cubicExact_out`, `Easing.exact_out_cubic`): at every exact
  progress `s` the turned cubic reads what is left of the whole after the cubic at `1 - s`. It
  is d3's `t => 1 - easeIn(1 - t)` (d3-ease `test/generic.js`, commit `4099c6d715f5`), as an
  identity of two polynomials.
- **Played backwards** (`Easing.backward_cubic`): a value on its way from `u` to `v` under a
  cubic, read at the progress `1 - s`, is the value on its way from `v` to `u` under the turned
  cubic at `s`. An exit that is an entrance played backwards is the opposite change with the
  turned easing.
- **An easing that passes `Easing.Rises` reads no less at a later progress**
  (`Easing.exact_mono`). For stops whose values never fall it is a straight line between two
  values in order. For a cubic it is a fact with no counterpart in a tween library: *a cubic
  whose two heights are from `0` to `1000` never goes back*, although its control points may
  go down between them (`cubic 1000 0` rises, and stands still at the middle).
- **In whole numbers** (`Easing.of_mono`, `Easing.at_mono`, `Transition.at_mono`): the reading
  at a later share, and the reading of a transition at a later moment, is no less. Rounding
  down keeps the order.
- **Nothing goes back** (`Transition.mix_mono`, `Transition.mix_anti`): a value on its way up
  under a transition whose easing rises is no lower at a later moment, and one on its way down
  is no higher. A kept thing that moves so travels toward its new place at every moment, on
  each axis.

What this module does not claim: the turn of stops at an exact progress between two stops,
which is the same line read from the other end and is not proved here (at the stops it is the
definition); that an easing which fails `Rises` goes back; anything for `inOut` in exact
numbers, where halving a value rounds it.

Every law here depends on `propext`, `Quot.sound` and `Classical.choice` at most.
-/

namespace Whatwg.Svg.Scene

open Whatwg.Svg.Value

namespace Easing

/-! ## The turn, in exact numbers -/

/-- **The turned cubic reads what is left of the whole after the cubic at `1 - s`**, at every
exact progress. -/
theorem cubicExact_out (y1 y2 : Int) (s : Rat) :
    cubicExact (1000 - y2) (1000 - y1) s = 1 - cubicExact y1 y2 (1 - s) := by
  simp only [cubicExact, Rat.intCast_sub, Rat.intCast_ofNat]
  grind

/-- **The turn of a cubic easing, in exact numbers.** -/
theorem exact_out_cubic (y1 y2 : Int) (s : Rat) :
    (cubic y1 y2).out.exact s = 1 - (cubic y1 y2).exact (1 - s) :=
  cubicExact_out y1 y2 s

/-- **A change played backwards is the opposite change under the turned easing.** The value on
its way from `u` to `v` under a cubic, at the progress `1 - s`, is the value on its way from
`v` to `u` under the turned cubic at `s`. -/
theorem backward_cubic (y1 y2 : Int) (u v s : Rat) :
    mixExact u v ((cubic y1 y2).exact (1 - s)) = mixExact v u ((cubic y1 y2).out.exact s) := by
  rw [exact_out_cubic]
  simp only [mixExact]
  grind

/-! ## Easings that never go back -/

/-- A number of per mille from `0` to `1000` is a share from `0` to `1`. -/
theorem share_of_mille {y : Int} (h0 : 0 ≤ y) (h1 : y ≤ 1000) :
    0 ≤ (y : Rat) / 1000 ∧ (y : Rat) / 1000 ≤ 1 := by
  have a : (0 : Rat) ≤ (y : Rat) := Rat.intCast_le_intCast.mpr h0
  have b : (y : Rat) ≤ (1000 : Rat) := Rat.intCast_le_intCast.mpr h1
  constructor <;> grind

/-- The rise of a cubic easing between two exact progresses, as their difference times a sum
of three products: the rise to the first height, the rise between the two heights and the rise
from the second, each with a weight that depends on the two progresses alone. -/
theorem cubicExact_rise (y1 y2 : Int) (s t : Rat) :
    cubicExact y1 y2 t - cubicExact y1 y2 s =
      (t - s) * ((y1 : Rat) / 1000 *
          ((1 - s) * (1 - s) + (1 - s) * (1 - t) + (1 - t) * (1 - t)) +
        (1 - (y1 : Rat) / 1000 - (1 - (y2 : Rat) / 1000)) *
          (3 * (s + t) - 2 * (s * s + s * t + t * t)) +
        (1 - (y2 : Rat) / 1000) * (s * s + s * t + t * t)) := by
  simp only [cubicExact]
  grind

/-- **A cubic whose two heights are from `0` to `1000` never goes back**: it reads no less at a
later exact progress. -/
theorem cubicExact_mono {y1 y2 : Int} (h1 : 0 ≤ y1) (h2 : y1 ≤ 1000) (h3 : 0 ≤ y2)
    (h4 : y2 ≤ 1000) {s t : Rat} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    cubicExact y1 y2 s ≤ cubicExact y1 y2 t := by
  obtain ⟨a0, a1⟩ := share_of_mille h1 h2
  obtain ⟨b0, b1⟩ := share_of_mille h3 h4
  have r := Monotone.rise_nonneg (d := 1) (α := (y1 : Rat) / 1000)
    (β := 1 - (y2 : Rat) / 1000) a0 a1 (by grind) (by grind) hs hst ht
  rw [← cubicExact_rise y1 y2 s t] at r
  grind

/-- In values that never fall, no value is more than the last. -/
theorem le_last {vs : List Int} (h : vs.Pairwise fun a b => a ≤ b) :
    ∀ v ∈ vs, v ≤ vs.getLast?.getD 0 := by
  intro v hv
  have hr : vs.reverse.Pairwise fun a b => b ≤ a := List.pairwise_reverse.mpr h
  have hv' : v ∈ vs.reverse := List.mem_reverse.mpr hv
  rw [← List.head?_reverse]
  generalize vs.reverse = r at hr hv'
  cases r with
  | nil => cases hv'
  | cons l rest =>
    show v ≤ l
    rcases List.mem_cons.mp hv' with rfl | hm
    · exact Int.le_refl _
    · exact (List.pairwise_cons.mp hr).1 v hm

/-- In values that never fall, a later place reads no less, where a place past the end reads a
value that none of them is more than. -/
theorem getD_mono_of {d : Int} : ∀ {vs : List Int}, (vs.Pairwise fun a b => a ≤ b) →
    (∀ v ∈ vs, v ≤ d) → ∀ {k m : Nat}, k ≤ m → vs.getD k d ≤ vs.getD m d
  | [], _, _, _, _, _ => Int.le_refl _
  | _ :: _, _, _, 0, 0, _ => Int.le_refl _
  | a :: rest, h, hd, 0, m + 1, _ =>
    getD_of_all (a ≤ ·) rest m d (hd a List.mem_cons_self) (List.pairwise_cons.mp h).1
  | a :: rest, h, hd, _ + 1, _ + 1, hkm =>
    getD_mono_of (vs := rest) (List.pairwise_cons.mp h).2
      (fun v hv => hd v (List.mem_cons_of_mem a hv)) (Nat.le_of_succ_le_succ hkm)

/-- **In stops that never fall, a later place reads no less**, and a place past the end reads
the last value. -/
theorem getD_mono {vs : List Int} (h : vs.Pairwise fun a b => a ≤ b) {k m : Nat} (hkm : k ≤ m) :
    vs.getD k (vs.getLast?.getD 0) ≤ vs.getD m (vs.getLast?.getD 0) :=
  getD_mono_of h (le_last h) hkm

/-- **Stops whose values never fall read no less at a later exact progress.** Past the last
stop they read the last value, so the later progress has no upper bound. -/
theorem stopsExact_mono {vs : List Int} (h : vs.Pairwise fun a b => a ≤ b) {s t : Rat}
    (hs : 0 ≤ s) (hst : s ≤ t) : stopsExact vs s ≤ stopsExact vs t := by
  have hn : (0 : Rat) ≤ ((vs.length - 1 : Nat) : Rat) := Rat.natCast_nonneg
  have hle0 := Rat.mul_le_mul_of_nonneg_left hst hn
  have hsn : 0 ≤ s * ((vs.length - 1 : Nat) : Rat) := Rat.mul_nonneg hs hn
  have htn : 0 ≤ t * ((vs.length - 1 : Nat) : Rat) := Rat.mul_nonneg (by grind) hn
  have hle : s * ((vs.length - 1 : Nat) : Rat) ≤ t * ((vs.length - 1 : Nat) : Rat) := by grind
  have fs := rat_sub_floor_toNat_mem hsn
  have ft := rat_sub_floor_toNat_mem htn
  have hij : (s * ((vs.length - 1 : Nat) : Rat)).floor.toNat ≤
      (t * ((vs.length - 1 : Nat) : Rat)).floor.toNat :=
    Int.toNat_le_toNat (Rat.le_floor_iff.mpr (Rat.le_trans (Rat.floor_le _) hle))
  have cast : ∀ k m : Nat, k ≤ m →
      ((vs.getD k (vs.getLast?.getD 0) : Int) : Rat) ≤
        ((vs.getD m (vs.getLast?.getD 0) : Int) : Rat) :=
    fun k m hkm => Rat.intCast_le_intCast.mpr (getD_mono h hkm)
  rw [stopsExact_piece vs s _ rfl, stopsExact_piece vs t _ rfl]
  generalize s * ((vs.length - 1 : Nat) : Rat) = x at hle fs hij ⊢
  generalize t * ((vs.length - 1 : Nat) : Rat) = y at hle ft hij ⊢
  generalize x.floor.toNat = i at fs hij ⊢
  generalize y.floor.toNat = j at ft hij ⊢
  by_cases hsame : i = j
  · subst hsame
    have ab := cast i (i + 1) (Nat.le_succ i)
    have p := Rat.mul_le_mul_of_nonneg_left (show x - (i : Rat) ≤ y - (i : Rat) by grind)
      (show (0 : Rat) ≤ ((vs.getD (i + 1) (vs.getLast?.getD 0) : Int) : Rat) -
        ((vs.getD i (vs.getLast?.getD 0) : Int) : Rat) by grind)
    grind
  · have hlt : i + 1 ≤ j := by omega
    have ab := cast i (i + 1) (Nat.le_succ i)
    have bc := cast (i + 1) j hlt
    have cd := cast j (j + 1) (Nat.le_succ j)
    have p1 := Rat.mul_le_mul_of_nonneg_left (show x - (i : Rat) ≤ 1 by grind)
      (show (0 : Rat) ≤ ((vs.getD (i + 1) (vs.getLast?.getD 0) : Int) : Rat) -
        ((vs.getD i (vs.getLast?.getD 0) : Int) : Rat) by grind)
    have p2 := Rat.mul_nonneg
      (show (0 : Rat) ≤ ((vs.getD (j + 1) (vs.getLast?.getD 0) : Int) : Rat) -
        ((vs.getD j (vs.getLast?.getD 0) : Int) : Rat) by grind)
      (show (0 : Rat) ≤ y - (j : Rat) by grind)
    grind

/-- **An easing that passes `Rises` reads no less at a later exact progress**, from `0` to
`1`. -/
theorem exact_mono {e : Easing} (h : e.Rises) {s t : Rat} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1) : e.exact s ≤ e.exact t := by
  cases e with
  | stops vs => exact stopsExact_mono h hs hst
  | cubic y1 y2 =>
    obtain ⟨a, b, c, d⟩ := h
    exact cubicExact_mono a b c d hs hst ht

/-! ## In whole numbers -/

/-- A count that is no more than another is no more as a rational number. -/
theorem natCast_le {m n : Nat} (h : m ≤ n) : (m : Rat) ≤ (n : Rat) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hk : (0 : Rat) ≤ (k : Rat) := Rat.natCast_nonneg
  rw [Rat.natCast_add]
  grind

/-- **An easing that passes `Rises` reads no less at a later share**, in whole numbers: the
reading of a transition. Rounding down keeps the order. -/
theorem of_mono {e : Easing} (h : e.Rises) {m n den : Nat} (hmn : m ≤ n) (hn : n ≤ den) :
    e.of m den ≤ e.of n den := by
  rw [of_eq_floor, of_eq_floor]
  rcases Nat.eq_zero_or_pos den with hd | hd
  · have hn0 : n = 0 := by omega
    have hm0 : m = 0 := by omega
    rw [hn0, hm0]
    exact Int.le_refl _
  · have hD : (0 : Rat) < (den : Rat) := rat_natCast_pos hd
    have hm' : (0 : Rat) ≤ (m : Rat) := Rat.natCast_nonneg
    have x := Decimal.rat_div_le_div hD (natCast_le hmn)
    have m0 := (rat_div_mem hD hm' (natCast_le (Nat.le_trans hmn hn))).1
    have n1 := (rat_div_mem hD (Rat.natCast_nonneg (a := n)) (natCast_le hn)).2
    have y := Rat.mul_le_mul_of_nonneg_left (exact_mono h m0 x n1) (show (0 : Rat) ≤ 1000 by decide)
    exact Rat.le_floor_iff.mpr (Rat.le_trans (Rat.floor_le _) y)

/-- **An easing that passes `Rises` reads no less at a later moment**, in per mille. -/
theorem at_mono {e : Easing} (h : e.Rises) {p q : Nat} (hpq : p ≤ q) (hq : q ≤ 1000) :
    e.at p ≤ e.at q := by
  rw [← of_thousand, ← of_thousand]
  exact of_mono h hpq hq

end Easing

namespace Transition

/-- **A transition whose easing rises reads no less at a later moment.** Before its delay,
between its delay and its end, and after its end alike. -/
theorem at_mono {tr : Transition} (h : tr.ease.Rises) {t u : Nat} (htu : t ≤ u) :
    tr.at t ≤ tr.at u := by
  have ends : tr.ease.at 0 ≤ tr.ease.at 1000 := Easing.at_mono h (Nat.zero_le _) (Nat.le_refl _)
  have lo : ∀ n, n ≤ tr.duration → tr.ease.at 0 ≤ tr.ease.of n tr.duration := fun n hn => by
    rw [← Easing.of_zero tr.ease tr.duration]
    exact Easing.of_mono h (Nat.zero_le n) hn
  have hi : ∀ n, n ≤ tr.duration → 0 < tr.duration →
      tr.ease.of n tr.duration ≤ tr.ease.at 1000 := fun n hn hd => by
    rw [← Easing.of_self tr.ease tr.duration hd]
    exact Easing.of_mono h hn (Nat.le_refl _)
  by_cases hu : tr.delay + tr.duration ≤ u
  · rw [at_done tr u hu]
    by_cases ht : tr.delay + tr.duration ≤ t
    · rw [at_done tr t ht]
      exact Int.le_refl _
    · by_cases hb : t ≤ tr.delay
      · rw [at_before tr t hb (by omega)]
        exact ends
      · rw [at_between tr t (by omega) (by omega)]
        exact hi _ (by omega) (by omega)
  · by_cases hub : u ≤ tr.delay
    · rw [at_before tr u hub (by omega), at_before tr t (by omega) (by omega)]
      exact Int.le_refl _
    · rw [at_between tr u (by omega) (by omega)]
      by_cases hb : t ≤ tr.delay
      · rw [at_before tr t hb (by omega)]
        exact lo _ (by omega)
      · rw [at_between tr t (by omega) (by omega)]
        exact Easing.of_mono h (by omega) (by omega)

/-- **Nothing goes back, on the way up.** A value that a transition takes from `u` up to `v`,
under an easing that rises, is no lower at a later moment. -/
theorem mix_mono {tr : Transition} (h : tr.ease.Rises) {u v : Int} (huv : u ≤ v) {t t' : Nat}
    (ht : t ≤ t') : mix u v (tr.at t) ≤ mix u v (tr.at t') :=
  Scene.mix_mono huv (at_mono h ht)

/-- **Nothing goes back, on the way down.** A value that a transition takes from `u` down to
`v`, under an easing that rises, is no higher at a later moment. -/
theorem mix_anti {tr : Transition} (h : tr.ease.Rises) {u v : Int} (huv : v ≤ u) {t t' : Nat}
    (ht : t ≤ t') : mix u v (tr.at t') ≤ mix u v (tr.at t) :=
  Scene.mix_anti huv (at_mono h ht)

end Transition

end Whatwg.Svg.Scene
