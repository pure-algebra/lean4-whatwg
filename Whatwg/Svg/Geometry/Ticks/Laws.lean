import Whatwg.Svg.Geometry.Ticks
import Whatwg.Svg.Geometry.Rational.Laws

/-!
# Whatwg.Svg.Geometry.Ticks.Laws

Owner: the laws of the round numbers of an axis (slice S22 of `docs/SVG-PACKAGE-PLAN.md`). d3
tests each of these on a few ranges (`d3-array`, `test/ticks-test.js`); here each holds of
every range.

- `exponent_spec`: `Ticks.exponent q` is the power of ten at or below `q`:
  `10 ^ e ≤ q < 10 ^ (e + 1)`.
- **The step is `1`, `2` or `5` times a power of ten** (`step_mantissa`), and is more than zero
  (`step_pos`).
- **The step is near the range shared out evenly** (`plain_near`): the square of the step and
  the square of the even share are within the factor `5 / 2` of each other. So the step is
  within the factor `1.59` of the gap asked for, on either side. That is what d3's three
  square roots are for, said without a root.
- **The ticks are the multiples of the step that lie in the range, and no other**
  (`mem_ticks`). So a tick is a multiple of the step, it lies within the bounds
  (`ticks_within`), and no multiple of the step inside the range is left out.
- **The ticks rise** (`between_rising`), each more than the one before, and a range that falls
  has the same ticks in the other order (`ticks_reverse`).
- **How many ticks** (`between_count`): with `n` ticks, `n - 1` steps are no longer than the
  range, and `n + 1` steps are longer.

The bound on the count of the ticks by the count asked for follows from `plain_near` and
`between_count` by squaring. It is `plain_count` of `Whatwg/Svg/Geometry/Ticks/Count.lean`.

What this module does not claim: anything of a range that falls beyond `ticks_reverse`; a
step for a range of one value.
-/

namespace Whatwg.Svg.Value

namespace Ticks

/-! ## The power of ten at or below a number -/

/-- A whole number of one or more is between two powers of ten, the lesser of which
`magnitude` names. -/
theorem magnitude_spec (n : Nat) (h : 1 ≤ n) :
    10 ^ magnitude n ≤ n ∧ n < 10 ^ (magnitude n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n < 10
    · rw [magnitude, if_pos hn]
      exact ⟨h, hn⟩
    · rw [magnitude, if_neg hn]
      obtain ⟨h1, h2⟩ := ih (n / 10) (by omega) (by omega)
      rw [Nat.pow_succ] at h2
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
      generalize 10 ^ magnitude (n / 10) = x at h1 h2 ⊢
      omega

/-- A power of ten as a whole number is that power of ten as a rational number. -/
theorem natCast_ten_pow (k : Nat) : ((10 ^ k : Nat) : Rat) = (10 : Rat) ^ k := by
  rw [Rat.natCast_pow, Rat.natCast_ofNat]

theorem ten_zpow_natCast (k : Nat) : (10 : Rat) ^ ((k : Nat) : Int) = (10 : Rat) ^ k :=
  Rat.zpow_natCast 10 k

theorem ten_zpow_neg_natCast (k : Nat) :
    (10 : Rat) ^ (-((k : Nat) : Int)) = 1 / (10 : Rat) ^ k := by
  rw [Rat.zpow_neg, Rat.zpow_natCast, Rat.div_def, Rat.one_mul]

/-- Of two numbers more than zero, one is less than the reciprocal of the other exactly when
the other is less than the reciprocal of the one. -/
theorem lt_inv_comm {q t : Rat} (hq : 0 < q) (ht : 0 < t) : t < 1 / q ↔ q < 1 / t := by
  rw [Rat.lt_div_iff hq, Rat.lt_div_iff ht, Rat.mul_comm]

/-- **The power of ten at or below a number.** For `q` more than zero,
`10 ^ exponent q ≤ q < 10 ^ (exponent q + 1)`. -/
theorem exponent_spec {q : Rat} (h : 0 < q) :
    (10 : Rat) ^ exponent q ≤ q ∧ q < (10 : Rat) ^ (exponent q + 1) := by
  unfold exponent
  by_cases h1 : 1 ≤ q
  · rw [if_pos h1]
    have hf : (1 : Int) ≤ q.floor := Rat.le_floor_iff.mpr (by rw [Rat.intCast_ofNat]; exact h1)
    obtain ⟨m1, m2⟩ := magnitude_spec q.floor.toNat (by omega)
    have e : ((q.floor.toNat : Nat) : Int) = q.floor := Int.toNat_of_nonneg (by omega)
    generalize magnitude q.floor.toNat = k at m1 m2 ⊢
    have a1 : ((10 ^ k : Nat) : Int) ≤ q.floor := e ▸ Int.ofNat_le.mpr m1
    have a2 : q.floor < ((10 ^ (k + 1) : Nat) : Int) := e ▸ Int.ofNat_lt.mpr m2
    have b1 := Rat.le_floor_iff.mp a1
    have b2 := Rat.floor_lt_iff.mp a2
    rw [Rat.intCast_natCast, natCast_ten_pow] at b1 b2
    have e2 : ((k : Nat) : Int) + 1 = ((k + 1 : Nat) : Int) := by omega
    rw [e2, ten_zpow_natCast, ten_zpow_natCast]
    exact ⟨b1, b2⟩
  · rw [if_neg h1]
    have hx : (1 : Rat) < 1 / q :=
      (Rat.lt_div_iff h).mpr (by rw [Rat.one_mul]; exact Rat.not_le.mp h1)
    have hc : (1 : Int) < (1 / q).ceil := Rat.lt_ceil_iff.mpr (by rw [Rat.intCast_ofNat]; exact hx)
    have e : (((1 / q).ceil.toNat : Nat) : Int) = (1 / q).ceil := Int.toNat_of_nonneg (by omega)
    obtain ⟨m1, m2⟩ := magnitude_spec ((1 / q).ceil.toNat - 1) (by omega)
    generalize magnitude ((1 / q).ceil.toNat - 1) = j at m1 m2 ⊢
    have n1 : 10 ^ j < (1 / q).ceil.toNat := by omega
    have n2 : (1 / q).ceil.toNat ≤ 10 ^ (j + 1) := by omega
    have a1 : ((10 ^ j : Nat) : Int) < (1 / q).ceil := e ▸ Int.ofNat_lt.mpr n1
    have a2 : (1 / q).ceil ≤ ((10 ^ (j + 1) : Nat) : Int) := e ▸ Int.ofNat_le.mpr n2
    have b1 := Rat.lt_ceil_iff.mp a1
    have b2 := Rat.ceil_le_iff.mp a2
    rw [Rat.intCast_natCast, natCast_ten_pow] at b1 b2
    have p1 : (0 : Rat) < (10 : Rat) ^ j := Rat.pow_pos (by decide)
    have p2 : (0 : Rat) < (10 : Rat) ^ (j + 1) := Rat.pow_pos (by decide)
    have e1 : -((j : Int) + 1) = -(((j + 1 : Nat)) : Int) := by omega
    have e2 : -((j : Int) + 1) + 1 = -((j : Nat) : Int) := by omega
    rw [e2, ten_zpow_neg_natCast, e1, ten_zpow_neg_natCast]
    exact ⟨Rat.not_lt.mp fun hlt => absurd ((lt_inv_comm h p2).mpr hlt) (Rat.not_lt.mpr b2),
      (lt_inv_comm h p1).mp b1⟩

/-- A number over the power of ten at or below it is from one to less than ten. -/
theorem lead_spec {q : Rat} (h : 0 < q) : 1 ≤ lead q ∧ lead q < 10 := by
  obtain ⟨h1, h2⟩ := exponent_spec h
  have hp := Decimal.ratTen_zpow_pos (exponent q)
  rw [Rat.zpow_add_one Decimal.ratTen_ne] at h2
  unfold lead
  generalize (10 : Rat) ^ exponent q = p at h1 h2 hp ⊢
  constructor
  · exact Rat.not_lt.mp fun hlt =>
      absurd ((Rat.div_lt_iff hp).mp hlt) (by rw [Rat.one_mul]; exact Rat.not_lt.mpr h1)
  · exact (Rat.div_lt_iff hp).mpr (by rw [Rat.mul_comm]; exact h2)

/-! ## The round number nearest a number -/

/-- **Two numbers are near**: the square of each is within the factor `5 / 2` of the square of
the other. So each is within the factor `1.59` of the other. -/
def Near (s q : Rat) : Prop := 2 * (s * s) ≤ 5 * (q * q) ∧ 2 * (q * q) < 5 * (s * s)

/-- The numbers of a value whose mantissa is more than zero is more than zero. -/
theorem toRat_pos {d : Decimal} (h : 0 < d.mantissa) : 0 < d.toRat :=
  Rat.mul_pos (Rat.intCast_pos.mpr h) (Decimal.ratTen_zpow_pos _)

/-- **A round number is `1`, `2` or `5` times a power of ten.** -/
theorem nearest_mantissa (q : Rat) :
    (nearest q).mantissa = 1 ∨ (nearest q).mantissa = 2 ∨ (nearest q).mantissa = 5 := by
  unfold nearest
  by_cases c1 : 50 ≤ lead q * lead q
  · rw [if_pos c1]
    exact Or.inl rfl
  · rw [if_neg c1]
    by_cases c2 : 10 ≤ lead q * lead q
    · rw [if_pos c2]
      exact Or.inr (Or.inr rfl)
    · rw [if_neg c2]
      by_cases c3 : 2 ≤ lead q * lead q
      · rw [if_pos c3]
        exact Or.inr (Or.inl rfl)
      · rw [if_neg c3]
        exact Or.inl rfl

/-- A round number is more than zero. -/
theorem nearest_pos (q : Rat) : 0 < (nearest q).toRat :=
  toRat_pos (by
    rcases nearest_mantissa q with h | h | h
    · omega
    · omega
    · omega)

/-- Two multiples of one number that is more than zero are near where their multipliers are. -/
theorem near_mul {m p c : Rat} (hp : 0 < p) (h1 : 2 * (c * c) ≤ 5 * (m * m))
    (h2 : 2 * (m * m) < 5 * (c * c)) : Near (c * p) (m * p) := by
  have hpp : 0 < p * p := Rat.mul_pos hp hp
  have a := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hpp)
  have b := Rat.mul_lt_mul_of_pos_right h2 hpp
  constructor
  · grind
  · grind

/-- **The round number nearest a number is near it.** For `q` more than zero, the square of
`nearest q` and the square of `q` are within the factor `5 / 2` of each other. -/
theorem nearest_near {q : Rat} (h : 0 < q) : Near (nearest q).toRat q := by
  obtain ⟨l1, l2⟩ := lead_spec h
  have hp := Decimal.ratTen_zpow_pos (exponent q)
  have hq : lead q * (10 : Rat) ^ exponent q = q := Rat.div_mul_cancel (Rat.ne_of_gt hp)
  have l0 : (0 : Rat) < lead q := by grind
  have m1 : lead q * 1 ≤ lead q * lead q := Rat.mul_le_mul_of_nonneg_left l1 (Rat.le_of_lt l0)
  have m2 : lead q * lead q < lead q * 10 := Rat.mul_lt_mul_of_pos_left l2 l0
  unfold nearest
  by_cases c1 : 50 ≤ lead q * lead q
  · have e : (⟨1, exponent q + 1⟩ : Decimal).toRat = 10 * (10 : Rat) ^ exponent q := by
      show ((1 : Int) : Rat) * (10 : Rat) ^ (exponent q + 1) = 10 * (10 : Rat) ^ exponent q
      rw [Rat.intCast_ofNat, Rat.zpow_add_one Decimal.ratTen_ne, Rat.one_mul, Rat.mul_comm]
    have k := near_mul (c := 10) hp (m := lead q) (by grind) (by grind)
    rw [hq] at k
    rw [if_pos c1, e]
    exact k
  · rw [if_neg c1]
    by_cases c2 : 10 ≤ lead q * lead q
    · have e : (⟨5, exponent q⟩ : Decimal).toRat = 5 * (10 : Rat) ^ exponent q := by
        show ((5 : Int) : Rat) * (10 : Rat) ^ exponent q = 5 * (10 : Rat) ^ exponent q
        rw [Rat.intCast_ofNat]
      have k := near_mul (c := 5) hp (m := lead q) (by grind) (by grind)
      rw [hq] at k
      rw [if_pos c2, e]
      exact k
    · rw [if_neg c2]
      by_cases c3 : 2 ≤ lead q * lead q
      · have e : (⟨2, exponent q⟩ : Decimal).toRat = 2 * (10 : Rat) ^ exponent q := by
          show ((2 : Int) : Rat) * (10 : Rat) ^ exponent q = 2 * (10 : Rat) ^ exponent q
          rw [Rat.intCast_ofNat]
        have k := near_mul (c := 2) hp (m := lead q) (by grind) (by grind)
        rw [hq] at k
        rw [if_pos c3, e]
        exact k
      · have e : (⟨1, exponent q⟩ : Decimal).toRat = 1 * (10 : Rat) ^ exponent q := by
          show ((1 : Int) : Rat) * (10 : Rat) ^ exponent q = 1 * (10 : Rat) ^ exponent q
          rw [Rat.intCast_ofNat]
        have k := near_mul (c := 1) hp (m := lead q) (by grind) (by grind)
        rw [hq] at k
        rw [if_neg c3, e]
        exact k

/-! ## The step of a range -/

/-- The step of a range is the step for its count, or for the count `1` the step for two. -/
theorem step_cases (start stop : Rat) (count : Nat) :
    step start stop count = plain start stop count ∨
      step start stop count = plain start stop 2 := by
  unfold step
  by_cases h : count = 1 ∧ high stop (plain start stop 1) < low start (plain start stop 1)
  · rw [if_pos h]
    exact Or.inr rfl
  · rw [if_neg h]
    exact Or.inl rfl

/-- For a count other than `1` the step is the round number nearest the even share. -/
theorem step_of_ne_one (start stop : Rat) {count : Nat} (h : count ≠ 1) :
    step start stop count = plain start stop count := by
  unfold step
  rw [if_neg fun hc => h hc.1]

/-- **The step is `1`, `2` or `5` times a power of ten.** -/
theorem step_mantissa (start stop : Rat) (count : Nat) :
    (step start stop count).mantissa = 1 ∨ (step start stop count).mantissa = 2 ∨
      (step start stop count).mantissa = 5 := by
  rcases step_cases start stop count with h | h
  · rw [h]
    exact nearest_mantissa _
  · rw [h]
    exact nearest_mantissa _

/-- **The step is more than zero.** -/
theorem step_pos (start stop : Rat) (count : Nat) : 0 < (step start stop count).toRat := by
  rcases step_cases start stop count with h | h
  · rw [h]
    exact nearest_pos _
  · rw [h]
    exact nearest_pos _

/-- **The step is near the range shared out evenly.** For a range that rises and a count that
is not zero, the round number for the count and the length of the range over the count are
within the factor `1.59` of each other. -/
theorem plain_near {start stop : Rat} (h : start < stop) {count : Nat} (hc : count ≠ 0) :
    Near (plain start stop count).toRat ((stop - start) / (count : Rat)) := by
  have hn : (0 : Rat) < (count : Rat) := Rat.natCast_pos.mpr (Nat.pos_of_ne_zero hc)
  have hw : (0 : Rat) < stop - start := by grind
  have hq : (0 : Rat) < (stop - start) / (count : Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_pos hw (Rat.inv_pos.mpr hn)
  exact nearest_near hq

/-! ## The multiples of a step in a range -/

/-- The number of a multiple of a step is the multiple of the number of the step. -/
theorem toRat_times (s : Decimal) (k : Int) : (times s k).toRat = (k : Rat) * s.toRat := by
  show ((k * s.mantissa : Int) : Rat) * (10 : Rat) ^ s.exponent =
    (k : Rat) * ((s.mantissa : Rat) * (10 : Rat) ^ s.exponent)
  rw [Rat.intCast_mul, Rat.mul_assoc]

/-- A multiplier is no less than the first exactly when its multiple is no less than the
start. -/
theorem low_le_iff {start : Rat} {s : Decimal} (hs : 0 < s.toRat) (k : Int) :
    low start s ≤ k ↔ start ≤ (k : Rat) * s.toRat := by
  unfold low
  rw [Rat.ceil_le_iff]
  constructor
  · intro h
    exact Rat.not_lt.mp fun hlt => absurd h (Rat.not_le.mpr ((Rat.lt_div_iff hs).mpr hlt))
  · intro h
    exact Rat.not_lt.mp fun hlt => absurd h (Rat.not_le.mpr ((Rat.lt_div_iff hs).mp hlt))

/-- A multiplier is no more than the last exactly when its multiple is no more than the
stop. -/
theorem le_high_iff {stop : Rat} {s : Decimal} (hs : 0 < s.toRat) (k : Int) :
    k ≤ high stop s ↔ (k : Rat) * s.toRat ≤ stop := by
  unfold high
  rw [Rat.le_floor_iff]
  constructor
  · intro h
    exact Rat.not_lt.mp fun hlt => absurd h (Rat.not_le.mpr ((Rat.div_lt_iff hs).mpr hlt))
  · intro h
    exact Rat.not_lt.mp fun hlt => absurd h (Rat.not_le.mpr ((Rat.div_lt_iff hs).mp hlt))

/-- **The multiples of a step in a range are those that lie in it, and no other.** -/
theorem mem_between {start stop : Rat} {s : Decimal} (hs : 0 < s.toRat) (t : Decimal) :
    t ∈ between start stop s ↔
      ∃ k : Int, t = times s k ∧ start ≤ (k : Rat) * s.toRat ∧ (k : Rat) * s.toRat ≤ stop := by
  unfold between
  rw [List.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [List.mem_range] at hn
    exact ⟨low start s + n, rfl, (low_le_iff hs _).mp (by omega), (le_high_iff hs _).mp (by omega)⟩
  · rintro ⟨k, rfl, h1, h2⟩
    have a := (low_le_iff hs k).mpr h1
    have b := (le_high_iff hs k).mpr h2
    have e : low start s + ((k - low start s).toNat : Int) = k := by omega
    exact ⟨(k - low start s).toNat, List.mem_range.mpr (by omega), by rw [e]⟩

/-- **The multiples of a step in a range rise**: each is more than the one before. -/
theorem between_rising (start stop : Rat) {s : Decimal} (hs : 0 < s.toRat) :
    ((between start stop s).map Decimal.toRat).Pairwise (· < ·) := by
  unfold between
  rw [List.pairwise_map, List.pairwise_map]
  refine List.Pairwise.imp (fun {a b} hab => ?_) List.pairwise_lt_range
  rw [toRat_times, toRat_times]
  exact Rat.mul_lt_mul_of_pos_right (Rat.intCast_lt_intCast.mpr (by omega)) hs

/-! ## The ticks of a range -/

/-- **The ticks are the multiples of the step that lie in the range, and no other**, for a
range that rises and a count that is not zero. -/
theorem mem_ticks {start stop : Rat} (h : start < stop) {count : Nat} (hc : count ≠ 0)
    (t : Decimal) :
    t ∈ ticks start stop count ↔
      ∃ k : Int, t = times (step start stop count) k ∧
        start ≤ (k : Rat) * (step start stop count).toRat ∧
        (k : Rat) * (step start stop count).toRat ≤ stop := by
  unfold ticks
  rw [if_neg fun hn => hn.elim hc (Rat.ne_of_lt h), if_pos h]
  exact mem_between (step_pos start stop count) t

/-- **A tick lies within the bounds.** -/
theorem ticks_within {start stop : Rat} (h : start < stop) {count : Nat} (hc : count ≠ 0)
    {t : Decimal} (ht : t ∈ ticks start stop count) : start ≤ t.toRat ∧ t.toRat ≤ stop := by
  obtain ⟨k, rfl, h1, h2⟩ := (mem_ticks h hc t).mp ht
  rw [toRat_times]
  exact ⟨h1, h2⟩

/-- **The ticks of a range that rises rise.** -/
theorem ticks_rising {start stop : Rat} (h : start < stop) (count : Nat) :
    (values start stop count).Pairwise (· < ·) := by
  unfold values ticks
  by_cases hn : count = 0 ∨ start = stop
  · rw [if_pos hn]
    exact List.Pairwise.nil
  · rw [if_neg hn, if_pos h]
    exact between_rising start stop (step_pos start stop count)

/-- **A range that falls has the ticks of the range that rises, in the other order.** -/
theorem ticks_reverse {start stop : Rat} (h : start < stop) (count : Nat) :
    ticks stop start count = (ticks start stop count).reverse := by
  have hne : ¬ stop < start := Rat.not_lt.mpr (Rat.le_of_lt h)
  unfold ticks
  by_cases hc : count = 0
  · rw [if_pos (Or.inl hc), if_pos (Or.inl hc)]
    rfl
  · rw [if_neg fun hn => hn.elim hc (Rat.ne_of_gt h), if_neg hne,
      if_neg fun hn => hn.elim hc (Rat.ne_of_lt h), if_pos h]

/-! ## How many ticks -/

/-- **How many multiples of a step a range holds.** With `n` of them, `n - 1` steps are no
longer than the range and `n + 1` steps are longer. -/
theorem between_count {start stop : Rat} (h : start ≤ stop) {s : Decimal} (hs : 0 < s.toRat) :
    (((between start stop s).length : Rat) - 1) * s.toRat ≤ stop - start ∧
      stop - start < (((between start stop s).length : Rat) + 1) * s.toRat := by
  have f1 : ¬ start ≤ ((low start s - 1 : Int) : Rat) * s.toRat := fun hle => by
    have := (low_le_iff hs (low start s - 1)).mpr hle
    omega
  have f2 : ¬ ((high stop s + 1 : Int) : Rat) * s.toRat ≤ stop := fun hle => by
    have := (le_high_iff hs (high stop s + 1)).mpr hle
    omega
  have f3 := (low_le_iff hs (low start s)).mp (Int.le_refl _)
  have f4 := (le_high_iff hs (high stop s)).mp (Int.le_refl _)
  rw [Rat.intCast_sub, Rat.intCast_ofNat] at f1
  rw [Rat.intCast_add, Rat.intCast_ofNat] at f2
  have f5 : low start s - 1 ≤ high stop s := by
    refine Int.not_lt.mp fun hlt => ?_
    have hle : ((high stop s + 1 : Int) : Rat) ≤ ((low start s - 1 : Int) : Rat) :=
      Rat.intCast_le_intCast.mpr (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hs)
    rw [Rat.intCast_sub, Rat.intCast_add, Rat.intCast_ofNat] at hm
    grind
  have en : (((between start stop s).length : Nat) : Int) = high stop s - low start s + 1 := by
    unfold between
    rw [List.length_map, List.length_range]
    omega
  have er : ((between start stop s).length : Rat) =
      (high stop s : Rat) - (low start s : Rat) + 1 := by
    rw [← Rat.intCast_natCast, en, Rat.intCast_add, Rat.intCast_sub, Rat.intCast_ofNat]
  rw [er]
  generalize (high stop s : Rat) = hi at f2 f4 ⊢
  generalize (low start s : Rat) = lo at f1 f3 ⊢
  generalize s.toRat = w at hs f1 f2 f3 f4 ⊢
  constructor
  · grind
  · grind

end Ticks

end Whatwg.Svg.Value
