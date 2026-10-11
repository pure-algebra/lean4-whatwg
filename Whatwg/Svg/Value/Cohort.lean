import Whatwg.Svg.Value.Number

/-!
# Whatwg.Svg.Value.Cohort

Owner: the law that the canonical value of an exact decimal decides when two decimals denote
one number (slice S4b of `docs/SVG-PACKAGE-PLAN.md`, the number). It closes the sentence that
`Whatwg/Svg/Value/Number.lean` leaves open. The definitions are that module's: `Decimal.Same`,
`Decimal.reduce`, `Decimal.isReduced` and `Decimal.tidy`.

The values of one number are its cohort. This module proves:

- `Same` is an equivalence: `Same.refl`, `Same.symm` and `Same.trans`.
- A cohort has one canonical value: `eq_of_same_of_isReduced`.
- The main law, `same_iff_reduce`: two values denote one number exactly when their canonical
  values are equal.
- `tidy` keeps the number: `same_tidy`.
- `Same` is decidable by a `reduce` on each side: `decidableSame`. The decision takes no power
  of ten, whatever the exponents.

The route is one lemma, `same_iff_scaled`: `Same` holds exactly when the two mantissas agree at
any one common exponent. Transitivity compares three values at the least of their exponents.

What this module does not claim: that `Same` is equality in a type of numbers, since no such
type is built here and `Same` is its own statement on the integers; that `tidy` returns a
canonical value (`15e1` becomes `150`, which `isReduced` refuses); that the reader returns a
canonical value; or any law of order, rounding or arithmetic on decimals.
-/

namespace Whatwg.Svg.Value.Decimal

/-! ## Powers of ten -/

/-- A power of ten is not zero. -/
theorem ten_pow_ne_zero (n : Nat) : (10 : Int) ^ n ≠ 0 :=
  Int.pow_ne_zero (by decide)

/-- Ten divides a mantissa that carries at least one power of ten. -/
theorem mul_ten_pow_succ_emod (m : Int) (n : Nat) : m * 10 ^ (n + 1) % 10 = 0 := by
  rw [Int.pow_succ, ← Int.mul_assoc, Int.mul_emod_left]

/-! ## The relation at a common exponent -/

/-- `Same` with both sides scaled by `r` more powers of ten. -/
theorem same_iff_shift (a b : Decimal) (r : Nat) :
    a.Same b ↔
      a.mantissa * 10 ^ ((a.exponent - b.exponent).toNat + r) =
        b.mantissa * 10 ^ ((b.exponent - a.exponent).toNat + r) := by
  rw [Int.pow_add, Int.pow_add, ← Int.mul_assoc, ← Int.mul_assoc]
  constructor
  · intro h
    have h' : a.mantissa * 10 ^ (a.exponent - b.exponent).toNat =
        b.mantissa * 10 ^ (b.exponent - a.exponent).toNat := h
    rw [h']
  · intro h
    exact Int.eq_of_mul_eq_mul_right (ten_pow_ne_zero r) h

/-- Two values denote one number exactly when their mantissas agree at one common exponent.
`p` and `q` are the powers of ten that bring the two values to it. -/
theorem same_iff_scaled (a b : Decimal) (p q : Nat) (h : a.exponent - p = b.exponent - q) :
    a.Same b ↔ a.mantissa * 10 ^ p = b.mantissa * 10 ^ q := by
  have hp : (a.exponent - b.exponent).toNat + (p - (a.exponent - b.exponent).toNat) = p := by
    omega
  have hq : (b.exponent - a.exponent).toNat + (p - (a.exponent - b.exponent).toNat) = q := by
    omega
  have key := same_iff_shift a b (p - (a.exponent - b.exponent).toNat)
  rw [hp, hq] at key
  exact key

/-- `Same` at an exponent `k` that is at most both exponents. -/
theorem same_iff_at (a b : Decimal) (k : Int) (ha : k ≤ a.exponent) (hb : k ≤ b.exponent) :
    a.Same b ↔
      a.mantissa * 10 ^ (a.exponent - k).toNat = b.mantissa * 10 ^ (b.exponent - k).toNat :=
  same_iff_scaled a b (a.exponent - k).toNat (b.exponent - k).toNat (by omega)

/-! ## `Same` is an equivalence -/

/-- A value denotes its own number. -/
theorem Same.refl (a : Decimal) : a.Same a :=
  Eq.refl (a.mantissa * 10 ^ (a.exponent - a.exponent).toNat)

/-- `Same` is symmetric. -/
theorem Same.symm {a b : Decimal} (h : a.Same b) : b.Same a :=
  Eq.symm h

/-- `Same` is transitive: the three values are compared at the least of their exponents. -/
theorem Same.trans {a b c : Decimal} (hab : a.Same b) (hbc : b.Same c) : a.Same c := by
  have ha : min a.exponent (min b.exponent c.exponent) ≤ a.exponent := by omega
  have hb : min a.exponent (min b.exponent c.exponent) ≤ b.exponent := by omega
  have hc : min a.exponent (min b.exponent c.exponent) ≤ c.exponent := by omega
  exact (same_iff_at a c _ ha hc).mpr
    (((same_iff_at a b _ ha hb).mp hab).trans ((same_iff_at b c _ hb hc).mp hbc))

/-! ## One canonical value in a cohort -/

/-- Zero denotes only zero: a value with mantissa zero shares its number only with such
values. -/
theorem Same.mantissa_eq_zero {a b : Decimal} (h : a.Same b) (ha : a.mantissa = 0) :
    b.mantissa = 0 := by
  have h' : a.mantissa * 10 ^ (a.exponent - b.exponent).toNat =
      b.mantissa * 10 ^ (b.exponent - a.exponent).toNat := h
  rw [ha, Int.zero_mul] at h'
  cases Int.mul_eq_zero.mp h'.symm with
  | inl hb => exact hb
  | inr hp => exact absurd hp (ten_pow_ne_zero _)

/-- A value whose mantissa does not end in zero has the greatest exponent of its cohort. -/
theorem Same.exponent_le {a b : Decimal} (h : a.Same b) (hb : b.mantissa % 10 ≠ 0) :
    a.exponent ≤ b.exponent := by
  cases hd : (a.exponent - b.exponent).toNat with
  | zero => omega
  | succ n =>
    have hz : (b.exponent - a.exponent).toNat = 0 := by omega
    have h' : a.mantissa * 10 ^ (a.exponent - b.exponent).toNat =
        b.mantissa * 10 ^ (b.exponent - a.exponent).toNat := h
    rw [hd, hz, Int.pow_zero, Int.mul_one] at h'
    have hten := mul_ten_pow_succ_emod a.mantissa n
    rw [h'] at hten
    exact absurd hten hb

/-- A canonical value with mantissa zero has exponent zero. -/
theorem exponent_eq_zero_of_isReduced {d : Decimal} (h : d.isReduced = true)
    (hm : d.mantissa = 0) : d.exponent = 0 := by
  rw [isReduced, if_pos hm] at h
  exact eq_of_beq h

/-- A canonical value with a mantissa that is not zero does not end in zero. -/
theorem last_ne_zero_of_isReduced {d : Decimal} (h : d.isReduced = true)
    (hm : d.mantissa ≠ 0) : d.mantissa % 10 ≠ 0 := by
  rw [isReduced, if_neg hm, bne_iff_ne] at h
  exact h

/-- Two values with one mantissa and one exponent are one value. -/
theorem ext {a b : Decimal} (hm : a.mantissa = b.mantissa)
    (he : a.exponent = b.exponent) : a = b := by
  cases a with
  | mk ma ea =>
    cases b with
    | mk mb eb =>
      cases hm
      cases he
      rfl

/-- Two canonical values of one number are equal. -/
theorem eq_of_same_of_isReduced {a b : Decimal} (h : a.Same b) (ha : a.isReduced = true)
    (hb : b.isReduced = true) : a = b := by
  cases hz : decide (a.mantissa = 0) with
  | true =>
    have hma : a.mantissa = 0 := of_decide_eq_true hz
    have hmb : b.mantissa = 0 := h.mantissa_eq_zero hma
    have hea := exponent_eq_zero_of_isReduced ha hma
    have heb := exponent_eq_zero_of_isReduced hb hmb
    exact ext (hma.trans hmb.symm) (hea.trans heb.symm)
  | false =>
    have hma : a.mantissa ≠ 0 := of_decide_eq_false hz
    have hmb : b.mantissa ≠ 0 := fun hb0 => hma (h.symm.mantissa_eq_zero hb0)
    have hab := h.exponent_le (last_ne_zero_of_isReduced hb hmb)
    have hba := h.symm.exponent_le (last_ne_zero_of_isReduced ha hma)
    have hza : (a.exponent - b.exponent).toNat = 0 := by omega
    have hzb : (b.exponent - a.exponent).toNat = 0 := by omega
    have h' : a.mantissa * 10 ^ (a.exponent - b.exponent).toNat =
        b.mantissa * 10 ^ (b.exponent - a.exponent).toNat := h
    rw [hza, hzb, Int.pow_zero, Int.mul_one, Int.mul_one] at h'
    exact ext h' (by omega)

/-! ## The main law -/

/-- Two values denote one number exactly when their canonical values are equal. -/
theorem same_iff_reduce (a b : Decimal) : a.Same b ↔ a.reduce = b.reduce := by
  constructor
  · intro h
    exact eq_of_same_of_isReduced (((same_reduce a).trans h).trans (same_reduce b).symm)
      (isReduced_reduce a) (isReduced_reduce b)
  · intro h
    have ha : a.Same a.reduce := (same_reduce a).symm
    rw [h] at ha
    exact ha.trans (same_reduce b)

/-- Whether two values denote one number, decided by a `reduce` on each side. It takes no power
of ten. -/
instance decidableSame (a b : Decimal) : Decidable (a.Same b) :=
  decidable_of_iff (a.reduce = b.reduce) (same_iff_reduce a b).symm

/-! ## The tidy value -/

/-- The tidy value denotes the number of the canonical value. -/
theorem tidy_same_reduce (d : Decimal) : d.tidy.Same d.reduce := by
  unfold tidy
  generalize d.reduce = r
  cases r with
  | mk m e =>
    cases e with
    | negSucc n => exact Same.refl _
    | ofNat n =>
      match n with
      | 0 => exact Same.refl _
      | 1 =>
        show m * 10 * 10 ^ 0 = m * 10 ^ 1
        omega
      | 2 =>
        show m * 100 * 10 ^ 0 = m * 10 ^ 2
        omega
      | n + 3 => exact Same.refl _

/-- The tidy value denotes the number of the value. -/
theorem same_tidy (d : Decimal) : d.tidy.Same d :=
  (tidy_same_reduce d).trans (same_reduce d)

end Whatwg.Svg.Value.Decimal
