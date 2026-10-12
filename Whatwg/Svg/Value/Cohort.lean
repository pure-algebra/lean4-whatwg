import Whatwg.Svg.Value.Number

/-!
# Whatwg.Svg.Value.Cohort

Owner: the denotation layer of an exact decimal (slice S4b of `docs/SVG-PACKAGE-PLAN.md`, the
number): the relation `Decimal.Same`, that two values denote one number; the canonical value
`Decimal.reduce` with its invariant `Decimal.isReduced`; `Decimal.tidy`; and the law that the
canonical value decides the relation. `Whatwg/Svg/Value/Number.lean` holds the values and
their spelling, and the two definitions a program builds with, `stripZeros` and `trim`. No
carrier of the package reads this module, so an edit here rebuilds no grammar.

The values of one number are its cohort. This module proves:

- `reduce` returns a canonical value that denotes the number: `isReduced_reduce`,
  `reduce_of_isReduced` and `same_reduce`.
- `trim` keeps the number and takes no exponent from a whole number: `same_trim`,
  `trim_exponent_nonpos` and `trim_of_nonneg`.
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

/-! ## The canonical value of a number

A value is a spelling: `150`, `15e1` and `150.0` are three values that denote one number. The
values of one number are its cohort, and one of them has a mantissa that ten does not divide,
or is zero at exponent zero. `reduce` finds it at the cost of the mantissa's digits, whatever
the exponent. `Same` is the relation, stated by arithmetic and never evaluated. -/

/-- Two values denote one number: at a common exponent, the mantissas agree. This is a
statement. Nothing decides it by taking the power: `reduce` is the cheap test. -/
def Same (a b : Decimal) : Prop :=
  a.mantissa * 10 ^ (a.exponent - b.exponent).toNat =
    b.mantissa * 10 ^ (b.exponent - a.exponent).toNat

/-- The canonical value of a number: no zero at the end of the mantissa, and zero as `0`. Its
cost is the number of the mantissa's digits. -/
def reduce (d : Decimal) : Decimal :=
  if d.mantissa = 0 then ⟨0, 0⟩ else stripZeros d.mantissa.natAbs d.mantissa d.exponent

/-- The value is canonical: ten does not divide its mantissa, or it is zero at exponent
zero. -/
def isReduced (d : Decimal) : Bool :=
  if d.mantissa = 0 then d.exponent == 0 else d.mantissa % 10 != 0

/-- The value of a number that this module spells shortest among those with a whole mantissa
and the same digits: the canonical one, or its plain form where that is no longer. `15e1`
becomes `150` and `15e2` becomes `1500`; `15e3` stays. The cost is that of `reduce`. -/
def tidy (d : Decimal) : Decimal :=
  match (reduce d).exponent with
  | .ofNat 1 => ⟨(reduce d).mantissa * 10, 0⟩
  | .ofNat 2 => ⟨(reduce d).mantissa * 100, 0⟩
  | _ => reduce d

theorem stripZeros_exponent : ∀ (fuel : Nat) (m e : Int), e ≤ (stripZeros fuel m e).exponent
  | 0, _, e => Int.le_refl e
  | fuel + 1, m, e => by
    cases h : decide (m % 10 = 0) with
    | true =>
      rw [stripZeros, if_pos (of_decide_eq_true h)]
      have ih := stripZeros_exponent fuel (m / 10) (e + 1)
      omega
    | false =>
      rw [stripZeros, if_neg (of_decide_eq_false h)]
      exact Int.le_refl e

/-- With fuel for each digit, the mantissa that is left does not end in zero. -/
theorem stripZeros_last : ∀ (fuel : Nat) (m e : Int), m ≠ 0 → m.natAbs ≤ fuel →
    (stripZeros fuel m e).mantissa % 10 ≠ 0
  | 0, m, _, hm, hfuel => by omega
  | fuel + 1, m, e, hm, hfuel => by
    cases h : decide (m % 10 = 0) with
    | true =>
      have hz : m % 10 = 0 := of_decide_eq_true h
      rw [stripZeros, if_pos hz]
      exact stripZeros_last fuel (m / 10) (e + 1) (by omega) (by omega)
    | false =>
      rw [stripZeros, if_neg (of_decide_eq_false h)]
      exact of_decide_eq_false h

/-- Moving zeros into the exponent keeps the number. -/
theorem stripZeros_scale : ∀ (fuel : Nat) (m e : Int),
    (stripZeros fuel m e).mantissa * 10 ^ ((stripZeros fuel m e).exponent - e).toNat = m
  | 0, m, e => by
    show m * 10 ^ (e - e).toNat = m
    have h : (e - e).toNat = 0 := by omega
    rw [h, Int.pow_zero, Int.mul_one]
  | fuel + 1, m, e => by
    cases h : decide (m % 10 = 0) with
    | true =>
      have hz : m % 10 = 0 := of_decide_eq_true h
      have hle := stripZeros_exponent fuel (m / 10) (e + 1)
      have ih := stripZeros_scale fuel (m / 10) (e + 1)
      rw [stripZeros, if_pos hz]
      have hsub : ((stripZeros fuel (m / 10) (e + 1)).exponent - e).toNat =
          ((stripZeros fuel (m / 10) (e + 1)).exponent - (e + 1)).toNat + 1 := by omega
      rw [hsub, Int.pow_succ, ← Int.mul_assoc, ih]
      omega
    | false =>
      rw [stripZeros, if_neg (of_decide_eq_false h)]
      show m * 10 ^ (e - e).toNat = m
      have h : (e - e).toNat = 0 := by omega
      rw [h, Int.pow_zero, Int.mul_one]

/-- The canonical value is canonical. -/
theorem isReduced_reduce (d : Decimal) : d.reduce.isReduced = true := by
  cases h : decide (d.mantissa = 0) with
  | true =>
    rw [reduce, if_pos (of_decide_eq_true h)]
    rfl
  | false =>
    have hm : d.mantissa ≠ 0 := of_decide_eq_false h
    have hlast := stripZeros_last d.mantissa.natAbs d.mantissa d.exponent hm (Nat.le_refl _)
    have hne : (stripZeros d.mantissa.natAbs d.mantissa d.exponent).mantissa ≠ 0 := by omega
    rw [reduce, if_neg hm, isReduced, if_neg hne, bne_iff_ne]
    exact hlast

/-- A canonical value is its own canonical value. -/
theorem reduce_of_isReduced {d : Decimal} (h : d.isReduced = true) : d.reduce = d := by
  cases d with
  | mk m e =>
    cases hz : decide (m = 0) with
    | true =>
      have hm : m = 0 := of_decide_eq_true hz
      have he : (e == 0) = true := by
        have h' := h
        rw [isReduced, if_pos hm] at h'
        exact h'
      rw [reduce, if_pos hm, hm, eq_of_beq he]
    | false =>
      have hm : m ≠ 0 := of_decide_eq_false hz
      have hlast : ¬ m % 10 = 0 := by
        have h' := h
        rw [isReduced, if_neg hm, bne_iff_ne] at h'
        exact h'
      rw [reduce, if_neg hm]
      cases hfuel : m.natAbs with
      | zero => omega
      | succ fuel => rw [stripZeros, if_neg hlast]

/-- Moving zeros into the exponent keeps the number, whatever the fuel. -/
theorem stripZeros_same (fuel : Nat) (m e : Int) : (stripZeros fuel m e).Same ⟨m, e⟩ := by
  have hle := stripZeros_exponent fuel m e
  have hzero : (e - (stripZeros fuel m e).exponent).toNat = 0 := by omega
  show (stripZeros fuel m e).mantissa * 10 ^ ((stripZeros fuel m e).exponent - e).toNat =
    m * 10 ^ (e - (stripZeros fuel m e).exponent).toNat
  rw [hzero, stripZeros_scale, Int.pow_zero, Int.mul_one]

/-- The canonical value denotes the number of the value. -/
theorem same_reduce (d : Decimal) : d.reduce.Same d := by
  cases h : decide (d.mantissa = 0) with
  | true =>
    have hm : d.mantissa = 0 := of_decide_eq_true h
    rw [reduce, if_pos hm, Same, hm, Int.zero_mul, Int.zero_mul]
  | false =>
    rw [reduce, if_neg (of_decide_eq_false h)]
    exact stripZeros_same _ d.mantissa d.exponent

/-- Each step moves one zero, so the exponent rises by the fuel at most. -/
theorem stripZeros_exponent_le : ∀ (fuel : Nat) (m e : Int),
    (stripZeros fuel m e).exponent ≤ e + fuel
  | 0, _, e => by
    show e ≤ e + ((0 : Nat) : Int)
    omega
  | fuel + 1, m, e => by
    cases h : decide (m % 10 = 0) with
    | true =>
      rw [stripZeros, if_pos (of_decide_eq_true h)]
      have ih := stripZeros_exponent_le fuel (m / 10) (e + 1)
      omega
    | false =>
      rw [stripZeros, if_neg (of_decide_eq_false h)]
      show e ≤ e + ((fuel + 1 : Nat) : Int)
      omega

/-- The trimmed value denotes the number of the value. -/
theorem same_trim (d : Decimal) : d.trim.Same d :=
  stripZeros_same _ d.mantissa d.exponent

/-- Trimming takes no exponent from a whole number: a fraction stays a fraction or becomes
whole, and no positive exponent appears. -/
theorem trim_exponent_nonpos {d : Decimal} (h : d.exponent ≤ 0) : d.trim.exponent ≤ 0 := by
  have hle := stripZeros_exponent_le (-d.exponent).toNat d.mantissa d.exponent
  rw [trim]
  omega

/-- A value at an exponent that is not negative is its own trimmed value. -/
theorem trim_of_nonneg {d : Decimal} (h : 0 ≤ d.exponent) : d.trim = d := by
  have hfuel : (-d.exponent).toNat = 0 := by omega
  rw [trim, hfuel, stripZeros]

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
