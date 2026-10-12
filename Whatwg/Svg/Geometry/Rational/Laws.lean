import Whatwg.Svg.Geometry.Rational

/-!
# Whatwg.Svg.Geometry.Rational.Laws

Owner: the laws of the number that a `Decimal` denotes (slice S11 of `docs/SVG-PACKAGE-PLAN.md`;
ruling SV-50). `Decimal.toRat` takes the sum, the difference, the product, the opposite and the
half of values to those of `Rat`; two values are `Same` exactly when their numbers are equal,
and `≤` and `<` on values are the order of their numbers. Each of the three roundings is held
between two bounds: `ofRatDown` is below its number by less than one unit of the last place,
`ofRatUp` is above it by less than one, and `ofRat` is within half a unit, a half going up. A
count over the power of ten that is kept is written exactly, as an equation of values, and the
rounded quotient of S10 (`ofQuotient`) is `ofRat` of the rational quotient. The same laws for a
point (`Point.toVec`, `Vec.round`) follow coordinate by coordinate.

What this module does not claim: that `ofRat d.toRat places` is the value `d`. It denotes the
number of `d` when `d` has no more places than are kept, and it is the value `d` when `d` is a
`fixed` value.
-/

namespace Whatwg.Svg.Value

namespace Decimal

/-! ## Ten and its powers -/

/-- Ten is not zero. -/
theorem ratTen_ne : (10 : Rat) ≠ 0 := by decide

/-- Ten is more than zero. -/
theorem ratTen_pos : (0 : Rat) < 10 := by decide

/-- A power of ten is more than zero. -/
theorem ratTen_pow_pos (n : Nat) : (0 : Rat) < (10 : Rat) ^ n := Rat.pow_pos ratTen_pos

/-- A power of ten is not zero. -/
theorem ratTen_pow_ne (n : Nat) : (10 : Rat) ^ n ≠ 0 := Rat.ne_of_gt (ratTen_pow_pos n)

/-- A power of ten with a whole exponent of either sign is more than zero. -/
theorem ratTen_zpow_pos (e : Int) : (0 : Rat) < (10 : Rat) ^ e := Rat.zpow_pos ratTen_pos

/-- A power of ten with a whole exponent of either sign is not zero. -/
theorem ratTen_zpow_ne (e : Int) : (10 : Rat) ^ e ≠ 0 := Rat.ne_of_gt (ratTen_zpow_pos e)

/-! ## Rational numbers: a factor or a divisor that is more than zero -/

/-- A factor that is not zero may be taken from both sides of an equation. -/
theorem rat_mul_right_cancel {x y p : Rat} (hp : p ≠ 0) (h : x * p = y * p) : x = y := by
  grind

/-- A factor that is more than zero keeps `≤`, and may be taken from both sides. -/
theorem rat_mul_le_mul_right {a b c : Rat} (hc : 0 < c) : a * c ≤ b * c ↔ a ≤ b := by
  rw [← Rat.not_lt, ← Rat.not_lt, Rat.mul_lt_mul_right hc]

/-- Dividing both sides by a number that is more than zero keeps `≤`. -/
theorem rat_div_le_div {a b c : Rat} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Rat.inv_pos.mpr hc))

/-- Dividing both sides by a number that is more than zero keeps `<`. -/
theorem rat_div_lt_div {a b c : Rat} (hc : 0 < c) (h : a < b) : a / c < b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_lt_mul_of_pos_right h (Rat.inv_pos.mpr hc)

/-- A rational number between an integer and the next one has that integer as its floor. -/
theorem rat_floor_eq {x : Rat} {k : Int} (h1 : (k : Rat) ≤ x) (h2 : x < (k : Rat) + 1) :
    x.floor = k := by
  have a : k ≤ x.floor := Rat.le_floor_iff.mpr h1
  have b : x.floor < k + 1 := Rat.floor_lt_iff.mpr (by rw [Rat.intCast_add]; exact h2)
  omega

/-! ## The number of a value -/

/-- The number of a value is its mantissa times ten to the power of its exponent. -/
theorem toRat_def (d : Decimal) : d.toRat = (d.mantissa : Rat) * (10 : Rat) ^ d.exponent := rfl

/-- The number of a value is its mantissa at a lower exponent times ten to that power. -/
theorem toRat_eq_mantissaAt (d : Decimal) (e : Int) (h : e ≤ d.exponent) :
    d.toRat = (d.mantissaAt e : Rat) * (10 : Rat) ^ e := by
  have hn : ((d.exponent - e).toNat : Int) + e = d.exponent := by omega
  have hp : (10 : Rat) ^ (d.exponent - e).toNat * (10 : Rat) ^ e = (10 : Rat) ^ d.exponent := by
    rw [← Rat.zpow_natCast, ← Rat.zpow_add ratTen_ne, hn]
  rw [toRat_def, mantissaAt_def, Rat.intCast_mul, Rat.intCast_pow, Rat.intCast_ofNat,
    Rat.mul_assoc, hp]

/-- The number of an integer as a value is the integer. -/
theorem toRat_ofInt (n : Int) : (ofInt n).toRat = (n : Rat) := by
  simp only [toRat, ofInt, Rat.zpow_zero, Rat.mul_one]

/-- The number of the cast of an integer is the integer. -/
theorem toRat_intCast (n : Int) : ((n : Decimal)).toRat = (n : Rat) := toRat_ofInt n

/-- The number of the value zero is zero. -/
theorem toRat_zero : (0 : Decimal).toRat = 0 := toRat_ofInt 0

/-- The number of the value one is one. -/
theorem toRat_one : (1 : Decimal).toRat = 1 := toRat_ofInt 1

/-- The number of a sum is the sum of the numbers. -/
theorem toRat_add (a b : Decimal) : (a + b).toRat = a.toRat + b.toRat := by
  rw [toRat_eq_mantissaAt a _ (Int.min_le_left a.exponent b.exponent),
    toRat_eq_mantissaAt b _ (Int.min_le_right a.exponent b.exponent), ← Rat.add_mul,
    ← Rat.intCast_add]
  rfl

/-- The number of the opposite value is the opposite number. -/
theorem toRat_neg (a : Decimal) : (-a).toRat = -a.toRat := by
  simp only [toRat, neg_def, Rat.intCast_neg]
  grind

/-- The number of a difference is the difference of the numbers. -/
theorem toRat_sub (a b : Decimal) : (a - b).toRat = a.toRat - b.toRat := by
  rw [sub_eq_add_neg, toRat_add, toRat_neg, Rat.sub_eq_add_neg]

/-- The number of a product is the product of the numbers. -/
theorem toRat_mul (a b : Decimal) : (a * b).toRat = a.toRat * b.toRat := by
  simp only [toRat, mul_def, Rat.intCast_mul, Rat.zpow_add ratTen_ne]
  grind

/-- The number of a half is half of the number. -/
theorem toRat_half (d : Decimal) : d.half.toRat = d.toRat / 2 := by
  simp only [toRat, half, Rat.intCast_mul, Rat.intCast_ofNat, Rat.zpow_sub_one ratTen_ne]
  grind

/-- Two values denote one number exactly when their numbers are equal. -/
theorem same_iff_toRat (a b : Decimal) : a.Same b ↔ a.toRat = b.toRat := by
  have ha := Int.min_le_left a.exponent b.exponent
  have hb := Int.min_le_right a.exponent b.exponent
  rw [same_iff_mantissaAt a b _ ha hb, toRat_eq_mantissaAt a _ ha, toRat_eq_mantissaAt b _ hb]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Rat.intCast_inj.mp (rat_mul_right_cancel (ratTen_zpow_ne _) h)

/-- Dropping the zeros at the end of a fraction keeps the number. -/
theorem toRat_trim (d : Decimal) : d.trim.toRat = d.toRat :=
  (same_iff_toRat d.trim d).mp (same_trim d)

/-- The number of the middle of two values is half of the sum of their numbers. -/
theorem toRat_mid (a b : Decimal) : (mid a b).toRat = (a.toRat + b.toRat) / 2 := by
  rw [mid, toRat_trim, toRat_half, toRat_add]

/-- A count with a number of places is the value with that count and the opposite exponent. -/
theorem ofScaled_eq (n : Int) (places : Nat) : ofScaled n places = ⟨n, -(places : Int)⟩ := by
  cases places with
  | zero => rfl
  | succ p => rfl

/-- The number of a count with a number of places is the count over that power of ten. -/
theorem toRat_ofScaled (n : Int) (places : Nat) :
    (ofScaled n places).toRat = (n : Rat) / (10 : Rat) ^ places := by
  rw [ofScaled_eq, toRat_def, Rat.zpow_neg, Rat.zpow_natCast, Rat.div_def]

/-- The number of `fixed places n` is `n` over ten to the power `places`. -/
theorem toRat_fixed (places : Nat) (n : Int) :
    (fixed places n).toRat = (n : Rat) / (10 : Rat) ^ places := by
  rw [fixed, toRat_trim, toRat_ofScaled]

/-- `≤` on values is `≤` on their numbers. -/
theorem le_iff_toRat (a b : Decimal) : a ≤ b ↔ a.toRat ≤ b.toRat := by
  have ha := Int.min_le_left a.exponent b.exponent
  have hb := Int.min_le_right a.exponent b.exponent
  rw [le_iff_at a b _ ha hb, toRat_eq_mantissaAt a _ ha, toRat_eq_mantissaAt b _ hb,
    rat_mul_le_mul_right (ratTen_zpow_pos _), Rat.intCast_le_intCast]

/-- `<` on values is `<` on their numbers. -/
theorem lt_iff_toRat (a b : Decimal) : a < b ↔ a.toRat < b.toRat := by
  have ha := Int.min_le_left a.exponent b.exponent
  have hb := Int.min_le_right a.exponent b.exponent
  rw [lt_iff_at a b _ ha hb, toRat_eq_mantissaAt a _ ha, toRat_eq_mantissaAt b _ hb,
    Rat.mul_lt_mul_right (ratTen_zpow_pos _), Rat.intCast_lt_intCast]

/-! ## The three roundings -/

/-- Rounding down gives a number that is no more than the number rounded. -/
theorem toRat_ofRatDown_le (q : Rat) (places : Nat) : (ofRatDown q places).toRat ≤ q := by
  have h := rat_div_le_div (ratTen_pow_pos places) (Rat.floor_le (q * (10 : Rat) ^ places))
  rw [Rat.mul_div_cancel (ratTen_pow_ne places)] at h
  rw [ofRatDown, toRat_fixed]
  exact h

/-- Rounding down takes away less than one unit of the last place. -/
theorem lt_toRat_ofRatDown (q : Rat) (places : Nat) :
    q - 1 / (10 : Rat) ^ places < (ofRatDown q places).toRat := by
  have h := rat_div_lt_div (ratTen_pow_pos places) (Rat.lt_floor (x := q * (10 : Rat) ^ places))
  have e : (q * (10 : Rat) ^ places - 1) / (10 : Rat) ^ places = q - 1 / (10 : Rat) ^ places := by
    have hp := ratTen_pow_ne places
    grind
  rw [e] at h
  rw [ofRatDown, toRat_fixed]
  exact h

/-- Rounding up gives a number that is no less than the number rounded. -/
theorem le_toRat_ofRatUp (q : Rat) (places : Nat) : q ≤ (ofRatUp q places).toRat := by
  have h := rat_div_le_div (ratTen_pow_pos places) (Rat.le_ceil (x := q * (10 : Rat) ^ places))
  rw [Rat.mul_div_cancel (ratTen_pow_ne places)] at h
  rw [ofRatUp, toRat_fixed]
  exact h

/-- Rounding up adds less than one unit of the last place. -/
theorem toRat_ofRatUp_lt (q : Rat) (places : Nat) :
    (ofRatUp q places).toRat < q + 1 / (10 : Rat) ^ places := by
  have h := rat_div_lt_div (ratTen_pow_pos places) (Rat.ceil_lt (x := q * (10 : Rat) ^ places))
  have e : (q * (10 : Rat) ^ places + 1) / (10 : Rat) ^ places = q + 1 / (10 : Rat) ^ places := by
    have hp := ratTen_pow_ne places
    grind
  rw [e] at h
  rw [ofRatUp, toRat_fixed]
  exact h

/-- Rounding to the nearest adds at most half a unit of the last place. -/
theorem toRat_ofRat_le (q : Rat) (places : Nat) :
    (ofRat q places).toRat ≤ q + 1 / (2 * (10 : Rat) ^ places) := by
  have h := rat_div_le_div (ratTen_pow_pos places)
    (Rat.floor_le (q * (10 : Rat) ^ places + 1 / 2))
  have e : (q * (10 : Rat) ^ places + 1 / 2) / (10 : Rat) ^ places =
      q + 1 / (2 * (10 : Rat) ^ places) := by
    have hp := ratTen_pow_ne places
    grind
  rw [e] at h
  rw [ofRat, toRat_fixed]
  exact h

/-- Rounding to the nearest takes away less than half a unit of the last place. -/
theorem lt_toRat_ofRat (q : Rat) (places : Nat) :
    q - 1 / (2 * (10 : Rat) ^ places) < (ofRat q places).toRat := by
  have h := rat_div_lt_div (ratTen_pow_pos places)
    (Rat.lt_floor (x := q * (10 : Rat) ^ places + 1 / 2))
  have e : (q * (10 : Rat) ^ places + 1 / 2 - 1) / (10 : Rat) ^ places =
      q - 1 / (2 * (10 : Rat) ^ places) := by
    have hp := ratTen_pow_ne places
    grind
  rw [e] at h
  rw [ofRat, toRat_fixed]
  exact h

/-! ## A number with no more places than are kept -/

/-- A count over the power of ten that is kept rounds to that count, as a value. -/
theorem ofRat_div_pow (k : Int) (places : Nat) :
    ofRat ((k : Rat) / (10 : Rat) ^ places) places = fixed places k := by
  have hf : ((k : Rat) + 1 / 2).floor = k := by
    apply rat_floor_eq <;> grind
  rw [ofRat, Rat.div_mul_cancel (ratTen_pow_ne places), hf]

/-- A count over the power of ten that is kept rounds down to that count, as a value. -/
theorem ofRatDown_div_pow (k : Int) (places : Nat) :
    ofRatDown ((k : Rat) / (10 : Rat) ^ places) places = fixed places k := by
  rw [ofRatDown, Rat.div_mul_cancel (ratTen_pow_ne places), Rat.floor_intCast]

/-- A count over the power of ten that is kept rounds up to that count, as a value. -/
theorem ofRatUp_div_pow (k : Int) (places : Nat) :
    ofRatUp ((k : Rat) / (10 : Rat) ^ places) places = fixed places k := by
  rw [ofRatUp, Rat.div_mul_cancel (ratTen_pow_ne places), Rat.ceil_intCast]

/-- A value with no more places than are kept is a count over that power of ten. -/
theorem toRat_eq_div_pow (d : Decimal) (places : Nat) (h : -d.exponent ≤ (places : Int)) :
    d.toRat = (d.mantissaAt (-(places : Int)) : Rat) / (10 : Rat) ^ places := by
  have he : -(places : Int) ≤ d.exponent := by omega
  rw [toRat_eq_mantissaAt d _ he, Rat.zpow_neg, Rat.zpow_natCast, Rat.div_def]

/-- Writing the number of a value with no more places than are kept gives back the number. -/
theorem toRat_ofRat_toRat (d : Decimal) (places : Nat) (h : -d.exponent ≤ (places : Int)) :
    (ofRat d.toRat places).toRat = d.toRat := by
  rw [toRat_eq_div_pow d places h, ofRat_div_pow, toRat_fixed]

/-- Writing the number of `fixed places k` at `places` places gives back the value. -/
theorem ofRat_fixed (places : Nat) (k : Int) :
    ofRat (fixed places k).toRat places = fixed places k := by
  rw [toRat_fixed, ofRat_div_pow]

/-! ## The rounding of a quotient of two integers -/

/-- With a positive divisor, the rounded count is the floor of the scaled quotient and a
half. -/
theorem roundQuotient_eq_floor (num den : Int) (places : Nat) (h : 0 < den) :
    roundQuotient num den places =
      ((num : Rat) / (den : Rat) * (10 : Rat) ^ places + 1 / 2).floor := by
  obtain ⟨h1, h2⟩ := roundQuotient_bound num den places h
  have hd : (0 : Rat) < (den : Rat) := Rat.intCast_pos.mpr h
  have hne : (den : Rat) ≠ 0 := Rat.ne_of_gt hd
  have c1 := Rat.intCast_le_intCast.mpr h1
  have c2 := Rat.intCast_lt_intCast.mpr h2
  simp only [Rat.intCast_mul, Rat.intCast_add, Rat.intCast_pow, Rat.intCast_ofNat] at c1 c2
  have h2d : (0 : Rat) < 2 * (den : Rat) := by grind
  have e : ((num : Rat) / (den : Rat) * (10 : Rat) ^ places + 1 / 2) * (2 * (den : Rat)) =
      2 * ((num : Rat) * (10 : Rat) ^ places) + (den : Rat) := by
    grind
  symm
  apply rat_floor_eq
  · apply (rat_mul_le_mul_right h2d).mp
    rw [e]
    grind
  · apply (Rat.mul_lt_mul_right h2d).mp
    rw [e]
    grind

/-- The quotient of two integers rounded as in S10 is the rational quotient rounded to the
nearest. -/
theorem ofQuotient_eq_ofRat (num den : Int) (places : Nat) (h : den ≠ 0) :
    ofQuotient num den places = ofRat ((num : Rat) / (den : Rat)) places := by
  rw [ofQuotient, ofRat]
  obtain hneg | hz | hpos := Int.lt_trichotomy den 0
  · have hne : (den : Rat) ≠ 0 := by
      intro hc
      exact h (Rat.intCast_eq_zero_iff.mp hc)
    have e : ((-num : Int) : Rat) / ((-den : Int) : Rat) = (num : Rat) / (den : Rat) := by
      rw [Rat.intCast_neg, Rat.intCast_neg]
      grind
    rw [roundQuotient_neg num den places hneg,
      roundQuotient_eq_floor (-num) (-den) places (by omega), e]
  · exact absurd hz h
  · rw [roundQuotient_eq_floor num den places hpos]

end Decimal

/-! ## Points -/

/-- The point of a sum is the sum of the points. -/
theorem Point.toVec_add (p q : Point) : (p + q).toVec = p.toVec + q.toVec :=
  Vec.ext (Decimal.toRat_add p.x q.x) (Decimal.toRat_add p.y q.y)

/-- The point of a difference is the difference of the points. -/
theorem Point.toVec_sub (p q : Point) : (p - q).toVec = p.toVec - q.toVec :=
  Vec.ext (Decimal.toRat_sub p.x q.x) (Decimal.toRat_sub p.y q.y)

/-- The point of a scaled coordinate pair is the point scaled by the number of the factor. -/
theorem Point.toVec_scale (k : Decimal) (p : Point) :
    (Point.scale k p).toVec = Vec.scale k.toRat p.toVec :=
  Vec.ext (Decimal.toRat_mul k p.x) (Decimal.toRat_mul k p.y)

/-- The point of a pair of whole units is that pair of whole units. -/
theorem Point.toVec_ofInts (x y : Int) : (Point.ofInts x y).toVec = Vec.ofInts x y :=
  Vec.ext (Decimal.toRat_ofInt x) (Decimal.toRat_ofInt y)

/-- The point of a pair of counts is that pair of counts, each over the power of ten. -/
theorem Point.toVec_fixed (places : Nat) (x y : Int) :
    (Point.fixed places x y).toVec = Vec.fixed places x y :=
  Vec.ext (Decimal.toRat_fixed places x) (Decimal.toRat_fixed places y)

/-- A point of counts is written at that many places as the coordinate pair of the counts. -/
theorem Vec.round_fixed (places : Nat) (x y : Int) :
    (Vec.fixed places x y).round places = Point.fixed places x y := by
  show (⟨Decimal.ofRat ((x : Rat) / (10 : Rat) ^ places) places,
      Decimal.ofRat ((y : Rat) / (10 : Rat) ^ places) places⟩ : Point) =
    ⟨Decimal.fixed places x, Decimal.fixed places y⟩
  rw [Decimal.ofRat_div_pow, Decimal.ofRat_div_pow]

/-- A coordinate pair of counts, read as a point and written back, is the pair. -/
theorem Vec.round_toVec_fixed (places : Nat) (x y : Int) :
    (Point.fixed places x y).toVec.round places = Point.fixed places x y := by
  rw [Point.toVec_fixed, Vec.round_fixed]

end Whatwg.Svg.Value
