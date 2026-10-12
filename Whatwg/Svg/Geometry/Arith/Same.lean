import Whatwg.Svg.Geometry.Arith.Laws

/-!
# Whatwg.Svg.Geometry.Arith.Same

Owner: what the arithmetic of `Whatwg/Svg/Geometry/Arith.lean` means for the numbers that values
denote (slice S10 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-43). `Decimal.Same` of
`Whatwg/Svg/Value/Cohort.lean` says that two values denote one number. The sum, the product and
the opposite respect it, so a computation may replace a value by another spelling of its
number. Zero and the opposite are a unit and an inverse of the sum up to `Same`. `half` is half,
`fixed` is its count over a power of ten, and `ofQuotient` is within half a unit of the last
place of the quotient.
-/

namespace Whatwg.Svg.Value

namespace Decimal

/-! ## The value at a scale

`mantissaAt_add` and `mantissaAt_neg` are in `Whatwg/Svg/Geometry/Arith/Laws.lean`. -/

/-- The mantissa of a product at `j + k` is the product of the mantissas at `j` and at `k`. -/
theorem mantissaAt_mul (a b : Decimal) (j k : Int) (ha : j ≤ a.exponent) (hb : k ≤ b.exponent) :
    (a * b).mantissaAt (j + k) = a.mantissaAt j * b.mantissaAt k := by
  have h : (a.exponent - j).toNat + (b.exponent - k).toNat =
      (a.exponent + b.exponent - (j + k)).toNat := by omega
  show a.mantissa * b.mantissa * 10 ^ (a.exponent + b.exponent - (j + k)).toNat =
    a.mantissa * 10 ^ (a.exponent - j).toNat * (b.mantissa * 10 ^ (b.exponent - k).toNat)
  rw [← h, Int.pow_add, Int.mul_assoc, Int.mul_assoc, Int.mul_left_comm b.mantissa]

/-- Two values denote one number exactly when their mantissas agree at a common exponent. -/
theorem same_iff_mantissaAt (a b : Decimal) (k : Int) (ha : k ≤ a.exponent)
    (hb : k ≤ b.exponent) : a.Same b ↔ a.mantissaAt k = b.mantissaAt k :=
  same_iff_at a b k ha hb

/-! ## The operations respect the relation -/

/-- The number of a sum depends only on the numbers of its two terms. -/
theorem add_same {a a' b b' : Decimal} (ha : a.Same a') (hb : b.Same b') :
    (a + b).Same (a' + b') := by
  obtain ⟨k, h1, h2, h3, h4⟩ :
      ∃ k : Int, k ≤ a.exponent ∧ k ≤ a'.exponent ∧ k ≤ b.exponent ∧ k ≤ b'.exponent :=
    ⟨min (min a.exponent a'.exponent) (min b.exponent b'.exponent),
      by omega, by omega, by omega, by omega⟩
  refine (same_iff_mantissaAt (a + b) (a' + b') k (Int.le_min.mpr ⟨h1, h3⟩)
    (Int.le_min.mpr ⟨h2, h4⟩)).mpr ?_
  rw [mantissaAt_add a b k h1 h3, mantissaAt_add a' b' k h2 h4,
    (same_iff_mantissaAt a a' k h1 h2).mp ha, (same_iff_mantissaAt b b' k h3 h4).mp hb]

/-- The number of a product depends only on the numbers of its two factors. -/
theorem mul_same {a a' b b' : Decimal} (ha : a.Same a') (hb : b.Same b') :
    (a * b).Same (a' * b') := by
  have ha1 : min a.exponent a'.exponent ≤ a.exponent := Int.min_le_left _ _
  have ha2 : min a.exponent a'.exponent ≤ a'.exponent := Int.min_le_right _ _
  have hb1 : min b.exponent b'.exponent ≤ b.exponent := Int.min_le_left _ _
  have hb2 : min b.exponent b'.exponent ≤ b'.exponent := Int.min_le_right _ _
  refine (same_iff_mantissaAt (a * b) (a' * b') _ (Int.add_le_add ha1 hb1)
    (Int.add_le_add ha2 hb2)).mpr ?_
  rw [mantissaAt_mul a b _ _ ha1 hb1, mantissaAt_mul a' b' _ _ ha2 hb2,
    (same_iff_mantissaAt a a' _ ha1 ha2).mp ha, (same_iff_mantissaAt b b' _ hb1 hb2).mp hb]

/-- The number of an opposite depends only on the number of the value. -/
theorem neg_same {a a' : Decimal} (ha : a.Same a') : (-a).Same (-a') := by
  have h : a.mantissa * 10 ^ (a.exponent - a'.exponent).toNat =
      a'.mantissa * 10 ^ (a'.exponent - a.exponent).toNat := ha
  show -a.mantissa * 10 ^ (a.exponent - a'.exponent).toNat =
    -a'.mantissa * 10 ^ (a'.exponent - a.exponent).toNat
  rw [Int.neg_mul, Int.neg_mul, h]

/-- The number of a difference depends only on the numbers of its two terms. -/
theorem sub_same {a a' b b' : Decimal} (ha : a.Same a') (hb : b.Same b') :
    (a - b).Same (a' - b') :=
  show (a + -b).Same (a' + -b') from add_same ha (neg_same hb)

/-! ## Units and inverses up to the relation -/

/-- Zero added on the right keeps the number. -/
theorem add_zero_same (a : Decimal) : (a + 0).Same a := by
  have ha : min a.exponent 0 ≤ a.exponent := Int.min_le_left _ _
  have h0 : min a.exponent 0 ≤ (0 : Decimal).exponent := Int.min_le_right _ _
  have hz : (0 : Decimal).mantissaAt (min a.exponent 0) = 0 := Int.zero_mul _
  refine (same_iff_mantissaAt (a + 0) a (min a.exponent 0) (Int.le_refl _) ha).mpr ?_
  rw [mantissaAt_add a 0 _ ha h0, hz, Int.add_zero]

/-- Zero added on the left keeps the number. -/
theorem zero_add_same (a : Decimal) : (0 + a).Same a := by
  have ha : min 0 a.exponent ≤ a.exponent := Int.min_le_right _ _
  have h0 : min 0 a.exponent ≤ (0 : Decimal).exponent := Int.min_le_left _ _
  have hz : (0 : Decimal).mantissaAt (min 0 a.exponent) = 0 := Int.zero_mul _
  refine (same_iff_mantissaAt (0 + a) a (min 0 a.exponent) (Int.le_refl _) ha).mpr ?_
  rw [mantissaAt_add 0 a _ h0 ha, hz, Int.zero_add]

/-- A value and its opposite add to zero. -/
theorem add_neg_same (a : Decimal) : (a + -a).Same 0 := by
  have ha : min a.exponent 0 ≤ a.exponent := Int.min_le_left _ _
  have h0 : min a.exponent 0 ≤ (0 : Decimal).exponent := Int.min_le_right _ _
  have hz : (0 : Decimal).mantissaAt (min a.exponent 0) = 0 := Int.zero_mul _
  refine (same_iff_mantissaAt (a + -a) 0 _ (Int.le_min.mpr ⟨ha, ha⟩) h0).mpr ?_
  rw [mantissaAt_add a (-a) _ ha ha, mantissaAt_neg a, hz, Int.add_right_neg]

/-- A value times zero is zero. -/
theorem mul_zero_same (a : Decimal) : (a * 0).Same 0 := by
  show a.mantissa * 0 * 10 ^ (a.exponent + 0 - 0).toNat = 0 * 10 ^ (0 - (a.exponent + 0)).toNat
  rw [Int.mul_zero, Int.zero_mul, Int.zero_mul]

/-! ## Half, fixed and rounding -/

/-- Two halves of a value add to its number. -/
theorem half_add_half (d : Decimal) : (d.half + d.half).Same d := by
  have hh : d.exponent - 1 ≤ d.half.exponent := Int.le_refl _
  have hd : d.exponent - 1 ≤ d.exponent := by omega
  have h1 : (d.exponent - 1 - (d.exponent - 1)).toNat = 0 := by omega
  have h2 : (d.exponent - (d.exponent - 1)).toNat = 1 := by omega
  refine (same_iff_mantissaAt (d.half + d.half) d _ (Int.le_min.mpr ⟨hh, hh⟩) hd).mpr ?_
  rw [mantissaAt_add d.half d.half _ hh hh]
  show d.mantissa * 5 * 10 ^ (d.exponent - 1 - (d.exponent - 1)).toNat +
      d.mantissa * 5 * 10 ^ (d.exponent - 1 - (d.exponent - 1)).toNat =
    d.mantissa * 10 ^ (d.exponent - (d.exponent - 1)).toNat
  rw [h1, h2]
  omega

/-- The number of a half depends only on the number of the value. -/
theorem half_same {a b : Decimal} (h : a.Same b) : a.half.Same b.half :=
  show (a * ⟨5, -1⟩).Same (b * ⟨5, -1⟩) from mul_same h (Same.refl _)

/-- `fixed places n` denotes `n` over ten to the power `places`. -/
theorem fixed_same (places : Nat) (n : Int) : (fixed places n).Same (ofScaled n places) :=
  same_trim (ofScaled n places)

/-- `ofQuotient` denotes its rounded count over ten to the power `places`. -/
theorem ofQuotient_same (num den : Int) (places : Nat) :
    (ofQuotient num den places).Same (ofScaled (roundQuotient num den places) places) :=
  fixed_same places (roundQuotient num den places)

/-- With a positive divisor, the result is the integer nearest the quotient, a half going up. -/
theorem roundQuotient_bound (num den : Int) (places : Nat) (h : 0 < den) :
    2 * den * roundQuotient num den places ≤ 2 * (num * 10 ^ places) + den ∧
      2 * (num * 10 ^ places) + den < 2 * den * (roundQuotient num den places + 1) := by
  have hne : den ≠ 0 := Int.ne_of_gt h
  have habs : (den.natAbs : Int) = den := Int.natAbs_of_nonneg (Int.le_of_lt h)
  have hpos : 0 < 2 * den := by omega
  have hq : roundQuotient num den places = (2 * (num * 10 ^ places) + den) / (2 * den) := by
    simp only [roundQuotient, if_neg hne, if_pos h, habs]
  rw [hq, Int.mul_comm (2 * den), Int.mul_comm (2 * den)]
  exact ⟨Int.ediv_mul_le _ (Int.ne_of_gt hpos), Int.lt_ediv_add_one_mul_self _ hpos⟩

/-- A negative divisor rounds as its opposite does with the opposite numerator. -/
theorem roundQuotient_neg (num den : Int) (places : Nat) (h : den < 0) :
    roundQuotient num den places = roundQuotient (-num) (-den) places := by
  have h1 : den ≠ 0 := Int.ne_of_lt h
  have h2 : ¬ 0 < den := by omega
  have h3 : -den ≠ 0 := by omega
  have h4 : 0 < -den := by omega
  simp only [roundQuotient, if_neg h1, if_neg h2, if_neg h3, if_pos h4, Int.natAbs_neg]

/-- A zero divisor rounds to zero. -/
theorem roundQuotient_zero (num : Int) (places : Nat) : roundQuotient num 0 places = 0 := by
  rw [roundQuotient, if_pos rfl]

/-! ## Text -/

/-- The middle of two numbers is half of their sum. -/
theorem mid_same (a b : Decimal) : (mid a b).Same (a + b).half := same_trim _

/-- A number divided by an integer and rounded is its rounded count over the power of ten. -/
theorem divRound_same (d : Decimal) (den : Int) (places : Nat) :
    (divRound d den places).Same
      (ofScaled (roundQuotient (d.mantissa * 10 ^ (d.exponent + places).toNat)
        (den * 10 ^ (-(d.exponent + places)).toNat) 0) places) :=
  fixed_same _ _

/-- The text of a number is the string of the characters its grammar prints. -/
theorem toString_eq_ofList (d : Decimal) : toString d = String.ofList (grammar.print d) :=
  rfl

end Decimal

/-! ## Points -/

namespace Point

/-- Two points denote one place: their coordinates denote the same numbers. -/
def Same (p q : Point) : Prop := p.x.Same q.x ∧ p.y.Same q.y

/-- A point denotes its own place. -/
theorem Same.refl (p : Point) : p.Same p :=
  ⟨Decimal.Same.refl p.x, Decimal.Same.refl p.y⟩

/-- `Same` on points is symmetric. -/
theorem Same.symm {p q : Point} (h : p.Same q) : q.Same p :=
  ⟨Decimal.Same.symm h.1, Decimal.Same.symm h.2⟩

/-- `Same` on points is transitive. -/
theorem Same.trans {p q r : Point} (hpq : p.Same q) (hqr : q.Same r) : p.Same r :=
  ⟨Decimal.Same.trans hpq.1 hqr.1, Decimal.Same.trans hpq.2 hqr.2⟩

/-- The place of a sum depends only on the places of its two terms. -/
theorem add_same {p p' q q' : Point} (hp : p.Same p') (hq : q.Same q') :
    (p + q).Same (p' + q') :=
  ⟨Decimal.add_same hp.1 hq.1, Decimal.add_same hp.2 hq.2⟩

/-- The place of a scaled point depends only on the number of the factor and the place. -/
theorem scale_same {j k : Decimal} {p q : Point} (hk : j.Same k) (hp : p.Same q) :
    (scale j p).Same (scale k q) :=
  ⟨Decimal.mul_same hk hp.1, Decimal.mul_same hk hp.2⟩

/-- Two copies of the middle point add to the sum of the two points. -/
theorem mid_add_mid (p q : Point) : (mid p q + mid p q).Same (p + q) :=
  ⟨Decimal.half_add_half (p.x + q.x), Decimal.half_add_half (p.y + q.y)⟩

end Point

end Whatwg.Svg.Value
