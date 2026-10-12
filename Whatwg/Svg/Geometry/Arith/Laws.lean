import Whatwg.Svg.Geometry.Arith
import Whatwg.Svg.Value.Cohort

/-!
# Whatwg.Svg.Geometry.Arith.Laws

Owner: the laws of the sum, the difference and the product of `Whatwg/Svg/Geometry/Arith.lean` as
operations on values (slice S10 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-43). Each law here is
an equation of values, not of the numbers they denote: the sum is associative and commutative,
the product is associative and commutative, and the product distributes over the sum, with no
relation between spellings in the statement. Zero is not a unit of the sum as a value, since
`15e1 + 0` is `150`; that law and the others up to `Decimal.Same` are in
`Whatwg/Svg/Geometry/Arith/Same.lean`.
-/

namespace Whatwg.Svg.Value.Decimal

/-! ## The operations, unfolded -/

/-- The sum is the sum of the two mantissas at the lesser of the two exponents. -/
theorem add_def (a b : Decimal) :
    a + b = ⟨a.mantissaAt (min a.exponent b.exponent) + b.mantissaAt (min a.exponent b.exponent),
      min a.exponent b.exponent⟩ := rfl

/-- The product multiplies the mantissas and adds the exponents. -/
theorem mul_def (a b : Decimal) : a * b = ⟨a.mantissa * b.mantissa, a.exponent + b.exponent⟩ :=
  rfl

/-- The opposite number has the opposite mantissa and the same exponent. -/
theorem neg_def (a : Decimal) : -a = ⟨-a.mantissa, a.exponent⟩ := rfl

/-- The difference is the sum with the opposite number. -/
theorem sub_eq_add_neg (a b : Decimal) : a - b = a + -b := rfl

/-- The cast of an integer is the integer as a number. -/
theorem intCast_eq (n : Int) : ((n : Int) : Decimal) = ofInt n := rfl

/-! ## The mantissa at an exponent -/

/-- The mantissa at an exponent is the mantissa times the power of ten between the two. -/
theorem mantissaAt_def (d : Decimal) (e : Int) :
    d.mantissaAt e = d.mantissa * 10 ^ (d.exponent - e).toNat := rfl

/-- At an exponent that is at most both exponents, the mantissa of a sum is the sum of the
mantissas. -/
theorem mantissaAt_add (a b : Decimal) (e : Int) (ha : e ≤ a.exponent) (hb : e ≤ b.exponent) :
    (a + b).mantissaAt e = a.mantissaAt e + b.mantissaAt e := by
  have h1 : (a.exponent - min a.exponent b.exponent).toNat +
      (min a.exponent b.exponent - e).toNat = (a.exponent - e).toNat := by omega
  have h2 : (b.exponent - min a.exponent b.exponent).toNat +
      (min a.exponent b.exponent - e).toNat = (b.exponent - e).toNat := by omega
  show (a.mantissa * 10 ^ (a.exponent - min a.exponent b.exponent).toNat +
      b.mantissa * 10 ^ (b.exponent - min a.exponent b.exponent).toNat) *
      10 ^ (min a.exponent b.exponent - e).toNat =
    a.mantissa * 10 ^ (a.exponent - e).toNat + b.mantissa * 10 ^ (b.exponent - e).toNat
  rw [← h1, ← h2, Int.pow_add, Int.pow_add, Int.add_mul, Int.mul_assoc, Int.mul_assoc]

/-- The mantissa of a product, at the exponent of the left factor more than `e`, is the left
mantissa times the mantissa of the right factor at `e`. -/
theorem mul_mantissaAt (a b : Decimal) (e : Int) :
    (a * b).mantissaAt (a.exponent + e) = a.mantissa * b.mantissaAt e := by
  have h : (a.exponent + b.exponent - (a.exponent + e)).toNat = (b.exponent - e).toNat := by
    omega
  show a.mantissa * b.mantissa * 10 ^ (a.exponent + b.exponent - (a.exponent + e)).toNat =
    a.mantissa * (b.mantissa * 10 ^ (b.exponent - e).toNat)
  rw [h, Int.mul_assoc]

/-- The mantissa of the opposite number, at any exponent, is the opposite mantissa. -/
theorem mantissaAt_neg (a : Decimal) (e : Int) : (-a).mantissaAt e = -a.mantissaAt e :=
  Int.neg_mul a.mantissa (10 ^ (a.exponent - e).toNat)

/-! ## The sum -/

/-- The sum of two values does not depend on their order. -/
theorem add_comm (a b : Decimal) : a + b = b + a := by
  have he : min b.exponent a.exponent = min a.exponent b.exponent := by omega
  rw [add_def, add_def, he,
    Int.add_comm (a.mantissaAt (min a.exponent b.exponent))
      (b.mantissaAt (min a.exponent b.exponent))]

/-- The sum of three values does not depend on which two are added first. -/
theorem add_assoc (a b c : Decimal) : a + b + c = a + (b + c) := by
  have he : min (min a.exponent b.exponent) c.exponent =
      min a.exponent (min b.exponent c.exponent) := by omega
  have hab := mantissaAt_add a b (min a.exponent (min b.exponent c.exponent))
    (by omega) (by omega)
  have hbc := mantissaAt_add b c (min a.exponent (min b.exponent c.exponent))
    (by omega) (by omega)
  apply ext
  · show (a + b).mantissaAt (min (min a.exponent b.exponent) c.exponent) +
        c.mantissaAt (min (min a.exponent b.exponent) c.exponent) =
      a.mantissaAt (min a.exponent (min b.exponent c.exponent)) +
        (b + c).mantissaAt (min a.exponent (min b.exponent c.exponent))
    rw [he, hab, hbc, Int.add_assoc]
  · exact he

/-- The left value of a sum of three may change places with the middle one. -/
theorem add_left_comm (a b c : Decimal) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

/-! ## The product -/

/-- The product of two values does not depend on their order. -/
theorem mul_comm (a b : Decimal) : a * b = b * a :=
  ext (Int.mul_comm a.mantissa b.mantissa) (Int.add_comm a.exponent b.exponent)

/-- The product of three values does not depend on which two are multiplied first. -/
theorem mul_assoc (a b c : Decimal) : a * b * c = a * (b * c) :=
  ext (Int.mul_assoc a.mantissa b.mantissa c.mantissa)
    (Int.add_assoc a.exponent b.exponent c.exponent)

/-- One on the left is a unit of the product, as a value. -/
theorem one_mul (a : Decimal) : 1 * a = a :=
  ext (Int.one_mul a.mantissa) (Int.zero_add a.exponent)

/-- One on the right is a unit of the product, as a value. -/
theorem mul_one (a : Decimal) : a * 1 = a :=
  ext (Int.mul_one a.mantissa) (Int.add_zero a.exponent)

/-- The product distributes over the sum on the left, as an equation of values. -/
theorem mul_add (a b c : Decimal) : a * (b + c) = a * b + a * c := by
  have he : min (a.exponent + b.exponent) (a.exponent + c.exponent) =
      a.exponent + min b.exponent c.exponent := by omega
  apply ext
  · show a.mantissa * (b.mantissaAt (min b.exponent c.exponent) +
        c.mantissaAt (min b.exponent c.exponent)) =
      (a * b).mantissaAt (min (a.exponent + b.exponent) (a.exponent + c.exponent)) +
        (a * c).mantissaAt (min (a.exponent + b.exponent) (a.exponent + c.exponent))
    rw [he, mul_mantissaAt, mul_mantissaAt, Int.mul_add]
  · exact he.symm

/-- The product distributes over the sum on the right, as an equation of values. -/
theorem add_mul (a b c : Decimal) : (a + b) * c = a * c + b * c := by
  rw [mul_comm (a + b) c, mul_add, mul_comm c a, mul_comm c b]

/-! ## The opposite number -/

/-- The opposite of the opposite number is the value. -/
theorem neg_neg (a : Decimal) : - -a = a :=
  ext (Int.neg_neg a.mantissa) rfl

/-- The opposite of a sum is the sum of the opposites. -/
theorem neg_add (a b : Decimal) : -(a + b) = -a + -b := by
  apply ext
  · show -(a.mantissaAt (min a.exponent b.exponent) + b.mantissaAt (min a.exponent b.exponent)) =
      (-a).mantissaAt (min a.exponent b.exponent) + (-b).mantissaAt (min a.exponent b.exponent)
    rw [mantissaAt_neg, mantissaAt_neg, Int.neg_add]
  · rfl

/-- The opposite of the left factor is the opposite of the product. -/
theorem neg_mul (a b : Decimal) : -a * b = -(a * b) :=
  ext (Int.neg_mul a.mantissa b.mantissa) rfl

/-- The opposite of the right factor is the opposite of the product. -/
theorem mul_neg (a b : Decimal) : a * -b = -(a * b) :=
  ext (Int.mul_neg a.mantissa b.mantissa) rfl

/-! ## Integers -/

/-- The sum of two integers as numbers is their sum as a number. -/
theorem ofInt_add (m n : Int) : ofInt m + ofInt n = ofInt (m + n) := by
  have h : ((0 : Int) - min 0 0).toNat = 0 := by omega
  apply ext
  · show m * 10 ^ ((0 : Int) - min 0 0).toNat + n * 10 ^ ((0 : Int) - min 0 0).toNat = m + n
    rw [h, Int.pow_zero, Int.mul_one, Int.mul_one]
  · show min (0 : Int) 0 = 0
    omega

/-- The product of two integers as numbers is their product as a number. -/
theorem ofInt_mul (m n : Int) : ofInt m * ofInt n = ofInt (m * n) :=
  ext rfl (Int.add_zero 0)

/-- The opposite of an integer as a number is the opposite integer as a number. -/
theorem ofInt_neg (n : Int) : -ofInt n = ofInt (-n) := rfl

/-- The difference of two integers as numbers is their difference as a number. -/
theorem ofInt_sub (m n : Int) : ofInt m - ofInt n = ofInt (m - n) := by
  rw [sub_eq_add_neg, ofInt_neg, ofInt_add, Int.sub_eq_add_neg]

/-! ## Sums and products up to order -/

/-- The sum of decimals is associative, for `ac_rfl`. -/
instance : Std.Associative (α := Decimal) (· + ·) := ⟨add_assoc⟩

/-- The sum of decimals is commutative, for `ac_rfl`. -/
instance : Std.Commutative (α := Decimal) (· + ·) := ⟨add_comm⟩

/-- The product of decimals is associative, for `ac_rfl`. -/
instance : Std.Associative (α := Decimal) (· * ·) := ⟨mul_assoc⟩

/-- The product of decimals is commutative, for `ac_rfl`. -/
instance : Std.Commutative (α := Decimal) (· * ·) := ⟨mul_comm⟩

/-- The right value of a sum of three may change places with the middle one. -/
theorem add_right_comm (a b c : Decimal) : a + b + c = a + c + b := by
  ac_rfl

end Whatwg.Svg.Value.Decimal

namespace Whatwg.Svg.Value.Point

/-- The sum of two points is the sum of their coordinates. -/
theorem add_def (p q : Point) : p + q = ⟨p.x + q.x, p.y + q.y⟩ := rfl

/-- The sum of two points does not depend on their order. -/
theorem add_comm (p q : Point) : p + q = q + p := by
  rw [add_def, add_def, Decimal.add_comm p.x q.x, Decimal.add_comm p.y q.y]

/-- The sum of three points does not depend on which two are added first. -/
theorem add_assoc (p q r : Point) : p + q + r = p + (q + r) := by
  show (⟨p.x + q.x + r.x, p.y + q.y + r.y⟩ : Point) = ⟨p.x + (q.x + r.x), p.y + (q.y + r.y)⟩
  rw [Decimal.add_assoc, Decimal.add_assoc]

/-- Scaling a sum of two points is the sum of the scaled points. -/
theorem scale_add (k : Decimal) (p q : Point) : scale k (p + q) = scale k p + scale k q := by
  show (⟨k * (p.x + q.x), k * (p.y + q.y)⟩ : Point) = ⟨k * p.x + k * q.x, k * p.y + k * q.y⟩
  rw [Decimal.mul_add, Decimal.mul_add]

/-- Scaling twice is scaling once by the product. -/
theorem scale_scale (j k : Decimal) (p : Point) : scale j (scale k p) = scale (j * k) p := by
  show (⟨j * (k * p.x), j * (k * p.y)⟩ : Point) = ⟨j * k * p.x, j * k * p.y⟩
  rw [Decimal.mul_assoc, Decimal.mul_assoc]

/-- The point half way between two points does not depend on their order. -/
theorem mid_comm (p q : Point) : mid p q = mid q p := by
  show (⟨(p.x + q.x).half, (p.y + q.y).half⟩ : Point) = ⟨(q.x + p.x).half, (q.y + p.y).half⟩
  rw [Decimal.add_comm p.x q.x, Decimal.add_comm p.y q.y]

end Whatwg.Svg.Value.Point
