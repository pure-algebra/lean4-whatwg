import Whatwg.Svg.Geometry.Arith.Laws
import Whatwg.Svg.Geometry.Arith.Same

/-!
# Whatwg.Svg.Geometry.Order

Owner: the order of the exact numbers (slice S10 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-43).
Two values are compared as the numbers they denote: at the lesser of their exponents, by their
mantissas there. So `15e1` and `150` compare equal though they are two values, and the order
is that of the numbers and not of the spellings. `compare`, `<`, `≤`, `min`, `max`, `abs` and
`clamp` are decided by integer arithmetic, with no quotient.

The laws say that the order is total, that it reads the number and not the spelling
(`compare_congr`), that comparing equal is denoting one number (`compare_eq_iff_same`), and that
the sum and a product by a number that is not negative keep it.
-/

namespace Whatwg.Svg.Value.Decimal

/-! ## The order -/

/-- The order of two values as numbers: that of their mantissas at the lesser exponent. -/
def compare (a b : Decimal) : Ordering :=
  Ord.compare (a.mantissaAt (min a.exponent b.exponent))
    (b.mantissaAt (min a.exponent b.exponent))

/-- Values are compared as the numbers they denote. -/
instance : Ord Decimal := ⟨compare⟩

/-- `a < b`: the number of `a` is less than the number of `b`. -/
instance : LT Decimal := ⟨fun a b => compare a b = .lt⟩

/-- `a ≤ b`: the number of `a` is not greater than the number of `b`. -/
instance : LE Decimal := ⟨fun a b => compare a b ≠ .gt⟩

/-- `a < b` is decided by comparing the two values. -/
instance (a b : Decimal) : Decidable (a < b) :=
  inferInstanceAs (Decidable (compare a b = .lt))

/-- `a ≤ b` is decided by comparing the two values. -/
instance (a b : Decimal) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (compare a b ≠ .gt))

/-- The lesser of two values, and the left one when they denote one number. -/
instance : Min Decimal := ⟨fun a b => if a ≤ b then a else b⟩

/-- The greater of two values, and the right one when they denote one number. -/
instance : Max Decimal := ⟨fun a b => if a ≤ b then b else a⟩

/-- The number without its sign: the absolute value of the mantissa at the same exponent. -/
def abs (d : Decimal) : Decimal := ⟨d.mantissa.natAbs, d.exponent⟩

/-- Whether the number is less than zero: its mantissa is. -/
def isNegative (d : Decimal) : Bool := decide (d.mantissa < 0)

/-- The value `d` held between `lo` and `hi`: at most `hi` first, and then at least `lo`. -/
def clamp (lo hi d : Decimal) : Decimal := max lo (min hi d)

/-! ## The definitions, unfolded -/

/-- Comparing two values is comparing their mantissas at the lesser of their exponents. -/
theorem compare_def (a b : Decimal) :
    compare a b = Ord.compare (a.mantissaAt (min a.exponent b.exponent))
      (b.mantissaAt (min a.exponent b.exponent)) := rfl

/-- `a < b` says that comparing `a` with `b` answers less. -/
theorem lt_def (a b : Decimal) : a < b ↔ compare a b = .lt := Iff.rfl

/-- `a ≤ b` says that comparing `a` with `b` does not answer greater. -/
theorem le_def (a b : Decimal) : a ≤ b ↔ compare a b ≠ .gt := Iff.rfl

/-- The lesser of two values is the left one when it is at most the right one. -/
theorem min_def (a b : Decimal) : min a b = if a ≤ b then a else b := rfl

/-- The greater of two values is the right one when the left one is at most it. -/
theorem max_def (a b : Decimal) : max a b = if a ≤ b then b else a := rfl

/-! ## Comparing integers -/

/-- Comparing two integers asks whether the left is less, and then whether they are equal. -/
theorem intCompare_def (x y : Int) :
    Ord.compare x y = if x < y then .lt else if x = y then .eq else .gt := rfl

/-- An integer less than another compares less. -/
theorem intCompare_of_lt {x y : Int} (h : x < y) : Ord.compare x y = .lt := by
  rw [intCompare_def, if_pos h]

/-- Equal integers compare equal. -/
theorem intCompare_of_eq {x y : Int} (h : x = y) : Ord.compare x y = .eq := by
  have hn : ¬ x < y := by omega
  rw [intCompare_def, if_neg hn, if_pos h]

/-- An integer greater than another compares greater. -/
theorem intCompare_of_gt {x y : Int} (h : y < x) : Ord.compare x y = .gt := by
  have hn : ¬ x < y := by omega
  have hne : ¬ x = y := by omega
  rw [intCompare_def, if_neg hn, if_neg hne]

/-- Two integers stand in one of three orders, and each order fixes the comparison. -/
theorem intCompare_cases (x y : Int) :
    x < y ∧ Ord.compare x y = .lt ∨ x = y ∧ Ord.compare x y = .eq ∨
      y < x ∧ Ord.compare x y = .gt := by
  obtain h | h | h := Int.lt_trichotomy x y
  · exact Or.inl ⟨h, intCompare_of_lt h⟩
  · exact Or.inr (Or.inl ⟨h, intCompare_of_eq h⟩)
  · exact Or.inr (Or.inr ⟨h, intCompare_of_gt h⟩)

/-- Two integers compare less exactly when the left one is less. -/
theorem intCompare_eq_lt_iff (x y : Int) : Ord.compare x y = .lt ↔ x < y := by
  obtain ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ := intCompare_cases x y
  · exact ⟨fun _ => h, fun _ => e⟩
  · rw [e]
    exact ⟨fun c => (nomatch c), fun c => absurd c (by omega)⟩
  · rw [e]
    exact ⟨fun c => (nomatch c), fun c => absurd c (by omega)⟩

/-- Two integers compare equal exactly when they are equal. -/
theorem intCompare_eq_eq_iff (x y : Int) : Ord.compare x y = .eq ↔ x = y := by
  obtain ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ := intCompare_cases x y
  · rw [e]
    exact ⟨fun c => (nomatch c), fun c => absurd c (by omega)⟩
  · exact ⟨fun _ => h, fun _ => e⟩
  · rw [e]
    exact ⟨fun c => (nomatch c), fun c => absurd c (by omega)⟩

/-- Two integers do not compare greater exactly when the left one is at most the right one. -/
theorem intCompare_ne_gt_iff (x y : Int) : Ord.compare x y ≠ .gt ↔ x ≤ y := by
  obtain ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ := intCompare_cases x y
  · rw [e]
    exact ⟨fun _ => Int.le_of_lt h, fun _ c => nomatch c⟩
  · rw [e]
    exact ⟨fun _ => Int.le_of_eq h, fun _ c => nomatch c⟩
  · rw [e]
    exact ⟨fun c => absurd rfl c, fun c => absurd c (by omega)⟩

/-- Comparing two integers in the other order gives the opposite answer. -/
theorem intCompare_swap (x y : Int) : Ord.compare y x = (Ord.compare x y).swap := by
  obtain ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ := intCompare_cases x y
  · rw [e]
    exact intCompare_of_gt h
  · rw [e]
    exact intCompare_of_eq h.symm
  · rw [e]
    exact intCompare_of_lt h

/-- Multiplying two integers by one positive integer keeps their comparison. -/
theorem intCompare_mul_right (x y : Int) {p : Int} (hp : 0 < p) :
    Ord.compare (x * p) (y * p) = Ord.compare x y := by
  obtain ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ := intCompare_cases x y
  · rw [e]
    exact intCompare_of_lt (Int.mul_lt_mul_of_pos_right h hp)
  · rw [e]
    exact intCompare_of_eq (by rw [h])
  · rw [e]
    exact intCompare_of_gt (Int.mul_lt_mul_of_pos_right h hp)

/-! ## The order at a common exponent -/

/-- The mantissa at a lower exponent is the one at a higher exponent times a power of ten. -/
theorem mantissaAt_rescale (a : Decimal) (e k : Int) (he : e ≤ a.exponent) (hk : k ≤ e) :
    a.mantissaAt k = a.mantissaAt e * 10 ^ (e - k).toNat := by
  have h : (a.exponent - e).toNat + (e - k).toNat = (a.exponent - k).toNat := by omega
  rw [mantissaAt_def, mantissaAt_def, ← h, Int.pow_add, Int.mul_assoc]

/-- Any exponent that is at most both exponents gives the same comparison. -/
theorem compare_at (a b : Decimal) (k : Int) (ha : k ≤ a.exponent) (hb : k ≤ b.exponent) :
    compare a b = Ord.compare (a.mantissaAt k) (b.mantissaAt k) := by
  have hk : k ≤ min a.exponent b.exponent := Int.le_min.mpr ⟨ha, hb⟩
  have hp : (0 : Int) < 10 ^ (min a.exponent b.exponent - k).toNat := Int.pow_pos (by decide)
  rw [compare_def, mantissaAt_rescale a _ k (Int.min_le_left _ _) hk,
    mantissaAt_rescale b _ k (Int.min_le_right _ _) hk, intCompare_mul_right _ _ hp]

/-- Two values compare equal exactly when they denote one number. -/
theorem compare_eq_iff_same (a b : Decimal) : compare a b = .eq ↔ a.Same b := by
  have ha := Int.min_le_left a.exponent b.exponent
  have hb := Int.min_le_right a.exponent b.exponent
  rw [compare_def, same_iff_mantissaAt a b _ ha hb]
  exact intCompare_eq_eq_iff _ _

/-- The comparison reads the numbers of its two values and not their spellings. -/
theorem compare_congr {a a' b b' : Decimal} (ha : a.Same a') (hb : b.Same b') :
    compare a b = compare a' b' := by
  obtain ⟨k, h1, h2, h3, h4⟩ :
      ∃ k : Int, k ≤ a.exponent ∧ k ≤ a'.exponent ∧ k ≤ b.exponent ∧ k ≤ b'.exponent :=
    ⟨min (min a.exponent a'.exponent) (min b.exponent b'.exponent),
      by omega, by omega, by omega, by omega⟩
  rw [compare_at a b k h1 h3, compare_at a' b' k h2 h4,
    (same_iff_mantissaAt a a' k h1 h2).mp ha, (same_iff_mantissaAt b b' k h3 h4).mp hb]

/-- Comparing two values in the other order gives the opposite answer. -/
theorem compare_swap (a b : Decimal) : compare b a = (compare a b).swap := by
  have ha := Int.min_le_left a.exponent b.exponent
  have hb := Int.min_le_right a.exponent b.exponent
  rw [compare_at a b _ ha hb, compare_at b a _ hb ha]
  exact intCompare_swap _ _

/-- `a < b` is the order of the mantissas at any exponent that is at most both exponents. -/
theorem lt_iff_at (a b : Decimal) (k : Int) (ha : k ≤ a.exponent) (hb : k ≤ b.exponent) :
    a < b ↔ a.mantissaAt k < b.mantissaAt k := by
  rw [lt_def, compare_at a b k ha hb]
  exact intCompare_eq_lt_iff _ _

/-- `a ≤ b` is the order of the mantissas at any exponent that is at most both exponents. -/
theorem le_iff_at (a b : Decimal) (k : Int) (ha : k ≤ a.exponent) (hb : k ≤ b.exponent) :
    a ≤ b ↔ a.mantissaAt k ≤ b.mantissaAt k := by
  rw [le_def, compare_at a b k ha hb]
  exact intCompare_ne_gt_iff _ _

/-! ## The order is total -/

/-- A value is at most itself. -/
theorem le_refl (a : Decimal) : a ≤ a :=
  (le_iff_at a a a.exponent (Int.le_refl _) (Int.le_refl _)).mpr (Int.le_refl _)

/-- A value is at most any value that denotes the same number. -/
theorem le_of_same {a b : Decimal} (h : a.Same b) : a ≤ b := by
  have ha := Int.min_le_left a.exponent b.exponent
  have hb := Int.min_le_right a.exponent b.exponent
  exact (le_iff_at a b _ ha hb).mpr (Int.le_of_eq ((same_iff_mantissaAt a b _ ha hb).mp h))

/-- `≤` is transitive: the three values are compared at the least of their exponents. -/
theorem le_trans {a b c : Decimal} : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  obtain ⟨k, h1, h2, h3⟩ : ∃ k : Int, k ≤ a.exponent ∧ k ≤ b.exponent ∧ k ≤ c.exponent :=
    ⟨min a.exponent (min b.exponent c.exponent), by omega, by omega, by omega⟩
  exact (le_iff_at a c k h1 h3).mpr
    (Int.le_trans ((le_iff_at a b k h1 h2).mp hab) ((le_iff_at b c k h2 h3).mp hbc))

/-- A value less than one that is at most a third is less than the third. -/
theorem lt_of_lt_of_le {a b c : Decimal} : a < b → b ≤ c → a < c := by
  intro hab hbc
  obtain ⟨k, h1, h2, h3⟩ : ∃ k : Int, k ≤ a.exponent ∧ k ≤ b.exponent ∧ k ≤ c.exponent :=
    ⟨min a.exponent (min b.exponent c.exponent), by omega, by omega, by omega⟩
  exact (lt_iff_at a c k h1 h3).mpr
    (Int.lt_of_lt_of_le ((lt_iff_at a b k h1 h2).mp hab) ((le_iff_at b c k h2 h3).mp hbc))

/-- A value at most one that is less than a third is less than the third. -/
theorem lt_of_le_of_lt {a b c : Decimal} : a ≤ b → b < c → a < c := by
  intro hab hbc
  obtain ⟨k, h1, h2, h3⟩ : ∃ k : Int, k ≤ a.exponent ∧ k ≤ b.exponent ∧ k ≤ c.exponent :=
    ⟨min a.exponent (min b.exponent c.exponent), by omega, by omega, by omega⟩
  exact (lt_iff_at a c k h1 h3).mpr
    (Int.lt_of_le_of_lt ((le_iff_at a b k h1 h2).mp hab) ((lt_iff_at b c k h2 h3).mp hbc))

/-- Of two values, one is at most the other. -/
theorem le_total (a b : Decimal) : a ≤ b ∨ b ≤ a := by
  have ha := Int.min_le_left a.exponent b.exponent
  have hb := Int.min_le_right a.exponent b.exponent
  rw [le_iff_at a b _ ha hb, le_iff_at b a _ hb ha]
  exact Int.le_total _ _

/-- Two values that are each at most the other denote one number. -/
theorem le_antisymm_same {a b : Decimal} : a ≤ b → b ≤ a → a.Same b := by
  intro hab hba
  have ha := Int.min_le_left a.exponent b.exponent
  have hb := Int.min_le_right a.exponent b.exponent
  exact (same_iff_mantissaAt a b _ ha hb).mpr
    (Int.le_antisymm ((le_iff_at a b _ ha hb).mp hab) ((le_iff_at b a _ hb ha).mp hba))

/-- A value is not less than another exactly when the other is at most it. -/
theorem not_lt_iff_le (a b : Decimal) : ¬ a < b ↔ b ≤ a := by
  have ha := Int.min_le_left a.exponent b.exponent
  have hb := Int.min_le_right a.exponent b.exponent
  rw [lt_iff_at a b _ ha hb, le_iff_at b a _ hb ha]
  exact Int.not_lt

/-! ## Integers -/

/-- The mantissa of an integer as a number, at the exponent zero, is the integer. -/
theorem mantissaAt_ofInt (n : Int) : (ofInt n).mantissaAt 0 = n := by
  have h : ((0 : Int) - 0).toNat = 0 := by omega
  show n * 10 ^ ((0 : Int) - 0).toNat = n
  rw [h, Int.pow_zero, Int.mul_one]

/-- Two integers as numbers are ordered by `≤` as the integers are. -/
theorem ofInt_le_ofInt (m n : Int) : ofInt m ≤ ofInt n ↔ m ≤ n := by
  rw [le_iff_at (ofInt m) (ofInt n) 0 (Int.le_refl 0) (Int.le_refl 0), mantissaAt_ofInt,
    mantissaAt_ofInt]

/-- Two integers as numbers are ordered by `<` as the integers are. -/
theorem ofInt_lt_ofInt (m n : Int) : ofInt m < ofInt n ↔ m < n := by
  rw [lt_iff_at (ofInt m) (ofInt n) 0 (Int.le_refl 0) (Int.le_refl 0), mantissaAt_ofInt,
    mantissaAt_ofInt]

/-! ## The sum, the opposite and the product -/

/-- Adding one value on the right of both sides keeps `≤`. -/
theorem add_le_add_right {a b : Decimal} (h : a ≤ b) (c : Decimal) : a + c ≤ b + c := by
  obtain ⟨k, h1, h2, h3⟩ : ∃ k : Int, k ≤ a.exponent ∧ k ≤ b.exponent ∧ k ≤ c.exponent :=
    ⟨min a.exponent (min b.exponent c.exponent), by omega, by omega, by omega⟩
  rw [le_iff_at (a + c) (b + c) k (Int.le_min.mpr ⟨h1, h3⟩) (Int.le_min.mpr ⟨h2, h3⟩),
    mantissaAt_add a c k h1 h3, mantissaAt_add b c k h2 h3]
  exact Int.add_le_add_right ((le_iff_at a b k h1 h2).mp h) _

/-- Adding one value on the left of both sides keeps `≤`. -/
theorem add_le_add_left {a b : Decimal} (h : a ≤ b) (c : Decimal) : c + a ≤ c + b := by
  rw [add_comm c a, add_comm c b]
  exact add_le_add_right h c

/-- The opposites of two values stand in the opposite order. -/
theorem neg_le_neg {a b : Decimal} (h : a ≤ b) : -b ≤ -a := by
  have ha := Int.min_le_left a.exponent b.exponent
  have hb := Int.min_le_right a.exponent b.exponent
  rw [le_iff_at (-b) (-a) _ hb ha, mantissaAt_neg, mantissaAt_neg]
  exact Int.neg_le_neg ((le_iff_at a b _ ha hb).mp h)

/-- Multiplying both sides on the left by a value that is not negative keeps `≤`. -/
theorem mul_le_mul_of_nonneg_left {a b : Decimal} (h : a ≤ b) {c : Decimal} (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  obtain ⟨k, h1, h2⟩ : ∃ k : Int, k ≤ a.exponent ∧ k ≤ b.exponent :=
    ⟨min a.exponent b.exponent, Int.min_le_left _ _, Int.min_le_right _ _⟩
  obtain ⟨j, h0, h3⟩ : ∃ j : Int, j ≤ (0 : Decimal).exponent ∧ j ≤ c.exponent :=
    ⟨min 0 c.exponent, Int.min_le_left _ _, Int.min_le_right _ _⟩
  have hz : (0 : Decimal).mantissaAt j = 0 := Int.zero_mul _
  have hj : 0 ≤ c.mantissaAt j := by
    rw [← hz]
    exact (le_iff_at 0 c j h0 h3).mp hc
  rw [le_iff_at (c * a) (c * b) (j + k) (Int.add_le_add h3 h1) (Int.add_le_add h3 h2),
    mantissaAt_mul c a j k h3 h1, mantissaAt_mul c b j k h3 h2]
  exact Int.mul_le_mul_of_nonneg_left ((le_iff_at a b k h1 h2).mp h) hj

/-! ## The lesser and the greater -/

/-- The lesser of two values is at most the left one. -/
theorem min_le_left (a b : Decimal) : min a b ≤ a := by
  cases Decidable.em (a ≤ b) with
  | inl h =>
    rw [min_def, if_pos h]
    exact le_refl a
  | inr h =>
    rw [min_def, if_neg h]
    exact (le_total a b).resolve_left h

/-- The lesser of two values is at most the right one. -/
theorem min_le_right (a b : Decimal) : min a b ≤ b := by
  cases Decidable.em (a ≤ b) with
  | inl h =>
    rw [min_def, if_pos h]
    exact h
  | inr h =>
    rw [min_def, if_neg h]
    exact le_refl b

/-- The left one of two values is at most the greater. -/
theorem le_max_left (a b : Decimal) : a ≤ max a b := by
  cases Decidable.em (a ≤ b) with
  | inl h =>
    rw [max_def, if_pos h]
    exact h
  | inr h =>
    rw [max_def, if_neg h]
    exact le_refl a

/-- The right one of two values is at most the greater. -/
theorem le_max_right (a b : Decimal) : b ≤ max a b := by
  cases Decidable.em (a ≤ b) with
  | inl h =>
    rw [max_def, if_pos h]
    exact le_refl b
  | inr h =>
    rw [max_def, if_neg h]
    exact (le_total a b).resolve_left h

/-- The lesser of two values is one of the two. -/
theorem min_eq_or (a b : Decimal) : min a b = a ∨ min a b = b := by
  cases Decidable.em (a ≤ b) with
  | inl h => exact Or.inl ((min_def a b).trans (if_pos h))
  | inr h => exact Or.inr ((min_def a b).trans (if_neg h))

/-- The greater of two values is one of the two. -/
theorem max_eq_or (a b : Decimal) : max a b = a ∨ max a b = b := by
  cases Decidable.em (a ≤ b) with
  | inl h => exact Or.inr ((max_def a b).trans (if_pos h))
  | inr h => exact Or.inl ((max_def a b).trans (if_neg h))

/-- A clamped value is at least the lower bound. -/
theorem le_clamp {lo hi : Decimal} (d : Decimal) : lo ≤ clamp lo hi d :=
  le_max_left lo (min hi d)

/-- A clamped value is at most the upper bound, when the lower bound is. -/
theorem clamp_le {lo hi : Decimal} (h : lo ≤ hi) (d : Decimal) : clamp lo hi d ≤ hi := by
  show max lo (min hi d) ≤ hi
  cases max_eq_or lo (min hi d) with
  | inl e =>
    rw [e]
    exact h
  | inr e =>
    rw [e]
    exact min_le_left hi d

/-- The number without its sign is not negative. -/
theorem abs_nonneg (d : Decimal) : 0 ≤ abs d := by
  obtain ⟨k, h0, h1⟩ : ∃ k : Int, k ≤ (0 : Decimal).exponent ∧ k ≤ (abs d).exponent :=
    ⟨min 0 d.exponent, Int.min_le_left _ _, Int.min_le_right _ _⟩
  have hz : (0 : Decimal).mantissaAt k = 0 := Int.zero_mul _
  have hp : (0 : Int) < 10 ^ (d.exponent - k).toNat := Int.pow_pos (by decide)
  rw [le_iff_at 0 (abs d) k h0 h1, hz]
  exact Int.mul_nonneg (Int.natCast_nonneg d.mantissa.natAbs) (Int.le_of_lt hp)

end Whatwg.Svg.Value.Decimal
