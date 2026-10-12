import Whatwg.Svg.Geometry.Root
import Whatwg.Svg.Geometry.Rational.Laws

/-!
# Whatwg.Svg.Geometry.Root.Laws

Owner: the laws of the root rounded down, and of what is stated through it (slice S11 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-56).

- **The root.** `sqrtDown q places` is not negative, and it is zero for a `q` that is not
  positive. For a `q` that is not negative its square is no more than `q`
  (`sqrtDown_mul_self_le`), and for every `q` the square of the next number of that many places
  is more than `q` (`lt_sqrtDown_succ`). So the root of `q` lies from `sqrtDown q places` to
  less than one unit of the last place above it. On the square of a count of that many places
  it is the count (`sqrtDown_sq`). The two bounds are the two bounds that core proves for
  `Nat.sqrt`, divided by a power of ten.
- **Lengths.** A length is not negative and its square is no more than the square of the
  length (`Vec.norm_mul_self_le`). A quarter turn keeps it, a distance is the same both ways
  and between two points moved together, a unit vector is no shorter than one where the length
  does not round down to zero and longer by less than the part that one unit of the last place
  is of its rounded length (`Vec.normSq_unit_lt`), and a vector is at a right angle to its
  normal.
- **Beside a segment.** A moved segment has the samples, moved, the same normal, the points
  beside it, moved, and the same length through chords. A point no distance beside a segment
  is the point of the segment.

The lemmas under "Numbers" are about numbers alone and serve the proofs after them.

What this module does not claim: that a unit vector of a short vector is near length one,
which `Vec.normSq_unit_lt` shows it need not be; that a
normal is not zero, which fails where the length of a direction rounds down to zero, as for a
segment whose four points are one point; a bound between the length through chords and the
length of the curve.
-/

namespace Whatwg.Svg.Value

open Decimal (ratTen_pow_pos ratTen_pow_ne rat_div_le_div rat_div_lt_div)

/-! ## Numbers -/

/-- A hundred to a power is ten to that power, twice. -/
theorem ratHundred_pow (n : Nat) : (100 : Rat) ^ n = (10 : Rat) ^ n * (10 : Rat) ^ n := by
  induction n with
  | zero => simp only [Rat.pow_zero, Rat.mul_one]
  | succ n ih =>
    rw [Rat.pow_succ, Rat.pow_succ, ih]
    grind

/-- The whole root of a square is the number that was squared. -/
theorem natSqrt_mul_self (k : Nat) : Nat.sqrt (k * k) = k :=
  Nat.le_antisymm (Nat.mul_self_le_mul_self_iff.mp (Nat.sqrt_le (k * k)))
    (Nat.lt_succ_iff.mp (Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_succ_sqrt (k * k))))


/-- The count of the floor of a number that is not negative is no more than the number. -/
theorem rat_floor_toNat_le {x : Rat} (h : 0 ≤ x) : ((x.floor.toNat : Nat) : Rat) ≤ x := by
  have hf : 0 ≤ x.floor := Rat.le_floor_iff.mpr h
  rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hf]
  exact Rat.floor_le x

/-- Every rational number is less than the count of its floor and one. -/
theorem rat_lt_floor_toNat_succ (x : Rat) : x < ((x.floor.toNat + 1 : Nat) : Rat) := by
  have h1 : x < ((x.floor + 1 : Int) : Rat) := Rat.lt_floor_add_one x
  have h2 : x.floor + 1 ≤ ((x.floor.toNat + 1 : Nat) : Int) := by
    have := Int.self_le_toNat x.floor
    omega
  have h3 := Rat.intCast_le_intCast.mpr h2
  rw [Rat.intCast_natCast] at h3
  grind

/-- A count whose square is no more than a number scaled twice has, over the scale, a square
that is no more than the number. -/
theorem rat_div_mul_self_le {s q c : Rat} (hc : 0 < c) (h : s * s ≤ q * (c * c)) :
    s / c * (s / c) ≤ q := by
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  have hle := rat_div_le_div (Rat.mul_pos hc hc) h
  have e1 : s * s / (c * c) = s / c * (s / c) := by grind
  have e2 : q * (c * c) / (c * c) = q := by grind
  rw [e1, e2] at hle
  exact hle

/-- A number that, scaled twice, is less than the square of the next count is less than the
square of the count over the scale and one unit of the scale. -/
theorem rat_lt_div_mul_self {s q c : Rat} (hc : 0 < c) (h : q * (c * c) < (s + 1) * (s + 1)) :
    q < (s / c + 1 / c) * (s / c + 1 / c) := by
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  have hlt := rat_div_lt_div (Rat.mul_pos hc hc) h
  have e1 : (s + 1) * (s + 1) / (c * c) = (s / c + 1 / c) * (s / c + 1 / c) := by grind
  have e2 : q * (c * c) / (c * c) = q := by grind
  rw [e1, e2] at hlt
  exact hlt

/-! ## The root, rounded down -/

/-- The root rounded down is not negative. -/
theorem sqrtDown_nonneg (q : Rat) (places : Nat) : 0 ≤ sqrtDown q places := by
  rw [sqrtDown, Rat.div_def]
  exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr (ratTen_pow_pos places)))

/-- The root rounded down of a number that is not positive is zero. -/
theorem sqrtDown_of_nonpos {q : Rat} (h : q ≤ 0) (places : Nat) : sqrtDown q places = 0 := by
  have hs : q * (100 : Rat) ^ places ≤ 0 := by
    have hm := Rat.mul_le_mul_of_nonneg_right h
      (Rat.pow_nonneg (a := 100) (n := places) (by decide))
    rw [Rat.zero_mul] at hm
    exact hm
  have hf : (q * (100 : Rat) ^ places).floor ≤ 0 :=
    Rat.intCast_nonpos.mp (Rat.le_trans (Rat.floor_le _) hs)
  have h0 : Nat.sqrt 0 = 0 := by decide
  rw [sqrtDown, Int.toNat_of_nonpos hf, h0, Rat.div_def]
  exact Rat.zero_mul _

/-- **The root rounded down is no more than the root**: its square is no more than the
number, for a number that is not negative. -/
theorem sqrtDown_mul_self_le {q : Rat} (h : 0 ≤ q) (places : Nat) :
    sqrtDown q places * sqrtDown q places ≤ q := by
  have hs : (0 : Rat) ≤ q * (100 : Rat) ^ places :=
    Rat.mul_nonneg h (Rat.pow_nonneg (by decide))
  rw [sqrtDown]
  apply rat_div_mul_self_le (ratTen_pow_pos places)
  rw [← ratHundred_pow, ← Rat.natCast_mul]
  exact Rat.le_trans (Rat.natCast_le_natCast.mpr (Nat.sqrt_le _)) (rat_floor_toNat_le hs)

/-- **The root is less than one unit of the last place above the root rounded down**: the
square of that next number is more than the number. -/
theorem lt_sqrtDown_succ (q : Rat) (places : Nat) :
    q < (sqrtDown q places + 1 / (10 : Rat) ^ places) *
      (sqrtDown q places + 1 / (10 : Rat) ^ places) := by
  have h1 := rat_lt_floor_toNat_succ (q * (100 : Rat) ^ places)
  have h2 := Rat.natCast_le_natCast.mpr
    (Nat.succ_le_of_lt (Nat.lt_succ_sqrt (q * (100 : Rat) ^ places).floor.toNat))
  rw [Rat.natCast_mul, Nat.succ_eq_add_one, Rat.natCast_add, Rat.natCast_ofNat] at h2
  rw [sqrtDown]
  apply rat_lt_div_mul_self (ratTen_pow_pos places)
  rw [← ratHundred_pow]
  grind

/-- **The root rounded down is exact on a square**: of the square of a count of that many
places it is the count. -/
theorem sqrtDown_sq (k places : Nat) :
    sqrtDown (((k : Rat) / (10 : Rat) ^ places) * ((k : Rat) / (10 : Rat) ^ places)) places =
      (k : Rat) / (10 : Rat) ^ places := by
  have hne := ratTen_pow_ne places
  have e : (k : Rat) / (10 : Rat) ^ places * ((k : Rat) / (10 : Rat) ^ places) *
      (100 : Rat) ^ places = (((k * k : Nat) : Int) : Rat) := by
    rw [ratHundred_pow, Rat.intCast_natCast, Rat.natCast_mul]
    grind
  rw [sqrtDown, e, Rat.floor_intCast, Int.toNat_natCast, natSqrt_mul_self]

/-! ## Lengths -/

/-- The square of a length is not negative. -/
theorem Vec.normSq_nonneg (v : Vec) : 0 ≤ v.normSq := by
  simp only [Vec.normSq, Vec.dot]
  exact Rat.add_nonneg (rat_mul_self_nonneg v.x) (rat_mul_self_nonneg v.y)

/-- A length is not negative. -/
theorem Vec.norm_nonneg (v : Vec) (places : Nat) : 0 ≤ v.norm places :=
  sqrtDown_nonneg v.normSq places

/-- A length is rounded down: its square is no more than the square of the length. -/
theorem Vec.norm_mul_self_le (v : Vec) (places : Nat) : v.norm places * v.norm places ≤ v.normSq :=
  sqrtDown_mul_self_le v.normSq_nonneg places

/-- A quarter turn keeps the square of the length. -/
theorem Vec.normSq_perp (v : Vec) : v.perp.normSq = v.normSq := by
  simp only [Vec.normSq, Vec.dot, Vec.perp]
  grind

/-- A quarter turn keeps the length. -/
theorem Vec.norm_perp (v : Vec) (places : Nat) : v.perp.norm places = v.norm places := by
  simp only [Vec.norm, Vec.normSq_perp]

/-- Two points moved together are as far apart as they were. -/
theorem Vec.dist_move (d a b : Vec) (places : Nat) :
    (a + d).dist (b + d) places = a.dist b places := by
  have e : b + d - (a + d) = b - a := by
    apply Vec.ext <;> simp only [Vec.add_def, Vec.sub_def] <;> grind
  simp only [Vec.dist, e]

/-- The distance from one point to another is the distance back. -/
theorem Vec.dist_comm (a b : Vec) (places : Nat) : a.dist b places = b.dist a places := by
  have e : (b - a).normSq = (a - b).normSq := by
    simp only [Vec.normSq, Vec.dot, Vec.sub_def]
    grind
  simp only [Vec.dist, Vec.norm, e]

/-- A unit vector is no shorter than one, where the length does not round down to zero. -/
theorem Vec.one_le_normSq_unit (v : Vec) (places : Nat) (h : v.norm places ≠ 0) :
    1 ≤ (v.unit places).normSq := by
  have hpos : 0 < v.norm places := Rat.lt_of_le_of_ne (v.norm_nonneg places) (Ne.symm h)
  have hle := rat_div_le_div (Rat.mul_pos hpos hpos) (v.norm_mul_self_le places)
  have e1 : v.norm places * v.norm places / (v.norm places * v.norm places) = 1 := by grind
  have e2 : (v.unit places).normSq = v.normSq / (v.norm places * v.norm places) := by
    simp only [Vec.unit, if_neg h, Vec.normSq, Vec.dot, Vec.scale]
    grind
  rw [e1] at hle
  rw [e2]
  exact hle

/-- A unit vector is longer than one by less than the part that one unit of the last place is
of the rounded length. For a vector that is long against one unit of the last place that part
is small; for a short one it is not. -/
theorem Vec.normSq_unit_lt (v : Vec) (places : Nat) (h : v.norm places ≠ 0) :
    (v.unit places).normSq <
      (1 + 1 / ((10 : Rat) ^ places * v.norm places)) *
        (1 + 1 / ((10 : Rat) ^ places * v.norm places)) := by
  have hpos : 0 < v.norm places := Rat.lt_of_le_of_ne (v.norm_nonneg places) (Ne.symm h)
  have hc := ratTen_pow_ne places
  have hlt := rat_div_lt_div (Rat.mul_pos hpos hpos) (lt_sqrtDown_succ v.normSq places)
  have e2 : (v.unit places).normSq = v.normSq / (v.norm places * v.norm places) := by
    simp only [Vec.unit, if_neg h, Vec.normSq, Vec.dot, Vec.scale]
    grind
  have hn : sqrtDown v.normSq places = v.norm places := rfl
  rw [hn, ← e2] at hlt
  have e1 : (v.norm places + 1 / (10 : Rat) ^ places) * (v.norm places + 1 / (10 : Rat) ^ places) /
      (v.norm places * v.norm places) =
        (1 + 1 / ((10 : Rat) ^ places * v.norm places)) *
          (1 + 1 / ((10 : Rat) ^ places * v.norm places)) := by
    grind
  rw [e1] at hlt
  exact hlt

/-- A vector is at a right angle to its normal. -/
theorem Vec.dot_normal (v : Vec) (places : Nat) : v.dot (v.normal places) = 0 := by
  simp only [Vec.normal, Vec.unit]
  split
  · simp only [Vec.dot, Vec.zero]
    grind
  · simp only [Vec.dot, Vec.scale, Vec.perp]
    grind

/-! ## Beside a segment -/

/-- A segment sampled at `n` steps gives `n + 1` points. -/
theorem Cubic.length_samples (c : Cubic) (n : Nat) : (c.samples n).length = n + 1 := by
  simp only [Cubic.samples, List.length_map, List.length_range]

/-- The samples of a moved segment are the samples, moved. -/
theorem Cubic.samples_move (d : Vec) (c : Cubic) (n : Nat) :
    (c.move d).samples n = (c.samples n).map fun p => p + d := by
  simp only [Cubic.samples, List.map_map, Cubic.move_pointAt]
  rfl

/-- A moved segment has the normal of the segment. -/
theorem Cubic.normalAt_move (d : Vec) (c : Cubic) (t : Rat) (places : Nat) :
    (c.move d).normalAt t places = c.normalAt t places := by
  simp only [Cubic.normalAt, Cubic.move_direction]

/-- A point beside a moved segment is the point beside the segment, moved. -/
theorem Cubic.offsetAt_move (d : Vec) (c : Cubic) (t distance : Rat) (places : Nat) :
    (c.move d).offsetAt t distance places = c.offsetAt t distance places + d := by
  simp only [Cubic.offsetAt, Cubic.normalAt_move, Cubic.move_pointAt]
  apply Vec.ext <;> simp only [Vec.add_def] <;> grind

/-- A point no distance beside a segment is the point of the segment. -/
theorem Cubic.offsetAt_zero (c : Cubic) (t : Rat) (places : Nat) :
    c.offsetAt t 0 places = c.pointAt t := by
  apply Vec.ext <;> simp only [Cubic.offsetAt, Vec.add_def, Vec.scale_def] <;> grind

/-- A moved segment has the length through chords of the segment. -/
theorem Cubic.chordLength_move (d : Vec) (c : Cubic) (n places : Nat) :
    (c.move d).chordLength n places = c.chordLength n places := by
  simp only [Cubic.chordLength, Cubic.samples_move, ← List.map_tail, List.zip_map, List.foldl_map,
    Prod.map_fst, Prod.map_snd, Vec.dist_move]

end Whatwg.Svg.Value
