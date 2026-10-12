/-!
# Whatwg.Svg.Geometry.Vec

Owner: a point of the plane with exact rational coordinates (slice S11 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-50). The typed values of `Whatwg/Svg/Value/` are
spellings: a `Decimal` keeps the digits it was written with, has no quotient, and `1.0` and `1`
are two values. Geometry needs the numbers and not the spellings, and it divides: a third of a
chord, a sixth of a difference, the middle of two points.

So the geometry of this package computes in `Rat`, the rational numbers of Lean's core
library. Every operation is exact, an equation between two computations is an equation of
values, and core's `grind` proves the algebra. A number is rounded where it is written into a
typed value (`Vec.round` of `Whatwg/Svg/Geometry/Rational.lean`), and where a square root is
taken (`Whatwg/Svg/Geometry/Root.lean`), each to a stated number of places, and nowhere else.

`Vec` is a point, and also the difference of two points. What is here: the sum, the
difference, the opposite, a multiple (`k • v`), the step between two points (`lerp`), the
middle, the two products (`dot`, `cross`), a quarter turn (`perp`), and the distance along the
axes (`taxi`).

What this module does not claim: a length or a unit vector, which take a square root; an
angle.
-/

namespace Whatwg.Svg.Value

/-- The square of a rational number is not negative. -/
theorem rat_mul_self_nonneg (a : Rat) : 0 ≤ a * a := by
  cases Rat.le_total (a := 0) (b := a) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hn : 0 ≤ -a := by grind
    have e : a * a = -a * -a := by grind
    rw [e]
    exact Rat.mul_nonneg hn hn
/-- A point of the plane, or the difference of two points, with rational coordinates. -/
structure Vec where
  x : Rat
  y : Rat
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Vec

/-- The origin. -/
def zero : Vec := ⟨0, 0⟩

/-- The sum, coordinate by coordinate. -/
instance : Add Vec := ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩

/-- The difference, coordinate by coordinate. -/
instance : Sub Vec := ⟨fun p q => ⟨p.x - q.x, p.y - q.y⟩⟩

/-- The opposite. -/
instance : Neg Vec := ⟨fun p => ⟨-p.x, -p.y⟩⟩

/-- The point with each coordinate multiplied by `k`. -/
def scale (k : Rat) (p : Vec) : Vec := ⟨k * p.x, k * p.y⟩

/-- A multiple of a point: `k • p`. -/
instance : SMul Rat Vec := ⟨scale⟩

/-- The point `t` of the way from `a` to `b`: `a` at `0`, `b` at `1`, and beyond them for a `t`
outside. -/
def lerp (a b : Vec) (t : Rat) : Vec := ⟨a.x + t * (b.x - a.x), a.y + t * (b.y - a.y)⟩

/-- The point half way between two points. -/
def mid (a b : Vec) : Vec := ⟨(a.x + b.x) / 2, (a.y + b.y) / 2⟩

/-- The scalar product. -/
def dot (a b : Vec) : Rat := a.x * b.x + a.y * b.y

/-- The cross product: zero when the two point along one line. -/
def cross (a b : Vec) : Rat := a.x * b.y - a.y * b.x

/-- The same length, a quarter turn on: `(x, y)` becomes `(-y, x)`. On a screen, where `y`
grows downwards, the turn is clockwise: `perp` of a direction of travel points to its right. -/
def perp (a : Vec) : Vec := ⟨-a.y, a.x⟩

/-- The square of the length. -/
def normSq (a : Vec) : Rat := a.dot a

/-- The distance between two points along the axes. -/
def taxi (a b : Vec) : Rat := max (a.x - b.x) (b.x - a.x) + max (a.y - b.y) (b.y - a.y)

/-- A point of whole units. -/
def ofInts (x y : Int) : Vec := ⟨x, y⟩

/-- A point of a pair of whole units. -/
def ofPair (p : Int × Int) : Vec := ⟨p.1, p.2⟩

/-- A point whose coordinates are counts of `10 ^ -places`: `fixed 3 1500 250` is
`(3/2, 1/4)`. A program that counts in thousandths enters the geometry so. -/
def fixed (places : Nat) (x y : Int) : Vec := ⟨x / (10 : Rat) ^ places, y / (10 : Rat) ^ places⟩

/-! ## The algebra

Each is an equation of values, which `grind` reads as an equation of two rational
coordinates. -/

theorem ext {p q : Vec} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p
  cases q
  cases hx
  cases hy
  rfl

theorem add_def (p q : Vec) : p + q = ⟨p.x + q.x, p.y + q.y⟩ := rfl
theorem sub_def (p q : Vec) : p - q = ⟨p.x - q.x, p.y - q.y⟩ := rfl
theorem neg_def (p : Vec) : -p = ⟨-p.x, -p.y⟩ := rfl
theorem smul_def (k : Rat) (p : Vec) : k • p = ⟨k * p.x, k * p.y⟩ := rfl
theorem scale_def (k : Rat) (p : Vec) : scale k p = ⟨k * p.x, k * p.y⟩ := rfl

theorem add_comm (p q : Vec) : p + q = q + p := ext (Rat.add_comm _ _) (Rat.add_comm _ _)

theorem add_assoc (p q r : Vec) : p + q + r = p + (q + r) :=
  ext (Rat.add_assoc _ _ _) (Rat.add_assoc _ _ _)

theorem add_zero (p : Vec) : p + zero = p := ext (Rat.add_zero _) (Rat.add_zero _)

theorem zero_add (p : Vec) : zero + p = p := ext (Rat.zero_add _) (Rat.zero_add _)

theorem add_sub_cancel (p q : Vec) : p + q - q = p := by
  apply ext <;> simp only [add_def, sub_def] <;> grind

theorem sub_add_cancel (p q : Vec) : p - q + q = p := by
  apply ext <;> simp only [add_def, sub_def] <;> grind

theorem sub_self (p : Vec) : p - p = zero := by
  apply ext <;> simp only [sub_def, zero] <;> grind

theorem neg_add_cancel (p : Vec) : -p + p = zero := by
  apply ext <;> simp only [add_def, neg_def, zero] <;> grind

theorem add_right_comm (p q r : Vec) : p + q + r = p + r + q := by
  apply ext <;> simp only [add_def] <;> grind

/-- The distance along the axes between two points moved together is their distance. -/
theorem taxi_move (d a b : Vec) : (a + d).taxi (b + d) = a.taxi b := by
  simp only [taxi, add_def]
  grind

theorem lerp_zero (a b : Vec) : a.lerp b 0 = a := by
  apply ext <;> simp only [lerp] <;> grind

theorem lerp_one (a b : Vec) : a.lerp b 1 = b := by
  apply ext <;> simp only [lerp] <;> grind

theorem lerp_self (a : Vec) (t : Rat) : a.lerp a t = a := by
  apply ext <;> simp only [lerp] <;> grind

/-- A step the other way round: `t` from `a` to `b` is `1 - t` from `b` to `a`. -/
theorem lerp_swap (a b : Vec) (t : Rat) : a.lerp b t = b.lerp a (1 - t) := by
  apply ext <;> simp only [lerp] <;> grind

/-- A step between two moved points is the step, moved. -/
theorem lerp_add (a b d : Vec) (t : Rat) : (a + d).lerp (b + d) t = a.lerp b t + d := by
  apply ext <;> simp only [lerp, add_def] <;> grind

/-- A step between two scaled points is the step, scaled. -/
theorem lerp_scale (k : Rat) (a b : Vec) (t : Rat) :
    (scale k a).lerp (scale k b) t = scale k (a.lerp b t) := by
  apply ext <;> simp only [lerp, scale] <;> grind

/-- A step of a step: `s` of the way to the point `t` of the way is `s * t` of the way. -/
theorem lerp_lerp (a b : Vec) (s t : Rat) : a.lerp (a.lerp b t) s = a.lerp b (s * t) := by
  apply ext <;> simp only [lerp] <;> grind

theorem mid_eq_lerp (a b : Vec) : a.mid b = a.lerp b (1 / 2) := by
  apply ext <;> simp only [mid, lerp] <;> grind

theorem mid_comm (a b : Vec) : a.mid b = b.mid a := by
  apply ext <;> simp only [mid] <;> grind

/-- A quarter turn twice is the opposite. -/
theorem perp_perp (a : Vec) : a.perp.perp = -a := by
  apply ext <;> simp only [perp, neg_def] <;> grind

/-- A quarter turn of a vector is at a right angle to it. -/
theorem dot_perp (a : Vec) : a.dot a.perp = 0 := by
  simp only [dot, perp]
  grind

/-- A count of whole units is the point of those units. -/
theorem fixed_zero (x y : Int) : fixed 0 x y = ofInts x y := by
  apply ext <;> simp only [fixed, ofInts] <;> grind

end Vec

end Whatwg.Svg.Value
