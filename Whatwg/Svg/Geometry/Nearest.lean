import Whatwg.Svg.Scene.Nearest
import Whatwg.Svg.Geometry.Easing

/-!
# Whatwg.Svg.Geometry.Nearest

Owner: what the nearest cubic of `Whatwg/Svg/Scene/Nearest.lean` is nearest to, in exact numbers
(slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Easing.nearestCubic` solves two equations in whole numbers and rounds each height once. This
module says, in the rational numbers of the kit, what those heights are.

- `Easing.cost rows h1 h2`: the sum, over the rows, of the square of what a row leaves at the
  heights `h1` and `h2`. `Easing.distance values h1 h2` is that sum over the rows of stops.
  `Easing.row_cost` says what a row leaves: `n³` times the distance, at the stop, between the
  cubic of those heights and the value of the stop, both in per mille. So the distance is `n⁶`
  times the sum of the squares of the distances between the cubic and the stops.
- `Easing.nearestExact values`: the two heights before they are rounded.
- **No heights are nearer** (`Easing.nearestExact_least`, `Easing.cost_least`): the distance at
  the exact heights is no more than at any two rational heights. The proof is of two
  polynomials. The distance is a quadratic in the two heights (`Easing.cost_eq`); the exact
  heights satisfy the two equations; and what is left over is a sum of squares
  (`Easing.form_nonneg`).
- **The whole-number answer is the exact answer, rounded** (`Easing.nearestCubic_eq_round`):
  each height is the exact height to the nearest whole number, a half going up
  (`Easing.roundDiv_eq_floor`).
- **Stops that stand on a cubic give the cubic back** (`Easing.nearestCubic_of_cubic`): where
  the value of every stop is the exact reading of the cubic of the whole heights `y1` and `y2`
  at that stop, the answer is `y1` and `y2`, with nothing rounded away.

What this module does not claim. Every law asks that `Sums.det` is more than `0`. It is for
four stops or more, which a program checks of its own number of stops by evaluation; that it is
so for every such number is not proved here. The stops of a cubic of the kit are its readings
rounded down (`Easing.values`), and they do not stand on the cubic: what comes back from them
is within one per mille of the heights for the named easings, by the evaluations of
`WhatwgTest/Svg/Nearest.lean`, and no law here bounds it. Such a law would say that the
heights move by a bounded multiple of how far the stops move, which is true and linear, and
whose bound depends on the number of stops.

Every law here depends on `propext`, `Quot.sound` and `Classical.choice` at most.
-/

namespace Whatwg.Svg.Scene

namespace Easing

open Whatwg.Svg.Value

/-! ## The distance is a quadratic in the two heights -/

/-- **The sum of the squares of what the rows leave** at the heights `h1` and `h2`: for a row
of the two terms `b1` and `b2` that leaves `r`, the square of `h1 b1 + h2 b2 - r`. -/
def cost : List (Int × Int × Int) → Rat → Rat → Rat
  | [], _, _ => 0
  | row :: rest, h1, h2 =>
    (h1 * (row.1 : Rat) + h2 * (row.2.1 : Rat) - (row.2.2 : Rat)) *
        (h1 * (row.1 : Rat) + h2 * (row.2.1 : Rat) - (row.2.2 : Rat)) +
      cost rest h1 h2

/-- The sum of the squares of what the rows leave with no heights: the part of the cost that
the heights do not change. -/
def spare : List (Int × Int × Int) → Rat
  | [] => 0
  | row :: rest => (row.2.2 : Rat) * (row.2.2 : Rat) + spare rest

/-- **The cost is a quadratic in the two heights**, whose numbers are the five sums. -/
theorem cost_eq : ∀ (rows : List (Int × Int × Int)) (h1 h2 : Rat),
    cost rows h1 h2 =
      ((Sums.of rows).a11 : Rat) * h1 * h1 + 2 * ((Sums.of rows).a12 : Rat) * h1 * h2 +
        ((Sums.of rows).a22 : Rat) * h2 * h2 - 2 * ((Sums.of rows).r1 : Rat) * h1 -
          2 * ((Sums.of rows).r2 : Rat) * h2 + spare rows
  | [], h1, h2 => by
    simp only [cost, Sums.of, spare, Rat.intCast_zero]
    grind
  | row :: rest, h1, h2 => by
    have ih := cost_eq rest h1 h2
    simp only [cost, Sums.of, spare, Rat.intCast_add, Rat.intCast_mul]
    grind

/-- **The quadratic part of the cost is never negative**: it is the sum, over the rows, of the
square of `u b1 + v b2`. -/
theorem form_nonneg : ∀ (rows : List (Int × Int × Int)) (u v : Rat),
    0 ≤ ((Sums.of rows).a11 : Rat) * u * u + 2 * ((Sums.of rows).a12 : Rat) * u * v +
      ((Sums.of rows).a22 : Rat) * v * v
  | [], u, v => by
    simp only [Sums.of, Rat.intCast_zero]
    grind
  | row :: rest, u, v => by
    have ih := form_nonneg rest u v
    have sq := rat_mul_self_nonneg (u * (row.1 : Rat) + v * (row.2.1 : Rat))
    simp only [Sums.of, Rat.intCast_add, Rat.intCast_mul]
    grind

/-- **No two heights cost less than the solution of the two equations.** With `det` more than
`0`, the cost at `num1 / det` and `num2 / det` is no more than the cost at any two rational
heights. -/
theorem cost_least (rows : List (Int × Int × Int)) (hd : 0 < (Sums.of rows).det) (h1 h2 : Rat) :
    cost rows (((Sums.of rows).num1 : Rat) / ((Sums.of rows).det : Rat))
        (((Sums.of rows).num2 : Rat) / ((Sums.of rows).det : Rat)) ≤ cost rows h1 h2 := by
  have hD : (0 : Rat) < ((Sums.of rows).det : Rat) := Rat.intCast_pos.mpr hd
  have f := form_nonneg rows
    (h1 - ((Sums.of rows).num1 : Rat) / ((Sums.of rows).det : Rat))
    (h2 - ((Sums.of rows).num2 : Rat) / ((Sums.of rows).det : Rat))
  rw [cost_eq, cost_eq]
  simp only [Sums.det, Sums.num1, Sums.num2, Rat.intCast_sub, Rat.intCast_mul] at hD f ⊢
  generalize ((Sums.of rows).a11 : Rat) = a11 at hD f ⊢
  generalize ((Sums.of rows).a12 : Rat) = a12 at hD f ⊢
  generalize ((Sums.of rows).a22 : Rat) = a22 at hD f ⊢
  generalize ((Sums.of rows).r1 : Rat) = r1 at hD f ⊢
  generalize ((Sums.of rows).r2 : Rat) = r2 at hD f ⊢
  have hne : a11 * a22 - a12 * a12 ≠ 0 := Rat.ne_of_gt hD
  have e1 : a11 * ((r1 * a22 - r2 * a12) / (a11 * a22 - a12 * a12)) +
      a12 * ((a11 * r2 - a12 * r1) / (a11 * a22 - a12 * a12)) = r1 := by grind
  have e2 : a12 * ((r1 * a22 - r2 * a12) / (a11 * a22 - a12 * a12)) +
      a22 * ((a11 * r2 - a12 * r1) / (a11 * a22 - a12 * a12)) = r2 := by grind
  generalize (r1 * a22 - r2 * a12) / (a11 * a22 - a12 * a12) = s1 at e1 e2 f ⊢
  generalize (a11 * r2 - a12 * r1) / (a11 * a22 - a12 * a12) = s2 at e1 e2 f ⊢
  subst e1 e2
  grind

/-! ## The exact heights -/

/-- **The two heights of the cubic nearest to stops, before they are rounded**, in per mille:
the solution of the two equations. -/
def nearestExact (values : List Int) : Rat × Rat :=
  (((Sums.of (nearestRows values)).num1 : Rat) / ((Sums.of (nearestRows values)).det : Rat),
    ((Sums.of (nearestRows values)).num2 : Rat) / ((Sums.of (nearestRows values)).det : Rat))

/-- **How far the cubic of two heights is from stops**: the sum over the stops of the square of
what each row leaves. It is `n⁶` times the sum of the squares of the distances between the
cubic and the stops, in per mille, with `n` the number of pieces (`row_cost`). -/
def distance (values : List Int) (h1 h2 : Rat) : Rat := cost (nearestRows values) h1 h2

/-- **What a row leaves is the distance between the cubic and the stop**, times `n³`. At the
heights `h1` and `h2` in per mille, the row of the stop `i` of `n` pieces with the value `v`
leaves `n³` times what the cubic of those heights reads at `i / n`, in per mille, less `v`. -/
theorem row_cost {pieces : Nat} (hp : 0 < pieces) (i : Nat) (v : Int) (h1 h2 : Rat) :
    h1 * ((nearestRow pieces i v).1 : Rat) + h2 * ((nearestRow pieces i v).2.1 : Rat) -
        ((nearestRow pieces i v).2.2 : Rat) =
      (pieces : Rat) ^ 3 *
        (3 * h1 * ((i : Rat) / (pieces : Rat)) * (1 - (i : Rat) / (pieces : Rat)) *
            (1 - (i : Rat) / (pieces : Rat)) +
          3 * h2 * ((i : Rat) / (pieces : Rat)) * ((i : Rat) / (pieces : Rat)) *
            (1 - (i : Rat) / (pieces : Rat)) +
          1000 * ((i : Rat) / (pieces : Rat) * ((i : Rat) / (pieces : Rat)) *
            ((i : Rat) / (pieces : Rat))) - (v : Rat)) := by
  have hn : (pieces : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hp)
  simp only [nearestRow, Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_pow, Rat.intCast_ofNat,
    Rat.intCast_natCast]
  generalize (i : Rat) = k
  generalize (pieces : Rat) = n at hn ⊢
  grind

/-- **At whole heights, what a row leaves is `n³` times the reading of the cubic easing less
the value of the stop**, in per mille. -/
theorem row_cost_cubic {pieces : Nat} (hp : 0 < pieces) (i : Nat) (v y1 y2 : Int) :
    (y1 : Rat) * ((nearestRow pieces i v).1 : Rat) + (y2 : Rat) * ((nearestRow pieces i v).2.1 : Rat) -
        ((nearestRow pieces i v).2.2 : Rat) =
      (pieces : Rat) ^ 3 * (1000 * cubicExact y1 y2 ((i : Rat) / (pieces : Rat)) - (v : Rat)) := by
  rw [row_cost hp]
  simp only [cubicExact]
  grind

/-- **No two rational heights are nearer the stops than the exact heights**, where `det` is
more than `0`. -/
theorem nearestExact_least (values : List Int) (hd : 0 < (Sums.of (nearestRows values)).det)
    (h1 h2 : Rat) :
    distance values (nearestExact values).1 (nearestExact values).2 ≤ distance values h1 h2 :=
  cost_least (nearestRows values) hd h1 h2

/-! ## The whole-number answer -/

/-- **The quotient to the nearest whole number is the floor of the exact quotient and a
half**, for a divisor that is more than zero. -/
theorem roundDiv_eq_floor (a : Int) {b : Int} (hb : 0 < b) :
    roundDiv a b = ((a : Rat) / (b : Rat) + 1 / 2).floor := by
  have hB : (b : Rat) ≠ 0 := Rat.ne_of_gt (Rat.intCast_pos.mpr hb)
  have e : (a : Rat) / (b : Rat) + 1 / 2 = ((2 * a + b : Int) : Rat) / ((2 * b : Int) : Rat) := by
    simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_ofNat]
    generalize (a : Rat) = A
    generalize (b : Rat) = B at hB ⊢
    grind
  rw [e, rat_floor_intCast_div _ (show (0 : Int) < 2 * b by omega)]
  rfl

/-- **The whole-number heights are the exact heights, each rounded to the nearest whole
number**, a half going up. -/
theorem nearestCubic_eq_round (values : List Int)
    (hd : 0 < (Sums.of (nearestRows values)).det) :
    nearestCubic values =
      (((nearestExact values).1 + 1 / 2).floor, ((nearestExact values).2 + 1 / 2).floor) := by
  show (roundDiv _ _, roundDiv _ _) = _
  rw [roundDiv_eq_floor _ hd, roundDiv_eq_floor _ hd]
  rfl

/-! ## Stops that stand on a cubic -/

/-- Where every row leaves what the whole heights `y1` and `y2` make of its two terms, the two
sums of what the rows leave are what `y1` and `y2` make of the three other sums. -/
theorem sums_of_on : ∀ (rows : List (Int × Int × Int)) (y1 y2 : Int),
    (∀ row ∈ rows, row.2.2 = y1 * row.1 + y2 * row.2.1) →
      (Sums.of rows).r1 = y1 * (Sums.of rows).a11 + y2 * (Sums.of rows).a12 ∧
        (Sums.of rows).r2 = y1 * (Sums.of rows).a12 + y2 * (Sums.of rows).a22
  | [], _, _, _ => by
    simp only [Sums.of]
    constructor <;> grind
  | row :: rest, y1, y2, h => by
    obtain ⟨i1, i2⟩ := sums_of_on rest y1 y2 fun r hr => h r (List.mem_cons_of_mem _ hr)
    have hr := h row List.mem_cons_self
    simp only [Sums.of]
    constructor <;> grind

/-- Rows that the whole heights `y1` and `y2` satisfy give those heights back. -/
theorem nearestCubic_of_rows (values : List Int) (y1 y2 : Int)
    (hd : 0 < (Sums.of (nearestRows values)).det)
    (h : ∀ row ∈ nearestRows values, row.2.2 = y1 * row.1 + y2 * row.2.1) :
    nearestCubic values = (y1, y2) := by
  obtain ⟨e1, e2⟩ := sums_of_on _ y1 y2 h
  have n1 : (Sums.of (nearestRows values)).num1 = y1 * (Sums.of (nearestRows values)).det := by
    simp only [Sums.num1, Sums.det]
    grind
  have n2 : (Sums.of (nearestRows values)).num2 = y2 * (Sums.of (nearestRows values)).det := by
    simp only [Sums.num2, Sums.det]
    grind
  show (roundDiv (Sums.of (nearestRows values)).num1 (Sums.of (nearestRows values)).det,
    roundDiv (Sums.of (nearestRows values)).num2 (Sums.of (nearestRows values)).det) = (y1, y2)
  rw [n1, n2, roundDiv_mul y1 hd, roundDiv_mul y2 hd]

/-- **Stops that stand on a cubic give the cubic back.** Where the value of every stop is the
exact reading, in per mille, of the cubic of the whole heights `y1` and `y2` at that stop, the
nearest cubic is that cubic: nothing is rounded away. There are two stops or more, and `det` is
more than `0`. -/
theorem nearestCubic_of_cubic (values : List Int) (y1 y2 : Int) (hp : 1 < values.length)
    (hd : 0 < (Sums.of (nearestRows values)).det)
    (h : ∀ vi ∈ values.zipIdx, (vi.1 : Rat) =
      1000 * cubicExact y1 y2 ((vi.2 : Rat) / ((values.length - 1 : Nat) : Rat))) :
    nearestCubic values = (y1, y2) := by
  refine nearestCubic_of_rows values y1 y2 hd fun row hrow => ?_
  obtain ⟨vi, hvi, rfl⟩ := List.mem_map.mp hrow
  have hv := h vi hvi
  have hpos : 0 < values.length - 1 := by omega
  have e := row_cost_cubic hpos vi.2 vi.1 y1 y2
  rw [hv] at e
  have e' : ((nearestRow (values.length - 1) vi.2 vi.1).2.2 : Rat) =
      ((y1 * (nearestRow (values.length - 1) vi.2 vi.1).1 +
        y2 * (nearestRow (values.length - 1) vi.2 vi.1).2.1 : Int) : Rat) := by
    simp only [Rat.intCast_add, Rat.intCast_mul]
    grind
  exact Rat.intCast_inj.mp e'

end Easing

end Whatwg.Svg.Scene
