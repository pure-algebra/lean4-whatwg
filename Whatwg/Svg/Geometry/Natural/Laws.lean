import Whatwg.Svg.Geometry.Natural
import Whatwg.Svg.Geometry.Through
import Whatwg.Svg.Geometry.Smooth

/-!
# Whatwg.Svg.Geometry.Natural.Laws

Owner: the laws of the natural cubic spline, and the spline as a generator (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

d3-shape tests its `curveNatural` on five lists of points (`test/curve/natural-test.js`, commit
`a82254af78f0`) and states no law. Here the curve is exact, and the laws below are of every list
of points: none has a premise on the points.

- **The curve passes through its points** (`natural_starts`, `natural_ends`): its pieces start
  at every point but the last and end at every point but the first, in order. So it is a chain
  (`chained_natural`).
- **Nothing is divided by zero** (`pivots_rows`): the number each row is divided by is `2` or
  more. The first is `2`, and each other is `4` or `7` less a part of the row before that is no
  more than a half or than one.
- **A curve through moved points is the curve, moved** (`natural_move`). The rule reads every
  point, so this is a law of the system and not of four points in a row: the unknowns of the
  moved points are the unknowns, moved (`solve_shift`), since in each row the numbers on the
  left add up to the numbers on the right.
- **The curve has one velocity at every point** (`smooth_natural`): it is smooth in the sense
  of `Whatwg/Svg/Geometry/Smooth.lean`. The monotone curve is not.
- `Curve.Through.natural`: the curve as a generator of `Whatwg/Svg/Geometry/Through.lean`, by
  the laws above. It has a line, a pen and an area with no code of its own.

What this module does not claim: that the curve bends the same way on both sides of a point,
and does not bend at its two ends. Both hold, and they are what the rows of the system say of
its pieces; here the rows are solved, and that the solution satisfies them is not stated. That
the curve is the smoothest through its points is a statement about an integral, and belongs in
`analysis/`.
-/

namespace Whatwg.Svg.Value

namespace Natural

/-! ## The pieces pass through the points -/

/-- The pieces start at every point but the last, where there is a first control point for
each. -/
theorem pieces_starts : ∀ (ks ps : List Vec), ps.length + 1 = ks.length →
    (pieces ks ps).map (fun c => c.p0) = ks.dropLast
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | [_, _], [], h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | [_, _], [_], _ => rfl
  | [_, _], _ :: _ :: _, h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | _ :: _ :: _ :: _, [], h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | _ :: _ :: _ :: _, [_], h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | k0 :: k1 :: k2 :: ks, p :: q :: ps, h => by
    have ih := pieces_starts (k1 :: k2 :: ks) (q :: ps) (by
      simp only [List.length_cons] at h ⊢
      omega)
    show k0 :: (pieces (k1 :: k2 :: ks) (q :: ps)).map (fun c => c.p0) =
      k0 :: (k1 :: k2 :: ks).dropLast
    rw [ih]

/-- The pieces end at every point but the first, where there is a first control point for
each. -/
theorem pieces_ends : ∀ (ks ps : List Vec), ps.length + 1 = ks.length →
    (pieces ks ps).map (fun c => c.p3) = ks.tail
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | [_, _], [], h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | [_, _], [_], _ => rfl
  | [_, _], _ :: _ :: _, h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | _ :: _ :: _ :: _, [], h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | _ :: _ :: _ :: _, [_], h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | k0 :: k1 :: k2 :: ks, p :: q :: ps, h => by
    have ih := pieces_ends (k1 :: k2 :: ks) (q :: ps) (by
      simp only [List.length_cons] at h ⊢
      omega)
    show k1 :: (pieces (k1 :: k2 :: ks) (q :: ps)).map (fun c => c.p3) = k1 :: k2 :: ks
    rw [ih]
    rfl

/-- The system has one unknown more than rows after the first. -/
theorem length_solve : ∀ (rest : List (Rat × Rat × Vec)) (b : Rat) (r : Vec),
    (solve b r rest).length = rest.length + 1
  | [], _, _ => rfl
  | (a', b', r') :: rest, b, r =>
    congrArg (· + 1) (length_solve rest (b' - a' / b) (r' - Vec.scale (a' / b) r))

/-- There is a row after the first for each point but one. -/
theorem length_rows : ∀ ks : List Vec, (rows ks).length = ks.length - 1
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | k :: k' :: k'' :: rest => by
    have ih := length_rows (k' :: k'' :: rest)
    show (rows (k' :: k'' :: rest)).length + 1 = (k :: k' :: k'' :: rest).length - 1
    rw [ih]
    simp only [List.length_cons]
    omega

/-- Three points or more have a first control point for each piece. -/
theorem length_firsts (k0 k1 k2 : Vec) (rest : List Vec) :
    (firsts (k0 :: k1 :: k2 :: rest)).length + 1 = (k0 :: k1 :: k2 :: rest).length := by
  show (solve 2 (k0 + Vec.scale 2 k1) (rows (k1 :: k2 :: rest))).length + 1 = _
  rw [length_solve, length_rows]
  simp only [List.length_cons]
  omega

end Natural

namespace Curve

open Natural

/-- **The natural spline starts a piece at every point but the last**, in order. -/
theorem natural_starts : ∀ points : List Vec,
    (natural points).map (fun c => c.p0) = points.dropLast
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | k0 :: k1 :: k2 :: rest =>
    pieces_starts (k0 :: k1 :: k2 :: rest) _ (length_firsts k0 k1 k2 rest)

/-- **The natural spline ends a piece at every point but the first**, in order. -/
theorem natural_ends : ∀ points : List Vec, (natural points).map (fun c => c.p3) = points.tail
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | k0 :: k1 :: k2 :: rest =>
    pieces_ends (k0 :: k1 :: k2 :: rest) _ (length_firsts k0 k1 k2 rest)

/-- **The natural spline is a chain**: each piece starts where the one before it ends. -/
theorem chained_natural (points : List Vec) : Cubic.Chained (natural points) = true :=
  chained_of_passing _ points (natural_starts points) (natural_ends points)

end Curve

namespace Natural

/-! ## Nothing is divided by zero -/

/-- What stands before the unknown of the row after a row: `1` where a row follows, and `0`
where none does. -/
def over : List (Rat × Rat × Vec) → Rat
  | [] => 0
  | _ :: _ => 1

/-- **No row is divided by zero**: the number before the unknown of the row is not `0`, and so
for each row after it, once the row before has been taken out of it. -/
def Pivots (b : Rat) : List (Rat × Rat × Vec) → Prop
  | [] => b ≠ 0
  | (a', b', _) :: rest => b ≠ 0 ∧ Pivots (b' - a' / b) rest

/-- One over a number that is `2` or more is from `0` to a half. -/
theorem inv_bounds {b : Rat} (h : 2 ≤ b) : 0 ≤ 1 / b ∧ 1 / b ≤ 1 / 2 := by
  have hb : b ≠ 0 := by grind
  have e : b * (1 / b) = 1 := by grind
  generalize 1 / b = u at e ⊢
  have hu : 0 ≤ u := by
    by_cases hu : 0 ≤ u
    · exact hu
    · have p := Rat.mul_pos (show 0 < b by grind) (show 0 < -u by grind)
      grind
  have p := Rat.mul_nonneg (show 0 ≤ b - 2 by grind) hu
  constructor <;> grind

/-- **The rows of the natural spline are never divided by zero**, from a row whose number is
`2` or more on. The first row has `2`. -/
theorem pivots_rows : ∀ (ks : List Vec) (b : Rat), 2 ≤ b → Pivots b (rows ks)
  | [], b, h => show b ≠ 0 by grind
  | [_], b, h => show b ≠ 0 by grind
  | [_, _], b, h => by
    obtain ⟨u0, u1⟩ := inv_bounds h
    have e : (2 : Rat) / b = 2 * (1 / b) := by grind
    show b ≠ 0 ∧ (7 : Rat) - 2 / b ≠ 0
    constructor <;> grind
  | _ :: k' :: k'' :: rest, b, h => by
    obtain ⟨u0, u1⟩ := inv_bounds h
    show b ≠ 0 ∧ Pivots (4 - 1 / b) (rows (k' :: k'' :: rest))
    exact ⟨by grind, pivots_rows (k' :: k'' :: rest) (4 - 1 / b) (by grind)⟩

/-! ## Moved points -/

/-- The rows with each right side moved by `d` as many times as the numbers on its left add up
to. -/
def shifted (d : Vec) : List (Rat × Rat × Vec) → List (Rat × Rat × Vec)
  | [] => []
  | (a, b, r) :: rest => (a, b, r + Vec.scale (a + b + over rest) d) :: shifted d rest

/-- The system has an unknown. -/
theorem solve_cons (b : Rat) (r : Vec) (rest : List (Rat × Rat × Vec)) :
    ∃ x xs, solve b r rest = x :: xs := by
  cases rest with
  | nil => exact ⟨_, _, rfl⟩
  | cons row rest => exact ⟨_, _, rfl⟩

/-- **The unknowns of a moved system are the unknowns, moved.** Where each right side moves by
`d` as many times as the numbers on its left add up to, each unknown moves by `d`. -/
theorem solve_shift (d : Vec) : ∀ (rest : List (Rat × Rat × Vec)) (b : Rat) (r : Vec),
    Pivots b rest →
      solve b (r + Vec.scale (b + over rest) d) (shifted d rest) =
        (solve b r rest).map fun p => p + d
  | [], b, r, hb => by
    have hb' : b ≠ 0 := hb
    show [Vec.scale (1 / b) (r + Vec.scale (b + 0) d)] = [Vec.scale (1 / b) r + d]
    congr 1
    apply Vec.ext <;> simp only [Vec.scale, Vec.add_def] <;> grind
  | (a', b', r') :: rest, b, r, hp => by
    have hb : b ≠ 0 := hp.1
    have ih := solve_shift d rest (b' - a' / b) (r' - Vec.scale (a' / b) r) hp.2
    have e : r' + Vec.scale (a' + b' + over rest) d - Vec.scale (a' / b) (r + Vec.scale (b + 1) d) =
        r' - Vec.scale (a' / b) r + Vec.scale (b' - a' / b + over rest) d := by
      apply Vec.ext <;> simp only [Vec.scale, Vec.add_def, Vec.sub_def] <;> grind
    obtain ⟨h, t, ht⟩ := solve_cons (b' - a' / b) (r' - Vec.scale (a' / b) r) rest
    show back b (r + Vec.scale (b + 1) d)
        (solve (b' - a' / b)
          (r' + Vec.scale (a' + b' + over rest) d - Vec.scale (a' / b) (r + Vec.scale (b + 1) d))
          (shifted d rest)) =
      (back b r (solve (b' - a' / b) (r' - Vec.scale (a' / b) r) rest)).map fun p => p + d
    rw [e, ih, ht]
    show Vec.scale (1 / b) (r + Vec.scale (b + 1) d - (h + d)) :: (h + d) :: t.map (fun p => p + d) =
      (Vec.scale (1 / b) (r - h) + d) :: (h + d) :: t.map fun p => p + d
    congr 1
    apply Vec.ext <;> simp only [Vec.scale, Vec.add_def, Vec.sub_def] <;> grind

/-- Two points or more have a row after the first. -/
theorem over_rows (k k' : Vec) (rest : List Vec) : over (rows (k :: k' :: rest)) = 1 := by
  cases rest <;> rfl

/-- **The rows of moved points are the rows, each right side moved** as many times as the
numbers on its left add up to: six times in a row between two others, and nine in the last. -/
theorem rows_shift (d : Vec) : ∀ ks : List Vec,
    rows (ks.map fun p => p + d) = shifted d (rows ks)
  | [] => rfl
  | [_] => rfl
  | [k, kn] => by
    have e : Vec.scale 8 (k + d) + (kn + d) = Vec.scale 8 k + kn + Vec.scale (2 + 7 + 0) d := by
      apply Vec.ext <;> simp only [Vec.scale, Vec.add_def] <;> grind
    show [((2 : Rat), (7 : Rat), Vec.scale 8 (k + d) + (kn + d))] =
      [((2 : Rat), (7 : Rat), Vec.scale 8 k + kn + Vec.scale (2 + 7 + 0) d)]
    rw [e]
  | k :: k' :: k'' :: rest => by
    have ih := rows_shift d (k' :: k'' :: rest)
    have e : Vec.scale 4 (k + d) + Vec.scale 2 (k' + d) =
        Vec.scale 4 k + Vec.scale 2 k' +
          Vec.scale (1 + 4 + over (rows (k' :: k'' :: rest))) d := by
      rw [over_rows]
      apply Vec.ext <;> simp only [Vec.scale, Vec.add_def] <;> grind
    show ((1 : Rat), (4 : Rat), Vec.scale 4 (k + d) + Vec.scale 2 (k' + d)) ::
        rows ((k' :: k'' :: rest).map fun p => p + d) =
      ((1 : Rat), (4 : Rat), Vec.scale 4 k + Vec.scale 2 k' +
          Vec.scale (1 + 4 + over (rows (k' :: k'' :: rest))) d) ::
        shifted d (rows (k' :: k'' :: rest))
    rw [e, ih]

/-- **The first control points of moved points are the first control points, moved**, for three
points or more. -/
theorem firsts_move (d : Vec) (k0 k1 k2 : Vec) (rest : List Vec) :
    firsts ((k0 :: k1 :: k2 :: rest).map fun p => p + d) =
      (firsts (k0 :: k1 :: k2 :: rest)).map fun p => p + d := by
  have e : k0 + d + Vec.scale 2 (k1 + d) =
      k0 + Vec.scale 2 k1 + Vec.scale (2 + over (rows (k1 :: k2 :: rest))) d := by
    rw [over_rows]
    apply Vec.ext <;> simp only [Vec.scale, Vec.add_def] <;> grind
  show solve 2 (k0 + d + Vec.scale 2 (k1 + d)) (rows ((k1 :: k2 :: rest).map fun p => p + d)) = _
  rw [e, rows_shift]
  exact solve_shift d (rows (k1 :: k2 :: rest)) 2 (k0 + Vec.scale 2 k1)
    (pivots_rows _ 2 Rat.le_refl)

/-- The pieces through moved points with moved first control points are the pieces, moved. -/
theorem pieces_move (d : Vec) : ∀ (ks ps : List Vec),
    pieces (ks.map fun p => p + d) (ps.map fun p => p + d) = (pieces ks ps).map (Cubic.move d)
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], [] => rfl
  | [k0, k1], [p] => by
    have e : Vec.scale (1 / 2) (k1 + d + (p + d)) = Vec.scale (1 / 2) (k1 + p) + d := by
      apply Vec.ext <;> simp only [Vec.scale, Vec.add_def] <;> grind
    show [(⟨k0 + d, p + d, Vec.scale (1 / 2) (k1 + d + (p + d)), k1 + d⟩ : Cubic)] =
      [(⟨k0 + d, p + d, Vec.scale (1 / 2) (k1 + p) + d, k1 + d⟩ : Cubic)]
    rw [e]
  | [_, _], _ :: _ :: _ => rfl
  | _ :: _ :: _ :: _, [] => rfl
  | _ :: _ :: _ :: _, [_] => rfl
  | k0 :: k1 :: k2 :: ks, p :: q :: ps => by
    have ih := pieces_move d (k1 :: k2 :: ks) (q :: ps)
    have e : Vec.scale 2 (k1 + d) - (q + d) = Vec.scale 2 k1 - q + d := by
      apply Vec.ext <;> simp only [Vec.scale, Vec.add_def, Vec.sub_def] <;> grind
    show (⟨k0 + d, p + d, Vec.scale 2 (k1 + d) - (q + d), k1 + d⟩ : Cubic) ::
        pieces ((k1 :: k2 :: ks).map fun p => p + d) ((q :: ps).map fun p => p + d) =
      (⟨k0 + d, p + d, Vec.scale 2 k1 - q + d, k1 + d⟩ : Cubic) ::
        (pieces (k1 :: k2 :: ks) (q :: ps)).map (Cubic.move d)
    rw [e, ih]

/-! ## One velocity at every point -/

/-- A piece whose second control point mirrors the first control point of the next piece, in
the point between them, arrives with the velocity that the next leaves with. -/
theorem joint_velocity (k0 p k1 q x k2 : Vec) :
    (⟨k0, p, Vec.scale 2 k1 - q, k1⟩ : Cubic).velocity 1 = (⟨k1, q, x, k2⟩ : Cubic).velocity 0 := by
  rw [Cubic.velocity_one, Cubic.velocity_zero]
  apply Vec.ext <;> simp only [Vec.scale, Vec.sub_def] <;> grind

/-- The pieces have one velocity at every joint, whatever the first control points are. -/
theorem smooth_pieces : ∀ (ks ps : List Vec), Cubic.Smooth (pieces ks ps)
  | [], _ => trivial
  | [_], _ => trivial
  | [_, _], [] => trivial
  | [_, _], [_] => trivial
  | [_, _], _ :: _ :: _ => trivial
  | _ :: _ :: _ :: _, [] => trivial
  | _ :: _ :: _ :: _, [_] => trivial
  | [_, _, _], [_, _] => ⟨rfl, joint_velocity _ _ _ _ _ _, trivial⟩
  | [_, _, _], _ :: _ :: _ :: _ => trivial
  | _ :: _ :: _ :: _ :: _, [_, _] => trivial
  | _ :: k1 :: k2 :: k3 :: ks, _ :: q :: q' :: ps =>
    ⟨rfl, joint_velocity _ _ _ _ _ _, smooth_pieces (k1 :: k2 :: k3 :: ks) (q :: q' :: ps)⟩

end Natural

namespace Curve

open Natural

/-- **The natural spline through moved points is the spline, moved.** -/
theorem natural_move (d : Vec) : ∀ points : List Vec,
    natural (points.map fun p => p + d) = (natural points).map (Cubic.move d)
  | [] => rfl
  | [_] => rfl
  | [a, b] => list_one (Cubic.move_line d a b).symm
  | k0 :: k1 :: k2 :: rest => by
    show pieces ((k0 :: k1 :: k2 :: rest).map fun p => p + d)
        (firsts ((k0 :: k1 :: k2 :: rest).map fun p => p + d)) =
      (pieces (k0 :: k1 :: k2 :: rest) (firsts (k0 :: k1 :: k2 :: rest))).map (Cubic.move d)
    rw [firsts_move, pieces_move]

/-- **The natural spline has one velocity at every point**: it is smooth at each joint. -/
theorem smooth_natural : ∀ points : List Vec, Cubic.Smooth (natural points)
  | [] => trivial
  | [_] => trivial
  | [_, _] => trivial
  | k0 :: k1 :: k2 :: rest => smooth_pieces (k0 :: k1 :: k2 :: rest) _

/-- **The natural spline** as a generator: d3's `curveNatural`. -/
def Through.natural : Through where
  cubics := Curve.natural
  chained := chained_natural
  starts points c h := by
    have e := congrArg List.head? (natural_starts points)
    rw [List.head?_map, h] at e
    exact head?_of_dropLast e.symm
  ends points c h := by
    have e := congrArg List.getLast? (natural_ends points)
    rw [List.getLast?_map, h] at e
    exact getLast?_of_tail e.symm
  moved := natural_move

end Curve

end Whatwg.Svg.Value
