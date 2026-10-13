import Whatwg.Svg.Geometry.Monotone
import Whatwg.Svg.Geometry.Box
import Whatwg.Svg.Geometry.Cubic.Laws

/-!
# Whatwg.Svg.Geometry.Monotone.Laws

Owner: what the monotone curve keeps (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

d3-shape names its curve "monotone" and tests one vector under the words "preserves
monotonicity in y" (`test/curve/monotoneX-test.js`, commit `a82254af78f0`). No law is stated
there. Here the curve is exact, and the laws below are of every list of points: none has a
premise on the points.

- **The curve passes through its points** (`monotoneX_starts`, `monotoneX_ends`): its pieces
  start at every point but the last and end at every point but the first, in order, where a
  point that is the one before it again counts once. It is a chain (`chained_monotoneX`), and
  the two ends of each piece are a point and a later one (`monotoneX_related`).
- **Its abscissa runs evenly** (`monotoneX_x`): on each piece the abscissa at the parameter `s`
  is `s` of the way from the piece's start to its end. So where the abscissae of the points
  never go back the curve is the graph of a function, and a reader finds the piece of an
  abscissa by its two ends.
- **It does not overshoot** (`monotoneX_within`): no piece leaves the box of its own two
  points. A cardinal spline does, and the control of `WhatwgTest/Svg/Monotone.lean` shows one.
  So the curve never leaves the range of its data (`monotoneX_range`): a curve through values
  that are never negative is never negative, and one through shares of a whole never passes
  the whole.
- **A curve through moved points is the curve, moved** (`monotoneX_move`), as for every other
  curve of the kit: no slope reads where the points stand.
- **Rising data give a rising curve** (`monotoneX_rises`): on a piece whose end is no lower
  than its start, a later parameter is no lower. With `monotoneX_x` the curve is then a
  function of `x` that never falls where the data never fall.

How the proof goes. `Tame h d t` says of a slope `t` at an end of a piece that runs across by
`h` and rises by `d`: `h * t` lies between `0` and `3 * d`. Then the control point a third of
the way across lies between the two ends in height (`segment_within`), and the box of four
points holds the piece (`Cubic.contains_pointAt_of`). `slope3` is tame for both pieces that meet
at its point (`slope3_tame`): it is `0` where the two chords go opposite ways and no more than
twice either chord, which is Steffen's bound, and each of d3's readings of an upright chord is
within it. `slope2` of a tame slope is tame (`slope2_tame`). The rise of a piece between two
parameters is their difference times a sum of three products (`segment_rise`), and for a tame
piece that sum is shared among four products of numbers that are not negative (`rise_nonneg`).
`Fits c` is what the two laws ask of a piece, and every piece of the curve fits
(`monotoneX_fits`).

What this module does not claim: that a piece whose end is lower than its start never rises,
which holds by the mirror image and is not stated; that the curve is smooth at a joint in the
sense of `Whatwg/Svg/Geometry/Smooth.lean`, since two pieces of different widths meet with one
slope and two speeds; laws of `monotoneY` beyond its definition, which exchanges the axes; the
same at every real parameter, which is a statement about real numbers and belongs in
`analysis/`.
-/
namespace Whatwg.Svg.Value

namespace Monotone

/-! ## The points of the curve -/

/-- The pieces from a point start with the piece from that point. -/
theorem pieces_cons (p0 : Vec) (t0 : Rat) (p1 : Vec) (rest : List Vec) :
    ∃ t1 tail, pieces p0 t0 p1 rest = segment p0 p1 t0 t1 :: tail := by
  cases rest with
  | nil => exact ⟨_, _, rfl⟩
  | cons p2 rest => exact ⟨_, _, rfl⟩

/-- The pieces start at every point but the last, in order. -/
theorem pieces_starts : ∀ (rest : List Vec) (p0 : Vec) (t0 : Rat) (p1 : Vec),
    (pieces p0 t0 p1 rest).map (fun c => c.p0) = (p0 :: p1 :: rest).dropLast
  | [], _, _, _ => rfl
  | p2 :: rest, p0, _, p1 => congrArg (List.cons p0) (pieces_starts rest p1 _ p2)

/-- The pieces end at every point but the first, in order. -/
theorem pieces_ends : ∀ (rest : List Vec) (p0 : Vec) (t0 : Rat) (p1 : Vec),
    (pieces p0 t0 p1 rest).map (fun c => c.p3) = p1 :: rest
  | [], _, _, _ => rfl
  | p2 :: rest, _, _, p1 => congrArg (List.cons p1) (pieces_ends rest p1 _ p2)

/-- The pieces are a chain. -/
theorem chained_pieces : ∀ (rest : List Vec) (p0 : Vec) (t0 : Rat) (p1 : Vec),
    Cubic.Chained (pieces p0 t0 p1 rest) = true
  | [], _, _, _ => rfl
  | p2 :: rest, p0, t0, p1 => by
    have ih := chained_pieces rest p1 (slope3 p0 p1 p2) p2
    obtain ⟨t1, tail, e⟩ := pieces_cons p1 (slope3 p0 p1 p2) p2 rest
    show Cubic.Chained
      (segment p0 p1 t0 (slope3 p0 p1 p2) :: pieces p1 (slope3 p0 p1 p2) p2 rest) = true
    rw [e] at ih ⊢
    rw [Cubic.chained_cons, ih]
    exact (Bool.and_true _).trans (decide_eq_true rfl)

/-- Every piece is a `segment` between two points. -/
theorem pieces_segment : ∀ (rest : List Vec) (p0 : Vec) (t0 : Rat) (p1 : Vec),
    ∀ c ∈ pieces p0 t0 p1 rest, ∃ a b u v, c = segment a b u v
  | [], p0, t0, p1, c, hc => by
    cases List.mem_singleton.mp hc
    exact ⟨_, _, _, _, rfl⟩
  | p2 :: rest, p0, t0, p1, c, hc => by
    rcases List.mem_cons.mp hc with rfl | h
    · exact ⟨_, _, _, _, rfl⟩
    · exact pieces_segment rest p1 _ p2 c h

/-- **The two ends of a piece are a point and a later point.** A relation that holds of every
point and every later one holds of the two ends of each piece. -/
theorem pieces_related (R : Vec → Vec → Prop) : ∀ (rest : List Vec) (p0 : Vec) (t0 : Rat)
    (p1 : Vec), (p0 :: p1 :: rest).Pairwise R → ∀ c ∈ pieces p0 t0 p1 rest, R c.p0 c.p3
  | [], p0, t0, p1, hp, c, hc => by
    cases List.mem_singleton.mp hc
    exact (List.pairwise_cons.mp hp).1 p1 List.mem_cons_self
  | p2 :: rest, p0, t0, p1, hp, c, hc => by
    rcases List.mem_cons.mp hc with rfl | h
    · exact (List.pairwise_cons.mp hp).1 p1 List.mem_cons_self
    · exact pieces_related R rest p1 _ p2 (List.pairwise_cons.mp hp).2 c h

/-- The points with no repeat are among the points, in their order. -/
theorem distinct_sublist : ∀ l : List Vec, (distinct l).Sublist l
  | [] => List.Sublist.refl _
  | [_] => List.Sublist.refl _
  | a :: b :: rest => by
    show (if a = b then distinct (b :: rest) else a :: distinct (b :: rest)).Sublist
      (a :: b :: rest)
    split
    · exact (distinct_sublist (b :: rest)).cons a
    · exact (distinct_sublist (b :: rest)).cons_cons a

end Monotone

namespace Curve

open Monotone

/-- **The monotone curve starts a piece at every point but the last**, in order, where a point
that is the one before it again counts once. -/
theorem monotoneX_starts (points : List Vec) :
    (monotoneX points).map (fun c => c.p0) = (distinct points).dropLast := by
  unfold monotoneX
  generalize distinct points = ps
  match ps with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: rest => exact pieces_starts (c :: rest) a _ b

/-- **The monotone curve ends a piece at every point but the first**, in order. -/
theorem monotoneX_ends (points : List Vec) :
    (monotoneX points).map (fun c => c.p3) = (distinct points).tail := by
  unfold monotoneX
  generalize distinct points = ps
  match ps with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: rest => exact pieces_ends (c :: rest) a _ b

/-- **The monotone curve is a chain**: each piece starts where the one before it ends. -/
theorem chained_monotoneX (points : List Vec) : Cubic.Chained (monotoneX points) = true := by
  unfold monotoneX
  generalize distinct points = ps
  match ps with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: rest => exact chained_pieces (c :: rest) a _ b

/-- The two ends of a piece of the monotone curve are two of the points. -/
theorem mem_of_mem_monotoneX {points : List Vec} {c : Cubic} (hc : c ∈ monotoneX points) :
    c.p0 ∈ points ∧ c.p3 ∈ points := by
  have h0 : c.p0 ∈ (monotoneX points).map (fun c => c.p0) := List.mem_map_of_mem hc
  have h3 : c.p3 ∈ (monotoneX points).map (fun c => c.p3) := List.mem_map_of_mem hc
  rw [monotoneX_starts] at h0
  rw [monotoneX_ends] at h3
  exact ⟨(distinct_sublist points).subset ((List.dropLast_sublist _).subset h0),
    (distinct_sublist points).subset (List.mem_of_mem_tail h3)⟩

/-- **The two ends of a piece are a point and a later point**: a relation that holds of every
point and every later one holds of the two ends of each piece of the curve. -/
theorem monotoneX_related (R : Vec → Vec → Prop) (points : List Vec) (h : points.Pairwise R)
    {c : Cubic} (hc : c ∈ monotoneX points) : R c.p0 c.p3 := by
  have hd : (distinct points).Pairwise R := List.Pairwise.sublist (distinct_sublist points) h
  unfold monotoneX at hc
  generalize distinct points = ps at hd hc
  match ps, hd, hc with
  | [], _, hc => cases hc
  | [_], _, hc => cases hc
  | [a, b], hd, hc =>
    cases List.mem_singleton.mp hc
    exact (List.pairwise_cons.mp hd).1 b List.mem_cons_self
  | a :: b :: d :: rest, hd, hc => exact pieces_related R (d :: rest) a _ b hd c hc

end Curve

namespace Monotone

/-! ## The graph of a function -/

/-- **The abscissa of a piece runs evenly**: at the parameter `s` it is `s` of the way across.
The two control points stand a third of the way from each end. -/
theorem segment_x (p0 p1 : Vec) (t0 t1 s : Rat) :
    ((segment p0 p1 t0 t1).pointAt s).x = p0.x + s * (p1.x - p0.x) := by
  simp only [segment, Cubic.pointAt, Cubic.blossom, Vec.lerp]
  grind

/-! ## Slopes that keep a piece between its ends -/

/-- **The slope `t` suits a piece** that runs across by `h` and rises by `d`: `h * t` lies
between `0` and `3 * d`. A control point a third of the way across, set by such a slope, lies
between the two ends in height. -/
def Tame (h d t : Rat) : Prop :=
  (0 ≤ d → 0 ≤ h * t ∧ h * t ≤ 3 * d) ∧ (d ≤ 0 → 3 * d ≤ h * t ∧ h * t ≤ 0)

/-- The slope `t` lies between `0` and twice the slope `s`: Steffen's bound. -/
def Bound (s t : Rat) : Prop := (0 ≤ s → 0 ≤ t ∧ t ≤ 2 * s) ∧ (s ≤ 0 → 2 * s ≤ t ∧ t ≤ 0)

/-- No slope suits every piece. -/
theorem tame_zero (h d : Rat) : Tame h d 0 := by
  simp only [Tame]
  grind

/-- Every slope suits a piece that stands upright: its control points are its ends. -/
theorem tame_upright (d t : Rat) : Tame 0 d t := by
  simp only [Tame]
  grind

/-- A slope within Steffen's bound of a chord suits the piece of that chord, for a piece that
does not run back. -/
theorem tame_of_bound_forth {h s t : Rat} (hh : 0 ≤ h) (b : Bound s t) : Tame h (h * s) t := by
  by_cases h0 : 0 ≤ s
  · obtain ⟨t0, t1⟩ := b.1 h0
    have a1 : 0 ≤ h * t := Rat.mul_nonneg hh t0
    have a2 : h * t ≤ h * (2 * s) := Rat.mul_le_mul_of_nonneg_left t1 hh
    have a3 : 0 ≤ h * s := Rat.mul_nonneg hh h0
    simp only [Tame]
    grind
  · have h0' : s ≤ 0 := by grind
    obtain ⟨t0, t1⟩ := b.2 h0'
    have a1 : h * t ≤ h * 0 := Rat.mul_le_mul_of_nonneg_left t1 hh
    have a2 : h * (2 * s) ≤ h * t := Rat.mul_le_mul_of_nonneg_left t0 hh
    have a3 : h * s ≤ h * 0 := Rat.mul_le_mul_of_nonneg_left h0' hh
    simp only [Tame]
    grind

/-- **A slope within Steffen's bound of a chord suits the piece of that chord**, whichever way
the piece runs. -/
theorem tame_of_bound {h s t : Rat} (b : Bound s t) : Tame h (h * s) t := by
  by_cases hh : 0 ≤ h
  · exact tame_of_bound_forth hh b
  · have f := tame_of_bound_forth (h := -h) (by grind) b
    simp only [Tame] at f ⊢
    grind

theorem sign_cases (x : Rat) : sign x = 1 ∨ sign x = -1 := by
  unfold sign
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem upright_cases (d h : Rat) : upright d h = 1 ∨ upright d h = -1 := by
  unfold upright
  split <;> split
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem size_nonneg (x : Rat) : 0 ≤ size x := by
  unfold size
  split <;> grind

/-- **Steffen's bound.** A sign and the sign of a slope, times a size no more than the size of
that slope, is `0` where the two signs differ and no more than twice the slope where they
agree. -/
theorem bound_steffen {σ s m : Rat} (hσ : σ = 1 ∨ σ = -1) (hm0 : 0 ≤ m) (hm : m ≤ size s) :
    Bound s ((σ + sign s) * m) := by
  unfold Bound
  by_cases hs : s < 0
  · have e1 : sign s = -1 := if_pos hs
    have e2 : size s = -s := if_pos hs
    rw [e1]
    rw [e2] at hm
    rcases hσ with rfl | rfl <;> grind
  · have e1 : sign s = 1 := if_neg hs
    have e2 : size s = s := if_neg hs
    rw [e1]
    rw [e2] at hm
    rcases hσ with rfl | rfl <;> grind

/-- A run that is not `0` times the slope over it is the rise. -/
theorem run_mul_slope {h d : Rat} (hne : h ≠ 0) : h * (d / h) = d := by grind

/-- **The slope at the middle of three points suits both pieces that meet there**, for every
three points. -/
theorem slope3_tame (p0 p1 p2 : Vec) :
    Tame (p1.x - p0.x) (p1.y - p0.y) (slope3 p0 p1 p2) ∧
      Tame (p2.x - p1.x) (p2.y - p1.y) (slope3 p0 p1 p2) := by
  simp only [slope3]
  generalize p1.x - p0.x = a
  generalize p2.x - p1.x = b
  generalize p1.y - p0.y = d
  generalize p2.y - p1.y = e
  by_cases ha0 : a = 0
  · rw [if_pos ha0]
    by_cases hz : b = 0 ∨ d = 0
    · rw [if_pos hz]
      exact ⟨tame_zero a d, tame_zero b e⟩
    · rw [if_neg hz]
      have hb0 : b ≠ 0 := fun h => hz (Or.inl h)
      have t := tame_of_bound (h := b)
        (bound_steffen (upright_cases d b) (size_nonneg (e / b)) Rat.le_refl)
      rw [run_mul_slope hb0] at t
      rw [ha0]
      exact ⟨tame_upright d _, t⟩
  · rw [if_neg ha0]
    by_cases hb0 : b = 0
    · rw [if_pos hb0]
      by_cases he : e = 0
      · rw [if_pos he]
        exact ⟨tame_zero a d, tame_zero b e⟩
      · rw [if_neg he]
        have t := tame_of_bound (h := a)
          (bound_steffen (upright_cases e a) (size_nonneg (d / a)) Rat.le_refl)
        rw [run_mul_slope ha0, Rat.add_comm] at t
        rw [hb0]
        exact ⟨t, tame_upright e _⟩
    · rw [if_neg hb0]
      have s0 := size_nonneg (d / a)
      have s1 := size_nonneg (e / b)
      have both : ∀ M : Rat, 0 ≤ M → M ≤ size (d / a) → M ≤ size (e / b) →
          Tame a d ((sign (d / a) + sign (e / b)) * M) ∧
            Tame b e ((sign (d / a) + sign (e / b)) * M) := fun M hM0 hM1 hM2 => by
        have t0 := tame_of_bound (h := a) (bound_steffen (sign_cases (e / b)) hM0 hM1)
        have t1 := tame_of_bound (h := b) (bound_steffen (sign_cases (d / a)) hM0 hM2)
        rw [run_mul_slope ha0, Rat.add_comm] at t0
        rw [run_mul_slope hb0] at t1
        exact ⟨t0, t1⟩
      by_cases hsum : a + b = 0
      · rw [if_pos hsum]
        by_cases hde : d + e = 0
        · rw [if_pos hde]
          exact ⟨tame_zero a d, tame_zero b e⟩
        · rw [if_neg hde]
          exact both _ (by grind) (by grind) (by grind)
      · rw [if_neg hsum]
        have hq : 0 ≤ size ((d / a * b + e / b * a) / (a + b)) / 2 := by
          have hp := size_nonneg ((d / a * b + e / b * a) / (a + b))
          grind
        generalize size ((d / a * b + e / b * a) / (a + b)) / 2 = q at hq ⊢
        exact both _ (by grind) (by grind) (by grind)

/-- **The slope at an end of the curve suits its piece**, where the slope it is taken from
does. -/
theorem slope2_tame {p0 p1 : Vec} {t : Rat} (h : Tame (p1.x - p0.x) (p1.y - p0.y) t) :
    Tame (p1.x - p0.x) (p1.y - p0.y) (slope2 p0 p1 t) := by
  unfold slope2
  generalize p1.x - p0.x = a at h ⊢
  generalize p1.y - p0.y = d at h ⊢
  by_cases ha : a = 0
  · rw [if_pos ha]
    exact h
  · rw [if_neg ha]
    have e : a * ((3 * d / a - t) / 2) = (3 * d - a * t) / 2 := by grind
    simp only [Tame] at h ⊢
    rw [e]
    grind

/-! ## A piece that fits -/

/-- **A piece that fits its two points**: a `segment` whose two slopes suit it, or a straight
segment. Every piece of the monotone curve is one, where the abscissae do not go back
(`Curve.monotoneX_fits`). -/
def Fits (c : Cubic) : Prop :=
  (∃ a b u v, c = segment a b u v ∧ Tame (b.x - a.x) (b.y - a.y) u ∧
      Tame (b.x - a.x) (b.y - a.y) v) ∨
    ∃ a b, c = Cubic.line a b

/-- A piece whose two slopes suit it stays in the box of its two points. -/
theorem segment_within {p0 p1 : Vec} {t0 t1 : Rat}
    (h0 : Tame (p1.x - p0.x) (p1.y - p0.y) t0) (h1 : Tame (p1.x - p0.x) (p1.y - p0.y) t1)
    {s : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (Box.ofCorners p0 p1).Contains ((segment p0 p1 t0 t1).pointAt s) := by
  have e0 : (p1.x - p0.x) / 3 * t0 = (p1.x - p0.x) * t0 / 3 := by grind
  have e1 : (p1.x - p0.x) / 3 * t1 = (p1.x - p0.x) * t1 / 3 := by grind
  refine Cubic.contains_pointAt_of ?_ ?_ ?_ ?_ hs0 hs1
  · simp only [Box.Contains, Box.ofCorners, segment]
    grind
  · simp only [Box.Contains, Box.ofCorners, segment, Tame, e0] at h0 ⊢
    generalize (p1.x - p0.x) * t0 = w at h0 ⊢
    grind
  · simp only [Box.Contains, Box.ofCorners, segment, Tame, e1] at h1 ⊢
    generalize (p1.x - p0.x) * t1 = w at h1 ⊢
    grind
  · simp only [Box.Contains, Box.ofCorners, segment]
    grind

/-- A straight segment stays in the box of its two ends. -/
theorem line_within (a b : Vec) {s : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (Box.ofCorners a b).Contains ((Cubic.line a b).pointAt s) := by
  rw [Cubic.line_pointAt]
  refine Box.contains_lerp ?_ ?_ hs0 hs1
  · simp only [Box.Contains, Box.ofCorners]
    grind
  · simp only [Box.Contains, Box.ofCorners]
    grind

/-- **A piece that fits stays in the box of its two points.** -/
theorem Fits.within {c : Cubic} (h : Fits c) {s : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (Box.ofCorners c.p0 c.p3).Contains (c.pointAt s) := by
  rcases h with ⟨a, b, u, v, rfl, hu, hv⟩ | ⟨a, b, rfl⟩
  · exact segment_within hu hv hs0 hs1
  · exact line_within a b hs0 hs1

/-- The rise of a piece between two parameters, as their difference times a sum of three
products: the first control point's rise, the rise between the two control points and the
second control point's rise, each with a weight that depends on the parameters alone. -/
theorem segment_rise (p0 p1 : Vec) (t0 t1 s t : Rat) :
    ((segment p0 p1 t0 t1).pointAt t).y - ((segment p0 p1 t0 t1).pointAt s).y =
      (t - s) * ((p1.x - p0.x) / 3 * t0 *
          ((1 - s) * (1 - s) + (1 - s) * (1 - t) + (1 - t) * (1 - t)) +
        (p1.y - p0.y - (p1.x - p0.x) / 3 * t0 - (p1.x - p0.x) / 3 * t1) *
          (3 * (s + t) - 2 * (s * s + s * t + t * t)) +
        (p1.x - p0.x) / 3 * t1 * (s * s + s * t + t * t)) := by
  simp only [segment, Cubic.pointAt, Cubic.blossom, Vec.lerp]
  grind

/-- The sum of `segment_rise` is not negative where the piece rises by `d`, each control point
rises by no less than nothing and no more than `d`, and the parameters are in order. The sum is
shared among the four corners of the square of the two rises, and at each corner it is a
product of numbers that are not negative. -/
theorem rise_nonneg {d α β s t : Rat} (ha0 : 0 ≤ α) (ha1 : α ≤ d) (hb0 : 0 ≤ β)
    (hb1 : β ≤ d) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    0 ≤ (t - s) * (α * ((1 - s) * (1 - s) + (1 - s) * (1 - t) + (1 - t) * (1 - t)) +
      (d - α - β) * (3 * (s + t) - 2 * (s * s + s * t + t * t)) +
      β * (s * s + s * t + t * t)) := by
  have h1s : 0 ≤ 1 - s := by grind
  have h1t : 0 ≤ 1 - t := by grind
  have ht0 : 0 ≤ t := by grind
  have hA : 0 ≤ (1 - s) * (1 - s) + (1 - s) * (1 - t) + (1 - t) * (1 - t) := by
    have x1 := Rat.mul_nonneg h1s h1s
    have x2 := Rat.mul_nonneg h1s h1t
    have x3 := Rat.mul_nonneg h1t h1t
    grind
  have hC : 0 ≤ s * s + s * t + t * t := by
    have x1 := Rat.mul_nonneg hs hs
    have x2 := Rat.mul_nonneg hs ht0
    have x3 := Rat.mul_nonneg ht0 ht0
    grind
  have hB : 0 ≤ 3 * (s + t) - 2 * (s * s + s * t + t * t) := by
    have x1 := Rat.mul_nonneg hs (show 0 ≤ 3 - 2 * s - t by grind)
    have x2 := Rat.mul_nonneg ht0 (show 0 ≤ 3 - s - 2 * t by grind)
    grind
  have hS : 0 ≤ (1 - s) * (1 - s) + (1 - s) * (1 - t) + (1 - t) * (1 - t) -
      (3 * (s + t) - 2 * (s * s + s * t + t * t)) + (s * s + s * t + t * t) := by
    have x1 := rat_mul_self_nonneg (2 * s + t - 3 / 2)
    have x2 := rat_mul_self_nonneg (t - 1 / 2)
    grind
  generalize (1 - s) * (1 - s) + (1 - s) * (1 - t) + (1 - t) * (1 - t) = A at hA hS ⊢
  generalize 3 * (s + t) - 2 * (s * s + s * t + t * t) = B at hB hS ⊢
  generalize s * s + s * t + t * t = C at hC hS ⊢
  have hda : 0 ≤ d - α := by grind
  have hdb : 0 ≤ d - β := by grind
  have y1 := Rat.mul_nonneg (Rat.mul_nonneg hda hdb) hB
  have y2 := Rat.mul_nonneg (Rat.mul_nonneg ha0 hdb) hA
  have y3 := Rat.mul_nonneg (Rat.mul_nonneg hda hb0) hC
  have y4 := Rat.mul_nonneg (Rat.mul_nonneg ha0 hb0) hS
  have hdQ : 0 ≤ d * (α * A + (d - α - β) * B + β * C) := by grind
  have hQ : 0 ≤ α * A + (d - α - β) * B + β * C := by
    by_cases hd0 : d = 0
    · have e1 : α = 0 := by grind
      have e2 : β = 0 := by grind
      rw [e1, e2, hd0]
      grind
    · by_cases hneg : 0 ≤ α * A + (d - α - β) * B + β * C
      · exact hneg
      · have hp := Rat.mul_pos (show 0 < d by grind)
          (show 0 < -(α * A + (d - α - β) * B + β * C) by grind)
        grind
  exact Rat.mul_nonneg (by grind) hQ

/-- A piece whose two slopes suit it, and whose end is no lower than its start, is no lower at
a later parameter. -/
theorem segment_rises {p0 p1 : Vec} {t0 t1 : Rat}
    (h0 : Tame (p1.x - p0.x) (p1.y - p0.y) t0) (h1 : Tame (p1.x - p0.x) (p1.y - p0.y) t1)
    (hy : p0.y ≤ p1.y) {s t : Rat} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ((segment p0 p1 t0 t1).pointAt s).y ≤ ((segment p0 p1 t0 t1).pointAt t).y := by
  have e0 : (p1.x - p0.x) / 3 * t0 = (p1.x - p0.x) * t0 / 3 := by grind
  have e1 : (p1.x - p0.x) / 3 * t1 = (p1.x - p0.x) * t1 / 3 := by grind
  have hd : 0 ≤ p1.y - p0.y := by grind
  obtain ⟨a0, a1⟩ := h0.1 hd
  obtain ⟨b0, b1⟩ := h1.1 hd
  have r := rise_nonneg (d := p1.y - p0.y) (α := (p1.x - p0.x) / 3 * t0)
    (β := (p1.x - p0.x) / 3 * t1) (by grind) (by grind) (by grind) (by grind) hs hst ht
  rw [← segment_rise p0 p1 t0 t1 s t] at r
  grind

/-- A straight segment whose end is no lower than its start is no lower at a later
parameter. -/
theorem line_rises (a b : Vec) (hy : a.y ≤ b.y) {s t : Rat} (hst : s ≤ t) :
    ((Cubic.line a b).pointAt s).y ≤ ((Cubic.line a b).pointAt t).y := by
  rw [Cubic.line_pointAt, Cubic.line_pointAt]
  have p := Rat.mul_nonneg (show 0 ≤ t - s by grind) (show 0 ≤ b.y - a.y by grind)
  simp only [Vec.lerp]
  grind

/-- **A piece that fits, and whose end is no lower than its start, never falls**: it is no
lower at a later parameter. -/
theorem Fits.rises {c : Cubic} (h : Fits c) (hy : c.p0.y ≤ c.p3.y) {s t : Rat} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ 1) : (c.pointAt s).y ≤ (c.pointAt t).y := by
  rcases h with ⟨a, b, u, v, rfl, hu, hv⟩ | ⟨a, b, rfl⟩
  · exact segment_rises hu hv hy hs hst ht
  · exact line_rises a b hy hst

/-- Every piece from a point on fits, where the slope at the first point suits the first
piece. -/
theorem pieces_fit : ∀ (rest : List Vec) (p0 : Vec) (t0 : Rat) (p1 : Vec),
    Tame (p1.x - p0.x) (p1.y - p0.y) t0 → ∀ c ∈ pieces p0 t0 p1 rest, Fits c
  | [], p0, t0, p1, ht, c, hc => by
    cases List.mem_singleton.mp hc
    exact Or.inl ⟨p0, p1, t0, _, rfl, ht, slope2_tame ht⟩
  | p2 :: rest, p0, t0, p1, ht, c, hc => by
    have tame := slope3_tame p0 p1 p2
    rcases List.mem_cons.mp hc with rfl | h
    · exact Or.inl ⟨p0, p1, t0, _, rfl, ht, tame.1⟩
    · exact pieces_fit rest p1 _ p2 tame.2 c h

end Monotone

namespace Curve

open Monotone

/-- **Every piece of the monotone curve fits its two points**, for every list of points. The
two laws of a piece that fits are then laws of the curve. -/
theorem monotoneX_fits (points : List Vec) {c : Cubic} (hc : c ∈ monotoneX points) : Fits c := by
  unfold monotoneX at hc
  generalize distinct points = ps at hc
  match ps, hc with
  | [], hc => cases hc
  | [_], hc => cases hc
  | [a, b], hc =>
    cases List.mem_singleton.mp hc
    exact Or.inr ⟨a, b, rfl⟩
  | a :: b :: d :: rest, hc =>
    exact pieces_fit (d :: rest) a _ b (slope2_tame (slope3_tame a b d).1) c hc

/-- **The monotone curve does not overshoot.** No piece of the curve leaves the box of its own
two points, at any parameter from `0` to `1`. It holds for every list of points. -/
theorem monotoneX_within (points : List Vec) {c : Cubic} (hc : c ∈ monotoneX points) {s : Rat}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (Box.ofCorners c.p0 c.p3).Contains (c.pointAt s) :=
  (monotoneX_fits points hc).within hs0 hs1

/-- **The monotone curve never leaves the range of its data.** Where every point is between
`lo` and `hi` in height, so is every point of the curve. A curve through values that are never
negative is never negative. -/
theorem monotoneX_range (points : List Vec) {lo hi : Rat}
    (hr : ∀ p ∈ points, lo ≤ p.y ∧ p.y ≤ hi) {c : Cubic} (hc : c ∈ monotoneX points) {s : Rat}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : lo ≤ (c.pointAt s).y ∧ (c.pointAt s).y ≤ hi := by
  have w := monotoneX_within points hc hs0 hs1
  obtain ⟨m0, m3⟩ := mem_of_mem_monotoneX hc
  have r0 := hr _ m0
  have r3 := hr _ m3
  simp only [Box.Contains, Box.ofCorners] at w
  grind

/-- **Rising data give a rising curve.** A piece whose end is no lower than its start is no
lower at a later parameter. With `monotoneX_x`, where the abscissae never go back, the curve is
a function of `x` that never falls between two points of which the second is no lower. -/
theorem monotoneX_rises (points : List Vec) {c : Cubic} (hc : c ∈ monotoneX points)
    (hy : c.p0.y ≤ c.p3.y) {s t : Rat} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (c.pointAt s).y ≤ (c.pointAt t).y :=
  (monotoneX_fits points hc).rises hy hs hst ht

/-- **The monotone curve is the graph of a function**: on each piece the abscissa at the
parameter `s` is `s` of the way from the piece's start to its end. -/
theorem monotoneX_x (points : List Vec) {c : Cubic} (hc : c ∈ monotoneX points) (s : Rat) :
    (c.pointAt s).x = c.p0.x + s * (c.p3.x - c.p0.x) := by
  unfold monotoneX at hc
  generalize distinct points = ps at hc
  match ps, hc with
  | [], hc => cases hc
  | [_], hc => cases hc
  | [a, b], hc =>
    cases List.mem_singleton.mp hc
    rw [Cubic.line_pointAt]
    rfl
  | a :: b :: d :: rest, hc =>
    obtain ⟨u, v, t0, t1, rfl⟩ := pieces_segment (d :: rest) a _ b c hc
    exact segment_x u v t0 t1 s

end Curve

/-! ## Moved points -/

namespace Monotone

/-- A difference of two numbers moved alike is their difference. -/
theorem add_sub_add (a b d : Rat) : a + d - (b + d) = a - b := by grind

/-- The slope at the middle of three points does not depend on where they stand. -/
theorem slope3_move (d p0 p1 p2 : Vec) :
    slope3 (p0 + d) (p1 + d) (p2 + d) = slope3 p0 p1 p2 := by
  simp only [slope3, Vec.add_def, add_sub_add]

/-- The slope at an end does not depend on where the piece stands. -/
theorem slope2_move (d p0 p1 : Vec) (t : Rat) : slope2 (p0 + d) (p1 + d) t = slope2 p0 p1 t := by
  simp only [slope2, Vec.add_def, add_sub_add]

/-- The piece between two moved points is the piece, moved. -/
theorem segment_move (d p0 p1 : Vec) (t0 t1 : Rat) :
    segment (p0 + d) (p1 + d) t0 t1 = (segment p0 p1 t0 t1).move d := by
  apply Cubic.ext <;> apply Vec.ext <;>
    simp only [segment, Cubic.move, Cubic.map, Vec.add_def] <;> grind

/-- The pieces through moved points are the pieces, moved. -/
theorem pieces_move (d : Vec) : ∀ (rest : List Vec) (p0 : Vec) (t0 : Rat) (p1 : Vec),
    pieces (p0 + d) t0 (p1 + d) (rest.map fun p => p + d) =
      (pieces p0 t0 p1 rest).map (Cubic.move d)
  | [], p0, t0, p1 => by
    show [segment (p0 + d) (p1 + d) t0 (slope2 (p0 + d) (p1 + d) t0)] =
      [(segment p0 p1 t0 (slope2 p0 p1 t0)).move d]
    rw [slope2_move, segment_move]
  | p2 :: rest, p0, t0, p1 => by
    show segment (p0 + d) (p1 + d) t0 (slope3 (p0 + d) (p1 + d) (p2 + d)) ::
        pieces (p1 + d) (slope3 (p0 + d) (p1 + d) (p2 + d)) (p2 + d) (rest.map fun p => p + d) =
      (segment p0 p1 t0 (slope3 p0 p1 p2)).move d ::
        (pieces p1 (slope3 p0 p1 p2) p2 rest).map (Cubic.move d)
    rw [slope3_move, segment_move, pieces_move d rest p1 _ p2]

/-- Two points moved alike are one point exactly where they were one. -/
theorem add_right_cancel {a b d : Vec} (h : a + d = b + d) : a = b :=
  calc a = a + d - d := (Vec.add_sub_cancel a d).symm
    _ = b + d - d := by rw [h]
    _ = b := Vec.add_sub_cancel b d

/-- The moved points with no repeat are the points with no repeat, moved. -/
theorem distinct_move (d : Vec) : ∀ l : List Vec,
    distinct (l.map fun p => p + d) = (distinct l).map fun p => p + d
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    have ih := distinct_move d (b :: rest)
    show (if a + d = b + d then distinct ((b + d) :: rest.map fun p => p + d)
        else (a + d) :: distinct ((b + d) :: rest.map fun p => p + d)) =
      (if a = b then distinct (b :: rest) else a :: distinct (b :: rest)).map fun p => p + d
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (congrArg (fun p => p + d) hab)]
      exact ih
    · rw [if_neg hab, if_neg fun e => hab (add_right_cancel e)]
      exact congrArg (List.cons (a + d)) ih

end Monotone

namespace Curve

open Monotone

/-- **The monotone curve through moved points is the curve, moved.** A curve computed at one
place stands for the curve at every other, as for every other curve of the kit. -/
theorem monotoneX_move (d : Vec) (points : List Vec) :
    monotoneX (points.map fun p => p + d) = (monotoneX points).map (Cubic.move d) := by
  unfold monotoneX
  rw [distinct_move]
  generalize distinct points = ps
  match ps with
  | [] => rfl
  | [_] => rfl
  | [a, b] =>
    show [Cubic.line (a + d) (b + d)] = [(Cubic.line a b).move d]
    rw [Cubic.move_line]
  | a :: b :: c :: rest =>
    show pieces (a + d) (slope2 (a + d) (b + d) (slope3 (a + d) (b + d) (c + d))) (b + d)
        ((c + d) :: rest.map fun p => p + d) =
      (pieces a (slope2 a b (slope3 a b c)) b (c :: rest)).map (Cubic.move d)
    rw [slope3_move, slope2_move]
    exact pieces_move d (c :: rest) a _ b

end Curve

end Whatwg.Svg.Value
