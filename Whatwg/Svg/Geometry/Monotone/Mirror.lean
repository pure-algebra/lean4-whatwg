import Whatwg.Svg.Geometry.Monotone.Laws

/-!
# Whatwg.Svg.Geometry.Monotone.Mirror

Owner: the laws of the monotone curve that hold by a mirror image (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Geometry/Monotone/Laws.lean` proves that a piece of the monotone curve whose end is
no lower than its start never falls, and says of two more groups of laws that they hold by
symmetry and are not stated: the same for a piece that ends lower, and the laws of the curve
along `y`. They are stated and proved here.

- **Falling data give a falling curve** (`Curve.monotoneX_falls`): a piece whose end is no
  higher than its start is no higher at a later parameter. It is `monotoneX_rises` in the
  mirror of the axis: the proof gives `Monotone.rise_nonneg` the heights with their signs
  turned.
- **Level data give a level curve** (`Curve.monotoneX_level`): a piece between two points of
  one height is at that height at every parameter. A cardinal spline bulges there.
- **The curve along `y`** (`Curve.monotoneY_within`, `monotoneY_range`, `monotoneY_y`,
  `monotoneY_rises`, `monotoneY_falls`): each law of the curve along `x`, read through the
  exchange of the two axes. A piece never leaves the box of its two points; the curve never
  leaves the range of its data across; its ordinate runs evenly; and a piece whose end is no
  further left never goes back to the left. Its chain, its two ends and its move are the laws
  of the generator `Curve.Through.monotoneY` of `Whatwg/Svg/Geometry/Through.lean`.

What this module does not claim: the same at every real parameter, which belongs in
`analysis/`; that the pieces of the curve along `y` start and end at the points in the words of
`monotoneX_starts`, which needs that the points with no repeat are the exchanged points with no
repeat, exchanged.
-/

namespace Whatwg.Svg.Value

namespace Monotone

/-- A piece whose two slopes suit it, and whose end is no higher than its start, is no higher
at a later parameter. -/
theorem segment_falls {p0 p1 : Vec} {t0 t1 : Rat}
    (h0 : Tame (p1.x - p0.x) (p1.y - p0.y) t0) (h1 : Tame (p1.x - p0.x) (p1.y - p0.y) t1)
    (hy : p1.y ≤ p0.y) {s t : Rat} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ((segment p0 p1 t0 t1).pointAt t).y ≤ ((segment p0 p1 t0 t1).pointAt s).y := by
  have e0 : (p1.x - p0.x) / 3 * t0 = (p1.x - p0.x) * t0 / 3 := by grind
  have e1 : (p1.x - p0.x) / 3 * t1 = (p1.x - p0.x) * t1 / 3 := by grind
  have hd : p1.y - p0.y ≤ 0 := by grind
  obtain ⟨a0, a1⟩ := h0.2 hd
  obtain ⟨b0, b1⟩ := h1.2 hd
  have r := rise_nonneg (d := -(p1.y - p0.y)) (α := -((p1.x - p0.x) / 3 * t0))
    (β := -((p1.x - p0.x) / 3 * t1)) (by grind) (by grind) (by grind) (by grind) hs hst ht
  have e := segment_rise p0 p1 t0 t1 s t
  grind

/-- A straight segment whose end is no higher than its start is no higher at a later
parameter. -/
theorem line_falls (a b : Vec) (hy : b.y ≤ a.y) {s t : Rat} (hst : s ≤ t) :
    ((Cubic.line a b).pointAt t).y ≤ ((Cubic.line a b).pointAt s).y := by
  rw [Cubic.line_pointAt, Cubic.line_pointAt]
  have p := Rat.mul_nonneg (show 0 ≤ t - s by grind) (show 0 ≤ a.y - b.y by grind)
  simp only [Vec.lerp]
  grind

/-- **A piece that fits, and whose end is no higher than its start, never rises**: it is no
higher at a later parameter. -/
theorem Fits.falls {c : Cubic} (h : Fits c) (hy : c.p3.y ≤ c.p0.y) {s t : Rat} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ 1) : (c.pointAt t).y ≤ (c.pointAt s).y := by
  rcases h with ⟨a, b, u, v, rfl, hu, hv⟩ | ⟨a, b, rfl⟩
  · exact segment_falls hu hv hy hs hst ht
  · exact line_falls a b hy hst

end Monotone

namespace Curve

open Monotone

/-- **Falling data give a falling curve.** A piece whose end is no higher than its start is no
higher at a later parameter. With `monotoneX_x`, where the abscissae never go back, the curve is
a function of `x` that never rises between two points of which the second is no higher. -/
theorem monotoneX_falls (points : List Vec) {c : Cubic} (hc : c ∈ monotoneX points)
    (hy : c.p3.y ≤ c.p0.y) {s t : Rat} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (c.pointAt t).y ≤ (c.pointAt s).y :=
  (monotoneX_fits points hc).falls hy hs hst ht

/-- **Level data give a level curve.** A piece between two points of one height is at that
height at every parameter from `0` to `1`. -/
theorem monotoneX_level (points : List Vec) {c : Cubic} (hc : c ∈ monotoneX points)
    (hy : c.p0.y = c.p3.y) {s : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (c.pointAt s).y = c.p0.y := by
  have w := monotoneX_within points hc hs0 hs1
  simp only [Box.Contains, Box.ofCorners] at w
  grind

/-! ## The curve along `y` -/

/-- A piece of the monotone curve along `y` is a piece of the monotone curve along `x` through
the exchanged points, exchanged. -/
theorem mem_monotoneY {points : List Vec} {c : Cubic} (hc : c ∈ monotoneY points) :
    ∃ c0 ∈ monotoneX (points.map Monotone.swap), c = c0.map Monotone.swap := by
  obtain ⟨c0, h0, rfl⟩ := List.mem_map.mp hc
  exact ⟨c0, h0, rfl⟩

/-- An exchanged piece at a parameter is the point of the piece, exchanged. -/
theorem swap_pointAt (c : Cubic) (s : Rat) :
    (c.map Monotone.swap).pointAt s = Monotone.swap (c.pointAt s) :=
  Cubic.map_pointAt Monotone.swap (fun _ _ _ => rfl) c s

/-- **The monotone curve along `y` does not overshoot**: no piece leaves the box of its own
two points. -/
theorem monotoneY_within (points : List Vec) {c : Cubic} (hc : c ∈ monotoneY points) {s : Rat}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (Box.ofCorners c.p0 c.p3).Contains (c.pointAt s) := by
  obtain ⟨c0, h0, rfl⟩ := mem_monotoneY hc
  have w := monotoneX_within _ h0 hs0 hs1
  rw [swap_pointAt]
  exact ⟨w.2.2.1, w.2.2.2, w.1, w.2.1⟩

/-- **The monotone curve along `y` never leaves the range of its data across**: where every
point is between `lo` and `hi` in its abscissa, so is every point of the curve. -/
theorem monotoneY_range (points : List Vec) {lo hi : Rat}
    (hr : ∀ p ∈ points, lo ≤ p.x ∧ p.x ≤ hi) {c : Cubic} (hc : c ∈ monotoneY points) {s : Rat}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : lo ≤ (c.pointAt s).x ∧ (c.pointAt s).x ≤ hi := by
  obtain ⟨c0, h0, rfl⟩ := mem_monotoneY hc
  rw [swap_pointAt]
  exact monotoneX_range (points.map Monotone.swap) (fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hr q hq) h0 hs0 hs1

/-- **The monotone curve along `y` is the graph of a function of `y`**: on each piece the
ordinate at the parameter `s` is `s` of the way from the piece's start to its end. -/
theorem monotoneY_y (points : List Vec) {c : Cubic} (hc : c ∈ monotoneY points) (s : Rat) :
    (c.pointAt s).y = c.p0.y + s * (c.p3.y - c.p0.y) := by
  obtain ⟨c0, h0, rfl⟩ := mem_monotoneY hc
  rw [swap_pointAt]
  exact monotoneX_x _ h0 s

/-- **Along `y`, a piece whose end is no further left never goes back to the left**: its
abscissa is no less at a later parameter. -/
theorem monotoneY_rises (points : List Vec) {c : Cubic} (hc : c ∈ monotoneY points)
    (hx : c.p0.x ≤ c.p3.x) {s t : Rat} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (c.pointAt s).x ≤ (c.pointAt t).x := by
  obtain ⟨c0, h0, rfl⟩ := mem_monotoneY hc
  rw [swap_pointAt, swap_pointAt]
  exact monotoneX_rises _ h0 hx hs hst ht

/-- **Along `y`, a piece whose end is no further right never goes back to the right**: its
abscissa is no more at a later parameter. -/
theorem monotoneY_falls (points : List Vec) {c : Cubic} (hc : c ∈ monotoneY points)
    (hx : c.p3.x ≤ c.p0.x) {s t : Rat} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (c.pointAt t).x ≤ (c.pointAt s).x := by
  obtain ⟨c0, h0, rfl⟩ := mem_monotoneY hc
  rw [swap_pointAt, swap_pointAt]
  exact monotoneX_falls _ h0 hx hs hst ht

end Curve

end Whatwg.Svg.Value
