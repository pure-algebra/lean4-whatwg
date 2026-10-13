import Whatwg.Svg.Geometry.Box

/-!
# Whatwg.Svg.Geometry.Around

Owner: the arc that goes out to a line and comes back (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

A graph that is laid out downward draws an edge that goes back up as one arc: out of the side of
its source, round through a lane beside the graph, and into the side of its target. An edge from
a box to itself is a small arc off the side of the box. lean4-effect4 writes both by hand
(`tools/Tools/View/Graph.lean`, the `back` and the `loop` case of `segments`), with the comment
"controls a third past the lane, so the arc's widest point reaches the lane". That sentence is a
law, and it holds on one condition, which the comment does not name. Here is the arc with the
law.

- `Cubic.around p q reach`: one cubic from `p` to `q` whose two control points stand past the
  line `x = reach` by a third of what the further end has to go to it. `swell` puts the control
  points beyond the two ends in height by that share of the height between them, which makes a
  loop of an arc; it is `0` unless given.
- `Cubic.x_of_controls`, `Cubic.x_le_of_controls`: of every cubic whose two control points
  stand at one abscissa `k`. Where its two ends stand at `m` at the most and `m ≤ k`, it goes
  no further than three quarters of the way from `m` to `k`. So a control point has to stand a
  third past a line for the arc to reach it.
- **The arc never passes the reach** (`Cubic.around_x_le`), where neither end is past it.
- **It touches the reach at its middle exactly where the two ends stand at one abscissa**
  (`Cubic.around_touches`, `Cubic.around_x_lt`). Where one end stands further in than the
  other, the arc stays short of the reach at every parameter: the control of
  `WhatwgTest/Svg/Around.lean` is a back edge of the consumer between two boxes of different
  widths, whose arc stops three pixels short of its lane.
- **It stays between its ends** (`Cubic.around_within`, with no swell): no point of it is left
  of the nearer end, above the higher or below the lower. So an arc in a lane does not cross the
  boxes it passes, where the lane is clear of them.
- `Cubic.around_level`: with no swell it leaves and arrives level. `Cubic.around_y`: its height
  runs from one end to the other with no turn. `Cubic.around_move`: the arc of moved ends round
  a moved line is the arc, moved. `Cubic.around_reverse`: backwards it is the arc from `q` to
  `p`.

The line is upright and the arc bulges toward greater `x`: a lane at the right. An arc that
bulges another way is this one under a map of the plane (`Cubic.map`).

What this module does not claim: the highest and the lowest point of an arc with a swell, which
take the roots of a quadratic; that two arcs in two lanes do not cross, which is false of two
whose ends interleave.
-/

namespace Whatwg.Svg.Value

namespace Cubic

/-! ## Two control points at one abscissa -/

/-- **The abscissa of a cubic whose two control points stand at one abscissa `k`**: the two
ends by the cubes of the two shares of the parameter, and `k` by what is left of the whole. -/
theorem x_of_controls (c : Cubic) {k : Rat} (h1 : c.p1.x = k) (h2 : c.p2.x = k) (t : Rat) :
    (c.pointAt t).x =
      (1 - t) * (1 - t) * (1 - t) * c.p0.x + 3 * t * (1 - t) * k + t * t * t * c.p3.x := by
  simp only [pointAt, blossom, Vec.lerp, h1, h2]
  grind

/-- **A cubic whose two control points stand at `k` goes three quarters of the way to `k` at the
most**, from the `m` that neither of its ends is past. It is the same on the other side, with
every order turned. -/
theorem x_le_of_controls {c : Cubic} {k m : Rat} (h1 : c.p1.x = k) (h2 : c.p2.x = k)
    (h0 : c.p0.x ≤ m) (h3 : c.p3.x ≤ m) (hk : m ≤ k) {t : Rat} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (c.pointAt t).x ≤ m + 3 / 4 * (k - m) := by
  have hr : 0 ≤ 1 - t := by grind
  have w0 : 0 ≤ (1 - t) * (1 - t) * (1 - t) := Rat.mul_nonneg (Rat.mul_nonneg hr hr) hr
  have w3 : 0 ≤ t * t * t := Rat.mul_nonneg (Rat.mul_nonneg ht0 ht0) ht0
  have a0 := Rat.mul_nonneg w0 (show 0 ≤ m - c.p0.x by grind)
  have a3 := Rat.mul_nonneg w3 (show 0 ≤ m - c.p3.x by grind)
  have q := rat_mul_self_nonneg (t - 1 / 2)
  have b := Rat.mul_nonneg (show 0 ≤ k - m by grind) (show 0 ≤ 1 / 4 - t * (1 - t) by grind)
  rw [x_of_controls c h1 h2]
  grind

/-! ## The arc -/

/-- **The arc from `p` to `q` round the line `x = reach`.** Both control points stand past the
line by a third of what the further end has to go to it, each at the height of its end. With a
`swell`, each stands beyond its end in height by that share of the height from `p` to `q`: at a
half, an arc between two points of one side of a box is a loop off that side. -/
def around (p q : Vec) (reach : Rat) (swell : Rat := 0) : Cubic :=
  ⟨p, ⟨reach + (reach - max p.x q.x) / 3, p.y - swell * (q.y - p.y)⟩,
    ⟨reach + (reach - max p.x q.x) / 3, q.y + swell * (q.y - p.y)⟩, q⟩

/-- **The arc never passes the reach**, where neither end is past it: at every parameter from
`0` to `1` its abscissa is the reach at the most. -/
theorem around_x_le (p q : Vec) {reach : Rat} (swell : Rat) (h : max p.x q.x ≤ reach) {t : Rat}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ((around p q reach swell).pointAt t).x ≤ reach := by
  have e := x_le_of_controls (c := around p q reach swell)
    (k := reach + (reach - max p.x q.x) / 3) (m := max p.x q.x) rfl rfl
    (show p.x ≤ max p.x q.x by grind) (show q.x ≤ max p.x q.x by grind) (by grind) ht0 ht1
  grind

/-- **The arc touches the reach at its middle**, where its two ends stand at one abscissa. -/
theorem around_touches (p q : Vec) (reach swell : Rat) (h : p.x = q.x) :
    ((around p q reach swell).pointAt (1 / 2)).x = reach := by
  rw [x_of_controls (around p q reach swell) (k := reach + (reach - max p.x q.x) / 3) rfl rfl]
  show (1 - 1 / 2) * (1 - 1 / 2) * (1 - 1 / 2) * p.x +
    3 * (1 / 2) * (1 - 1 / 2) * (reach + (reach - max p.x q.x) / 3) +
      1 / 2 * (1 / 2) * (1 / 2) * q.x = reach
  rw [h]
  grind

/-- **The arc stays short of the reach where one end stands further in than the other**, at
every parameter from `0` to `1`, with both ends short of the reach. So an arc touches the line
only where its two ends stand at one abscissa. -/
theorem around_x_lt (p q : Vec) {reach : Rat} (swell : Rat) (h : max p.x q.x < reach)
    (hne : p.x ≠ q.x) {t : Rat} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((around p q reach swell).pointAt t).x < reach := by
  have hr : 0 ≤ 1 - t := by grind
  have w0 : 0 ≤ (1 - t) * (1 - t) * (1 - t) := Rat.mul_nonneg (Rat.mul_nonneg hr hr) hr
  have w3 : 0 ≤ t * t * t := Rat.mul_nonneg (Rat.mul_nonneg ht0 ht0) ht0
  have q' := rat_mul_self_nonneg (t - 1 / 2)
  have b := Rat.mul_nonneg (show 0 ≤ reach - max p.x q.x by grind)
    (show 0 ≤ 1 / 4 - t * (1 - t) by grind)
  rw [x_of_controls (around p q reach swell) (k := reach + (reach - max p.x q.x) / 3) rfl rfl]
  show (1 - t) * (1 - t) * (1 - t) * p.x +
    3 * t * (1 - t) * (reach + (reach - max p.x q.x) / 3) + t * t * t * q.x < reach
  by_cases hlt : p.x < q.x
  · have hm : max p.x q.x = q.x := by grind
    rw [hm] at b h ⊢
    by_cases h1 : t = 1
    · subst h1
      grind
    · have a0 := Rat.mul_pos
        (Rat.mul_pos (Rat.mul_pos (show 0 < 1 - t by grind) (show 0 < 1 - t by grind))
          (show 0 < 1 - t by grind)) (show 0 < q.x - p.x by grind)
      grind
  · have hgt : q.x < p.x := by grind
    have hm : max p.x q.x = p.x := by grind
    rw [hm] at b h ⊢
    by_cases h0 : t = 0
    · subst h0
      grind
    · have a3 := Rat.mul_pos
        (Rat.mul_pos (Rat.mul_pos (show 0 < t by grind) (show 0 < t by grind))
          (show 0 < t by grind)) (show 0 < p.x - q.x by grind)
      grind
/-- **The height of the arc runs from one end to the other with no turn**, with no swell: at
the parameter `t` it is `3 t² - 2 t³` of the way from `p` to `q`. -/
theorem around_y (p q : Vec) (reach t : Rat) :
    ((around p q reach).pointAt t).y = p.y + (q.y - p.y) * (t * t * (3 - 2 * t)) := by
  simp only [around, pointAt, blossom, Vec.lerp]
  grind

/-- **The arc stays between its ends and the reach**, with no swell and neither end past the
reach: it is never left of the nearer end, never right of the reach, and never above the higher
end or below the lower. -/
theorem around_within (p q : Vec) {reach : Rat} (h : max p.x q.x ≤ reach) {t : Rat}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Box.mk (min p.x q.x) (min p.y q.y) reach (max p.y q.y)).Contains
      ((around p q reach).pointAt t) := by
  have wide : (Box.mk (min p.x q.x) (min p.y q.y) (reach + (reach - max p.x q.x) / 3)
      (max p.y q.y)).Contains ((around p q reach).pointAt t) := by
    refine contains_pointAt_of ?_ ?_ ?_ ?_ ht0 ht1 <;> simp only [Box.Contains, around] <;> grind
  have hx := around_x_le p q 0 h ht0 ht1
  exact ⟨wide.1, hx, wide.2.2.1, wide.2.2.2⟩

/-- **The arc leaves and arrives level**, with no swell: its velocity at each end has no part
along `y`. An arc out of the side of a box leaves at a right angle to the side. -/
theorem around_level (p q : Vec) (reach : Rat) :
    ((around p q reach).velocity 0).y = 0 ∧ ((around p q reach).velocity 1).y = 0 := by
  rw [velocity_zero, velocity_one]
  constructor <;> simp only [around, Vec.scale, Vec.sub_def] <;> grind

/-- **The arc of moved ends round a moved line is the arc, moved.** -/
theorem around_move (d p q : Vec) (reach swell : Rat) :
    around (p + d) (q + d) (reach + d.x) swell = (around p q reach swell).move d := by
  apply ext <;> apply Vec.ext <;> simp only [around, move, map, Vec.add_def] <;> grind

/-- **The arc backwards is the arc from `q` to `p`.** -/
theorem around_reverse (p q : Vec) (reach swell : Rat) :
    (around p q reach swell).reverse = around q p reach swell := by
  apply ext <;> apply Vec.ext <;> simp only [around, reverse] <;> grind

end Cubic

end Whatwg.Svg.Value
