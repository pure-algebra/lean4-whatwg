import Whatwg.Svg.Geometry.Outline

/-!
# Whatwg.Svg.Geometry.Outline.Laws

Owner: the laws of the closed outlines (slice S11 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-55).
They say three things of the outlines of `Whatwg/Svg/Geometry/Outline.lean`, and each holds for
every rational argument that its statement does not bound.

- **Closed** (`closed_rect`, `closed_roundRect`, `closed_ellipse`, `closed_circle`): each
  outline is a chain that ends where it starts, for every box, radius and roundness.
- **Within its box** (`rect_within`, `roundRect_within`, `roundRect_contains`,
  `ellipse_within`): the box of every segment of an outline lies in the box of the outline, so
  every point of the outline does. A box must not be inside out (`x0 ≤ x1`, `y0 ≤ y1`), and
  the radii of an ellipse must not be negative. A round corner asks for a roundness from `0` to
  `1`: a control point is that share of the way from an end to the corner (`corner_within`),
  and at a share above `1`, with a radius above zero, it is outside the box. The radius of a
  box needs no bound, since it is fitted (`fitRadius_nonneg`, `fitRadius_le_half_width`,
  `fitRadius_le_half_height`, `fitRadius_le`).
- **Moved** (`rect_move`, `roundRect_move`, `ring_move`, `ellipse_move`): the outline of a
  moved box is the outline, moved. A move keeps the width and the height of a box
  (`Box.width_move`, `Box.height_move`), so it keeps the fitted radius (`fitRadius_move`).

`corner_near_circle` is a finite evaluation and no law of every parameter: at five parameters
the quarter turn of radius one, at the default roundness, has the square of its distance from
the centre between `0.9997` and `1.0006`. The kernel evaluates it.

What this module does not claim: that the quarter turn is that near the circle at every
parameter; that the inner outline of a frame lies in the box of the frame.
-/

namespace Whatwg.Svg.Value

namespace Box

/-- A moved box has the width of the box. -/
theorem width_move (d : Vec) (b : Box) : (b.move d).width = b.width := by
  simp only [move, width]
  grind

/-- A moved box has the height of the box. -/
theorem height_move (d : Vec) (b : Box) : (b.move d).height = b.height := by
  simp only [move, height]
  grind

/-- A moved box, padded, is the padded box, moved. -/
theorem pad_move (d : Vec) (m : Rat) (b : Box) : (b.move d).pad m = (b.pad m).move d := by
  simp only [pad, move, Box.mk.injEq]
  grind

end Box

namespace Cubic

/-! ## Each outline is a chain that ends where it starts -/

/-- The four sides of a box are a closed outline. -/
theorem closed_rect (b : Box) : Closed (rect b) = true := by
  simp only [Closed, rect, chained_cons, chained_singleton, line, List.getLast?_cons_cons,
    List.getLast?_singleton, Option.map_some, decide_true, Bool.and_self, beq_self_eq_true]

/-- A box with round corners is a closed outline, for every radius and roundness. -/
theorem closed_roundRect (b : Box) (r k : Rat) : Closed (roundRect b r k) = true := by
  simp only [Closed, roundRect, chained_cons, chained_singleton, line, corner,
    List.getLast?_cons_cons, List.getLast?_singleton, Option.map_some, decide_true, Bool.and_self,
    beq_self_eq_true]

/-- The four quarter turns of an ellipse are a closed outline. -/
theorem closed_ellipse (center : Vec) (rx ry k : Rat) : Closed (ellipse center rx ry k) = true := by
  simp only [Closed, ellipse, chained_cons, chained_singleton, corner, List.getLast?_cons_cons,
    List.getLast?_singleton, Option.map_some, decide_true, Bool.and_self, beq_self_eq_true]

/-- The four quarter turns of a circle are a closed outline. -/
theorem closed_circle (center : Vec) (r k : Rat) : Closed (circle center r k) = true :=
  closed_ellipse center r r k

/-! ## The fitted radius -/

/-- The fitted radius is no less than zero. -/
theorem fitRadius_nonneg (b : Box) (r : Rat) : 0 ≤ fitRadius b r := by
  simp only [fitRadius]
  grind

/-- The fitted radius is no more than half the width of a box that is not inside out. -/
theorem fitRadius_le_half_width (b : Box) (r : Rat) (h : b.x0 ≤ b.x1) :
    fitRadius b r ≤ b.width / 2 := by
  simp only [fitRadius, Box.width]
  grind

/-- The fitted radius is no more than half the height of a box that is not inside out. -/
theorem fitRadius_le_half_height (b : Box) (r : Rat) (h : b.y0 ≤ b.y1) :
    fitRadius b r ≤ b.height / 2 := by
  simp only [fitRadius, Box.height]
  grind

/-- The fitted radius is no more than the radius asked for, when that is no less than zero. -/
theorem fitRadius_le (b : Box) (r : Rat) (h : 0 ≤ r) : fitRadius b r ≤ r := by
  simp only [fitRadius]
  grind

/-! ## Each outline stays in its box -/

/-- A box that holds two points holds the box of the straight segment between them. -/
theorem line_within {b : Box} {p q : Vec} (hp : b.Contains p) (hq : b.Contains q) :
    b.Includes (line p q).box :=
  includes_box hp (Box.contains_lerp hp hq (by grind) (by grind))
    (Box.contains_lerp hp hq (by grind) (by grind)) hq

/-- A box that holds the two ends and the corner holds the box of the segment that rounds the
corner, for a roundness from `0` to `1`. -/
theorem corner_within {b : Box} {a c e : Vec} {k : Rat} (ha : b.Contains a) (hc : b.Contains c)
    (he : b.Contains e) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) : b.Includes (corner a c e k).box :=
  includes_box ha (Box.contains_lerp ha hc hk0 hk1) (Box.contains_lerp he hc hk0 hk1) he

/-- The box of each side of a box lies in the box. -/
theorem rect_within (b : Box) (hx : b.x0 ≤ b.x1) (hy : b.y0 ≤ b.y1) (c : Cubic) (h : c ∈ rect b) :
    b.Includes c.box := by
  simp only [rect, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> refine line_within ?_ ?_ <;>
    simp only [Box.Contains] <;> grind

/-- The box of each side and of each corner of a box with round corners lies in the box, for a
roundness from `0` to `1`. -/
theorem roundRect_within (b : Box) (r k : Rat) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hx : b.x0 ≤ b.x1)
    (hy : b.y0 ≤ b.y1) (c : Cubic) (h : c ∈ roundRect b r k) : b.Includes c.box := by
  have f0 := fitRadius_nonneg b r
  have fx := fitRadius_le_half_width b r hx
  have fy := fitRadius_le_half_height b r hy
  simp only [Box.width, Box.height] at fx fy
  simp only [roundRect, List.mem_cons, List.mem_nil_iff, or_false] at h
  generalize fitRadius b r = f at f0 fx fy h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine line_within ?_ ?_ <;> simp only [Box.Contains] <;> grind
  · refine corner_within ?_ ?_ ?_ hk0 hk1 <;> simp only [Box.Contains] <;> grind
  · refine line_within ?_ ?_ <;> simp only [Box.Contains] <;> grind
  · refine corner_within ?_ ?_ ?_ hk0 hk1 <;> simp only [Box.Contains] <;> grind
  · refine line_within ?_ ?_ <;> simp only [Box.Contains] <;> grind
  · refine corner_within ?_ ?_ ?_ hk0 hk1 <;> simp only [Box.Contains] <;> grind
  · refine line_within ?_ ?_ <;> simp only [Box.Contains] <;> grind
  · refine corner_within ?_ ?_ ?_ hk0 hk1 <;> simp only [Box.Contains] <;> grind

/-- **A box with round corners stays in its box**: every point of every side and corner, for a
roundness from `0` to `1`. -/
theorem roundRect_contains (b : Box) (r k : Rat) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hx : b.x0 ≤ b.x1)
    (hy : b.y0 ≤ b.y1) (c : Cubic) (h : c ∈ roundRect b r k) {t : Rat} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    b.Contains (c.pointAt t) :=
  Box.contains_of_includes (roundRect_within b r k hk0 hk1 hx hy c h) (c.contains_pointAt h0 h1)

/-- The box of each quarter turn of an ellipse lies in the box of the two radii about the
centre, for radii that are not negative and a roundness from `0` to `1`. -/
theorem ellipse_within (center : Vec) (rx ry k : Rat) (hrx : 0 ≤ rx) (hry : 0 ≤ ry) (hk0 : 0 ≤ k)
    (hk1 : k ≤ 1) (c : Cubic) (h : c ∈ ellipse center rx ry k) :
    (Box.mk (center.x - rx) (center.y - ry) (center.x + rx) (center.y + ry)).Includes c.box := by
  simp only [ellipse, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> refine corner_within ?_ ?_ ?_ hk0 hk1 <;>
    simp only [Box.Contains] <;> grind

/-! ## The outline of a moved box is the outline, moved -/

/-- The segment that rounds a moved corner is the segment, moved. -/
theorem corner_move (d a c b : Vec) (k : Rat) :
    corner (a + d) (c + d) (b + d) k = (corner a c b k).move d := by
  apply ext <;> apply Vec.ext <;> simp only [corner, move, map, Vec.lerp, Vec.add_def] <;> grind

/-- The sides of a moved box are the sides, moved. -/
theorem rect_move (d : Vec) (b : Box) : rect (b.move d) = (rect b).map (move d) := by
  simp only [rect, Box.move, List.map_cons, List.map_nil, move_line, Vec.add_def]

/-- A moved box takes the fitted radius of the box. -/
theorem fitRadius_move (d : Vec) (b : Box) (r : Rat) : fitRadius (b.move d) r = fitRadius b r := by
  simp only [fitRadius, Box.width_move, Box.height_move]

/-- The outline of a moved box with round corners is the outline, moved. -/
theorem roundRect_move (d : Vec) (b : Box) (r k : Rat) :
    roundRect (b.move d) r k = (roundRect b r k).map (move d) := by
  simp only [roundRect, fitRadius_move, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply ext <;> apply Vec.ext <;>
    simp only [line, corner, move, map, Vec.lerp, Vec.add_def, Box.move] <;> grind

/-- The frame of a moved box is the frame, moved. -/
theorem ring_move (d : Vec) (b : Box) (r thickness k : Rat) :
    ring (b.move d) r thickness k = (ring b r thickness k).map (List.map (move d)) := by
  unfold ring
  rw [Box.width_move, Box.height_move]
  split
  · simp only [List.map_cons, List.map_nil, roundRect_move]
  · simp only [List.map_cons, List.map_nil, Box.pad_move, roundRect_move]

/-- The ellipse about a moved centre is the ellipse, moved. -/
theorem ellipse_move (d center : Vec) (rx ry k : Rat) :
    ellipse (center + d) rx ry k = (ellipse center rx ry k).map (move d) := by
  simp only [ellipse, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ext <;> apply Vec.ext <;>
    simp only [corner, move, map, Vec.lerp, Vec.add_def] <;> grind

/-! ## How round a corner is -/

/-- At five parameters, the quarter turn of radius one at the default roundness has the square
of its distance from the centre between `0.9997` and `1.0006`: a finite evaluation, by the
kernel. -/
theorem corner_near_circle :
    ∀ t ∈ [(0 : Rat), 1 / 4, 1 / 2, 3 / 4, 1],
      (9997 : Rat) / 10000 < ((corner ⟨1, 0⟩ ⟨1, 1⟩ ⟨0, 1⟩).pointAt t).normSq ∧
        ((corner ⟨1, 0⟩ ⟨1, 1⟩ ⟨0, 1⟩).pointAt t).normSq < (10006 : Rat) / 10000 := by
  decide +kernel

end Cubic

end Whatwg.Svg.Value
