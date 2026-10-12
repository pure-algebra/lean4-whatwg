import Whatwg.Svg.Geometry.Cubic.Laws

/-!
# Whatwg.Svg.Geometry.Box

Owner: a box with sides along the axes, and the box that holds a cubic segment (slice S11 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-52). A program asks for one to size a picture to what it
draws, to keep two marks apart, or to find what is under a point.

A `Box` is its least and its greatest `x` and `y`. `Contains` and `Includes` read it as closed:
its edges belong to it. `Disjoint` reads it as a consumer of pixels does, so two boxes that
share an edge and no area are apart.

**The box of a segment.** `Cubic.box` is the box of the four points of a segment. It holds the
whole segment (`Cubic.contains_pointAt`): a point of the segment is three rounds of steps
between points of the box, and a step between two points of a box stays in it
(`Box.contains_lerp`). It is not the least box that holds the segment, which takes the roots of
the derivative. It can be made as tight as is wanted with no root: the box of a part lies in
the box of the whole (`Cubic.includes_between`), so the union of the boxes of the parts of a
split holds the segment and lies in its box.

What this module does not claim: the least box of a segment; the box of an elliptical arc; the
box of a stroke, which is wider than its centre line by half its width.
-/

namespace Whatwg.Svg.Value

/-- A box with sides along the axes: `x0 ≤ x ≤ x1` and `y0 ≤ y ≤ y1`. -/
structure Box where
  x0 : Rat
  y0 : Rat
  x1 : Rat
  y1 : Rat
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Box

/-- The box of one point. -/
def ofPoint (p : Vec) : Box := ⟨p.x, p.y, p.x, p.y⟩

/-- The box with two points at opposite corners, in either order. -/
def ofCorners (a b : Vec) : Box := ⟨min a.x b.x, min a.y b.y, max a.x b.x, max a.y b.y⟩

/-- The box by a corner, a width and a height. -/
def ofSize (corner : Vec) (width height : Rat) : Box :=
  ⟨corner.x, corner.y, corner.x + width, corner.y + height⟩

/-- The least box that holds two boxes. -/
def union (a b : Box) : Box := ⟨min a.x0 b.x0, min a.y0 b.y0, max a.x1 b.x1, max a.y1 b.y1⟩

/-- The least box that holds a box and a point. -/
def grow (b : Box) (p : Vec) : Box := b.union (ofPoint p)

/-- The least box that holds a point and the points of a list. -/
def ofPoints (p : Vec) (ps : List Vec) : Box := ps.foldl grow (ofPoint p)

/-- The least box that holds the points of a list, and none for no point. -/
def ofList? : List Vec → Option Box
  | [] => none
  | p :: ps => some (ofPoints p ps)

/-- The least box that holds the boxes of a list, and none for no box. -/
def unionAll? : List Box → Option Box
  | [] => none
  | b :: bs => some (bs.foldl union b)

/-- The point is in the box, its edges included. -/
def Contains (b : Box) (p : Vec) : Prop := b.x0 ≤ p.x ∧ p.x ≤ b.x1 ∧ b.y0 ≤ p.y ∧ p.y ≤ b.y1

instance (b : Box) (p : Vec) : Decidable (b.Contains p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The box `a` holds the box `b`. -/
def Includes (a b : Box) : Prop := a.x0 ≤ b.x0 ∧ b.x1 ≤ a.x1 ∧ a.y0 ≤ b.y0 ∧ b.y1 ≤ a.y1

instance (a b : Box) : Decidable (a.Includes b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The two boxes share no area: one ends where the other starts, or before, along an axis. -/
def Disjoint (a b : Box) : Prop := a.x1 ≤ b.x0 ∨ b.x1 ≤ a.x0 ∨ a.y1 ≤ b.y0 ∨ b.y1 ≤ a.y0

instance (a b : Box) : Decidable (a.Disjoint b) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- The width. -/
def width (b : Box) : Rat := b.x1 - b.x0

/-- The height. -/
def height (b : Box) : Rat := b.y1 - b.y0

/-- The corner of the least `x` and `y`. -/
def corner (b : Box) : Vec := ⟨b.x0, b.y0⟩

/-- The corner of the greatest `x` and `y`. -/
def far (b : Box) : Vec := ⟨b.x1, b.y1⟩

/-- The middle. -/
def center (b : Box) : Vec := ⟨(b.x0 + b.x1) / 2, (b.y0 + b.y1) / 2⟩

/-- The middle of the side of least `y`: the top, on a screen. -/
def top (b : Box) : Vec := ⟨(b.x0 + b.x1) / 2, b.y0⟩

/-- The middle of the side of greatest `y`: the bottom, on a screen. -/
def bottom (b : Box) : Vec := ⟨(b.x0 + b.x1) / 2, b.y1⟩

/-- The middle of the side of least `x`. -/
def left (b : Box) : Vec := ⟨b.x0, (b.y0 + b.y1) / 2⟩

/-- The middle of the side of greatest `x`. -/
def right (b : Box) : Vec := ⟨b.x1, (b.y0 + b.y1) / 2⟩

/-- The box moved by `d`. -/
def move (d : Vec) (b : Box) : Box := ⟨b.x0 + d.x, b.y0 + d.y, b.x1 + d.x, b.y1 + d.y⟩

/-- The box wider by `m` on every side; narrower for a negative `m`. -/
def pad (m : Rat) (b : Box) : Box := ⟨b.x0 - m, b.y0 - m, b.x1 + m, b.y1 + m⟩

/-! ## Laws -/

theorem contains_ofPoint (p : Vec) : (ofPoint p).Contains p := by
  simp only [Contains, ofPoint]
  grind

theorem includes_refl (b : Box) : b.Includes b := by
  simp only [Includes]
  grind

theorem includes_trans {a b c : Box} (hab : a.Includes b) (hbc : b.Includes c) : a.Includes c := by
  simp only [Includes] at *
  grind

/-- A box that holds a box holds its points. -/
theorem contains_of_includes {a b : Box} {p : Vec} (hab : a.Includes b) (hp : b.Contains p) :
    a.Contains p := by
  simp only [Includes, Contains] at *
  grind

theorem includes_union_left (a b : Box) : (a.union b).Includes a := by
  simp only [Includes, union]
  grind

theorem includes_union_right (a b : Box) : (a.union b).Includes b := by
  simp only [Includes, union]
  grind

/-- The union is the least box that holds both. -/
theorem includes_union {a b c : Box} (ha : c.Includes a) (hb : c.Includes b) :
    c.Includes (a.union b) := by
  simp only [Includes, union] at *
  grind

theorem contains_union_left {a : Box} {p : Vec} (b : Box) (h : a.Contains p) :
    (a.union b).Contains p :=
  contains_of_includes (includes_union_left a b) h

theorem contains_union_right {b : Box} {p : Vec} (a : Box) (h : b.Contains p) :
    (a.union b).Contains p :=
  contains_of_includes (includes_union_right a b) h

theorem union_comm (a b : Box) : a.union b = b.union a := by
  simp only [union, Box.mk.injEq]
  grind

theorem union_self (a : Box) : a.union a = a := by
  cases a
  simp only [union, Box.mk.injEq]
  grind

theorem contains_grow_self (b : Box) (p : Vec) : (b.grow p).Contains p :=
  contains_union_right b (contains_ofPoint p)

theorem includes_grow (b : Box) (p : Vec) : (b.grow p).Includes b := includes_union_left b _

/-- The box of a list grown from a box holds that box. -/
theorem includes_foldl_grow : ∀ (ps : List Vec) (b : Box), (ps.foldl grow b).Includes b
  | [], b => includes_refl b
  | p :: ps, b => includes_trans (includes_foldl_grow ps (b.grow p)) (includes_grow b p)

/-- The box of a list grown from a box holds every point of the list. -/
theorem contains_foldl_grow : ∀ (ps : List Vec) (b : Box) (q : Vec), q ∈ ps →
    (ps.foldl grow b).Contains q
  | p :: ps, b, q, h => by
    cases h with
    | head => exact contains_of_includes (includes_foldl_grow ps _) (contains_grow_self b _)
    | tail _ h' => exact contains_foldl_grow ps (b.grow p) q h'

/-- **The box of some points holds each of them.** -/
theorem contains_ofPoints (p : Vec) (ps : List Vec) (q : Vec) (h : q ∈ p :: ps) :
    (ofPoints p ps).Contains q := by
  cases h with
  | head => exact contains_of_includes (includes_foldl_grow ps _) (contains_ofPoint _)
  | tail _ h' => exact contains_foldl_grow ps (ofPoint p) q h'

/-- A step between two numbers of an interval stays in it. -/
theorem step_mem {lo hi a b t : Rat} (ha0 : lo ≤ a) (ha1 : a ≤ hi) (hb0 : lo ≤ b) (hb1 : b ≤ hi)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : lo ≤ a + t * (b - a) ∧ a + t * (b - a) ≤ hi := by
  have e : a + t * (b - a) = (1 - t) * a + t * b := by grind
  have h1' : 0 ≤ 1 - t := by grind
  have p1 : (1 - t) * lo ≤ (1 - t) * a := Rat.mul_le_mul_of_nonneg_left ha0 h1'
  have p2 : t * lo ≤ t * b := Rat.mul_le_mul_of_nonneg_left hb0 h0
  have p3 : (1 - t) * a ≤ (1 - t) * hi := Rat.mul_le_mul_of_nonneg_left ha1 h1'
  have p4 : t * b ≤ t * hi := Rat.mul_le_mul_of_nonneg_left hb1 h0
  rw [e]
  constructor <;> grind

/-- **A box is convex**: a step between two of its points, at a parameter from `0` to `1`,
stays in it. -/
theorem contains_lerp {b : Box} {p q : Vec} (hp : b.Contains p) (hq : b.Contains q) {t : Rat}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : b.Contains (p.lerp q t) := by
  have hx := step_mem hp.1 hp.2.1 hq.1 hq.2.1 h0 h1
  have hy := step_mem hp.2.2.1 hp.2.2.2 hq.2.2.1 hq.2.2.2 h0 h1
  exact ⟨hx.1, hx.2, hy.1, hy.2⟩

/-- A moved box holds the moved points, and no others. -/
theorem contains_move (d : Vec) (b : Box) (p : Vec) : (b.move d).Contains (p + d) ↔ b.Contains p := by
  simp only [Contains, move, Vec.add_def]
  grind

/-- The box by a moved corner and a size is the box, moved. -/
theorem ofSize_move (d corner : Vec) (width height : Rat) :
    ofSize (corner + d) width height = (ofSize corner width height).move d := by
  simp only [ofSize, move, Vec.add_def, Box.mk.injEq]
  grind

theorem move_union (d : Vec) (a b : Box) : (a.union b).move d = (a.move d).union (b.move d) := by
  simp only [union, move, Box.mk.injEq]
  grind

/-- A box padded by no less than nothing holds the box. -/
theorem includes_pad {m : Rat} (h : 0 ≤ m) (b : Box) : (b.pad m).Includes b := by
  simp only [Includes, pad]
  grind

theorem disjoint_comm {a b : Box} (h : a.Disjoint b) : b.Disjoint a := by
  simp only [Disjoint] at *
  grind

/-- Two boxes moved together are apart when they were. -/
theorem disjoint_move (d : Vec) {a b : Box} (h : a.Disjoint b) : (a.move d).Disjoint (b.move d) := by
  simp only [Disjoint, move] at *
  grind

/-- Boxes that are apart share no point off their edges: a point inside one, strictly, is not
in the other. -/
theorem not_contains_of_disjoint {a b : Box} {p : Vec} (h : a.Disjoint b)
    (hp : a.x0 < p.x ∧ p.x < a.x1 ∧ a.y0 < p.y ∧ p.y < a.y1) : ¬ b.Contains p := by
  simp only [Disjoint, Contains] at *
  grind

end Box

namespace Cubic

/-- The box of the four points of a segment. It holds the segment (`contains_pointAt`). -/
def box (c : Cubic) : Box := Box.ofPoints c.p0 [c.p1, c.p2, c.p3]

/-- The least box that holds the boxes of the segments of a list, and none for no segment. -/
def boxAll? (cs : List Cubic) : Option Box := Box.unionAll? (cs.map box)

theorem contains_p0 (c : Cubic) : c.box.Contains c.p0 :=
  Box.contains_ofPoints _ _ _ List.mem_cons_self

theorem contains_p1 (c : Cubic) : c.box.Contains c.p1 :=
  Box.contains_ofPoints _ _ _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem contains_p2 (c : Cubic) : c.box.Contains c.p2 :=
  Box.contains_ofPoints _ _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem contains_p3 (c : Cubic) : c.box.Contains c.p3 :=
  Box.contains_ofPoints _ _ _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- A box that holds the four points holds every blossom at parameters from `0` to `1`. -/
theorem contains_blossom_of {b : Box} {c : Cubic} (h0 : b.Contains c.p0) (h1 : b.Contains c.p1)
    (h2 : b.Contains c.p2) (h3 : b.Contains c.p3) {r s t : Rat} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : b.Contains (c.blossom r s t) :=
  Box.contains_lerp
    (Box.contains_lerp (Box.contains_lerp h0 h1 hr0 hr1) (Box.contains_lerp h1 h2 hr0 hr1) hs0 hs1)
    (Box.contains_lerp (Box.contains_lerp h1 h2 hr0 hr1) (Box.contains_lerp h2 h3 hr0 hr1) hs0 hs1)
    ht0 ht1

/-- **The box of the control points holds the segment.** -/
theorem contains_pointAt (c : Cubic) {t : Rat} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    c.box.Contains (c.pointAt t) :=
  contains_blossom_of c.contains_p0 c.contains_p1 c.contains_p2 c.contains_p3 h0 h1 h0 h1 h0 h1

/-- A box that holds the four points holds the segment. -/
theorem contains_pointAt_of {b : Box} {c : Cubic} (h0 : b.Contains c.p0) (h1 : b.Contains c.p1)
    (h2 : b.Contains c.p2) (h3 : b.Contains c.p3) {t : Rat} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    b.Contains (c.pointAt t) :=
  contains_blossom_of h0 h1 h2 h3 ht0 ht1 ht0 ht1 ht0 ht1

/-- The box of a segment is the least box that holds its four points. -/
theorem includes_box {b : Box} {c : Cubic} (h0 : b.Contains c.p0) (h1 : b.Contains c.p1)
    (h2 : b.Contains c.p2) (h3 : b.Contains c.p3) : b.Includes c.box := by
  simp only [box, Box.ofPoints, List.foldl, Box.grow, Box.union, Box.ofPoint, Box.Includes,
    Box.Contains] at *
  grind

/-- **The box of a part lies in the box of the whole**, for two parameters from `0` to `1`. -/
theorem includes_between (c : Cubic) {a b : Rat} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) : c.box.Includes (c.between a b).box :=
  includes_box
    (contains_blossom_of c.contains_p0 c.contains_p1 c.contains_p2 c.contains_p3 ha0 ha1 ha0 ha1 ha0 ha1)
    (contains_blossom_of c.contains_p0 c.contains_p1 c.contains_p2 c.contains_p3 ha0 ha1 ha0 ha1 hb0 hb1)
    (contains_blossom_of c.contains_p0 c.contains_p1 c.contains_p2 c.contains_p3 ha0 ha1 hb0 hb1 hb0 hb1)
    (contains_blossom_of c.contains_p0 c.contains_p1 c.contains_p2 c.contains_p3 hb0 hb1 hb0 hb1 hb0 hb1)

/-- The box of a moved segment is the box, moved. -/
theorem move_box (d : Vec) (c : Cubic) : (c.move d).box = c.box.move d := by
  simp only [box, move, map, Box.ofPoints, List.foldl, Box.grow, Box.union, Box.ofPoint, Box.move,
    Vec.add_def, Box.mk.injEq]
  grind

end Cubic

end Whatwg.Svg.Value
