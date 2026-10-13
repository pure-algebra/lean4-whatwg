import Whatwg.Svg.Scene.Moves

/-!
# Whatwg.Svg.Scene.Extent

Owner: the room that a thing takes, in whole units (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A layout asks three things of what it places: where it is, what it lies inside, and what it
does not touch. Each is a fact of a box with sides along the axes. This layer counts in whole
units, so the box is of whole units too, beside `IVec` and `ICubic` of
`Whatwg/Svg/Scene/Moves.lean`. The box of exact numbers is `Box` of
`Whatwg/Svg/Geometry/Box.lean`, and a program under the strict ceiling cannot call it.

- `IBox`: from `x0` to `x1` across and from `y0` to `y1` down. The first of each pair is in the
  box and the second is not, so two boxes that share an edge share no point. lean4-effect4's
  `Rect` has the same four fields.
- `IBox.Holds b p`: the point is in the box. `IBox.Inside a b`: every point of `a` is in `b`.
  `IBox.Disjoint a b`: one axis holds the two apart.
- `IBox.hull a b`: the least box that holds both. `IBox.merge` is the same where either may be
  missing, and `IBox.hullAll` the least box that holds each of a list: none for the empty
  list.
- `IBox.grow`: a margin on each side.
- `Boxed α`: **a thing that takes room.** A type gives the box of each of its things, and shows
  that the box of a moved thing is the box, moved. `boxAll` is the room of a list of them. A
  box, a point and a segment are instances: a point has the box with no room at it
  (`IBox.ofPoint`), and a segment the hull of its four points.

What the laws say:

- `Inside` is an order (`Inside.refl`, `Inside.trans`, `Inside.antisymm`), and `hull` is its
  least upper bound (`inside_hull_left`, `inside_hull_right`, `hull_least`). So `hull` does not
  depend on the order or the grouping of its boxes (`hull_comm`, `hull_assoc`, `hull_self`),
  and a box inside another adds nothing to it (`hull_of_inside`).
- `merge` has the missing box as its identity and is associative (`merge_none_left`,
  `merge_none_right`, `merge_assoc`). The room of two lists in a row is the `merge` of their
  rooms (`hullAll_append`), and each of the two is inside it (`inside_merge_left`,
  `inside_merge_right`). Every box of a list is inside the room of the list
  (`inside_hullAll`), and the room is inside every box that holds them all (`hullAll_least`).
- `Disjoint` is what its name says. Boxes that are disjoint share no point
  (`Disjoint.not_holds`), and two boxes that each have a point and are not disjoint share one
  (`disjoint_iff`). Boxes inside disjoint boxes are disjoint (`Disjoint.mono`).
- A move changes none of this. Moved boxes are inside each other, disjoint, or the hull of
  each other exactly when the boxes are (`inside_move`, `disjoint_move`, `hull_move`,
  `holds_move`), a moved box has its width and its height (`width_move`, `height_move`), and a
  margin and a move may be taken in either order (`grow_move`).
- `Boxed.commutes`: the box of a thing is `Commutes` of `Moves.lean`, so a box that was stored
  stands for the box of the moved thing (`Commutes.stored`). `boxAll_move` is the same for the
  room of a list, and `boxAll_append`, `inside_boxAll` are the laws of `hullAll` for things.

What this module does not claim: that the box of an `ICubic` holds the curve. It is the box of
the four points; that a segment lies inside the box of its points is a law of exact numbers
(`Cubic.contains_pointAt` of the geometry). A box whose second edge is before its first holds
no point, and the laws that need a box with a point say so (`Solid`).

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- **A box of whole units** with sides along the axes: from `x0` to `x1` across and from `y0`
to `y1` down. The first of each pair is in the box and the second is not. -/
structure IBox where
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace IBox

theorem ext {a b : IBox} (h0 : a.x0 = b.x0) (h1 : a.y0 = b.y0) (h2 : a.x1 = b.x1)
    (h3 : a.y1 = b.y1) : a = b := by
  cases a
  cases b
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

/-- The box at a corner, with a width and a height. -/
def ofSize (corner : IVec) (w h : Int) : IBox := ⟨corner.x, corner.y, corner.x + w, corner.y + h⟩

/-- The box with no room at a point. -/
def ofPoint (p : IVec) : IBox := ⟨p.x, p.y, p.x, p.y⟩

/-- How far the box reaches across. -/
def width (b : IBox) : Int := b.x1 - b.x0

/-- How far the box reaches down. -/
def height (b : IBox) : Int := b.y1 - b.y0

/-- The first corner of the box. -/
def corner (b : IBox) : IVec := ⟨b.x0, b.y0⟩

/-- **The point is in the box.** -/
def Holds (b : IBox) (p : IVec) : Prop := b.x0 ≤ p.x ∧ p.x < b.x1 ∧ b.y0 ≤ p.y ∧ p.y < b.y1

instance (b : IBox) (p : IVec) : Decidable (b.Holds p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The box has a point: it is one unit wide and one unit high at least. -/
def Solid (b : IBox) : Prop := b.x0 < b.x1 ∧ b.y0 < b.y1

instance (b : IBox) : Decidable b.Solid := inferInstanceAs (Decidable (_ ∧ _))

/-- **`a` is inside `b`**: `b` reaches as far as `a` on each of the four sides. -/
def Inside (a b : IBox) : Prop := b.x0 ≤ a.x0 ∧ a.x1 ≤ b.x1 ∧ b.y0 ≤ a.y0 ∧ a.y1 ≤ b.y1

instance (a b : IBox) : Decidable (a.Inside b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- **The two boxes share no room**: one ends, across or down, where the other begins or
before. -/
def Disjoint (a b : IBox) : Prop := a.x1 ≤ b.x0 ∨ b.x1 ≤ a.x0 ∨ a.y1 ≤ b.y0 ∨ b.y1 ≤ a.y0

instance (a b : IBox) : Decidable (a.Disjoint b) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- **The least box that holds both.** -/
def hull (a b : IBox) : IBox := ⟨min a.x0 b.x0, min a.y0 b.y0, max a.x1 b.x1, max a.y1 b.y1⟩

/-- The box with a margin on each side. -/
def grow (left top right bottom : Int) (b : IBox) : IBox :=
  ⟨b.x0 - left, b.y0 - top, b.x1 + right, b.y1 + bottom⟩

/-- The least box that holds both, where either may be missing. -/
def merge : Option IBox → Option IBox → Option IBox
  | none, b => b
  | some a, none => some a
  | some a, some b => some (hull a b)

/-- **The least box that holds each box of a list**: none for the empty list. -/
def hullAll : List IBox → Option IBox
  | [] => none
  | b :: bs => merge (some b) (hullAll bs)

/-- A box moves with its four sides. -/
instance : Moves IVec IBox where
  move d b := ⟨b.x0 + d.x, b.y0 + d.y, b.x1 + d.x, b.y1 + d.y⟩
  move_zero b := ext (Int.add_zero b.x0) (Int.add_zero b.y0) (Int.add_zero b.x1) (Int.add_zero b.y1)
  move_move d e b := ext (Int.add_assoc b.x0 d.x e.x) (Int.add_assoc b.y0 d.y e.y)
    (Int.add_assoc b.x1 d.x e.x) (Int.add_assoc b.y1 d.y e.y)

theorem move_x0 (d : IVec) (b : IBox) : (Moves.move d b).x0 = b.x0 + d.x := rfl

theorem move_y0 (d : IVec) (b : IBox) : (Moves.move d b).y0 = b.y0 + d.y := rfl

theorem move_x1 (d : IVec) (b : IBox) : (Moves.move d b).x1 = b.x1 + d.x := rfl

theorem move_y1 (d : IVec) (b : IBox) : (Moves.move d b).y1 = b.y1 + d.y := rfl

/-! ## Arithmetic that the laws below use, each once -/

private theorem le_min_of {a b c : Int} (h : c ≤ a) (k : c ≤ b) : c ≤ min a b := by omega

private theorem max_le_of {a b c : Int} (h : a ≤ c) (k : b ≤ c) : max a b ≤ c := by omega

private theorem max_lt_of {a b c : Int} (h : a < c) (k : b < c) : max a b < c := by omega

private theorem min_add (a b d : Int) : min (a + d) (b + d) = min a b + d := by omega

private theorem max_add (a b d : Int) : max (a + d) (b + d) = max a b + d := by omega

private theorem add_le_add_iff (a b c : Int) : a + c ≤ b + c ↔ a ≤ b :=
  ⟨fun h => by omega, fun h => by omega⟩

private theorem add_lt_add_iff (a b c : Int) : a + c < b + c ↔ a < b :=
  ⟨fun h => by omega, fun h => by omega⟩

/-! ## Inside -/

/-- A box is inside itself. -/
theorem Inside.refl (a : IBox) : a.Inside a :=
  ⟨Int.le_refl _, Int.le_refl _, Int.le_refl _, Int.le_refl _⟩

/-- A box inside a box inside a third is inside the third. -/
theorem Inside.trans {a b c : IBox} (h : a.Inside b) (k : b.Inside c) : a.Inside c :=
  ⟨Int.le_trans k.1 h.1, Int.le_trans h.2.1 k.2.1, Int.le_trans k.2.2.1 h.2.2.1,
    Int.le_trans h.2.2.2 k.2.2.2⟩

/-- Two boxes inside each other are one box. -/
theorem Inside.antisymm {a b : IBox} (h : a.Inside b) (k : b.Inside a) : a = b :=
  ext (Int.le_antisymm k.1 h.1) (Int.le_antisymm k.2.2.1 h.2.2.1) (Int.le_antisymm h.2.1 k.2.1)
    (Int.le_antisymm h.2.2.2 k.2.2.2)

/-- A point of a box is a point of every box that the box is inside. -/
theorem Holds.mono {a b : IBox} {p : IVec} (h : a.Inside b) (hp : a.Holds p) : b.Holds p :=
  ⟨Int.le_trans h.1 hp.1, Int.lt_of_lt_of_le hp.2.1 h.2.1, Int.le_trans h.2.2.1 hp.2.2.1,
    Int.lt_of_lt_of_le hp.2.2.2 h.2.2.2⟩

/-- A box of a size that is not negative, at a corner inside a room of a greater size, is
inside the room. -/
theorem ofSize_inside {p : IVec} {w h W H : Int} (hx : 0 ≤ p.x) (hy : 0 ≤ p.y) (hw : p.x + w ≤ W)
    (hh : p.y + h ≤ H) : (ofSize p w h).Inside (ofSize 0 W H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hx
  · show p.x + w ≤ (0 : IVec).x + W
    rw [IVec.zero_x, Int.zero_add]
    exact hw
  · exact hy
  · show p.y + h ≤ (0 : IVec).y + H
    rw [IVec.zero_y, Int.zero_add]
    exact hh

/-! ## The hull -/

theorem hull_comm (a b : IBox) : hull a b = hull b a :=
  ext (Int.min_comm _ _) (Int.min_comm _ _) (Int.max_comm _ _) (Int.max_comm _ _)

theorem hull_assoc (a b c : IBox) : hull (hull a b) c = hull a (hull b c) :=
  ext (Int.min_assoc _ _ _) (Int.min_assoc _ _ _) (Int.max_assoc _ _ _) (Int.max_assoc _ _ _)

theorem hull_self (a : IBox) : hull a a = a :=
  ext (Int.min_self _) (Int.min_self _) (Int.max_self _) (Int.max_self _)

/-- The first box is inside the hull. -/
theorem inside_hull_left (a b : IBox) : a.Inside (hull a b) :=
  ⟨Int.min_le_left _ _, Int.le_max_left _ _, Int.min_le_left _ _, Int.le_max_left _ _⟩

/-- The second box is inside the hull. -/
theorem inside_hull_right (a b : IBox) : b.Inside (hull a b) :=
  ⟨Int.min_le_right _ _, Int.le_max_right _ _, Int.min_le_right _ _, Int.le_max_right _ _⟩

/-- **The hull is the least box that holds both**: it is inside every box that both are
inside. -/
theorem hull_least {a b c : IBox} (h : a.Inside c) (k : b.Inside c) : (hull a b).Inside c :=
  ⟨le_min_of h.1 k.1, max_le_of h.2.1 k.2.1, le_min_of h.2.2.1 k.2.2.1,
    max_le_of h.2.2.2 k.2.2.2⟩

/-- A box inside another adds nothing to it. -/
theorem hull_of_inside {a b : IBox} (h : a.Inside b) : hull a b = b :=
  (hull_least h (Inside.refl b)).antisymm (inside_hull_right a b)

/-! ## Disjoint boxes -/

theorem Disjoint.symm {a b : IBox} (h : a.Disjoint b) : b.Disjoint a := by
  cases h with
  | inl h => exact Or.inr (Or.inl h)
  | inr h =>
    cases h with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inr (Or.inr h))
      | inr h => exact Or.inr (Or.inr (Or.inl h))

/-- Boxes inside disjoint boxes are disjoint. -/
theorem Disjoint.mono {a a' b b' : IBox} (ha : a.Inside a') (hb : b.Inside b')
    (h : a'.Disjoint b') : a.Disjoint b := by
  cases h with
  | inl h => exact Or.inl (Int.le_trans (Int.le_trans ha.2.1 h) hb.1)
  | inr h =>
    cases h with
    | inl h => exact Or.inr (Or.inl (Int.le_trans (Int.le_trans hb.2.1 h) ha.1))
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inr (Or.inl (Int.le_trans (Int.le_trans ha.2.2.2 h) hb.2.2.1)))
      | inr h => exact Or.inr (Or.inr (Or.inr (Int.le_trans (Int.le_trans hb.2.2.2 h) ha.2.2.1)))

/-- **Disjoint boxes share no point.** -/
theorem Disjoint.not_holds {a b : IBox} (h : a.Disjoint b) {p : IVec} (ha : a.Holds p) :
    ¬b.Holds p := by
  intro hb
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  cases h with
  | inl h => exact Int.lt_irrefl p.x (Int.lt_of_lt_of_le a2 (Int.le_trans h b1))
  | inr h =>
    cases h with
    | inl h => exact Int.lt_irrefl p.x (Int.lt_of_lt_of_le b2 (Int.le_trans h a1))
    | inr h =>
      cases h with
      | inl h => exact Int.lt_irrefl p.y (Int.lt_of_lt_of_le a4 (Int.le_trans h b3))
      | inr h => exact Int.lt_irrefl p.y (Int.lt_of_lt_of_le b4 (Int.le_trans h a3))

/-- **Two boxes that each have a point are disjoint exactly when they share none.** -/
theorem disjoint_iff {a b : IBox} (ha : a.Solid) (hb : b.Solid) :
    a.Disjoint b ↔ ∀ p : IVec, ¬(a.Holds p ∧ b.Holds p) := by
  constructor
  · intro h p hp
    exact h.not_holds hp.1 hp.2
  · intro h
    obtain ⟨a1, a2⟩ := ha
    obtain ⟨b1, b2⟩ := hb
    by_cases h1 : a.x1 ≤ b.x0
    · exact Or.inl h1
    · by_cases h2 : b.x1 ≤ a.x0
      · exact Or.inr (Or.inl h2)
      · by_cases h3 : a.y1 ≤ b.y0
        · exact Or.inr (Or.inr (Or.inl h3))
        · by_cases h4 : b.y1 ≤ a.y0
          · exact Or.inr (Or.inr (Or.inr h4))
          · exact absurd
              ⟨⟨Int.le_max_left _ _, max_lt_of a1 (Int.not_le.mp h1), Int.le_max_left _ _,
                  max_lt_of a2 (Int.not_le.mp h3)⟩,
                ⟨Int.le_max_right _ _, max_lt_of (Int.not_le.mp h2) b1, Int.le_max_right _ _,
                  max_lt_of (Int.not_le.mp h4) b2⟩⟩
              (h ⟨max a.x0 b.x0, max a.y0 b.y0⟩)

/-! ## Moves -/

/-- **Moved boxes are inside each other exactly when the boxes are.** -/
theorem inside_move (d : IVec) {a b : IBox} :
    (Moves.move d a).Inside (Moves.move d b) ↔ a.Inside b :=
  and_congr (add_le_add_iff _ _ _) (and_congr (add_le_add_iff _ _ _)
    (and_congr (add_le_add_iff _ _ _) (add_le_add_iff _ _ _)))

/-- **Moved boxes are disjoint exactly when the boxes are.** -/
theorem disjoint_move (d : IVec) {a b : IBox} :
    (Moves.move d a).Disjoint (Moves.move d b) ↔ a.Disjoint b :=
  or_congr (add_le_add_iff _ _ _) (or_congr (add_le_add_iff _ _ _)
    (or_congr (add_le_add_iff _ _ _) (add_le_add_iff _ _ _)))

/-- A moved box holds the moved point exactly when the box holds the point. -/
theorem holds_move (d : IVec) {b : IBox} {p : IVec} :
    (Moves.move d b).Holds (p + d) ↔ b.Holds p :=
  and_congr (add_le_add_iff _ _ _) (and_congr (add_lt_add_iff _ _ _)
    (and_congr (add_le_add_iff _ _ _) (add_lt_add_iff _ _ _)))

/-- **The hull of two moved boxes is the hull, moved.** -/
theorem hull_move (d : IVec) (a b : IBox) :
    hull (Moves.move d a) (Moves.move d b) = Moves.move d (hull a b) :=
  ext (min_add a.x0 b.x0 d.x) (min_add a.y0 b.y0 d.y) (max_add a.x1 b.x1 d.x)
    (max_add a.y1 b.y1 d.y)

theorem width_move (d : IVec) (b : IBox) : (Moves.move d b).width = b.width := by
  show b.x1 + d.x - (b.x0 + d.x) = b.x1 - b.x0
  omega

theorem height_move (d : IVec) (b : IBox) : (Moves.move d b).height = b.height := by
  show b.y1 + d.y - (b.y0 + d.y) = b.y1 - b.y0
  omega

/-- The box at a moved point is the box at the point, moved. -/
theorem ofPoint_move (d p : IVec) : ofPoint (p + d) = Moves.move d (ofPoint p) := rfl

/-- The box of a size at a moved corner is the box, moved. -/
theorem ofSize_move (d p : IVec) (w h : Int) :
    ofSize (p + d) w h = Moves.move d (ofSize p w h) := by
  refine ext rfl rfl ?_ ?_
  · show p.x + d.x + w = p.x + w + d.x
    omega
  · show p.y + d.y + h = p.y + h + d.y
    omega

/-- A margin and a move may be taken in either order. -/
theorem grow_move (d : IVec) (l t r b : Int) (x : IBox) :
    grow l t r b (Moves.move d x) = Moves.move d (grow l t r b x) := by
  refine ext ?_ ?_ ?_ ?_
  · show x.x0 + d.x - l = x.x0 - l + d.x
    omega
  · show x.y0 + d.y - t = x.y0 - t + d.y
    omega
  · show x.x1 + d.x + r = x.x1 + r + d.x
    omega
  · show x.y1 + d.y + b = x.y1 + b + d.y
    omega

/-- A box is inside itself with margins that are not negative. -/
theorem inside_grow {l t r b : Int} (hl : 0 ≤ l) (ht : 0 ≤ t) (hr : 0 ≤ r) (hb : 0 ≤ b)
    (x : IBox) : x.Inside (grow l t r b x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show x.x0 - l ≤ x.x0
    omega
  · show x.x1 ≤ x.x1 + r
    omega
  · show x.y0 - t ≤ x.y0
    omega
  · show x.y1 ≤ x.y1 + b
    omega

/-! ## The room of a list -/

theorem merge_none_left (b : Option IBox) : merge none b = b := rfl

theorem merge_none_right : ∀ a : Option IBox, merge a none = a
  | none => rfl
  | some _ => rfl

theorem merge_assoc : ∀ a b c : Option IBox, merge (merge a b) c = merge a (merge b c)
  | none, _, _ => rfl
  | some _, none, _ => rfl
  | some _, some _, none => rfl
  | some a, some b, some c => congrArg some (hull_assoc a b c)

theorem merge_comm : ∀ a b : Option IBox, merge a b = merge b a
  | none, none => rfl
  | none, some _ => rfl
  | some _, none => rfl
  | some a, some b => congrArg some (hull_comm a b)

/-- The first of two rooms is inside their `merge`. -/
theorem inside_merge_left {a b : Option IBox} {x h : IBox} (ha : a = some x)
    (hm : merge a b = some h) : x.Inside h := by
  subst ha
  cases b with
  | none =>
    have e : x = h := Option.some.inj hm
    rw [e]
    exact Inside.refl h
  | some y =>
    have e : hull x y = h := Option.some.inj hm
    rw [← e]
    exact inside_hull_left x y

/-- The second of two rooms is inside their `merge`. -/
theorem inside_merge_right {a b : Option IBox} {x h : IBox} (hb : b = some x)
    (hm : merge a b = some h) : x.Inside h := by
  subst hb
  cases a with
  | none =>
    have e : x = h := Option.some.inj hm
    rw [e]
    exact Inside.refl h
  | some y =>
    have e : hull y x = h := Option.some.inj hm
    rw [← e]
    exact inside_hull_right y x

theorem hullAll_nil : hullAll [] = none := rfl

theorem hullAll_cons (b : IBox) (bs : List IBox) :
    hullAll (b :: bs) = merge (some b) (hullAll bs) := rfl

/-- **The room of two lists in a row is the `merge` of their rooms.** -/
theorem hullAll_append : ∀ l m : List IBox, hullAll (l ++ m) = merge (hullAll l) (hullAll m)
  | [], _ => rfl
  | b :: l, m => by
    rw [List.cons_append, hullAll_cons, hullAll_append l m, hullAll_cons, merge_assoc]

/-- Only the empty list has no room. -/
theorem hullAll_eq_none : ∀ {bs : List IBox}, hullAll bs = none → bs = []
  | [], _ => rfl
  | b :: bs, h => by
    rw [hullAll_cons] at h
    cases hb : hullAll bs with
    | none =>
      rw [hb] at h
      exact nomatch h
    | some c =>
      rw [hb] at h
      exact nomatch h

/-- **Every box of a list is inside the room of the list.** -/
theorem inside_hullAll : ∀ {bs : List IBox} {b h : IBox}, b ∈ bs → hullAll bs = some h →
    b.Inside h
  | x :: xs, b, h, hm, hh => by
    rw [hullAll_cons] at hh
    cases hx : hullAll xs with
    | none =>
      rw [hx] at hh
      have e : x = h := Option.some.inj hh
      cases List.mem_cons.mp hm with
      | inl hb =>
        rw [hb, e]
        exact Inside.refl h
      | inr hb =>
        rw [hullAll_eq_none hx] at hb
        exact nomatch hb
    | some c =>
      rw [hx] at hh
      have e : hull x c = h := Option.some.inj hh
      rw [← e]
      cases List.mem_cons.mp hm with
      | inl hb =>
        rw [hb]
        exact inside_hull_left x c
      | inr hb => exact (inside_hullAll hb hx).trans (inside_hull_right x c)

/-- **The room of a list is the least box that holds each**: it is inside every box that each
box of the list is inside. -/
theorem hullAll_least : ∀ {bs : List IBox} {h c : IBox}, hullAll bs = some h →
    (∀ b ∈ bs, b.Inside c) → h.Inside c
  | [], _, _, hh, _ => nomatch hh
  | x :: xs, h, c, hh, hc => by
    rw [hullAll_cons] at hh
    cases hx : hullAll xs with
    | none =>
      rw [hx] at hh
      have e : x = h := Option.some.inj hh
      rw [← e]
      exact hc x List.mem_cons_self
    | some k =>
      rw [hx] at hh
      have e : hull x k = h := Option.some.inj hh
      rw [← e]
      exact hull_least (hc x List.mem_cons_self)
        (hullAll_least hx fun b hb => hc b (List.mem_cons_of_mem x hb))

/-- The `merge` of two moved rooms is the `merge`, moved. -/
theorem merge_move (d : IVec) : ∀ a b : Option IBox,
    merge (Moves.move d a) (Moves.move d b) = Moves.move d (merge a b)
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b => congrArg some (hull_move d a b)

/-- **The room of a moved list is the room, moved.** -/
theorem hullAll_move (d : IVec) : ∀ bs : List IBox,
    hullAll (Moves.move d bs) = Moves.move d (hullAll bs)
  | [] => rfl
  | b :: bs => by
    rw [Moves.move_cons, hullAll_cons, hullAll_cons, hullAll_move d bs]
    exact merge_move d (some b) (hullAll bs)

end IBox

/-- **A thing that takes room**: its box, and the law that the box of a moved thing is the box,
moved. A program gives an instance for a type of its own, and the laws of rooms here are then
laws of that type. -/
class Boxed (α : Type) [Moves IVec α] where
  /-- The least box that holds what is drawn of the thing. -/
  box : α → IBox
  /-- The box of a moved thing is the box, moved. -/
  box_move : ∀ (d : IVec) (a : α), box (Moves.move d a) = Moves.move d (box a)

/-- A box is its own box. -/
instance : Boxed IBox where
  box b := b
  box_move _ _ := rfl

/-- A point takes no room: its box is at the point and holds nothing. In a hull it counts as
the point. -/
instance : Boxed IVec where
  box p := IBox.ofPoint p
  box_move d p := IBox.ofPoint_move d p

/-- The box of a segment: the least box that holds its four points. -/
instance : Boxed ICubic where
  box c := IBox.hull (IBox.hull (IBox.ofPoint c.p0) (IBox.ofPoint c.p1))
    (IBox.hull (IBox.ofPoint c.p2) (IBox.ofPoint c.p3))
  box_move d c := by
    show IBox.hull (IBox.hull (IBox.ofPoint (c.p0 + d)) (IBox.ofPoint (c.p1 + d)))
        (IBox.hull (IBox.ofPoint (c.p2 + d)) (IBox.ofPoint (c.p3 + d))) =
      Moves.move d (IBox.hull (IBox.hull (IBox.ofPoint c.p0) (IBox.ofPoint c.p1))
        (IBox.hull (IBox.ofPoint c.p2) (IBox.ofPoint c.p3)))
    rw [IBox.ofPoint_move, IBox.ofPoint_move, IBox.ofPoint_move, IBox.ofPoint_move,
      IBox.hull_move, IBox.hull_move, IBox.hull_move]

namespace Boxed

variable {α : Type} [Moves IVec α] [Boxed α]

/-- **The box of a thing commutes with a move**, so a stored box stands for the box of the
moved thing (`Commutes.stored`). -/
theorem commutes : Commutes (Boxed.box : α → IBox) := fun d a => Boxed.box_move d a

end Boxed

/-- **The room of a list of things**: the least box that holds the box of each, and none for
the empty list. -/
def boxAll {α : Type} [Moves IVec α] [Boxed α] (l : List α) : Option IBox :=
  IBox.hullAll (l.map Boxed.box)

section

variable {α : Type} [Moves IVec α] [Boxed α]

/-- The room of two lists of things in a row is the `merge` of their rooms. -/
theorem boxAll_append (l m : List α) : boxAll (l ++ m) = IBox.merge (boxAll l) (boxAll m) := by
  rw [boxAll, List.map_append, IBox.hullAll_append]
  rfl

/-- The box of each thing of a list is inside the room of the list. -/
theorem inside_boxAll {l : List α} {a : α} {h : IBox} (ha : a ∈ l) (hh : boxAll l = some h) :
    (Boxed.box a).Inside h :=
  IBox.inside_hullAll (List.mem_map_of_mem ha) hh

/-- The room of a list is inside every box that the box of each thing is inside. -/
theorem boxAll_least {l : List α} {h c : IBox} (hh : boxAll l = some h)
    (hc : ∀ a ∈ l, (Boxed.box a).Inside c) : h.Inside c :=
  IBox.hullAll_least hh fun b hb => by
    obtain ⟨a, ha, e⟩ := List.mem_map.mp hb
    rw [← e]
    exact hc a ha

/-- **The room of a moved list of things is the room, moved.** A room is computed once. -/
theorem boxAll_move (d : IVec) (l : List α) :
    boxAll (Moves.move d l) = Moves.move d (boxAll l) := by
  have e : (Moves.move d l).map Boxed.box = Moves.move d (l.map Boxed.box) := by
    show (l.map (Moves.move d)).map Boxed.box = (l.map Boxed.box).map (Moves.move d)
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun a _ => Boxed.box_move d a
  rw [boxAll, e, IBox.hullAll_move]
  rfl

end

end Whatwg.Svg.Scene
