import Whatwg.Svg.Scene.Extent

/-!
# Whatwg.Svg.Scene.Layout

Owner: parts of a picture put together (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A picture is made of parts, and a part is made of parts. Each is laid out by itself, at the
origin, and whatever holds it moves it into place. lean4-effect4 draws a program so
(`lay` of its `tools/Tools/View/Flow.lean`): a series is its parts one above the other, each
centred, branches stand side by side a gap apart, and a region is its part inside a margin. It
writes each of those with its own arithmetic and proves of each, by hand, that the things stay
inside the width and apart. Here the three are operations on one value, with those laws once.

A layout is generic in its things. They need only move (`Moves`) and, for the laws of room,
have a box (`Boxed` of `Whatwg/Svg/Scene/Extent.lean`). A program's own type of placed thing
is an instance, and no data is converted.

- `Layout α`: a room, `w` across and `h` down, and things placed in it from the origin.
  `Layout.room` is the room as a box.
- `beside gap a b`, `above gap a b`: `b` moved to the right of `a`, or below it, with a gap.
  `over a b`: both in one room, `b` drawn after `a`.
- `row gap ls`, `column gap ls`: several parts with the gap between each two, and no gap
  before the first or after the last.
- `inset left top right bottom a`: the part inside margins. `centred width a`: the part in the
  middle of a width, across. `stack gap ls`: a column whose parts are centred in the width of
  the widest, which is lean4-effect4's series.
- `place origin l`: the things of a layout, moved to where its room stands.
- `map f l`: the same layout of other things.
- `Fits l`: the box of each thing is inside the room. `Clear l`: no two things share room. Both
  are decided, so a program can test a picture that it did not build with these operations.

What the laws say:

- **A monoid, three times.** `beside 0`, `above 0` and `over` are associative and have the
  empty layout as identity on both sides (`beside_assoc`, `beside_empty_left`,
  `beside_empty_right`, and so for `above` and `over`). `beside` and `above` are associative at
  every gap. So parts may be grouped in any way, and a picture built part by part is the
  picture built at once.
- **The room of a composite** is the least box that holds the rooms of its parts where they
  stand (`room_beside`, `room_above`, `room_over`, by `IBox.hull`), and the room of an inset
  part is the room of the part, moved and grown (`room_inset`). A row is as wide as its parts
  and the gaps between them (`row_w`), and a column as high (`column_h`).
- **What fits, fits** (`Fits.beside`, `Fits.above`, `Fits.over`, `Fits.inset`, `Fits.centred`,
  `Fits.row`, `Fits.column`, `Fits.stack`): where each thing of each part is inside its part's
  room, each thing of the composite is inside the composite's room.
- **What is clear stays clear** (`Clear.beside`, `Clear.above`, `Clear.inset`,
  `Clear.centred`, `Clear.row`, `Clear.column`, `Clear.stack`): parts that fit, with no two
  things sharing room in any of them, make a composite with no two things sharing room. A
  thing of the first part and a thing of the second are the gap apart at least
  (`beside_gap`, `above_gap`). `over` is not so, and has no such law.
- **Centring is even to one unit** (`centred_even`): the margin on the left is the margin on
  the right or one unit less.
- **A layout is placed anywhere** (`place_zero`, `place_add`, `Fits.place`, `Clear.place`):
  moved to an origin, its things are inside the moved room and still clear.
- **The things may be replaced** (`map_beside`, `map_above`, `map_over`): a function that
  commutes with moves goes through the operations.

What this module does not claim: places for the links between things, which have no room of
their own here; a layout that is the narrowest, since `beside` holds the whole rooms apart
and not the things; anything of `over` beyond its room; a baseline. A room is counted in whole
units that are not negative, so a part cannot have a negative size, and a gap cannot pull two
parts over each other.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- **A part of a picture, laid out at the origin**: its room, `w` across and `h` down, and its
things, each placed in that room. -/
structure Layout (α : Type) where
  /-- How far the room reaches across. -/
  w : Nat
  /-- How far the room reaches down. -/
  h : Nat
  /-- The things, in the order in which they are drawn. -/
  items : List α
  deriving Repr, DecidableEq

namespace Layout

variable {α β : Type}

theorem ext' {l m : Layout α} (hw : l.w = m.w) (hh : l.h = m.h) (hi : l.items = m.items) :
    l = m := by
  cases l
  cases m
  cases hw
  cases hh
  cases hi
  rfl

/-- The step of `n` units across. -/
def across (n : Nat) : IVec := ⟨n, 0⟩

/-- The step of `n` units down. -/
def down (n : Nat) : IVec := ⟨0, n⟩

/-- The room of a layout as a box, from the origin. -/
def room (l : Layout α) : IBox := ⟨0, 0, l.w, l.h⟩

/-- The layout with no room and no thing. -/
def empty : Layout α := ⟨0, 0, []⟩

/-- One thing in a room of its own. -/
def leaf (w h : Nat) (a : α) : Layout α := ⟨w, h, [a]⟩

/-- The same layout of other things. -/
def map (f : α → β) (l : Layout α) : Layout β := ⟨l.w, l.h, l.items.map f⟩

/-- **Both in one room**, `b` drawn after `a`. -/
def over (a b : Layout α) : Layout α where
  w := max a.w b.w
  h := max a.h b.h
  items := a.items ++ b.items

section

variable [Moves IVec α]

/-- **`b` to the right of `a`**, a gap apart. The room is as high as the higher of the two. -/
def beside (gap : Nat) (a b : Layout α) : Layout α where
  w := a.w + gap + b.w
  h := max a.h b.h
  items := a.items ++ Moves.move (across (a.w + gap)) b.items

/-- **`b` below `a`**, a gap apart. The room is as wide as the wider of the two. -/
def above (gap : Nat) (a b : Layout α) : Layout α where
  w := max a.w b.w
  h := a.h + gap + b.h
  items := a.items ++ Moves.move (down (a.h + gap)) b.items

/-- **The part inside margins.** -/
def inset (left top right bottom : Nat) (a : Layout α) : Layout α where
  w := left + a.w + right
  h := top + a.h + bottom
  items := Moves.move (across left + down top) a.items

/-- **The part in the middle of a width**, across. A part that is wider than the width keeps
its room and its place. -/
def centred (width : Nat) (a : Layout α) : Layout α where
  w := max width a.w
  h := a.h
  items := Moves.move (across ((width - a.w) / 2)) a.items

/-- **Parts side by side**, with the gap between each two. -/
def row (gap : Nat) : List (Layout α) → Layout α
  | [] => empty
  | [a] => a
  | a :: b :: rest => beside gap a (row gap (b :: rest))

/-- **Parts one above the other**, with the gap between each two. -/
def column (gap : Nat) : List (Layout α) → Layout α
  | [] => empty
  | [a] => a
  | a :: b :: rest => above gap a (column gap (b :: rest))

/-- The width of the widest of some parts. -/
def widest (ls : List (Layout α)) : Nat := ls.foldr (fun l m => max l.w m) 0

/-- **Parts one above the other, each centred** in the width of the widest. -/
def stack (gap : Nat) (ls : List (Layout α)) : Layout α :=
  column gap (ls.map (centred (widest ls)))

/-- **The things of a layout, moved to where its room stands.** -/
def place (origin : IVec) (l : Layout α) : List α := Moves.move origin l.items

end

/-! ## Steps across and down -/

theorem across_zero : across 0 = 0 := rfl

theorem down_zero : down 0 = 0 := rfl

theorem across_add (m n : Nat) : across (m + n) = across m + across n :=
  IVec.ext (by show ((m + n : Nat) : Int) = (m : Int) + (n : Int); omega) rfl

theorem down_add (m n : Nat) : down (m + n) = down m + down n :=
  IVec.ext rfl (by show ((m + n : Nat) : Int) = (m : Int) + (n : Int); omega)

/-! ## The same layout of other things -/

theorem map_id (l : Layout α) : map (fun a => a) l = l := ext' rfl rfl (List.map_id' l.items)

theorem map_map {γ : Type} (g : β → γ) (f : α → β) (l : Layout α) :
    map g (map f l) = map (fun a => g (f a)) l :=
  ext' rfl rfl (by
    show (l.items.map f).map g = l.items.map fun a => g (f a)
    rw [List.map_map]
    rfl)

/-! ## In one room -/

/-- **Parts in one room may be grouped in either way.** -/
theorem over_assoc (a b c : Layout α) : over (over a b) c = over a (over b c) :=
  ext' (Nat.max_assoc a.w b.w c.w) (Nat.max_assoc a.h b.h c.h)
    (List.append_assoc a.items b.items c.items)

theorem over_empty_left (a : Layout α) : over empty a = a :=
  ext' (Nat.zero_max a.w) (Nat.zero_max a.h) rfl

theorem over_empty_right (a : Layout α) : over a empty = a :=
  ext' (Nat.max_zero a.w) (Nat.max_zero a.h) (List.append_nil a.items)

/-- **The room of two parts in one room** is the least box that holds both rooms. -/
theorem room_over (a b : Layout α) : (over a b).room = IBox.hull a.room b.room := by
  refine IBox.ext ?_ ?_ ?_ ?_
  · show (0 : Int) = min 0 0
    omega
  · show (0 : Int) = min 0 0
    omega
  · show ((max a.w b.w : Nat) : Int) = max (a.w : Int) (b.w : Int)
    omega
  · show ((max a.h b.h : Nat) : Int) = max (a.h : Int) (b.h : Int)
    omega

theorem map_over (f : α → β) (a b : Layout α) : map f (over a b) = over (map f a) (map f b) :=
  ext' rfl rfl (List.map_append)

section

variable [Moves IVec α]

/-! ## The sizes -/

theorem beside_w (gap : Nat) (a b : Layout α) : (beside gap a b).w = a.w + gap + b.w := rfl

theorem beside_h (gap : Nat) (a b : Layout α) : (beside gap a b).h = max a.h b.h := rfl

theorem above_w (gap : Nat) (a b : Layout α) : (above gap a b).w = max a.w b.w := rfl

theorem above_h (gap : Nat) (a b : Layout α) : (above gap a b).h = a.h + gap + b.h := rfl

/-- **A row is as wide as its parts and the gaps between them.** With one gap more on each
side of the equation, so that it needs no subtraction. -/
theorem row_w (gap : Nat) : ∀ ls : List (Layout α), ls ≠ [] →
    (row gap ls).w + gap = (ls.map fun l => l.w + gap).sum
  | [], h => absurd rfl h
  | [a], _ => by
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rfl
  | a :: b :: rest, _ => by
    have ih := row_w gap (b :: rest) (List.cons_ne_nil b rest)
    rw [List.map_cons, List.sum_cons, ← ih]
    show a.w + gap + (row gap (b :: rest)).w + gap = a.w + gap + ((row gap (b :: rest)).w + gap)
    omega

/-- **A column is as high as its parts and the gaps between them.** -/
theorem column_h (gap : Nat) : ∀ ls : List (Layout α), ls ≠ [] →
    (column gap ls).h + gap = (ls.map fun l => l.h + gap).sum
  | [], h => absurd rfl h
  | [a], _ => by
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rfl
  | a :: b :: rest, _ => by
    have ih := column_h gap (b :: rest) (List.cons_ne_nil b rest)
    rw [List.map_cons, List.sum_cons, ← ih]
    show a.h + gap + (column gap (b :: rest)).h + gap =
      a.h + gap + ((column gap (b :: rest)).h + gap)
    omega

/-! ## A monoid, three times -/

/-- **Parts side by side may be grouped in either way**, at any gap. -/
theorem beside_assoc (gap : Nat) (a b c : Layout α) :
    beside gap (beside gap a b) c = beside gap a (beside gap b c) := by
  refine ext' ?_ ?_ ?_
  · show a.w + gap + b.w + gap + c.w = a.w + gap + (b.w + gap + c.w)
    omega
  · exact Nat.max_assoc a.h b.h c.h
  · show a.items ++ Moves.move (across (a.w + gap)) b.items ++
        Moves.move (across (a.w + gap + b.w + gap)) c.items =
      a.items ++ Moves.move (across (a.w + gap))
        (b.items ++ Moves.move (across (b.w + gap)) c.items)
    rw [Moves.move_append, Moves.move_move, List.append_assoc, ← across_add]
    have e : b.w + gap + (a.w + gap) = a.w + gap + b.w + gap := by omega
    rw [e]

/-- The empty layout to the left, with no gap, changes nothing. -/
theorem beside_empty_left (a : Layout α) : beside 0 empty a = a :=
  ext' (Nat.zero_add a.w) (Nat.zero_max a.h) (Moves.move_zero a.items)

/-- The empty layout to the right, with no gap, changes nothing. -/
theorem beside_empty_right (a : Layout α) : beside 0 a empty = a :=
  ext' rfl (Nat.max_zero a.h) (List.append_nil a.items)

/-- **Parts one above the other may be grouped in either way**, at any gap. -/
theorem above_assoc (gap : Nat) (a b c : Layout α) :
    above gap (above gap a b) c = above gap a (above gap b c) := by
  refine ext' ?_ ?_ ?_
  · exact Nat.max_assoc a.w b.w c.w
  · show a.h + gap + b.h + gap + c.h = a.h + gap + (b.h + gap + c.h)
    omega
  · show a.items ++ Moves.move (down (a.h + gap)) b.items ++
        Moves.move (down (a.h + gap + b.h + gap)) c.items =
      a.items ++ Moves.move (down (a.h + gap))
        (b.items ++ Moves.move (down (b.h + gap)) c.items)
    rw [Moves.move_append, Moves.move_move, List.append_assoc, ← down_add]
    have e : b.h + gap + (a.h + gap) = a.h + gap + b.h + gap := by omega
    rw [e]

/-- The empty layout above, with no gap, changes nothing. -/
theorem above_empty_left (a : Layout α) : above 0 empty a = a :=
  ext' (Nat.zero_max a.w) (Nat.zero_add a.h) (Moves.move_zero a.items)

/-- The empty layout below, with no gap, changes nothing. -/
theorem above_empty_right (a : Layout α) : above 0 a empty = a :=
  ext' (Nat.max_zero a.w) rfl (List.append_nil a.items)

/-! ## The room of a composite -/

/-- **The room of two parts side by side** is the least box that holds the room of the first
and the room of the second where it stands. -/
theorem room_beside (gap : Nat) (a b : Layout α) :
    (beside gap a b).room = IBox.hull a.room (Moves.move (across (a.w + gap)) b.room) := by
  refine IBox.ext ?_ ?_ ?_ ?_
  · show (0 : Int) = min 0 (0 + ((a.w + gap : Nat) : Int))
    omega
  · show (0 : Int) = min 0 (0 + 0)
    omega
  · show ((a.w + gap + b.w : Nat) : Int) = max (a.w : Int) ((b.w : Int) + ((a.w + gap : Nat) : Int))
    omega
  · show ((max a.h b.h : Nat) : Int) = max (a.h : Int) ((b.h : Int) + 0)
    omega

/-- **The room of two parts one above the other** is the least box that holds both rooms where
they stand. -/
theorem room_above (gap : Nat) (a b : Layout α) :
    (above gap a b).room = IBox.hull a.room (Moves.move (down (a.h + gap)) b.room) := by
  refine IBox.ext ?_ ?_ ?_ ?_
  · show (0 : Int) = min 0 (0 + 0)
    omega
  · show (0 : Int) = min 0 (0 + ((a.h + gap : Nat) : Int))
    omega
  · show ((max a.w b.w : Nat) : Int) = max (a.w : Int) ((b.w : Int) + 0)
    omega
  · show ((a.h + gap + b.h : Nat) : Int) = max (a.h : Int) ((b.h : Int) + ((a.h + gap : Nat) : Int))
    omega

/-- **The room of a part inside margins** is the room of the part where it stands, grown by
the margins. -/
theorem room_inset (left top right bottom : Nat) (a : Layout α) :
    (inset left top right bottom a).room =
      IBox.grow left top right bottom (Moves.move (across left + down top) a.room) := by
  refine IBox.ext ?_ ?_ ?_ ?_
  · show (0 : Int) = 0 + ((left : Int) + 0) - (left : Int)
    omega
  · show (0 : Int) = 0 + (0 + (top : Int)) - (top : Int)
    omega
  · show ((left + a.w + right : Nat) : Int) = (a.w : Int) + ((left : Int) + 0) + (right : Int)
    omega
  · show ((top + a.h + bottom : Nat) : Int) = (a.h : Int) + (0 + (top : Int)) + (bottom : Int)
    omega

/-- **Centring is even to one unit**: where the part is no wider than the width, the margin on
its left is the margin on its right, or one unit less. -/
theorem centred_even {width w : Nat} (h : w ≤ width) :
    (width - w) / 2 ≤ width - w - (width - w) / 2 ∧
      width - w - (width - w) / 2 ≤ (width - w) / 2 + 1 := by
  constructor
  · omega
  · omega

/-! ## Where a layout is placed -/

/-- The things of a moved list are the moved things. -/
private theorem mem_move {d : IVec} {l : List α} {x : α} (h : x ∈ Moves.move d l) :
    ∃ y ∈ l, Moves.move d y = x := List.mem_map.mp h

theorem place_zero (l : Layout α) : place 0 l = l.items := Moves.move_zero l.items

/-- Placed at an origin and then moved is placed at the origin further on. -/
theorem place_add (d e : IVec) (l : Layout α) : place (d + e) l = Moves.move e (place d l) :=
  (Moves.move_move d e l.items).symm

end

/-! ## What fits, and what is clear -/

section

variable [Moves IVec α] [Boxed α]

/-- **The layout fits**: the box of each of its things is inside its room. -/
def Fits (l : Layout α) : Prop := ∀ a ∈ l.items, (Boxed.box a).Inside l.room

/-- **The layout is clear**: no two of its things share room. -/
def Clear (l : Layout α) : Prop :=
  l.items.Pairwise fun x y => (Boxed.box x).Disjoint (Boxed.box y)

/-- Whether a layout fits is decided, so a program can test its picture. -/
instance (l : Layout α) : Decidable l.Fits :=
  inferInstanceAs (Decidable (∀ a ∈ l.items, (Boxed.box a).Inside l.room))

/-- Whether a layout is clear is decided. -/
instance (l : Layout α) : Decidable l.Clear :=
  inferInstanceAs (Decidable (l.items.Pairwise fun x y => (Boxed.box x).Disjoint (Boxed.box y)))

theorem fits_empty : (empty : Layout α).Fits := fun _ h => nomatch h

theorem clear_empty : (empty : Layout α).Clear := List.Pairwise.nil

/-- One thing in a room that holds its box fits. -/
theorem fits_leaf {w h : Nat} {a : α} (hb : (Boxed.box a).Inside ⟨0, 0, w, h⟩) :
    (leaf w h a).Fits := fun x hx => by
  rw [List.mem_singleton.mp hx]
  exact hb

/-- One thing is clear of every other, there being none. -/
theorem clear_leaf (w h : Nat) (a : α) : (leaf w h a).Clear :=
  List.Pairwise.cons (fun _ hx => nomatch hx) List.Pairwise.nil

/-- A moved list of things that share no room shares none. -/
private theorem pairwise_move (d : IVec) {l : List α}
    (h : l.Pairwise fun x y => (Boxed.box x).Disjoint (Boxed.box y)) :
    (Moves.move d l).Pairwise fun x y => (Boxed.box x).Disjoint (Boxed.box y) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons hx _ ih =>
    refine List.Pairwise.cons (fun y hy => ?_) ih
    obtain ⟨z, hz, e⟩ := mem_move hy
    rw [← e, Boxed.box_move, Boxed.box_move]
    exact (IBox.disjoint_move d).mpr (hx z hz)

/-- The things of a moved list are inside the moved box that held them. -/
private theorem inside_move_of {d : IVec} {l : List α} {room : IBox}
    (h : ∀ a ∈ l, (Boxed.box a).Inside room) :
    ∀ x ∈ Moves.move d l, (Boxed.box x).Inside (Moves.move d room) := fun x hx => by
  obtain ⟨y, hy, e⟩ := mem_move hx
  rw [← e, Boxed.box_move]
  exact (IBox.inside_move d).mpr (h y hy)

/-! ### Side by side -/

theorem Fits.beside {gap : Nat} {a b : Layout α} (ha : a.Fits) (hb : b.Fits) :
    (beside gap a b).Fits := fun x hx => by
  rw [room_beside]
  cases List.mem_append.mp hx with
  | inl h => exact (ha x h).trans (IBox.inside_hull_left _ _)
  | inr h => exact (inside_move_of hb x h).trans (IBox.inside_hull_right _ _)

/-- **A thing of the first part and a thing of the second are the gap apart**, across. -/
theorem beside_gap {gap : Nat} {a b : Layout α} (ha : a.Fits) (hb : b.Fits) {x y : α}
    (hx : x ∈ a.items) (hy : y ∈ b.items) :
    (Boxed.box x).x1 + gap ≤ (Boxed.box (Moves.move (across (a.w + gap)) y)).x0 := by
  have h1 : (Boxed.box x).x1 ≤ (a.w : Int) := (ha x hx).2.1
  have h2 : (0 : Int) ≤ (Boxed.box y).x0 := (hb y hy).1
  rw [Boxed.box_move]
  show (Boxed.box x).x1 + (gap : Int) ≤ (Boxed.box y).x0 + ((a.w + gap : Nat) : Int)
  omega

theorem Clear.beside {gap : Nat} {a b : Layout α} (fa : a.Fits) (fb : b.Fits) (ca : a.Clear)
    (cb : b.Clear) : (beside gap a b).Clear := by
  refine List.pairwise_append.mpr ⟨ca, pairwise_move _ cb, fun x hx y hy => ?_⟩
  refine IBox.Disjoint.mono (fa x hx) (inside_move_of fb y hy) (Or.inl ?_)
  show (a.w : Int) ≤ 0 + ((a.w + gap : Nat) : Int)
  omega

/-! ### One above the other -/

theorem Fits.above {gap : Nat} {a b : Layout α} (ha : a.Fits) (hb : b.Fits) :
    (above gap a b).Fits := fun x hx => by
  rw [room_above]
  cases List.mem_append.mp hx with
  | inl h => exact (ha x h).trans (IBox.inside_hull_left _ _)
  | inr h => exact (inside_move_of hb x h).trans (IBox.inside_hull_right _ _)

/-- **A thing of the upper part and a thing of the lower are the gap apart**, down. -/
theorem above_gap {gap : Nat} {a b : Layout α} (ha : a.Fits) (hb : b.Fits) {x y : α}
    (hx : x ∈ a.items) (hy : y ∈ b.items) :
    (Boxed.box x).y1 + gap ≤ (Boxed.box (Moves.move (down (a.h + gap)) y)).y0 := by
  have h1 : (Boxed.box x).y1 ≤ (a.h : Int) := (ha x hx).2.2.2
  have h2 : (0 : Int) ≤ (Boxed.box y).y0 := (hb y hy).2.2.1
  rw [Boxed.box_move]
  show (Boxed.box x).y1 + (gap : Int) ≤ (Boxed.box y).y0 + ((a.h + gap : Nat) : Int)
  omega

theorem Clear.above {gap : Nat} {a b : Layout α} (fa : a.Fits) (fb : b.Fits) (ca : a.Clear)
    (cb : b.Clear) : (above gap a b).Clear := by
  refine List.pairwise_append.mpr ⟨ca, pairwise_move _ cb, fun x hx y hy => ?_⟩
  refine IBox.Disjoint.mono (fa x hx) (inside_move_of fb y hy) (Or.inr (Or.inr (Or.inl ?_)))
  show (a.h : Int) ≤ 0 + ((a.h + gap : Nat) : Int)
  omega

/-! ### In one room, inside margins, centred -/

theorem Fits.over {a b : Layout α} (ha : a.Fits) (hb : b.Fits) : (over a b).Fits := fun x hx => by
  rw [room_over]
  cases List.mem_append.mp hx with
  | inl h => exact (ha x h).trans (IBox.inside_hull_left _ _)
  | inr h => exact (hb x h).trans (IBox.inside_hull_right _ _)

theorem Fits.inset {left top right bottom : Nat} {a : Layout α} (ha : a.Fits) :
    (inset left top right bottom a).Fits := fun x hx => by
  rw [room_inset]
  exact (inside_move_of ha x hx).trans
    (IBox.inside_grow (Int.natCast_nonneg left) (Int.natCast_nonneg top)
      (Int.natCast_nonneg right) (Int.natCast_nonneg bottom) _)

theorem Clear.inset {left top right bottom : Nat} {a : Layout α} (ca : a.Clear) :
    (inset left top right bottom a).Clear := pairwise_move _ ca

theorem Fits.centred {width : Nat} {a : Layout α} (ha : a.Fits) : (centred width a).Fits :=
  fun x hx => by
  refine (inside_move_of ha x hx).trans ⟨?_, ?_, ?_, ?_⟩
  · show (0 : Int) ≤ 0 + (((width - a.w) / 2 : Nat) : Int)
    omega
  · show (a.w : Int) + (((width - a.w) / 2 : Nat) : Int) ≤ ((max width a.w : Nat) : Int)
    omega
  · show (0 : Int) ≤ 0 + 0
    omega
  · show (a.h : Int) + 0 ≤ (a.h : Int)
    omega

theorem Clear.centred {width : Nat} {a : Layout α} (ca : a.Clear) : (centred width a).Clear :=
  pairwise_move _ ca

/-! ### Rows, columns and stacks -/

theorem Fits.row (gap : Nat) : ∀ ls : List (Layout α), (∀ l ∈ ls, l.Fits) → (row gap ls).Fits
  | [], _ => fits_empty
  | [a], h => h a List.mem_cons_self
  | a :: b :: rest, h =>
    Fits.beside (h a List.mem_cons_self)
      (Fits.row gap (b :: rest) fun l hl => h l (List.mem_cons_of_mem a hl))

/-- **Parts that fit and are clear, side by side, are clear.** -/
theorem Clear.row (gap : Nat) : ∀ ls : List (Layout α), (∀ l ∈ ls, l.Fits) →
    (∀ l ∈ ls, l.Clear) → (row gap ls).Clear
  | [], _, _ => clear_empty
  | [a], _, c => c a List.mem_cons_self
  | a :: b :: rest, f, c =>
    Clear.beside (f a List.mem_cons_self)
      (Fits.row gap (b :: rest) fun l hl => f l (List.mem_cons_of_mem a hl))
      (c a List.mem_cons_self)
      (Clear.row gap (b :: rest) (fun l hl => f l (List.mem_cons_of_mem a hl))
        fun l hl => c l (List.mem_cons_of_mem a hl))

theorem Fits.column (gap : Nat) : ∀ ls : List (Layout α), (∀ l ∈ ls, l.Fits) →
    (column gap ls).Fits
  | [], _ => fits_empty
  | [a], h => h a List.mem_cons_self
  | a :: b :: rest, h =>
    Fits.above (h a List.mem_cons_self)
      (Fits.column gap (b :: rest) fun l hl => h l (List.mem_cons_of_mem a hl))

/-- **Parts that fit and are clear, one above the other, are clear.** -/
theorem Clear.column (gap : Nat) : ∀ ls : List (Layout α), (∀ l ∈ ls, l.Fits) →
    (∀ l ∈ ls, l.Clear) → (column gap ls).Clear
  | [], _, _ => clear_empty
  | [a], _, c => c a List.mem_cons_self
  | a :: b :: rest, f, c =>
    Clear.above (f a List.mem_cons_self)
      (Fits.column gap (b :: rest) fun l hl => f l (List.mem_cons_of_mem a hl))
      (c a List.mem_cons_self)
      (Clear.column gap (b :: rest) (fun l hl => f l (List.mem_cons_of_mem a hl))
        fun l hl => c l (List.mem_cons_of_mem a hl))

theorem Fits.stack (gap : Nat) {ls : List (Layout α)} (h : ∀ l ∈ ls, l.Fits) :
    (stack gap ls).Fits :=
  Fits.column gap _ fun l hl => by
    obtain ⟨m, hm, e⟩ := List.mem_map.mp hl
    rw [← e]
    exact (h m hm).centred

/-- **A series of parts that fit and are clear is clear.** -/
theorem Clear.stack (gap : Nat) {ls : List (Layout α)} (f : ∀ l ∈ ls, l.Fits)
    (c : ∀ l ∈ ls, l.Clear) : (stack gap ls).Clear :=
  Clear.column gap _
    (fun l hl => by
      obtain ⟨m, hm, e⟩ := List.mem_map.mp hl
      rw [← e]
      exact (f m hm).centred)
    fun l hl => by
      obtain ⟨m, hm, e⟩ := List.mem_map.mp hl
      rw [← e]
      exact (c m hm).centred

/-! ### Placed -/

/-- **The things of a placed layout are inside its room where it stands.** -/
theorem Fits.place {l : Layout α} (h : l.Fits) (origin : IVec) :
    ∀ x ∈ place origin l, (Boxed.box x).Inside (Moves.move origin l.room) :=
  inside_move_of h

/-- **The things of a placed layout that is clear share no room.** -/
theorem Clear.place {l : Layout α} (h : l.Clear) (origin : IVec) :
    (place origin l).Pairwise fun x y => (Boxed.box x).Disjoint (Boxed.box y) :=
  pairwise_move origin h

end

/-! ## Other things in the same layout -/

section

variable [Moves IVec α] [Moves IVec β]

theorem map_beside {f : α → β} (hf : Commutes f) (gap : Nat) (a b : Layout α) :
    map f (beside gap a b) = beside gap (map f a) (map f b) :=
  ext' rfl rfl (by
    show (a.items ++ Moves.move (across (a.w + gap)) b.items).map f =
      a.items.map f ++ Moves.move (across (a.w + gap)) (b.items.map f)
    rw [List.map_append, ← Commutes.map hf (across (a.w + gap)) b.items])

theorem map_above {f : α → β} (hf : Commutes f) (gap : Nat) (a b : Layout α) :
    map f (above gap a b) = above gap (map f a) (map f b) :=
  ext' rfl rfl (by
    show (a.items ++ Moves.move (down (a.h + gap)) b.items).map f =
      a.items.map f ++ Moves.move (down (a.h + gap)) (b.items.map f)
    rw [List.map_append, ← Commutes.map hf (down (a.h + gap)) b.items])


end

end Layout

end Whatwg.Svg.Scene
