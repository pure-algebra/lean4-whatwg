import Whatwg.Svg.Scene.Layout.Laws

/-!
# Whatwg.Svg.Scene.Layout.Frame

Owner: what is drawn at the rooms of a layout (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; ask W15
of `docs/research/2026-10-12-whatwg-requests.md`).

`Whatwg/Svg/Scene/Layout.lean` places the things of its parts. A picture of a value draws more
than its parts: a record is a panel whose rows are ruled apart, a list is a row of cells ruled
apart, and each stands in a frame. A frame and a rule are not parts that a caller has before
the layout. Each is drawn at a room that the layout makes: the room of the whole, or the room
between two neighbours. lean4-effect4's value pictures write them by hand (ask W15). Here they
are three operations beside `Layout.lean`, which this module does not change.

- `centredDown height a`: **the part in the middle of a height**, down. The twin of
  `Layout.centred`, which is across.
- `framed frame a`: **a thing drawn at the room of a part**, before the part's things. The
  caller gives a function from the room, a box, to a thing: a frame around the part, or a ground
  behind it.
- `rulePart rule w h`: a rule as a part. A room, and the rule drawn at it.
- `ruledRow rule gap ls`, `ruledColumn rule gap ls`: **a row, or a column, with a rule at each
  joint.** A joint is the room between two neighbours: as wide as the gap and as high as the
  row, or as high as the gap and as wide as the column. The ruled row is the row of the parts
  with a rule part between each two and no gap, so every law of a row is a law of it.

What the laws say:

- `stands_centredDown`, `centredDown_even`, `Fits.centredDown`, `Clear.centredDown`: the part
  stands the margin down, the margin above it is the margin below it or one unit less, and it
  fits and is clear where the part is. `centred_centredDown`: a part may be centred across and
  down in either order.
- `Fits.framed`: a framed part fits, where the part fits and the frame is inside the room that
  it is drawn at. `stands_framed`: the part stands in it where it stood.
- **A frame holds what it frames, so a framed part is not clear.** `clear_framed_iff` says what
  `Clear` asks of it: that the part is clear, and that the frame shares room with no thing of
  the part. `framed_not_clear`: it is not clear where the frame's box holds the box of a thing
  that has a point. What is kept is the part's own `Clear`, which a caller carries beside the
  framed part: `framed_items` gives the things after the frame as the part's things.
- `room_ruledRow`: a ruled row has the room of the row. `stands_ruledRow`: each part stands in
  it at its step in the row, so the rules move no part.
- **There are as many rules as joints** (`ruledRow_count`): the things of a ruled row are the
  things of the row and one for each part but the last.
- **Each rule lies on its joint** (`ruledRow_joint`): the rule between a part and the next
  stands where the part's room ends, and its room ends where the next part begins.
- **A ruled row is clear** (`Clear.ruledRow`, with `Fits.ruledRow`), where the parts fit and are
  clear and each rule is inside the room that it is drawn at. A rule lies in the gap, which no
  part reaches. This is what a frame does not have.
- The same seven for a column (`room_ruledColumn`, `stands_ruledColumn`, `ruledColumn_count`,
  `ruledColumn_joint`, `Fits.ruledColumn`, `Clear.ruledColumn`).

What a caller must supply: the frame and the rule as functions from a box to a thing of its
own, each with the law that the thing's box is inside the box given. A rule is given the box of
a joint at the origin, and moves to its joint with its part.

What this module does not claim: that the things of a picture with frames are clear of each
other apart from the frames, for a picture of framed parts inside framed parts (a notion of
`Clear` among the things that pass a test would say it, and is not here); a rule between the
parts of a `stack` or of `over`; a frame with a margin, which is `framed` after `inset`; a
joint of a gap of no units, where a rule has a room of no width and the laws hold as written.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace IBox

/-- **A box with a point that is inside another shares room with it.** -/
theorem Inside.not_disjoint {a b : IBox} (h : a.Inside b) (s : a.Solid) : ¬b.Disjoint a := by
  intro d
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨s1, s2⟩ := s
  cases d with
  | inl d => exact absurd d (by omega)
  | inr d =>
    cases d with
    | inl d => exact absurd d (by omega)
    | inr d =>
      cases d with
      | inl d => exact absurd d (by omega)
      | inr d => exact absurd d (by omega)

end IBox

namespace Layout

variable {α : Type}

/-! ## The middle of a height -/

section

variable [Moves IVec α]

/-- **The part in the middle of a height**, down. A part that is higher than the height keeps
its room and its place. -/
def centredDown (height : Nat) (a : Layout α) : Layout α where
  w := a.w
  h := max height a.h
  items := Moves.move (down ((height - a.h) / 2)) a.items

theorem stands_centredDown (height : Nat) (a : Layout α) :
    (centredDown height a).Stands (down ((height - a.h) / 2)) a :=
  fun _ hx => List.mem_map_of_mem hx

/-- **Centring down is even to one unit**: where the part is no higher than the height, the
margin above it is the margin below it, or one unit less. The numbers are those of
`centred_even`. -/
theorem centredDown_even {height h : Nat} (hh : h ≤ height) :
    (height - h) / 2 ≤ height - h - (height - h) / 2 ∧
      height - h - (height - h) / 2 ≤ (height - h) / 2 + 1 := centred_even hh

/-- **A part may be centred across and down in either order.** -/
theorem centred_centredDown (width height : Nat) (a : Layout α) :
    centred width (centredDown height a) = centredDown height (centred width a) :=
  ext' rfl rfl (by
    show Moves.move (across ((width - a.w) / 2)) (Moves.move (down ((height - a.h) / 2)) a.items) =
      Moves.move (down ((height - a.h) / 2)) (Moves.move (across ((width - a.w) / 2)) a.items)
    rw [Moves.move_move, Moves.move_move, IVec.add_comm])

end

section

variable [Moves IVec α] [Boxed α]

theorem Fits.centredDown {height : Nat} {a : Layout α} (ha : a.Fits) :
    (centredDown height a).Fits := fun x hx => by
  refine (ha.place (down ((height - a.h) / 2)) x hx).trans ⟨?_, ?_, ?_, ?_⟩
  · show (0 : Int) ≤ 0 + 0
    omega
  · show (a.w : Int) + 0 ≤ (a.w : Int)
    omega
  · show (0 : Int) ≤ 0 + (((height - a.h) / 2 : Nat) : Int)
    omega
  · show (a.h : Int) + (((height - a.h) / 2 : Nat) : Int) ≤ ((max height a.h : Nat) : Int)
    omega

theorem Clear.centredDown {height : Nat} {a : Layout α} (ca : a.Clear) :
    (centredDown height a).Clear := ca.place (down ((height - a.h) / 2))

end

/-! ## A thing at the room of a part -/

/-- **A thing drawn at the room of a part**, before the part's things: a frame around the part,
or a ground behind it. The room is the part's, from the origin, and the thing moves with the
part from then on. -/
def framed (frame : IBox → α) (a : Layout α) : Layout α := ⟨a.w, a.h, frame a.room :: a.items⟩

theorem room_framed (frame : IBox → α) (a : Layout α) : (framed frame a).room = a.room := rfl

/-- The things of a framed part: the frame, and then the part's things as they were. -/
theorem framed_items (frame : IBox → α) (a : Layout α) :
    (framed frame a).items = frame a.room :: a.items := rfl

/-- The part stands in the framed part where it stood. -/
theorem stands_framed [Moves IVec α] (frame : IBox → α) (a : Layout α) :
    (framed frame a).Stands 0 a := fun x hx => by
  rw [Moves.move_zero]
  exact List.mem_cons_of_mem _ hx

section

variable [Moves IVec α] [Boxed α]

/-- **A framed part fits**, where the part fits and the frame is inside the room that it is
drawn at. -/
theorem Fits.framed {frame : IBox → α} {a : Layout α} (ha : a.Fits)
    (hf : (Boxed.box (frame a.room)).Inside a.room) : (framed frame a).Fits := fun x hx => by
  cases List.mem_cons.mp hx with
  | inl e =>
    rw [e]
    exact hf
  | inr h => exact ha x h

/-- **What `Clear` asks of a framed part**: that the frame shares room with no thing of the
part, and that the part is clear. -/
theorem clear_framed_iff (frame : IBox → α) (a : Layout α) :
    (framed frame a).Clear ↔
      (∀ x ∈ a.items, (Boxed.box (frame a.room)).Disjoint (Boxed.box x)) ∧ a.Clear :=
  List.pairwise_cons

/-- **A frame holds what it frames, so a framed part is not clear**: not where the box of the
frame holds the box of a thing of the part that has a point. -/
theorem framed_not_clear {frame : IBox → α} {a : Layout α} {x : α} (hx : x ∈ a.items)
    (hs : (Boxed.box x).Solid) (hin : (Boxed.box x).Inside (Boxed.box (frame a.room))) :
    ¬(framed frame a).Clear := fun c =>
  hin.not_disjoint hs (((clear_framed_iff frame a).mp c).1 x hx)

end

/-! ## Rules at the joints -/

/-- **A rule as a part**: a room, and the rule drawn at it. -/
def rulePart (rule : IBox → α) (w h : Nat) : Layout α := leaf w h (rule ⟨0, 0, w, h⟩)

section

variable [Moves IVec α]

/-- **A row with a rule at each joint.** The joint of two neighbours is the room between them:
as wide as the gap and as high as the row. It is the row of the parts with a rule part between
each two and no gap. -/
def ruledRow (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) : Layout α :=
  row 0 (ls.intersperse (rulePart rule gap (row gap ls).h))

/-- **A column with a rule at each joint.** The joint of two neighbours is the room between
them: as high as the gap and as wide as the column. -/
def ruledColumn (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) : Layout α :=
  column 0 (ls.intersperse (rulePart rule (column gap ls).w gap))

end

/-! ### Parts with a part between each two -/

private theorem intersperse_two (J a b : Layout α) (rest : List (Layout α)) :
    (a :: b :: rest).intersperse J = a :: J :: (b :: rest).intersperse J := rfl

/-- A list of parts that begins with a part, woven, begins with that part. -/
private theorem intersperse_head (J b : Layout α) : ∀ rest : List (Layout α),
    ∃ tl, (b :: rest).intersperse J = b :: tl
  | [] => ⟨[], rfl⟩
  | c :: rest => ⟨J :: (c :: rest).intersperse J, rfl⟩

/-- A part of the woven list is the part between, or a part of the list. -/
private theorem mem_woven {J x : Layout α} : ∀ {ls : List (Layout α)}, x ∈ ls.intersperse J →
    x = J ∨ x ∈ ls
  | [], h => nomatch h
  | [_], h => Or.inr h
  | a :: b :: rest, h => by
    rw [intersperse_two] at h
    cases List.mem_cons.mp h with
    | inl e => exact Or.inr (e ▸ List.mem_cons_self)
    | inr h1 =>
      cases List.mem_cons.mp h1 with
      | inl e => exact Or.inl e
      | inr h2 =>
        cases mem_woven h2 with
        | inl e => exact Or.inl e
        | inr m => exact Or.inr (List.mem_cons_of_mem a m)

/-- The woven list has the things of the list, and one for each part but the last, where the
part between has one thing. -/
private theorem length_woven {J : Layout α} {x : α} (hJ : J.items = [x]) :
    ∀ ls : List (Layout α), ((ls.intersperse J).flatMap fun l => l.items).length =
      (ls.flatMap fun l => l.items).length + (ls.length - 1)
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    have ih := length_woven hJ (b :: rest)
    show (a.items ++ (J.items ++ ((b :: rest).intersperse J).flatMap fun l => l.items)).length =
      (a.items ++ (b :: rest).flatMap fun l => l.items).length + (rest.length + 1 + 1 - 1)
    rw [List.length_append, List.length_append, ih, List.length_append, hJ]
    show a.items.length + (1 + (((b :: rest).flatMap fun l => l.items).length +
      (rest.length + 1 - 1))) = _
    omega

private theorem across_x (n : Nat) : (across n).x = n := rfl

private theorem across_y (n : Nat) : (across n).y = 0 := rfl

private theorem down_x (n : Nat) : (down n).x = 0 := rfl

private theorem down_y (n : Nat) : (down n).y = n := rfl

/-! ### A ruled row -/

section

variable [Moves IVec α]

/-- A woven row is as wide as the row with the gap, where the part between is as wide as the
gap. -/
private theorem woven_row_w {gap : Nat} {J : Layout α} (hJ : J.w = gap) :
    ∀ ls : List (Layout α), (row 0 (ls.intersperse J)).w = (row gap ls).w
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    obtain ⟨tl, e⟩ := intersperse_head J b rest
    have ih := woven_row_w hJ (b :: rest)
    rw [intersperse_two, e]
    rw [e] at ih
    show a.w + 0 + (J.w + 0 + (row 0 (b :: tl)).w) = a.w + gap + (row gap (b :: rest)).w
    rw [ih, hJ]
    omega

/-- A woven row is as high as the row at least, and no higher than the row and the part
between. -/
private theorem woven_row_h (gap : Nat) (J : Layout α) : ∀ ls : List (Layout α),
    (row gap ls).h ≤ (row 0 (ls.intersperse J)).h ∧
      (row 0 (ls.intersperse J)).h ≤ max (row gap ls).h J.h
  | [] => ⟨Nat.le_refl _, Nat.zero_le _⟩
  | [a] => ⟨Nat.le_refl _, Nat.le_max_left _ _⟩
  | a :: b :: rest => by
    obtain ⟨tl, e⟩ := intersperse_head J b rest
    have ih := woven_row_h gap J (b :: rest)
    rw [intersperse_two, e]
    rw [e] at ih
    show max a.h (row gap (b :: rest)).h ≤ max a.h (max J.h (row 0 (b :: tl)).h) ∧
      max a.h (max J.h (row 0 (b :: tl)).h) ≤ max (max a.h (row gap (b :: rest)).h) J.h
    have h1 := ih.1
    have h2 := ih.2
    constructor
    · omega
    · omega

omit [Moves IVec α] in
/-- The parts of a row stand at their steps among the parts of the woven row. -/
private theorem parts_woven_row {gap : Nat} {J : Layout α} (hJ : J.w = gap) :
    ∀ (ls : List (Layout α)) (P : Layout α × IVec), P ∈ rowParts gap ls →
      P ∈ rowParts 0 (ls.intersperse J)
  | [], _, h => nomatch h
  | [_], _, h => h
  | a :: b :: rest, P, h => by
    rw [rowParts_cons] at h
    rw [intersperse_two, rowParts_cons, rowParts_cons, List.map_cons]
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact List.mem_cons_self
    | inr h' =>
      obtain ⟨P', hP', e⟩ := List.mem_map.mp h'
      have ih := parts_woven_row hJ (b :: rest) P' hP'
      have e2 : (P'.1, P'.2 + across (J.w + 0) + across (a.w + 0)) = P := by
        rw [← e]
        refine congrArg (Prod.mk P'.1) (IVec.ext ?_ ?_)
        · simp only [IVec.add_x, across_x]
          omega
        · simp only [IVec.add_y, across_y]
          omega
      rw [← e2]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map_of_mem (f := fun Q : Layout α × IVec => (Q.1, Q.2 + across (a.w + 0)))
          (List.mem_map_of_mem (f := fun Q : Layout α × IVec => (Q.1, Q.2 + across (J.w + 0))) ih)))

omit [Moves IVec α] in
/-- The part between a part of a row and the next stands, in the woven row, where the part's
room ends. -/
private theorem joint_woven_row {gap : Nat} {J : Layout α} (hJ : J.w = gap) :
    ∀ (ls : List (Layout α)) (i : Nat) (P : Layout α × IVec), (rowParts gap ls)[i]? = some P →
      i + 1 < ls.length → (J, P.2 + across P.1.w) ∈ rowParts 0 (ls.intersperse J)
  | [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | [_], i, _, _, hl => absurd hl (by show ¬i + 1 < 1; omega)
  | a :: b :: rest, 0, P, h, _ => by
    rw [rowParts_cons, List.getElem?_cons_zero] at h
    rw [← Option.some.inj h, intersperse_two, rowParts_cons, rowParts_cons, List.map_cons]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  | a :: b :: rest, i + 1, P, h, hl => by
    rw [rowParts_cons, List.getElem?_cons_succ, List.getElem?_map] at h
    cases hP' : (rowParts gap (b :: rest))[i]? with
    | none =>
      rw [hP'] at h
      exact nomatch h
    | some P' =>
      rw [hP'] at h
      have e : (P'.1, P'.2 + across (a.w + gap)) = P := Option.some.inj h
      have ih := joint_woven_row hJ (b :: rest) i P' hP' (Nat.lt_of_succ_lt_succ hl)
      rw [intersperse_two, rowParts_cons, rowParts_cons, List.map_cons]
      have e2 : (J, P'.2 + across P'.1.w + across (J.w + 0) + across (a.w + 0)) =
          (J, P.2 + across P.1.w) := by
        rw [← e]
        refine congrArg (Prod.mk J) (IVec.ext ?_ ?_)
        · simp only [IVec.add_x, across_x]
          omega
        · simp only [IVec.add_y, across_y]
          omega
      rw [← e2]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map_of_mem (f := fun Q : Layout α × IVec => (Q.1, Q.2 + across (a.w + 0)))
          (List.mem_map_of_mem (f := fun Q : Layout α × IVec => (Q.1, Q.2 + across (J.w + 0))) ih)))

theorem ruledRow_w (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) :
    (ruledRow rule gap ls).w = (row gap ls).w := woven_row_w rfl ls

theorem ruledRow_h (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) :
    (ruledRow rule gap ls).h = (row gap ls).h := by
  have h := woven_row_h gap (rulePart rule gap (row gap ls).h) ls
  have h1 := h.1
  have h2 : (row 0 (ls.intersperse (rulePart rule gap (row gap ls).h))).h ≤
      max (row gap ls).h (row gap ls).h := h.2
  show (row 0 (ls.intersperse (rulePart rule gap (row gap ls).h))).h = (row gap ls).h
  omega

/-- **A ruled row has the room of the row.** -/
theorem room_ruledRow (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) :
    (ruledRow rule gap ls).room = (row gap ls).room := by
  show (⟨0, 0, (ruledRow rule gap ls).w, (ruledRow rule gap ls).h⟩ : IBox) = _
  rw [ruledRow_w, ruledRow_h]
  rfl

/-- **Each part stands in the ruled row at its step in the row**: the rules move no part. -/
theorem stands_ruledRow (rule : IBox → α) {gap : Nat} {ls : List (Layout α)}
    {P : Layout α × IVec} (h : P ∈ rowParts gap ls) : (ruledRow rule gap ls).Stands P.2 P.1 :=
  stands_row (parts_woven_row rfl ls P h)

/-- **Each rule lies on its joint.** The rule between a part of a row and the next stands where
the part's room ends, and its room, as wide as the gap, ends where the next part begins. -/
theorem ruledRow_joint (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) {i : Nat}
    {P Q : Layout α × IVec} (hP : (rowParts gap ls)[i]? = some P)
    (hQ : (rowParts gap ls)[i + 1]? = some Q) :
    (ruledRow rule gap ls).Stands (P.2 + across P.1.w) (rulePart rule gap (row gap ls).h) ∧
      P.2.x + (P.1.w : Int) + (gap : Int) = Q.2.x := by
  have hl := congrArg List.length (rowParts_parts gap ls)
  rw [List.length_map] at hl
  have hi : i + 1 < ls.length := hl ▸ (List.getElem?_eq_some_iff.mp hQ).1
  exact ⟨stands_row (joint_woven_row rfl ls i P hP hi), rowParts_next gap ls hP hQ⟩

/-- **There are as many rules as joints**: a ruled row has the things of the row, and one for
each part but the last. -/
theorem ruledRow_count (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) :
    (ruledRow rule gap ls).items.length = (row gap ls).items.length + (ls.length - 1) := by
  have h1 := congrArg List.length (row_items_map (f := fun _ : α => ()) (fun _ _ => rfl) 0
    (ls.intersperse (rulePart rule gap (row gap ls).h)))
  have h2 := congrArg List.length (row_items_map (f := fun _ : α => ()) (fun _ _ => rfl) gap ls)
  rw [List.length_map, List.length_map] at h1 h2
  show (row 0 (ls.intersperse (rulePart rule gap (row gap ls).h))).items.length = _
  rw [h1, h2]
  exact length_woven rfl ls

end

section

variable [Moves IVec α] [Boxed α]

/-- **A ruled row fits**, where its parts fit and each rule is inside the room that it is drawn
at. -/
theorem Fits.ruledRow {rule : IBox → α} (hr : ∀ b : IBox, (Boxed.box (rule b)).Inside b)
    (gap : Nat) {ls : List (Layout α)} (h : ∀ l ∈ ls, l.Fits) : (ruledRow rule gap ls).Fits :=
  Fits.row 0 _ fun l hl => by
    cases mem_woven hl with
    | inl e =>
      rw [e]
      exact fits_leaf (hr _)
    | inr m => exact h l m

/-- **A ruled row is clear**, where its parts fit and are clear and each rule is inside the
room that it is drawn at: a rule lies in the gap, which no part reaches. -/
theorem Clear.ruledRow {rule : IBox → α} (hr : ∀ b : IBox, (Boxed.box (rule b)).Inside b)
    (gap : Nat) {ls : List (Layout α)} (f : ∀ l ∈ ls, l.Fits) (c : ∀ l ∈ ls, l.Clear) :
    (ruledRow rule gap ls).Clear :=
  Clear.row 0 _
    (fun l hl => by
      cases mem_woven hl with
      | inl e =>
        rw [e]
        exact fits_leaf (hr _)
      | inr m => exact f l m)
    fun l hl => by
      cases mem_woven hl with
      | inl e =>
        rw [e]
        exact clear_leaf _ _ _
      | inr m => exact c l m

end

/-! ### A ruled column -/

section

variable [Moves IVec α]

/-- A woven column is as high as the column with the gap, where the part between is as high as
the gap. -/
private theorem woven_column_h {gap : Nat} {J : Layout α} (hJ : J.h = gap) :
    ∀ ls : List (Layout α), (column 0 (ls.intersperse J)).h = (column gap ls).h
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    obtain ⟨tl, e⟩ := intersperse_head J b rest
    have ih := woven_column_h hJ (b :: rest)
    rw [intersperse_two, e]
    rw [e] at ih
    show a.h + 0 + (J.h + 0 + (column 0 (b :: tl)).h) = a.h + gap + (column gap (b :: rest)).h
    rw [ih, hJ]
    omega

/-- A woven column is as wide as the column at least, and no wider than the column and the part
between. -/
private theorem woven_column_w (gap : Nat) (J : Layout α) : ∀ ls : List (Layout α),
    (column gap ls).w ≤ (column 0 (ls.intersperse J)).w ∧
      (column 0 (ls.intersperse J)).w ≤ max (column gap ls).w J.w
  | [] => ⟨Nat.le_refl _, Nat.zero_le _⟩
  | [a] => ⟨Nat.le_refl _, Nat.le_max_left _ _⟩
  | a :: b :: rest => by
    obtain ⟨tl, e⟩ := intersperse_head J b rest
    have ih := woven_column_w gap J (b :: rest)
    rw [intersperse_two, e]
    rw [e] at ih
    show max a.w (column gap (b :: rest)).w ≤ max a.w (max J.w (column 0 (b :: tl)).w) ∧
      max a.w (max J.w (column 0 (b :: tl)).w) ≤ max (max a.w (column gap (b :: rest)).w) J.w
    have h1 := ih.1
    have h2 := ih.2
    constructor
    · omega
    · omega

omit [Moves IVec α] in
/-- The parts of a column stand at their steps among the parts of the woven column. -/
private theorem parts_woven_column {gap : Nat} {J : Layout α} (hJ : J.h = gap) :
    ∀ (ls : List (Layout α)) (P : Layout α × IVec), P ∈ columnParts gap ls →
      P ∈ columnParts 0 (ls.intersperse J)
  | [], _, h => nomatch h
  | [_], _, h => h
  | a :: b :: rest, P, h => by
    rw [columnParts_cons] at h
    rw [intersperse_two, columnParts_cons, columnParts_cons, List.map_cons]
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact List.mem_cons_self
    | inr h' =>
      obtain ⟨P', hP', e⟩ := List.mem_map.mp h'
      have ih := parts_woven_column hJ (b :: rest) P' hP'
      have e2 : (P'.1, P'.2 + down (J.h + 0) + down (a.h + 0)) = P := by
        rw [← e]
        refine congrArg (Prod.mk P'.1) (IVec.ext ?_ ?_)
        · simp only [IVec.add_x, down_x]
          omega
        · simp only [IVec.add_y, down_y]
          omega
      rw [← e2]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map_of_mem (f := fun Q : Layout α × IVec => (Q.1, Q.2 + down (a.h + 0)))
          (List.mem_map_of_mem (f := fun Q : Layout α × IVec => (Q.1, Q.2 + down (J.h + 0))) ih)))

omit [Moves IVec α] in
/-- The part between a part of a column and the next stands, in the woven column, where the
part's room ends. -/
private theorem joint_woven_column {gap : Nat} {J : Layout α} (hJ : J.h = gap) :
    ∀ (ls : List (Layout α)) (i : Nat) (P : Layout α × IVec),
      (columnParts gap ls)[i]? = some P → i + 1 < ls.length →
      (J, P.2 + down P.1.h) ∈ columnParts 0 (ls.intersperse J)
  | [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | [_], i, _, _, hl => absurd hl (by show ¬i + 1 < 1; omega)
  | a :: b :: rest, 0, P, h, _ => by
    rw [columnParts_cons, List.getElem?_cons_zero] at h
    rw [← Option.some.inj h, intersperse_two, columnParts_cons, columnParts_cons, List.map_cons]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  | a :: b :: rest, i + 1, P, h, hl => by
    rw [columnParts_cons, List.getElem?_cons_succ, List.getElem?_map] at h
    cases hP' : (columnParts gap (b :: rest))[i]? with
    | none =>
      rw [hP'] at h
      exact nomatch h
    | some P' =>
      rw [hP'] at h
      have e : (P'.1, P'.2 + down (a.h + gap)) = P := Option.some.inj h
      have ih := joint_woven_column hJ (b :: rest) i P' hP' (Nat.lt_of_succ_lt_succ hl)
      rw [intersperse_two, columnParts_cons, columnParts_cons, List.map_cons]
      have e2 : (J, P'.2 + down P'.1.h + down (J.h + 0) + down (a.h + 0)) =
          (J, P.2 + down P.1.h) := by
        rw [← e]
        refine congrArg (Prod.mk J) (IVec.ext ?_ ?_)
        · simp only [IVec.add_x, down_x]
          omega
        · simp only [IVec.add_y, down_y]
          omega
      rw [← e2]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map_of_mem (f := fun Q : Layout α × IVec => (Q.1, Q.2 + down (a.h + 0)))
          (List.mem_map_of_mem (f := fun Q : Layout α × IVec => (Q.1, Q.2 + down (J.h + 0))) ih)))

theorem ruledColumn_h (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) :
    (ruledColumn rule gap ls).h = (column gap ls).h := woven_column_h rfl ls

theorem ruledColumn_w (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) :
    (ruledColumn rule gap ls).w = (column gap ls).w := by
  have h := woven_column_w gap (rulePart rule (column gap ls).w gap) ls
  have h1 := h.1
  have h2 : (column 0 (ls.intersperse (rulePart rule (column gap ls).w gap))).w ≤
      max (column gap ls).w (column gap ls).w := h.2
  show (column 0 (ls.intersperse (rulePart rule (column gap ls).w gap))).w = (column gap ls).w
  omega

/-- **A ruled column has the room of the column.** -/
theorem room_ruledColumn (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) :
    (ruledColumn rule gap ls).room = (column gap ls).room := by
  show (⟨0, 0, (ruledColumn rule gap ls).w, (ruledColumn rule gap ls).h⟩ : IBox) = _
  rw [ruledColumn_w, ruledColumn_h]
  rfl

/-- **Each part stands in the ruled column at its step in the column**: the rules move no
part. -/
theorem stands_ruledColumn (rule : IBox → α) {gap : Nat} {ls : List (Layout α)}
    {P : Layout α × IVec} (h : P ∈ columnParts gap ls) :
    (ruledColumn rule gap ls).Stands P.2 P.1 :=
  stands_column (parts_woven_column rfl ls P h)

/-- **Each rule lies on its joint.** The rule between a part of a column and the next stands
where the part's room ends, and its room, as high as the gap, ends where the next part
begins. -/
theorem ruledColumn_joint (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) {i : Nat}
    {P Q : Layout α × IVec} (hP : (columnParts gap ls)[i]? = some P)
    (hQ : (columnParts gap ls)[i + 1]? = some Q) :
    (ruledColumn rule gap ls).Stands (P.2 + down P.1.h) (rulePart rule (column gap ls).w gap) ∧
      P.2.y + (P.1.h : Int) + (gap : Int) = Q.2.y := by
  have hl := congrArg List.length (columnParts_parts gap ls)
  rw [List.length_map] at hl
  have hi : i + 1 < ls.length := hl ▸ (List.getElem?_eq_some_iff.mp hQ).1
  exact ⟨stands_column (joint_woven_column rfl ls i P hP hi), columnParts_next gap ls hP hQ⟩

/-- **There are as many rules as joints**: a ruled column has the things of the column, and one
for each part but the last. -/
theorem ruledColumn_count (rule : IBox → α) (gap : Nat) (ls : List (Layout α)) :
    (ruledColumn rule gap ls).items.length = (column gap ls).items.length + (ls.length - 1) := by
  have h1 := congrArg List.length (column_items_map (f := fun _ : α => ()) (fun _ _ => rfl) 0
    (ls.intersperse (rulePart rule (column gap ls).w gap)))
  have h2 := congrArg List.length
    (column_items_map (f := fun _ : α => ()) (fun _ _ => rfl) gap ls)
  rw [List.length_map, List.length_map] at h1 h2
  show (column 0 (ls.intersperse (rulePart rule (column gap ls).w gap))).items.length = _
  rw [h1, h2]
  exact length_woven rfl ls

end

section

variable [Moves IVec α] [Boxed α]

/-- **A ruled column fits**, where its parts fit and each rule is inside the room that it is
drawn at. -/
theorem Fits.ruledColumn {rule : IBox → α} (hr : ∀ b : IBox, (Boxed.box (rule b)).Inside b)
    (gap : Nat) {ls : List (Layout α)} (h : ∀ l ∈ ls, l.Fits) :
    (ruledColumn rule gap ls).Fits :=
  Fits.column 0 _ fun l hl => by
    cases mem_woven hl with
    | inl e =>
      rw [e]
      exact fits_leaf (hr _)
    | inr m => exact h l m

/-- **A ruled column is clear**, where its parts fit and are clear and each rule is inside the
room that it is drawn at. -/
theorem Clear.ruledColumn {rule : IBox → α} (hr : ∀ b : IBox, (Boxed.box (rule b)).Inside b)
    (gap : Nat) {ls : List (Layout α)} (f : ∀ l ∈ ls, l.Fits) (c : ∀ l ∈ ls, l.Clear) :
    (ruledColumn rule gap ls).Clear :=
  Clear.column 0 _
    (fun l hl => by
      cases mem_woven hl with
      | inl e =>
        rw [e]
        exact fits_leaf (hr _)
      | inr m => exact f l m)
    fun l hl => by
      cases mem_woven hl with
      | inl e =>
        rw [e]
        exact clear_leaf _ _ _
      | inr m => exact c l m

end

end Layout

end Whatwg.Svg.Scene
