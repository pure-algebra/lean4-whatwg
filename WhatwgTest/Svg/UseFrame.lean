import Whatwg.Svg.Scene.Layout.Frame

/-!
# WhatwgTest.Svg.UseFrame

A picture of a value on `Whatwg/Svg/Scene/Layout/Frame.lean` (slice S22; ask W15 of
`docs/research/2026-10-12-whatwg-requests.md`).

**This is not a port of a file.** The ask names `tools/Tools/View/Cell.lean` of lean4-effect4,
and that file is not in the consumer's checkout on this machine, which is at `6ad8f7b8d`. This
module is written from the words of the ask: "a record is a panel whose rows are ruled apart, a
list a row of cells ruled apart, each in a frame", with "a part centred down a height, as
`centred` is across". When the consumer's file is at hand, its own functions replace `draw`
here, and the laws below are what they should keep.

- `Mark`: what a value picture draws. A cell of text, a rule, a frame, each with its box.
- `Value`: a text, a record of values, a list of values.
- `draw width v`: the picture. A text is a cell. A record is its rows one above the other with
  a rule at each joint, inside a margin, in a frame. A list is its cells side by side, each in
  the middle of the height of the highest, with a rule at each joint, inside a margin, in a
  frame.

What holds of every value, by a fold with one case for each constructor:

- `draw_fits`: every mark is inside the room of the picture.
- `record_in_frame`, `list_in_frame`: the first mark of a record or a list is a frame at the
  room of its picture, and every mark of it is inside that room.

What holds of a column of texts:

- `texts_clear`: no two of the cells and rules share room. The frame is not among them: it
  holds them all, and the first control shows it.
- `rule_between`: the rule between two rows stands where the first ends, and its room ends
  where the second begins. It is `Layout.ruledColumn_joint` read at two rows.

The guards are of three kinds. Finite evaluations: a record, and a list with that record in
it, against boxes computed by hand in the comments. One evaluation of what no law here says:
the marks of the nested picture other than its frames share no room. Controls: a framed part
is not clear; and a row that is not ruled has no mark in its gap.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UseFrame

open Whatwg.Svg.Scene

/-! ## What is drawn -/

/-- What a value picture draws: a cell of text, a rule between two parts, a frame around a
part. Each has its box. -/
inductive Mark where
  | cell (text : String) (box : IBox)
  | rule (box : IBox)
  | frame (box : IBox)
  deriving DecidableEq, Repr

/-- The box of a mark. -/
def Mark.box : Mark → IBox
  | .cell _ b => b
  | .rule b => b
  | .frame b => b

/-- Whether a mark is a frame. -/
def Mark.isFrame : Mark → Bool
  | .frame _ => true
  | _ => false

/-- A mark moves with its box. -/
instance : Moves IVec Mark where
  move d
    | .cell s b => .cell s (Moves.move d b)
    | .rule b => .rule (Moves.move d b)
    | .frame b => .frame (Moves.move d b)
  move_zero
    | .cell s b => congrArg (Mark.cell s) (Moves.move_zero b)
    | .rule b => congrArg Mark.rule (Moves.move_zero b)
    | .frame b => congrArg Mark.frame (Moves.move_zero b)
  move_move d e
    | .cell s b => congrArg (Mark.cell s) (Moves.move_move d e b)
    | .rule b => congrArg Mark.rule (Moves.move_move d e b)
    | .frame b => congrArg Mark.frame (Moves.move_move d e b)

/-- The room of a mark is its box. -/
instance : Boxed Mark where
  box := Mark.box
  box_move d m := by cases m <;> rfl

/-- A rule is drawn at the whole of its joint, and a frame at the whole of its room. -/
theorem rule_inside (b : IBox) : (Boxed.box (Mark.rule b)).Inside b := IBox.Inside.refl b

theorem frame_inside (b : IBox) : (Boxed.box (Mark.frame b)).Inside b := IBox.Inside.refl b

/-! ## The picture of a value -/

/-- A value: a text, a record of values, a list of values. -/
inductive Value where
  | atom (text : String)
  | record (rows : List Value)
  | list (items : List Value)

/-- The height of a row of text, the margin inside a frame, and the gap that a rule lies in. -/
def ROWH : Nat := 24
def PAD : Nat := 8
def GAP : Nat := 8

/-- A cell of text. `width` is how wide a text is drawn. -/
def cell (width : String → Nat) (s : String) : Layout Mark :=
  Layout.leaf (width s) ROWH (.cell s ⟨0, 0, width s, ROWH⟩)

/-- A part inside a margin, in a frame. -/
def panel (a : Layout Mark) : Layout Mark :=
  Layout.framed Mark.frame (Layout.inset PAD PAD PAD PAD a)

mutual

/-- **The picture of a value**: a fold. -/
def draw (width : String → Nat) : Value → Layout Mark
  | .atom s => cell width s
  | .record rows => panel (Layout.ruledColumn Mark.rule GAP (drawAll width rows))
  | .list items =>
    panel (Layout.ruledRow Mark.rule GAP
      ((drawAll width items).map
        (Layout.centredDown (Layout.row GAP (drawAll width items)).h)))

/-- Values drawn. -/
def drawAll (width : String → Nat) : List Value → List (Layout Mark)
  | [] => []
  | v :: vs => draw width v :: drawAll width vs

end

theorem cell_fits (width : String → Nat) (s : String) : (cell width s).Fits :=
  Layout.fits_leaf (IBox.Inside.refl _)

/-- A part in a panel fits where the part fits. -/
theorem panel_fits {a : Layout Mark} (ha : a.Fits) : (panel a).Fits :=
  Layout.Fits.framed ha.inset (frame_inside _)

mutual

/-- **Every mark of the picture of a value is inside the room of the picture.** -/
theorem draw_fits (width : String → Nat) : ∀ v : Value, (draw width v).Fits
  | .atom s => by
    rw [draw]
    exact cell_fits width s
  | .record rows => by
    rw [draw]
    exact panel_fits (Layout.Fits.ruledColumn rule_inside GAP (drawAll_fits width rows))
  | .list items => by
    rw [draw]
    exact panel_fits (Layout.Fits.ruledRow rule_inside GAP fun l hl => by
      obtain ⟨m, hm, e⟩ := List.mem_map.mp hl
      rw [← e]
      exact (drawAll_fits width items m hm).centredDown)

/-- The same for a list of values. -/
theorem drawAll_fits (width : String → Nat) : ∀ (vs : List Value), ∀ l ∈ drawAll width vs, l.Fits
  | [], _, h => by
    rw [drawAll] at h
    exact nomatch h
  | v :: vs, l, h => by
    rw [drawAll] at h
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact draw_fits width v
    | inr h' => exact drawAll_fits width vs l h'

end

/-- **Every mark of a part in a panel is inside the box of the panel's frame**: "each in a
frame". The frame is the first mark, at the room. -/
theorem panel_in_frame {a : Layout Mark} (ha : a.Fits) :
    (panel a).items.head? = some (.frame (panel a).room) ∧
      ∀ m ∈ (panel a).items, (Boxed.box m).Inside (panel a).room :=
  ⟨rfl, panel_fits ha⟩

/-- **A record is in a frame**: its first mark is a frame at the room of its picture, and every
mark of it is inside that room. -/
theorem record_in_frame (width : String → Nat) (rows : List Value) :
    (draw width (.record rows)).items.head? = some (.frame (draw width (.record rows)).room) ∧
      ∀ m ∈ (draw width (.record rows)).items,
        (Boxed.box m).Inside (draw width (.record rows)).room :=
  ⟨by rw [draw]; rfl, draw_fits width (.record rows)⟩

/-- **A list is in a frame.** -/
theorem list_in_frame (width : String → Nat) (items : List Value) :
    (draw width (.list items)).items.head? = some (.frame (draw width (.list items)).room) ∧
      ∀ m ∈ (draw width (.list items)).items,
        (Boxed.box m).Inside (draw width (.list items)).room :=
  ⟨by rw [draw]; rfl, draw_fits width (.list items)⟩

/-- **The cells and the rules of a column of texts share no room**, for every list of texts. -/
theorem texts_clear (width : String → Nat) (texts : List String) :
    (Layout.ruledColumn Mark.rule GAP (texts.map (cell width))).Clear :=
  Layout.Clear.ruledColumn rule_inside GAP
    (fun l hl => by
      obtain ⟨s, _, e⟩ := List.mem_map.mp hl
      rw [← e]
      exact cell_fits width s)
    fun l hl => by
      obtain ⟨s, _, e⟩ := List.mem_map.mp hl
      rw [← e]
      exact Layout.clear_leaf _ _ _

/-- A reader of `Layout.ruledColumn_joint`: between two rows of a record, the rule stands where
the first row ends, and its room ends where the second begins. -/
theorem rule_between (a b : Layout Mark) :
    (Layout.ruledColumn Mark.rule GAP [a, b]).Stands (0 + Layout.down a.h)
        (Layout.rulePart Mark.rule (Layout.column GAP [a, b]).w GAP) ∧
      (0 : Int) + a.h + GAP = (0 + Layout.down (a.h + GAP)).y :=
  Layout.ruledColumn_joint Mark.rule GAP [a, b] (i := 0) (P := (a, 0))
    (Q := (b, 0 + Layout.down (a.h + GAP))) rfl rfl

/-! ## Two values, drawn -/

/-- How wide the texts of the examples are drawn. -/
def width : String → Nat
  | "a" => 8
  | "bc" => 16
  | _ => 24

/-- A record of two texts. -/
def pair : Value := .record [.atom "a", .atom "bc"]

-- By hand. The cells are 8 by 24 and 16 by 24. The column is 16 wide, so the rule's joint is
-- 16 by 8, between the rows: from 24 down to 32. The second row stands at 32, and the column
-- is 56 high. The margin moves each by 8 and 8, and the room is 32 by 72, which is the frame.
#guard ((draw width pair).w, (draw width pair).h) == (32, 72)
#guard (draw width pair).items ==
  [.frame ⟨0, 0, 32, 72⟩, .cell "a" ⟨8, 8, 16, 32⟩, .rule ⟨8, 32, 24, 40⟩,
    .cell "bc" ⟨8, 40, 24, 64⟩]

/-- A list of a text and that record. -/
def nested : Value := .list [.atom "a", pair]

-- By hand. The row is as high as the record, 72, so the text stands in the middle of 72: at
-- (72 - 24) / 2 = 24 down. The joint is 8 by 72, from 8 across to 16, and the record stands at
-- 16. The row is 8 + 8 + 32 = 48 wide. The margin moves each by 8 and 8, and the room is 64 by
-- 88.
#guard ((draw width nested).w, (draw width nested).h) == (64, 88)
#guard (draw width nested).items ==
  [.frame ⟨0, 0, 64, 88⟩, .cell "a" ⟨8, 32, 16, 56⟩, .rule ⟨16, 8, 24, 80⟩,
    .frame ⟨24, 8, 56, 80⟩, .cell "a" ⟨32, 16, 40, 40⟩, .rule ⟨32, 40, 48, 48⟩,
    .cell "bc" ⟨32, 48, 48, 72⟩]

-- What no law here says, evaluated for this picture: its marks other than its two frames share
-- no room.
#guard decide (((draw width nested).items.filter fun m => !m.isFrame).Pairwise
  fun x y => (Boxed.box x).Disjoint (Boxed.box y))

/-! ## Controls -/

-- A framed part is not clear: the frame holds the cell. The part without its frame is.
#guard !decide (panel (cell width "a")).Clear
#guard decide (Layout.inset PAD PAD PAD PAD (cell width "a")).Clear

-- A rule is one mark more for each joint. A row of three cells that is not ruled has three
-- marks, and ruled it has five, in a room of one size.
#guard (Layout.row GAP [cell width "a", cell width "bc", cell width "a"]).items.length == 3
#guard (Layout.ruledRow Mark.rule GAP
  [cell width "a", cell width "bc", cell width "a"]).items.length == 5
#guard (Layout.ruledRow Mark.rule GAP [cell width "a", cell width "bc", cell width "a"]).room ==
  (Layout.row GAP [cell width "a", cell width "bc", cell width "a"]).room

-- One part has no joint and no rule.
#guard (Layout.ruledRow Mark.rule GAP [cell width "a"]).items.length == 1

end WhatwgTest.Svg.UseFrame
