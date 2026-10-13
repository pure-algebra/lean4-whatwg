import Whatwg.Svg.Scene.Units.Laws

/-!
# WhatwgTest.Svg.UseUnits

The queue of lean4-effect4's sketch of living quantities, drawn as its units on
`Whatwg/Svg/Scene/Units.lean` (slice S22; ask W20). The sketch is
`docs/research/2026-10-13-living-quantities/sketch.html`: a queue of capacity 2 over nine
steps, placed by hand. The consumer is read at its checkout `6ad8f7b8d`, which has the queue's
cell (`src/Effect4/Library/Queue/Cell.lean`: `msgs`, `cap`, `takers`, `offers`) and has neither
the roles (`Library/Queue/View.lean`) nor the value pictures (`tools/Tools/View/Cell.lean`)
that the note names. This module imports nothing of that package: it restates the cell under
the consumer's names, and writes the fold that the note asks for.

**What is here, in the note's words.**

| The note's | Here |
| --- | --- |
| a place: `msgs`, `offers`, `takers` | a list of units; `Units.lane` |
| a bound: `msgs` by `cap` | `Units.slots c.cap c.msgs`, drawn by `Units.vessel` |
| an inlet, an outlet | `Units.Front`: the buffer and the offers have their front at the end, toward the outlet, and the takers at the start |
| an identity, a payload | the `Key` of a `Mark`; what `Units.Look.draw` shows |
| the marking: the cell and the roles to places with their units | `marking`, three places in a row |
| the flows of a step: the keyed join of two markings | `join Mark.key` of two markings; `Units.stays`, `Units.front_leaves`, `Units.back_enters` |

**What the consumer gains.** Its sketch has no law. Here every cell, and not only the ten of
the scene, has a buffer that fits and is clear (`buffer_fits`, `buffer_clear`) and a marking
that fits (`marking_fits`). A message that is in the buffer before a step and after it is one
thing that moves, in every step of every run (`Units.stays`), and after a take each message
behind the front is one slot nearer the outlet (`thirty_slides`).

One choice that is the consumer's to change: a message is keyed by its value, since the four
messages of the scene are four numbers. A queue that may hold a value twice keys a message by
its number in the journal, and the last control shows what the join does without that.

The lines are of three kinds: readers, which are laws of the kit applied to the scene's cells;
finite evaluations against the sketch; and controls, where a premise does not hold.
-/

namespace WhatwgTest.Svg.UseUnits

open Whatwg.Svg.Scene

/-! ## The queue's cell: the consumer's `cellFields` -/

/-- A waiting taker: its identity. The consumer's `takerFields`, less the hint. -/
structure Taker where
  id : Nat
  deriving DecidableEq, Repr

/-- A pending offer: its identity and the messages not yet accepted. The consumer's
`offerFields`, less the hint and the batch flag. -/
structure Offer where
  id : Nat
  rest : List Nat
  deriving DecidableEq, Repr

/-- The cell: the buffer, the capacity, the waiting takers and the pending offers. -/
structure Cell where
  msgs : List Nat := []
  cap : Nat := 2
  takers : List Taker := []
  offers : List Offer := []
  deriving DecidableEq, Repr

/-- **The scene of the sketch**: the cell before the first command and after each of the nine.
The front of each list is first. -/
def scene : List Cell :=
  [{},
    -- offer 10, request 1
    { msgs := [10] },
    -- offer 20, request 2
    { msgs := [10, 20] },
    -- offer 30, request 3: the buffer is full and the offer waits at the inlet
    { msgs := [10, 20], offers := [⟨3, [30]⟩] },
    -- take, request 4: 10 leaves, 20 slides, and the waiting 30 enters
    { msgs := [20, 30] },
    -- take, request 5
    { msgs := [30] },
    -- take, request 6
    {},
    -- take, request 7: the buffer is empty and the taker waits at the outlet
    { takers := [⟨7⟩] },
    -- offer 40, request 8: it is held and wakes the taker, who has not yet gone
    { msgs := [40], takers := [⟨7⟩] },
    -- request 7 resumes and takes 40
    {}]

/-- The cell after the command `i` of the scene, and before the first for `0`. -/
def cell (i : Nat) : Cell := scene.getD i {}

/-! ## What the consumer draws -/

/-- The key of a mark: a message by its value, a request by its identity, room by its slot.
The consumer's keys are strings; a type with constructors lets the kernel compare two. -/
inductive Key where
  | msg (value : Nat)
  | request (id : Nat)
  | room (slot : Nat)
  | group (i : Nat)
  deriving DecidableEq, Repr

/-- One mark of a picture, in whole pixels: its key, its box, a text, and whether it is drawn
hollow. -/
structure Mark where
  key : Key
  x : Int := 0
  y : Int := 0
  w : Int
  h : Int
  text : String := ""
  hollow : Bool := false
  deriving DecidableEq, Repr

/-- A mark moves by whole pixels. -/
instance : Moves IVec Mark where
  move d p := { p with x := p.x + d.x, y := p.y + d.y }
  move_zero p := by
    cases p
    simp only [IVec.zero_x, IVec.zero_y, Int.add_zero]
  move_move d e p := by
    cases p
    simp only [IVec.add_x, IVec.add_y, Int.add_assoc]

/-- The room of a mark. -/
instance : Boxed Mark where
  box p := ⟨p.x, p.y, p.x + p.w, p.y + p.h⟩
  box_move d p := IBox.ext rfl rfl (Int.add_right_comm p.x d.x p.w)
    (Int.add_right_comm p.y d.y p.h)

/-- A moved mark keeps its key. -/
theorem keeps : Units.Keeps Mark.key := fun _ _ => rfl

/-- A slot, the gap between two slots, and the gap between two places. The sketch draws a
droplet 21 wide and two droplets 28 apart. -/
def SLOT : Nat := 22
def GAP : Nat := 6
def CHANNEL : Nat := 12

/-- **The buffer's look**: a droplet with its value for a message held, a hollow slot for
room, and a counted mark where one stands for several. -/
def droplet : Units.Look Nat Mark where
  w := SLOT
  h := SLOT
  gap := GAP
  draw
    | .held v => { key := .msg v, w := SLOT, h := SLOT, text := toString v }
    | .mark i vs => { key := .group i, w := SLOT, h := SLOT, text := toString vs.length }
    | .room i => { key := .room i, w := SLOT, h := SLOT, hollow := true }

/-- **A parked request**: the hollow box of an offer or of a taker that waits. -/
def parked {υ : Type} (id : υ → Nat) : Units.Look υ Mark where
  w := SLOT
  h := SLOT
  gap := GAP
  draw
    | .held u => { key := .request (id u), w := SLOT, h := SLOT, hollow := true }
    | .mark i _ => { key := .group i, w := SLOT, h := SLOT }
    | .room i => { key := .room i, w := SLOT, h := SLOT, hollow := true }

/-- A mark at the origin, one slot wide and one high, is inside a slot. -/
theorem slot_inside (k : Key) (t : String) (b : Bool) :
    (Boxed.box ({ key := k, w := SLOT, h := SLOT, text := t, hollow := b } : Mark)).Inside
      ⟨0, 0, SLOT, SLOT⟩ :=
  ⟨Int.le_refl 0, Int.le_of_eq (Int.zero_add _), Int.le_refl 0, Int.le_of_eq (Int.zero_add _)⟩

/-- What the buffer's look draws of a slot is inside the slot. -/
theorem droplet_inside (s : Slot Nat) :
    (Boxed.box (droplet.draw s)).Inside ⟨0, 0, droplet.w, droplet.h⟩ := by
  cases s with
  | held v => exact slot_inside _ _ _
  | mark i vs => exact slot_inside _ _ _
  | room i => exact slot_inside _ _ _

/-- What the look of a parked request draws of a slot is inside the slot. -/
theorem parked_inside {υ : Type} (id : υ → Nat) (s : Slot υ) :
    (Boxed.box ((parked id).draw s)).Inside ⟨0, 0, (parked id).w, (parked id).h⟩ := by
  cases s with
  | held u => exact slot_inside _ _ _
  | mark i us => exact slot_inside _ _ _
  | room i => exact slot_inside _ _ _

/-! ## The marking: a cell as its places -/

/-- **The buffer**: `msgs` by `cap`, its front at the outlet on the right. -/
def buffer (c : Cell) : Layout Mark := Units.vessel droplet .atEnd c.cap c.msgs

/-- **The offers that wait at the inlet**: a lane of parked requests, the front nearest the
buffer, and over each the message that it holds. -/
def inlet (c : Cell) : Layout Mark :=
  Layout.over (Units.row (parked Offer.id) .atEnd (Units.lane c.offers))
    (Units.row droplet .atEnd (Units.lane (c.offers.flatMap Offer.rest)))

/-- **The takers that wait at the outlet**: a lane of parked requests, the front nearest the
buffer. -/
def outlet (c : Cell) : Layout Mark := Units.row (parked Taker.id) .atStart (Units.lane c.takers)

/-- A part at the end of a width, so that what follows it does not move when it grows. -/
def ended (width : Nat) (a : Layout Mark) : Layout Mark := Layout.inset (width - a.w) 0 0 0 a

/-- The room kept for the inlet: two slots. -/
def INLET : Nat := SLOT + GAP + SLOT

/-- **The marking of a cell**: the inlet, the buffer and the outlet in a row. -/
def marking (c : Cell) : Layout Mark :=
  Layout.row CHANNEL [ended INLET (inlet c), buffer c, outlet c]

/-! ## Laws of every cell -/

/-- **The buffer of every cell fits**: each droplet and each hollow slot is inside its room. -/
theorem buffer_fits (c : Cell) : (buffer c).Fits := Units.row_fits _ fun s _ => droplet_inside s

/-- **No two slots of the buffer of any cell share a pixel.** -/
theorem buffer_clear (c : Cell) : (buffer c).Clear := Units.row_clear _ fun s _ => droplet_inside s

/-- **The marking of every cell fits**: each mark is inside the room of the marking. -/
theorem marking_fits (c : Cell) : (marking c).Fits :=
  Layout.Fits.row CHANNEL _ fun l hl => by
    cases List.mem_cons.mp hl with
    | inl e =>
      rw [e]
      exact Layout.Fits.inset (Layout.Fits.over
        (Units.row_fits _ fun s _ => parked_inside Offer.id s)
        (Units.row_fits _ fun s _ => droplet_inside s))
    | inr h =>
      cases List.mem_cons.mp h with
      | inl e =>
        rw [e]
        exact buffer_fits c
      | inr h' =>
        rw [List.mem_singleton.mp h']
        exact Units.row_fits _ fun s _ => parked_inside Taker.id s

/-- **The count is kept in every cell**: the slots of the buffer stand for exactly the
messages, the front first. -/
theorem buffer_units (c : Cell) : (Units.slots c.cap c.msgs).flatMap Slot.units = c.msgs :=
  Units.slots_units c.cap c.msgs

/-! ## Readers: the steps of the scene -/

/-- **Take, request 4**, the step that the sketch draws: the buffer is full and an offer
waits; 10 leaves, 20 slides and 30 enters. The message 20 is in the buffer before and after,
so nothing that leaves and nothing that enters has its key: it is one droplet that moves. -/
theorem twenty_stays :
    (∀ a ∈ (join Mark.key (buffer (cell 3)).items (buffer (cell 4)).items).exit,
        a.key ≠ Key.msg 20) ∧
      ∀ a ∈ (join Mark.key (buffer (cell 3)).items (buffer (cell 4)).items).enter,
        a.key ≠ Key.msg 20 :=
  Units.stays keeps droplet .atEnd .atEnd 2 2 (List.mem_cons_of_mem 10 List.mem_cons_self)
    List.mem_cons_self

/-- **Take, request 5**: 20 leaves at the front, and 30 behind it updates from the second slot
to the first. -/
theorem thirty_slides :
    (Units.stand droplet .atEnd 2 1 (.held 30), Units.stand droplet .atEnd 2 0 (.held 30)) ∈
      (join Mark.key (buffer (cell 4)).items (buffer (cell 5)).items).update :=
  Units.front_leaves keeps droplet .atEnd 20 (Or.inr (by decide)) rfl
    (show ((buffer (cell 4)).items.map Mark.key).Nodup by decide)

/-- **Offer 20, request 2**: 20 enters at the back, and 10 at the front updates from its
droplet to the same droplet. -/
theorem ten_rests :
    (Units.stand droplet .atEnd 2 0 (.held 10), Units.stand droplet .atEnd 2 0 (.held 10)) ∈
      (join Mark.key (buffer (cell 1)).items (buffer (cell 2)).items).update :=
  Units.back_enters Mark.key droplet .atEnd 20 (Or.inr (by decide)) rfl
    (show ((buffer (cell 1)).items.map Mark.key).Nodup by decide)

/-- A pool of thirty permits with twenty-three free is past what a reader counts: one mark
stands for five. The marks stand for exactly the twenty-three. -/
theorem permits_kept :
    (Units.marks 5 30 (List.range 23)).flatMap Slot.units = List.range 23 :=
  Units.marks_units 5 30 (List.range 23)

/-! ## Finite evaluations against the sketch -/

/-- The keys and the places across of a layout's marks. -/
def places (l : Layout Mark) : List (Key × Int) := l.items.map fun p => (p.key, p.x)

-- The counts of the scene are the counts of the sketch's third picture: how many messages are
-- held after each command, how many offers wait and how many takers wait.
#guard scene.map (fun c => c.msgs.length) == [0, 1, 2, 2, 2, 1, 0, 0, 1, 0]
#guard scene.map (fun c => c.offers.length) == [0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
#guard scene.map (fun c => c.takers.length) == [0, 0, 0, 0, 0, 0, 0, 1, 1, 0]

-- The full buffer, as the sketch's first picture has it: 20 to the left and 10, the front, to
-- the right, 28 apart.
#guard places (buffer (cell 2)) == [(.msg 20, 0), (.msg 10, 28)]

-- One message and one slot of room (after offer 40): the droplet at the outlet's end, and the
-- hollow slot behind it under its own number.
#guard places (buffer (cell 8)) == [(.room 1, 0), (.msg 40, 28)]
#guard (buffer (cell 8)).items.map (·.hollow) == [true, false]

-- The room of the buffer does not depend on what it holds: two slots and a gap, one slot high.
#guard scene.map (fun c => ((buffer c).w, (buffer c).h)) == List.replicate 10 (50, 22)

-- The marking before take, request 4: the offer's box and its message at the end of the
-- inlet's room, and the buffer one channel after it.
#guard places (marking (cell 3)) ==
  [(.request 3, 28), (.msg 30, 28), (.msg 20, 62), (.msg 10, 90)]

-- **The flows of that step are its join.** The offer's box and the message 10 leave; nothing
-- enters; 30 travels from the inlet to the back slot of the buffer and 20 slides one slot to
-- the front. The key that leaves one place and enters another is one move, with no word of
-- the caller's.
#guard (join Mark.key (marking (cell 3)).items (marking (cell 4)).items).exit.map (·.key) ==
  [.request 3, .msg 10]
#guard (join Mark.key (marking (cell 3)).items (marking (cell 4)).items).enter.isEmpty
#guard (join Mark.key (marking (cell 3)).items (marking (cell 4)).items).update.map
    (fun p => (p.2.key, p.1.x, p.2.x)) == [(.msg 30, 28, 62), (.msg 20, 62, 90)]

-- The taker that waits stands one channel after the buffer, and stays there while the
-- message that wakes it is held.
#guard places (marking (cell 7)) == [(.room 1, 62), (.room 0, 90), (.request 7, 124)]
#guard places (marking (cell 8)) == [(.room 1, 62), (.msg 40, 90), (.request 7, 124)]

-- Marks of five for twenty-three permits in a pool of thirty: four whole marks, one mark for
-- the three that are left, and one slot of room.
#guard (Units.marks 5 30 (List.range 23)).map (fun s => s.units.length) == [5, 5, 5, 5, 3, 0]
#guard (Units.row droplet .atStart (Units.marks 5 30 (List.range 23))).items.map (·.text) ==
  ["5", "5", "5", "5", "3", ""]

-- The bound decides the form, and not the count: a buffer of two is drawn unit by unit when
-- empty and when full, and a pool of thirty by marks.
#guard Units.per 12 5 2 == 1
#guard Units.per 12 5 30 == 5
#guard (Units.shown 12 5 2 [10]).map (fun s => s.units.length) == [1, 0]
#guard (Units.shown 12 5 2 [10, 20]).map (fun s => s.units.length) == [1, 1]
#guard (Units.shown 12 5 30 [10]).map (fun s => s.units.length) == [1, 0, 0, 0, 0, 0]

/-! ## Controls -/

-- A place over its bound keeps every unit and shows no room: `Units.length_slots_of_le` asks
-- that the count is within the bound, and this is why.
#guard (Units.slots 2 [10, 20, 30]).length == 3

-- With its front at the end, a place over its bound grows at its origin, so a unit does not
-- slide in the row's own room when the front leaves: 20 stands at 28 before and after.
-- `Units.front_leaves` asks for the bound there, or for the front at the start.
#guard places (Units.vessel droplet .atEnd 0 [10, 20, 30]) ==
  [(.msg 30, 0), (.msg 20, 28), (.msg 10, 56)]
#guard places (Units.vessel droplet .atEnd 0 [20, 30]) == [(.msg 30, 0), (.msg 20, 28)]
-- With the front at the start it slides, whatever the bound.
#guard places (Units.vessel droplet .atStart 0 [10, 20, 30]) ==
  [(.msg 10, 0), (.msg 20, 28), (.msg 30, 56)]
#guard places (Units.vessel droplet .atStart 0 [20, 30]) == [(.msg 20, 0), (.msg 30, 28)]

-- A queue that holds one value twice, with messages keyed by their value: the keys of the
-- picture are not distinct. After a take the join has one pair for the two droplets, and
-- nothing leaves, though a message left: its key is still in the picture.
-- `Units.front_leaves` asks for distinct keys, and this is why.
#guard !decide (((Units.vessel droplet .atEnd 2 [7, 7]).items.map Mark.key).Nodup)
#guard (join Mark.key (Units.vessel droplet .atEnd 2 [7, 7]).items
    (Units.vessel droplet .atEnd 2 [7]).items).update.map (fun p => (p.1.x, p.2.x)) == [(0, 28)]
#guard (join Mark.key (Units.vessel droplet .atEnd 2 [7, 7]).items
    (Units.vessel droplet .atEnd 2 [7]).items).exit.isEmpty

end WhatwgTest.Svg.UseUnits
