import Whatwg.Svg.Scene.Layout

/-!
# Whatwg.Svg.Scene.Units

Owner: a quantity drawn as its units (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; ask W20 of
`docs/research/2026-10-12-whatwg-requests.md`).

A number in a picture says little. Two messages in a buffer of two say more as two droplets in
a vessel with two slots: the reader sees how many, in which order, and how much room is left. A
place holds its units in order, the front first. A place with a bound is drawn as one slot for
each unit of the bound: the first slots hold the units and the rest are room. A place with no
bound is a lane of its units. Past a size that a reader can count, one mark stands for several
units, as in Isotype: the mark is repeated and never scaled.

lean4-effect4 draws a queue so by hand (`docs/research/2026-10-13-living-quantities/sketch.html`):
the buffer is a vessel of `cap` slots, and the offers and takers that wait are lanes. This
module places the slots. A caller says how a slot is drawn, and converts no data.

- `Slot υ`: what stands in one slot: a unit that is held, a mark with the units it stands for,
  or room. `Slot.units` is the units that a slot stands for.
- `Units.slots bound us`: the slots of a place with a bound. `Units.lane us`: the slots of a
  place with none. `Units.marks k bound us`: the slots where one mark stands for `k` units.
  `Units.shown threshold k bound us` chooses between the two by the bound, and
  `Units.per threshold k bound` is how many units a mark then stands for.
- `Units.Look υ α`: how a caller draws a slot: its size, the gap between two, and the thing
  drawn of a slot at the slot's own origin.
- `Units.Front`: at which end of the row the front of the place is.
- `Units.row look front ss`: **the slots, placed**, as a `Layout` of the caller's things.
  `Units.vessel look front bound us` is the row of `slots bound us`.
- `Units.stand look front total i s`: the thing of the slot `i` of a row of `total` slots.

What the laws say:

- **The count is kept** (`slots_units`, `marks_units`, `shown_units`): the slots stand for
  exactly the units, in their order, with nothing left out and nothing twice. With marks the
  remainder is included.
- **The front stays at the front, and the order is kept** (`slots_held`): the unit at the place
  `i` is in the slot `i`. So the front is in the slot `0`.
- **The room is shown** (`length_slots`, `slots_room`): a place within its bound has exactly
  `bound` slots, and each slot from the count on is room, under its own number.
- **A mark stands for `k` units** (`groups_full`, `groups_bounds`, `length_groups`): every mark
  but the last stands for exactly `k`, the last for what is left, which is one unit at least
  and `k` at most, and the marks are as many as `k` goes into the count, rounded up.
- **The picture fits and is clear** (`row_fits`, `row_clear`): where what is drawn of each slot
  is inside the slot, each thing of the row is inside the row's room and no two share room.
  `row_w` and `row_h` are the room: as many slots and gaps across, and one slot down.
- **Where a slot stands** (`row_items`, `mem_row`): the slot `i` stands `i` slots and gaps from
  the front's end of the row, and the thing drawn there is what the look draws, moved.
- **One slot over is one move** (`stand_succ_atStart`, `stand_succ_atEnd`).

The laws of a step, where a unit leaves at the front or enters at the back, are in
`Whatwg/Svg/Scene/Units/Laws.lean`, against the join by key of `Whatwg/Svg/Scene/Join.lean`.

Three decisions, and their reasons.

- **What the remainder draws.** Where the count is not a multiple of `k`, the last mark carries
  the units that are left, fewer than `k`. The caller's look receives them and draws a part of
  a mark, as Isotype cuts a figure. They are not dropped and not rounded up to a whole mark, so
  the count that a reader takes from the picture is the count.
- **A mark is named by its number and room by its number**, and a held unit by itself. Above
  the threshold a unit has no place of its own: marks do not slide when the front leaves, the
  last mark shrinks. So a picture of marks changes by one thing at most in a step.
- **The choice between units and marks is by the bound and not by the count** (`shown`,
  `per`), so that a picture does not change its form while a place fills.

What this module does not claim: slots in more than one row, or down a column; a place over
its bound keeps every unit and shows no room, and `length_slots` says how many slots it then
has; anything of the look's things beyond their boxes; that `marks` shows the room inside a
mark that is not full, which the look draws from the units it is given.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- **What stands in one slot of a place.** -/
inductive Slot (υ : Type) where
  /-- One unit, held. -/
  | held (u : υ)
  /-- One mark that stands for several units: its number from the front, and the units. -/
  | mark (i : Nat) (us : List υ)
  /-- Room: the slot of this number from the front, with nothing in it. -/
  | room (i : Nat)
  deriving Repr, DecidableEq

namespace Slot

variable {υ : Type}

/-- The units that a slot stands for: one, those of a mark, or none. -/
def units : Slot υ → List υ
  | held u => [u]
  | mark _ us => us
  | room _ => []

end Slot

namespace Units

variable {υ α : Type}

/-! ## The slots of a place -/

/-- Slots of room, `count` of them, numbered from `first`. -/
def rooms (first : Nat) : Nat → List (Slot υ)
  | 0 => []
  | count + 1 => Slot.room first :: rooms (first + 1) count

/-- **The slots of a place with a bound**: one for each unit, the front first, and then room up
to the bound. -/
def slots (bound : Nat) (us : List υ) : List (Slot υ) :=
  us.map Slot.held ++ rooms us.length (bound - us.length)

/-- **The slots of a place with no bound**: a lane of its units, the front first. -/
def lane (us : List υ) : List (Slot υ) := us.map Slot.held

/-- The units in groups of `k`, the front first: each group but the last has `k` units, and the
last has what is left. A group has one unit at least, so `k = 0` groups as `k = 1` does. The
first number is fuel: the length of the list is enough. -/
def groups (k : Nat) : Nat → List υ → List (List υ)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, u :: us => (u :: us.take (k - 1)) :: groups k fuel (us.drop (k - 1))

/-- Groups as marks, numbered from `i`. -/
def marksFrom (i : Nat) : List (List υ) → List (Slot υ)
  | [] => []
  | g :: gs => Slot.mark i g :: marksFrom (i + 1) gs

/-- How many marks of `k` units hold `n` units: `n / k`, rounded up. -/
def marksFor (k n : Nat) : Nat := (n + (k - 1)) / k

/-- **The slots of a place where one mark stands for `k` units**: the marks, the front first,
and then room for the marks that the bound still allows. The last mark stands for what is
left. -/
def marks (k bound : Nat) (us : List υ) : List (Slot υ) :=
  marksFrom 0 (groups k us.length us) ++
    rooms (groups k us.length us).length (marksFor k bound - (groups k us.length us).length)

/-- **How many units a mark stands for**, by the bound of the place: one up to the threshold,
and `k` above it. The bound decides and not the count, so a place does not change its form
while it fills. -/
def per (threshold k bound : Nat) : Nat := if bound ≤ threshold then 1 else k

/-- **The slots of a place, by its bound**: one for each unit up to the threshold, and above
it marks of `k` units. -/
def shown (threshold k bound : Nat) (us : List υ) : List (Slot υ) :=
  if bound ≤ threshold then slots bound us else marks k bound us

/-! ### The count is kept -/

theorem rooms_zero (first : Nat) : (rooms first 0 : List (Slot υ)) = [] := rfl

theorem rooms_succ (first count : Nat) :
    (rooms first (count + 1) : List (Slot υ)) = Slot.room first :: rooms (first + 1) count := rfl

theorem length_rooms : ∀ (count first : Nat), (rooms first count : List (Slot υ)).length = count
  | 0, _ => rfl
  | count + 1, first => congrArg (· + 1) (length_rooms count (first + 1))

/-- Room stands for no unit. -/
theorem rooms_units : ∀ (count first : Nat),
    (rooms first count : List (Slot υ)).flatMap Slot.units = []
  | 0, _ => rfl
  | count + 1, first => rooms_units count (first + 1)

/-- The slot `j` of some room is the room of the number `first + j`. -/
theorem rooms_getElem? : ∀ (count first j : Nat), j < count →
    (rooms first count : List (Slot υ))[j]? = some (Slot.room (first + j))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => rfl
  | count + 1, first, j + 1, h => by
    have ih : (rooms (first + 1) count : List (Slot υ))[j]? = some (Slot.room (first + 1 + j)) :=
      rooms_getElem? count (first + 1) j (Nat.lt_of_succ_lt_succ h)
    have e : first + 1 + j = first + (j + 1) := by omega
    rw [e] at ih
    exact ih

theorem lane_units : ∀ us : List υ, (lane us).flatMap Slot.units = us
  | [] => rfl
  | u :: us => congrArg (u :: ·) (lane_units us)

/-- A place with the bound `0` is a lane. -/
theorem slots_zero (us : List υ) : slots 0 us = lane us := by
  show us.map Slot.held ++ rooms us.length (0 - us.length) = us.map Slot.held
  rw [Nat.zero_sub, rooms_zero, List.append_nil]

/-- **The count is kept**: the slots stand for exactly the units, in their order. -/
theorem slots_units (bound : Nat) (us : List υ) : (slots bound us).flatMap Slot.units = us := by
  show (lane us ++ rooms us.length (bound - us.length)).flatMap Slot.units = us
  rw [List.flatMap_append, lane_units, rooms_units, List.append_nil]

/-- **How many slots a place has**: its bound, or its count where that is more. -/
theorem length_slots (bound : Nat) (us : List υ) :
    (slots bound us).length = max bound us.length := by
  show (us.map Slot.held ++ rooms us.length (bound - us.length)).length = max bound us.length
  rw [List.length_append, List.length_map, length_rooms]
  omega

/-- **The room is shown**: a place within its bound has exactly `bound` slots. -/
theorem length_slots_of_le {bound : Nat} {us : List υ} (h : us.length ≤ bound) :
    (slots bound us).length = bound := by
  rw [length_slots]
  omega

/-- **The front stays at the front, and the order is kept**: the unit at the place `j` is in
the slot `j`. -/
theorem slots_held (bound : Nat) {us : List υ} {j : Nat} {u : υ} (h : us[j]? = some u) :
    (slots bound us)[j]? = some (Slot.held u) := by
  have hj : j < us.length := (List.getElem?_eq_some_iff.mp h).1
  show (us.map Slot.held ++ rooms us.length (bound - us.length))[j]? = some (Slot.held u)
  rw [List.getElem?_append_left (by rw [List.length_map]; exact hj), List.getElem?_map, h]
  rfl

/-- **Each slot from the count on is room**, under its own number. -/
theorem slots_room {bound : Nat} {us : List υ} {j : Nat} (h1 : us.length ≤ j) (h2 : j < bound) :
    (slots bound us)[j]? = some (Slot.room j) := by
  show (us.map Slot.held ++ rooms us.length (bound - us.length))[j]? = some (Slot.room j)
  rw [List.getElem?_append_right (by rw [List.length_map]; exact h1), List.length_map,
    rooms_getElem? (bound - us.length) us.length (j - us.length) (by omega)]
  have e : us.length + (j - us.length) = j := by omega
  rw [e]

/-- A unit of the place is held in one of its slots. -/
theorem held_mem_slots (bound : Nat) {us : List υ} {u : υ} (h : u ∈ us) :
    Slot.held u ∈ slots bound us :=
  List.mem_append_left _ (List.mem_map_of_mem h)

/-! ### Marks -/

theorem groups_nil (k : Nat) : ∀ fuel : Nat, groups k fuel ([] : List υ) = []
  | 0 => rfl
  | _ + 1 => rfl

/-- **The groups are the units**: in a row they are the list, where the fuel is enough. -/
theorem flatten_groups (k : Nat) : ∀ (fuel : Nat) (l : List υ), l.length ≤ fuel →
    (groups k fuel l).flatten = l
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, [], _ => rfl
  | fuel + 1, u :: us, h => by
    have hd : (us.drop (k - 1)).length ≤ fuel := by
      rw [List.length_drop]
      have h' : us.length + 1 ≤ fuel + 1 := h
      omega
    show (u :: us.take (k - 1)) ++ (groups k fuel (us.drop (k - 1))).flatten = u :: us
    rw [flatten_groups k fuel _ hd, List.cons_append, List.take_append_drop]

/-- **Every mark but the last stands for exactly `k` units.** -/
theorem groups_full {k : Nat} (hk : 0 < k) : ∀ (fuel : Nat) (l : List υ),
    (groups k fuel l).Pairwise fun g _ => g.length = k
  | 0, _ => List.Pairwise.nil
  | _ + 1, [] => List.Pairwise.nil
  | fuel + 1, u :: us => by
    refine List.Pairwise.cons (fun g hg => ?_) (groups_full hk fuel _)
    have hne : us.drop (k - 1) ≠ [] := fun e => by
      rw [e, groups_nil] at hg
      exact nomatch hg
    have hlen : 0 < (us.drop (k - 1)).length := List.length_pos_iff.mpr hne
    rw [List.length_drop] at hlen
    show (us.take (k - 1)).length + 1 = k
    rw [List.length_take]
    omega

/-- **A mark stands for one unit at least and `k` at most.** -/
theorem groups_bounds {k : Nat} (hk : 0 < k) : ∀ (fuel : Nat) (l : List υ),
    ∀ g ∈ groups k fuel l, 0 < g.length ∧ g.length ≤ k
  | 0, _, _, hg => nomatch hg
  | _ + 1, [], _, hg => nomatch hg
  | fuel + 1, u :: us, g, hg => by
    cases List.mem_cons.mp hg with
    | inl e =>
      rw [e]
      refine ⟨Nat.succ_pos _, ?_⟩
      show (us.take (k - 1)).length + 1 ≤ k
      rw [List.length_take]
      omega
    | inr h => exact groups_bounds hk fuel _ g h

/-- **The marks are as many as `k` goes into the count, rounded up.** -/
theorem length_groups {k : Nat} (hk : 0 < k) : ∀ (fuel : Nat) (l : List υ), l.length ≤ fuel →
    (groups k fuel l).length = marksFor k l.length
  | 0, [], _ => by
    show 0 = (0 + (k - 1)) / k
    exact (Nat.div_eq_of_lt (by omega)).symm
  | 0, _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, [], _ => by
    show 0 = (0 + (k - 1)) / k
    exact (Nat.div_eq_of_lt (by omega)).symm
  | fuel + 1, u :: us, h => by
    have h' : us.length + 1 ≤ fuel + 1 := h
    have hd : (us.drop (k - 1)).length ≤ fuel := by
      rw [List.length_drop]
      omega
    show (groups k fuel (us.drop (k - 1))).length + 1 = (us.length + 1 + (k - 1)) / k
    rw [length_groups hk fuel _ hd, List.length_drop]
    show (us.length - (k - 1) + (k - 1)) / k + 1 = (us.length + 1 + (k - 1)) / k
    rw [← Nat.add_div_right _ hk]
    by_cases hlt : us.length < k
    · have e1 : us.length - (k - 1) = 0 := by omega
      rw [e1, Nat.zero_add]
      have a : (k - 1 + k) / k = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have b : (us.length + 1 + (k - 1)) / k = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [a, b]
    · have e2 : us.length - (k - 1) + (k - 1) + k = us.length + 1 + (k - 1) := by omega
      rw [e2]

theorem marksFrom_units : ∀ (gs : List (List υ)) (i : Nat),
    (marksFrom i gs).flatMap Slot.units = gs.flatten
  | [], _ => rfl
  | g :: gs, i => by
    show g ++ (marksFrom (i + 1) gs).flatMap Slot.units = g ++ gs.flatten
    rw [marksFrom_units gs (i + 1)]

theorem length_marksFrom : ∀ (gs : List (List υ)) (i : Nat), (marksFrom i gs).length = gs.length
  | [], _ => rfl
  | _ :: gs, i => congrArg (· + 1) (length_marksFrom gs (i + 1))

/-- **With marks the count is kept, the remainder included**: the marks stand for exactly the
units, in their order. -/
theorem marks_units (k bound : Nat) (us : List υ) :
    (marks k bound us).flatMap Slot.units = us := by
  show (marksFrom 0 (groups k us.length us) ++ rooms _ _).flatMap Slot.units = us
  rw [List.flatMap_append, marksFrom_units, rooms_units, List.append_nil,
    flatten_groups k us.length us (Nat.le_refl _)]

/-- **How many slots a place of marks has**: the marks that its bound allows, or the marks of
its count where they are more. -/
theorem length_marks {k : Nat} (hk : 0 < k) (bound : Nat) (us : List υ) :
    (marks k bound us).length = max (marksFor k bound) (marksFor k us.length) := by
  show (marksFrom 0 (groups k us.length us) ++ rooms _ _).length = _
  rw [List.length_append, length_marksFrom, length_rooms,
    length_groups hk us.length us (Nat.le_refl _)]
  omega

/-- **The count is kept on both sides of the threshold**: unit by unit or by marks, the slots
stand for exactly the units, in their order. -/
theorem shown_units (threshold k bound : Nat) (us : List υ) :
    (shown threshold k bound us).flatMap Slot.units = us := by
  unfold shown
  by_cases h : bound ≤ threshold
  · rw [if_pos h]
    exact slots_units bound us
  · rw [if_neg h]
    exact marks_units k bound us

theorem per_of_le {threshold k bound : Nat} (h : bound ≤ threshold) : per threshold k bound = 1 :=
  if_pos h

theorem per_of_lt {threshold k bound : Nat} (h : threshold < bound) : per threshold k bound = k :=
  if_neg (by omega)

/-! ## The look, and the row -/

/-- **How a caller draws a slot**: the size of a slot, the gap between two, and the thing drawn
of a slot at the slot's own origin. A held unit is drawn from the unit alone, so it is the same
thing in whichever slot it stands. -/
structure Look (υ α : Type) where
  /-- How far a slot reaches across. -/
  w : Nat
  /-- How far a slot reaches down. -/
  h : Nat
  /-- The gap between two slots. -/
  gap : Nat
  /-- What is drawn of a slot, at the slot's own origin. -/
  draw : Slot υ → α

namespace Look

/-- From the start of one slot to the start of the next. -/
def pitch (look : Look υ α) : Nat := look.w + look.gap

/-- One slot as a part of a picture: its room and its thing. -/
def cell (look : Look υ α) (s : Slot υ) : Layout α := Layout.leaf look.w look.h (look.draw s)

end Look

/-- **At which end of the row the front of the place is.** A buffer that empties to the right
has its front at the end, and a lane of requests that wait to its right has it at the start. -/
inductive Front where
  /-- The front is the first slot of the row, at its origin. -/
  | atStart
  /-- The front is the last slot of the row. -/
  | atEnd
  deriving DecidableEq, Repr

namespace Front

/-- The slots in the order of the row. -/
def order {β : Type} : Front → List β → List β
  | atStart, l => l
  | atEnd, l => l.reverse

/-- The place in a row of `total` slots of the slot `i` from the front. -/
def place : Front → Nat → Nat → Nat
  | atStart, _, i => i
  | atEnd, total, i => total - 1 - i

theorem mem_order {β : Type} {front : Front} {l : List β} {x : β} :
    x ∈ front.order l ↔ x ∈ l := by
  cases front with
  | atStart => exact Iff.rfl
  | atEnd => exact List.mem_reverse

theorem length_order {β : Type} (front : Front) (l : List β) :
    (front.order l).length = l.length := by
  cases front with
  | atStart => rfl
  | atEnd => exact List.length_reverse

theorem order_ne_nil {β : Type} (front : Front) {l : List β} (h : l ≠ []) :
    front.order l ≠ [] := fun e => by
  have h1 := length_order front l
  rw [e] at h1
  exact h (List.eq_nil_of_length_eq_zero h1.symm)

end Front

/-- Some slots and a gap after each are as many pitches across. -/
private theorem sum_cells (look : Look υ α) : ∀ l : List (Slot υ),
    ((l.map look.cell).map fun c => c.w + look.gap).sum = l.length * look.pitch
  | [] => (Nat.zero_mul _).symm
  | _ :: l => by
    rw [List.map_cons, List.map_cons, List.sum_cons, sum_cells look l, List.length_cons,
      Nat.succ_mul, Nat.add_comm]
    rfl

section

variable [Moves IVec α]

/-- **The slots, placed**: a row of them with the gap of the look between each two, the front
at the end that `front` names. -/
def row (look : Look υ α) (front : Front) (ss : List (Slot υ)) : Layout α :=
  Layout.row look.gap ((front.order ss).map look.cell)

/-- **A place with a bound, drawn as its units**: the row of its slots. -/
def vessel (look : Look υ α) (front : Front) (bound : Nat) (us : List υ) : Layout α :=
  row look front (slots bound us)

/-- **The thing of the slot `i`** of a row of `total` slots: what the look draws of the slot,
moved to where the slot stands. -/
def stand (look : Look υ α) (front : Front) (total i : Nat) (s : Slot υ) : α :=
  Moves.move (Layout.across (front.place total i * look.pitch)) (look.draw s)

/-- The things of some slots in a row, the first at the place `i`. -/
def standFrom (look : Look υ α) : Nat → List (Slot υ) → List α
  | _, [] => []
  | i, s :: ss =>
    Moves.move (Layout.across (i * look.pitch)) (look.draw s) :: standFrom look (i + 1) ss

/-! ### Where a slot stands -/

/-- The things of a row of parts: those of the first, and those of the rest one part and one
gap over. -/
private theorem row_items_cons (gap : Nat) (a : Layout α) (l : List (Layout α)) :
    (Layout.row gap (a :: l)).items =
      a.items ++ Moves.move (Layout.across (a.w + gap)) (Layout.row gap l).items := by
  cases l with
  | nil => exact (List.append_nil a.items).symm
  | cons b rest => rfl

/-- One slot over is one move. -/
private theorem move_across_mul (look : Look υ α) (i : Nat) (a : α) :
    Moves.move (Layout.across look.pitch) (Moves.move (Layout.across (i * look.pitch)) a) =
      Moves.move (Layout.across ((i + 1) * look.pitch)) a := by
  rw [Moves.move_move, ← Layout.across_add, Nat.succ_mul]

private theorem move_standFrom (look : Look υ α) : ∀ (l : List (Slot υ)) (i : Nat),
    Moves.move (Layout.across look.pitch) (standFrom look i l) = standFrom look (i + 1) l
  | [], _ => rfl
  | s :: l, i => by
    show Moves.move (Layout.across look.pitch)
        (Moves.move (Layout.across (i * look.pitch)) (look.draw s)) ::
        Moves.move (Layout.across look.pitch) (standFrom look (i + 1) l) = _
    rw [move_across_mul, move_standFrom look l (i + 1)]
    rfl

private theorem row_cells (look : Look υ α) : ∀ l : List (Slot υ),
    (Layout.row look.gap (l.map look.cell)).items = standFrom look 0 l
  | [] => rfl
  | s :: l => by
    rw [List.map_cons, row_items_cons, row_cells look l]
    show look.draw s :: Moves.move (Layout.across look.pitch) (standFrom look 0 l) =
      Moves.move (Layout.across (0 * look.pitch)) (look.draw s) :: standFrom look (0 + 1) l
    rw [move_standFrom, Nat.zero_mul, Layout.across_zero, Moves.move_zero]

/-- **The things of a row**: those of its slots in the order of the row, the first at the
origin and each next one slot and one gap over. -/
theorem row_items (look : Look υ α) (front : Front) (ss : List (Slot υ)) :
    (row look front ss).items = standFrom look 0 (front.order ss) :=
  row_cells look (front.order ss)

private theorem mem_standFrom (look : Look υ α) : ∀ (l : List (Slot υ)) (i j : Nat) (s : Slot υ),
    l[j]? = some s →
      Moves.move (Layout.across ((i + j) * look.pitch)) (look.draw s) ∈ standFrom look i l
  | [], _, _, _, h => nomatch h
  | x :: l, i, 0, s, h => by
    have e : x = s := Option.some.inj h
    rw [e]
    exact List.mem_cons_self
  | x :: l, i, j + 1, s, h => by
    have ih := mem_standFrom look l (i + 1) j s h
    have e : i + 1 + j = i + (j + 1) := by omega
    rw [e] at ih
    exact List.mem_cons_of_mem _ ih

/-- **Where a slot stands**: the thing of the slot `j` of a row is among the row's things, and
it is what the look draws of the slot, `j` slots and gaps from the front's end of the row. -/
theorem mem_row (look : Look υ α) (front : Front) {ss : List (Slot υ)} {j : Nat} {s : Slot υ}
    (h : ss[j]? = some s) : stand look front ss.length j s ∈ (row look front ss).items := by
  have hj : j < ss.length := (List.getElem?_eq_some_iff.mp h).1
  rw [row_items]
  cases front with
  | atStart =>
    have m := mem_standFrom look ss 0 j s h
    rw [Nat.zero_add] at m
    exact m
  | atEnd =>
    have hr : ss.reverse[ss.length - 1 - j]? = some s := by
      rw [List.getElem?_reverse (by omega)]
      have e : ss.length - 1 - (ss.length - 1 - j) = j := by omega
      rw [e]
      exact h
    have m := mem_standFrom look ss.reverse 0 (ss.length - 1 - j) s hr
    rw [Nat.zero_add] at m
    exact m

/-- Each slot of a row has a thing in it: what the look draws of the slot, moved. -/
theorem exists_move_of_mem (look : Look υ α) (front : Front) {ss : List (Slot υ)} {s : Slot υ}
    (h : s ∈ ss) : ∃ d : IVec, Moves.move d (look.draw s) ∈ (row look front ss).items := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
  exact ⟨_, mem_row look front hj⟩

/-- Each thing of a row is what the look draws of one of its slots, moved. -/
theorem mem_row_elim (look : Look υ α) (front : Front) {ss : List (Slot υ)} {a : α}
    (h : a ∈ (row look front ss).items) : ∃ s ∈ ss, ∃ d : IVec, a = Moves.move d (look.draw s) := by
  rw [row_items] at h
  have key : ∀ (l : List (Slot υ)) (i : Nat), a ∈ standFrom look i l →
      ∃ s ∈ l, ∃ d : IVec, a = Moves.move d (look.draw s) := by
    intro l
    induction l with
    | nil => exact fun _ hm => nomatch hm
    | cons x l ih =>
      intro i hm
      cases List.mem_cons.mp hm with
      | inl e => exact ⟨x, List.mem_cons_self, _, e⟩
      | inr hm' =>
        obtain ⟨s, hs, d, e⟩ := ih (i + 1) hm'
        exact ⟨s, List.mem_cons_of_mem _ hs, d, e⟩
  obtain ⟨s, hs, d, e⟩ := key _ 0 h
  exact ⟨s, Front.mem_order.mp hs, d, e⟩

/-- **With the front at the start, one slot back is one move across.** -/
theorem stand_succ_atStart (look : Look υ α) (total i : Nat) (s : Slot υ) :
    stand look .atStart total (i + 1) s =
      Moves.move (Layout.across look.pitch) (stand look .atStart total i s) :=
  (move_across_mul look i (look.draw s)).symm

/-- **With the front at the end, one slot forward is one move across.** -/
theorem stand_succ_atEnd (look : Look υ α) {total i : Nat} (h : i + 1 < total) (s : Slot υ) :
    stand look .atEnd total i s =
      Moves.move (Layout.across look.pitch) (stand look .atEnd total (i + 1) s) := by
  show Moves.move (Layout.across ((total - 1 - i) * look.pitch)) (look.draw s) =
    Moves.move (Layout.across look.pitch)
      (Moves.move (Layout.across ((total - 1 - (i + 1)) * look.pitch)) (look.draw s))
  rw [move_across_mul]
  have e : total - 1 - (i + 1) + 1 = total - 1 - i := by omega
  rw [e]

/-- With the front at the start, where a slot stands does not depend on how many slots the row
has. -/
theorem stand_atStart (look : Look υ α) (total total' i : Nat) (s : Slot υ) :
    stand look .atStart total i s = stand look .atStart total' i s := rfl

/-! ### The room of a row -/

/-- **A row is as wide as its slots and the gaps between them**: with one gap more, as many
pitches as slots. -/
theorem row_w (look : Look υ α) (front : Front) {ss : List (Slot υ)} (h : ss ≠ []) :
    (row look front ss).w + look.gap = ss.length * look.pitch := by
  have hne : (front.order ss).map look.cell ≠ [] := fun e =>
    Front.order_ne_nil front h (List.map_eq_nil_iff.mp e)
  rw [row, Layout.row_w look.gap _ hne, sum_cells, Front.length_order]

private theorem h_cells (look : Look υ α) : ∀ l : List (Slot υ), l ≠ [] →
    (Layout.row look.gap (l.map look.cell)).h = look.h
  | [], h => absurd rfl h
  | [_], _ => rfl
  | s :: t :: l, _ => by
    show max look.h (Layout.row look.gap ((t :: l).map look.cell)).h = look.h
    rw [h_cells look (t :: l) (List.cons_ne_nil t l)]
    exact Nat.max_self look.h

/-- **A row is one slot high.** -/
theorem row_h (look : Look υ α) (front : Front) {ss : List (Slot υ)} (h : ss ≠ []) :
    (row look front ss).h = look.h :=
  h_cells look _ (Front.order_ne_nil front h)

end

/-! ### The picture fits and is clear -/

section

variable [Moves IVec α] [Boxed α]

/-- **The row fits**: where what is drawn of each slot is inside the slot, each thing of the
row is inside the row's room. -/
theorem row_fits {look : Look υ α} (front : Front) {ss : List (Slot υ)}
    (h : ∀ s ∈ ss, (Boxed.box (look.draw s)).Inside ⟨0, 0, look.w, look.h⟩) :
    (row look front ss).Fits :=
  Layout.Fits.row look.gap _ fun l hl => by
    obtain ⟨s, hs, e⟩ := List.mem_map.mp hl
    rw [← e]
    exact Layout.fits_leaf (h s (Front.mem_order.mp hs))

/-- **The row is clear**: where what is drawn of each slot is inside the slot, no two things of
the row share room. -/
theorem row_clear {look : Look υ α} (front : Front) {ss : List (Slot υ)}
    (h : ∀ s ∈ ss, (Boxed.box (look.draw s)).Inside ⟨0, 0, look.w, look.h⟩) :
    (row look front ss).Clear :=
  Layout.Clear.row look.gap _
    (fun l hl => by
      obtain ⟨s, hs, e⟩ := List.mem_map.mp hl
      rw [← e]
      exact Layout.fits_leaf (h s (Front.mem_order.mp hs)))
    fun l hl => by
      obtain ⟨s, _, e⟩ := List.mem_map.mp hl
      rw [← e]
      exact Layout.clear_leaf _ _ _

end

end Units

end Whatwg.Svg.Scene
