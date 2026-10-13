import Whatwg.Svg.Scene.Units
import Whatwg.Svg.Scene.Join.Laws

/-!
# Whatwg.Svg.Scene.Units.Laws

Owner: what a step does to a place drawn as its units (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; ask W20 of `docs/research/2026-10-12-whatwg-requests.md`).

A place changes by steps: a unit leaves at the front and the rest slide, or a unit enters at
the back. The picture before and the picture after are two rows of
`Whatwg/Svg/Scene/Units.lean`, and what a reader sees between them is their join by key
(`Whatwg/Svg/Scene/Join.lean`): a thing whose key both have moves, a thing whose key only the
old one has leaves, and a thing whose key only the new one has enters. These laws say that the
join reads a step as the step was: a unit that stays is one thing that moves one slot, and it
never leaves and comes back.

A caller gives its key, and one fact of it: a moved thing keeps its key (`Keeps`). For a thing
that stores its key in a field, the proof is `fun _ _ => rfl`.

- **A unit that stays neither leaves nor enters** (`stays`): between any two pictures of a
  place, whatever their bounds and their fronts, no thing that leaves and no thing that enters
  has the key of a unit that both hold. `exit_ne` and `enter_ne` are the same for any slot of
  any row, so they hold of marks and of room too.
- **The front leaves and the rest slide** (`front_leaves`): each unit behind the front updates,
  from its thing in the slot `j + 1` to its thing in the slot `j`. `stand_succ_atStart` and
  `stand_succ_atEnd` of `Units.lean` say that the two are one move of one slot apart.
- **A unit enters at the back and the others stay where they are** (`back_enters`): each unit
  that was held updates from its thing to the same thing.
- **Where a unit and where room stands** (`vessel_stand`, `vessel_room`): in a place within its
  bound, the unit at the place `j` stands in the slot `j`, and each slot from the count on is
  room.

`front_leaves` and `back_enters` ask that the keys of the old picture are distinct, which is
what `mem_update_iff` of the join asks. A program decides it of its own picture.

What this module does not claim: what a step does to a place over its bound with its front at
the end, where the row grows and shrinks at its origin (`stays` still holds of it); a step of
marks, whose keys are the caller's (`exit_ne` and `enter_ne` hold of it); that the thing that
leaves is the front's and the thing that enters is the room's, which holds where the keys of
units and of room differ and which the port `WhatwgTest/Svg/UseUnits.lean` reads at the
consumer's queue.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Units

variable {υ α κ : Type}

/-- **A moved thing keeps its key.** -/
def Keeps [Moves IVec α] (key : α → κ) : Prop := ∀ (d : IVec) (a : α), key (Moves.move d a) = key a

section

variable [Moves IVec α]

/-- The thing of a slot has the key of what the look draws of the slot. -/
theorem key_stand {key : α → κ} (hk : Keeps key) (look : Look υ α) (front : Front)
    (total i : Nat) (s : Slot υ) : key (stand look front total i s) = key (look.draw s) :=
  hk _ _

/-- **Where a unit stands**: in a place within its bound, or with its front at the start, the
unit at the place `j` stands in the slot `j`. -/
theorem vessel_stand (look : Look υ α) (front : Front) {bound : Nat} {us : List υ} {j : Nat}
    {u : υ} (hb : front = .atStart ∨ us.length ≤ bound) (h : us[j]? = some u) :
    stand look front bound j (Slot.held u) ∈ (vessel look front bound us).items := by
  have m := mem_row look front (slots_held bound h)
  cases hb with
  | inl e =>
    subst e
    exact m
  | inr hle =>
    rw [length_slots_of_le hle] at m
    exact m

/-- **Where room stands**: in a place within its bound, each slot from the count on is room,
in its own place. -/
theorem vessel_room (look : Look υ α) (front : Front) {bound : Nat} {us : List υ} {j : Nat}
    (h1 : us.length ≤ j) (h2 : j < bound) :
    stand look front bound j (Slot.room j) ∈ (vessel look front bound us).items := by
  have m := mem_row look front (slots_room (us := us) h1 h2)
  rw [length_slots_of_le (by omega)] at m
  exact m

end

section

variable [Moves IVec α] [BEq κ] [LawfulBEq κ]

/-- **A thing leaves only where the new row has no slot under its key.** -/
theorem exit_ne {key : α → κ} (hk : Keeps key) (old : List α) (look : Look υ α) (front : Front)
    {ss : List (Slot υ)} {s : Slot υ} (hs : s ∈ ss) {a : α}
    (ha : a ∈ (join key old (row look front ss).items).exit) : key a ≠ key (look.draw s) := by
  obtain ⟨d, hd⟩ := exists_move_of_mem look front hs
  have h := ((mem_exit key old _).mp ha).2 _ hd
  rw [hk] at h
  exact fun e => h e.symm

/-- **A thing enters only where the old row had no slot under its key.** -/
theorem enter_ne {key : α → κ} (hk : Keeps key) (new : List α) (look : Look υ α) (front : Front)
    {ss : List (Slot υ)} {s : Slot υ} (hs : s ∈ ss) {a : α}
    (ha : a ∈ (join key (row look front ss).items new).enter) : key a ≠ key (look.draw s) := by
  obtain ⟨d, hd⟩ := exists_move_of_mem look front hs
  have h := ((mem_enter key _ new).mp ha).2 _ hd
  rw [hk] at h
  exact fun e => h e.symm

/-- **The law of a step: a unit that stays neither leaves nor enters.** Between two pictures
of a place, whatever their bounds and their fronts, no thing that leaves and no thing that
enters has the key of a unit that both hold. So a reader never sees a unit go and come back. -/
theorem stays {key : α → κ} (hk : Keeps key) (look : Look υ α) (front front' : Front)
    (bound bound' : Nat) {us us' : List υ} {u : υ} (h : u ∈ us) (h' : u ∈ us') :
    (∀ a ∈ (join key (vessel look front bound us).items
        (vessel look front' bound' us').items).exit, key a ≠ key (look.draw (Slot.held u))) ∧
      ∀ a ∈ (join key (vessel look front bound us).items
        (vessel look front' bound' us').items).enter, key a ≠ key (look.draw (Slot.held u)) :=
  ⟨fun _ ha => exit_ne hk _ look front' (held_mem_slots bound' h') ha,
    fun _ ha => enter_ne hk _ look front (held_mem_slots bound h) ha⟩

/-- **The front leaves and the rest slide.** Each unit behind the front updates, from its
thing in the slot `j + 1` to its thing in the slot `j`: one key, one slot over. -/
theorem front_leaves {key : α → κ} (hk : Keeps key) (look : Look υ α) (front : Front)
    {bound : Nat} (u : υ) {rest : List υ} {j : Nat} {v : υ}
    (hb : front = .atStart ∨ rest.length + 1 ≤ bound) (hv : rest[j]? = some v)
    (hd : Distinct key (vessel look front bound (u :: rest)).items) :
    (stand look front bound (j + 1) (Slot.held v), stand look front bound j (Slot.held v)) ∈
      (join key (vessel look front bound (u :: rest)).items
        (vessel look front bound rest).items).update :=
  (mem_update_iff key _ _ hd).mpr
    ⟨vessel_stand look front (us := u :: rest) (hb.imp id id) hv,
      vessel_stand look front (hb.imp id Nat.le_of_succ_le) hv,
      (key_stand hk look front bound (j + 1) _).trans (key_stand hk look front bound j _).symm⟩

/-- **A unit enters at the back and the others stay where they are.** Each unit that was held
updates from its thing to the same thing. -/
theorem back_enters (key : α → κ) (look : Look υ α) (front : Front)
    {bound : Nat} {us : List υ} (x : υ) {j : Nat} {v : υ}
    (hb : front = .atStart ∨ us.length + 1 ≤ bound) (hv : us[j]? = some v)
    (hd : Distinct key (vessel look front bound us).items) :
    (stand look front bound j (Slot.held v), stand look front bound j (Slot.held v)) ∈
      (join key (vessel look front bound us).items
        (vessel look front bound (us ++ [x])).items).update := by
  have hj : j < us.length := (List.getElem?_eq_some_iff.mp hv).1
  have hv' : (us ++ [x])[j]? = some v := by
    rw [List.getElem?_append_left hj]
    exact hv
  have hb' : front = .atStart ∨ (us ++ [x]).length ≤ bound := by
    rw [List.length_append]
    exact hb
  exact (mem_update_iff key _ _ hd).mpr
    ⟨vessel_stand look front (hb.imp id Nat.le_of_succ_le) hv, vessel_stand look front hb' hv', rfl⟩

end

end Units

end Whatwg.Svg.Scene
