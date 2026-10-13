import Whatwg.Svg.Scene.Plan
import Whatwg.Svg.Scene.Score

/-!
# Whatwg.Svg.Scene.Stage

Owner: a step in stages and levels (slice S15 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-84).

The order in which the things of a step move says something to a reader. The kept things make
room first. Then the new things come, level by level from the top, and no thing appears before
the level above it is done. lean4-effect4's viewer has this order as arithmetic inside its
sampler (`sampleLaid` of its `tools/Tools/View/Motion.lean`), and no theorem there says that a
level is over before the next begins. This module has the order as one function,
`Motion.staged`, with the laws. A caller gives a `Plan` and three numbers, and keeps the
guarantees.

- `Transition.inWindow tr start slot`: a transition placed in a window of the step. Its own
  delay and duration are read in per mille of the window.
- `Transition.atMost tr most slot`: the same share of a window `slot` long, cut so that the
  placed transition lasts `most` at most. A choreography that says "no longer than this" keeps
  its word in a long window.
- `Motion.slotted m start slot rank`: each track in the window of its key's rank. The windows
  are `slot` long and follow one another from `start`.
- `Motion.endBy m budget`: the motion made to end by a moment. A motion that ends by then is
  left as it is, and a longer one is fitted (`Motion.fit`). It is never stretched.
- `Motion.staged key j p enterFrom levels rank`: **a step in stages.** The kept things and the
  things that leave come first, made to end by `enterFrom`. Then the new things enter level by
  level. The level `rank n` of a new thing has the window that starts at
  `enterFrom + rank n * slot`, with `slot = (1000 - enterFrom) / levels` (`Motion.slot`), and
  the transitions that the plan's `enter` gives count in per mille of that window.

What the laws say of a step:

- `Transition.inWindow_start`, `Transition.inWindow_end`: a transition that fits in a thousand
  stays in its window, with the rounding. Its easing is its own (`Transition.inWindow_ease`),
  and what is over before another starts is still so in the window
  (`Transition.inWindow_before`).
- `Motion.slotted_respects`: tracks placed by rank respect every order that the rank follows.
  `Motion.slotted_finish`: with every rank below `levels`, they end by `start + levels * slot`.
- **The same things, the same changes** (`Motion.staged_untimed`): a staged step has the tracks
  of `Motion.ofJoin`, one for one and in the same order, each with its key, its change and its
  easing. Only the delays and the durations differ.
- **The kept things first** (`Motion.staged_kept_first`): every track of a kept thing and of a
  thing that leaves is over by `enterFrom`, and every track of a new thing starts then or
  later. This asks nothing of the plan. With a plan that settles and is proper, each kept thing
  is at rest from `enterFrom` on (`Motion.staged_kept_rest`): no new thing appears before the
  kept things are at rest.
- **Level by level** (`Motion.staged_levels`): a track of a new thing of one level is over
  before a track of a new thing of a deeper level starts. Nothing appears before the level
  above it is done. `Motion.staged_respects` says the two together as an order in time
  (`Motion.Respects`).
- `Motion.staged_ends`: every track is over by the step's end, so the step needs no cut
  (`Motion.staged_within`), and with a proper plan every track is done there
  (`Motion.staged_done`).
- **The last picture** (`Motion.staged_end`): at the step's end and after, every pose that the
  step sets on a thing of the new list is at rest. `Join.drawn_end` still says which things are
  drawn then. Held inside its step, the staged step has that last picture with no term on the
  ranks or on the entrances (`Motion.staged_within_end`).

The three premises of the laws about the step's end are stated on each: `enterFrom ≤ 1000`;
every new thing has a rank below `levels`; and every transition that the plan gives a new thing
fits in a thousand, its delay and its duration together. The laws of order ask for the third
only, and for the things of the earlier level only.

**lean4-effect4's choreography on it.** Its sampler gives a new edge the first 45 per cent of
its level's slot, and the box at its end the slot from 40 per cent on. Here that is a plan
whose `enter` gives an edge `{ delay := 0, duration := 450 }` and a box
`{ delay := 400, duration := 600 }`. The two agree and differ as follows.

- *The start of each new thing* is the same number, for every `enterFrom`, number of levels and
  level: `10 * a * slot / 1000` is `slot * a / 100` (`Transition.per_cent`).
- *The duration of each new thing* is the same where the consumer's cap is the slot's share.
  The consumer takes `min` of its own duration and that share. With two levels or more its
  default numbers are cut by the share, and the two agree. With one level its own duration is
  the shorter, and the plain share here is longer. `Transition.atMost` gives the consumer's
  `min` exactly (`Transition.atMost_inWindow_cent`).
- *The kept things and the things that leave* differ where the consumer's first stage outlasts
  `enterFrom`. Its default move lasts 450 per mille and its new things start at 300, so its
  kept things are still moving when the first new thing appears. Here the first stage is fitted
  to end by `enterFrom`, which is the law. With `enterFrom` at 450 or later the two agree.
- *The cut at the step's end*: the consumer holds each transition inside its step. Here no
  track passes the end, so the cut changes nothing (`Motion.staged_within`).

The guards at the end of this file are these comparisons on a step of five things, and the two
examples before them read the law of a capped part at the consumer's two entrances.

How this differs from the sketch that it was written from. The first stage is `Motion.endBy`
and not `Motion.fit` alone: a first stage that is over early is not stretched, since a quick
move should stay quick. The tracks stand in the order of `Motion.ofJoin`: the kept things, the
new things, the things that leave. `Motion.staged_respects` has two premises that the sketch
does not name: the plan's first stage respects the order as the plan times it, and the order
puts no new thing before a thing of the first stage.

What this module does not claim: an order between two things of one level, such as an edge
that reaches its box before the box opens, since the consumer's two shares overlap by five per
cent, and `Transition.inWindow_before` is the law for shares that do not; a step that is
interrupted; that the ranks follow the tree, which is the caller's to show; that a slot is not
empty, since with more levels than room a slot is `0` and every new thing appears at once at
its moment.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-! ## Lists -/

/-- Two `flatMap`s whose results agree under a function, member by member, agree under it. -/
theorem map_flatMap_congr {α β γ : Type} (f : β → γ) (A B : α → List β)
    (h : ∀ a, (A a).map f = (B a).map f) : ∀ l : List α,
    (l.flatMap A).map f = (l.flatMap B).map f
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append, h a,
      map_flatMap_congr f A B h l]

variable {α κ : Type}

/-! ## A transition in a window -/

/-- A transition placed in a window of the step. The window starts at `start` and is `slot`
long, and the transition's own delay and duration count in per mille of the window. -/
def Transition.inWindow (tr : Transition) (start slot : Nat) : Transition :=
  { tr with delay := start + tr.delay * slot / 1000, duration := tr.duration * slot / 1000 }

namespace Transition

/-- A transition placed in a window keeps its easing: the thing moves in the same manner, in
less time. -/
theorem inWindow_ease (tr : Transition) (start slot : Nat) :
    (tr.inWindow start slot).ease = tr.ease := rfl

/-- **Nothing starts before its window.** A transition placed in a window starts at the
window's start or later, whatever its own numbers. -/
theorem inWindow_start (tr : Transition) (start slot : Nat) :
    start ≤ (tr.inWindow start slot).delay := Nat.le_add_right _ _

/-- **Nothing outlasts its window.** A transition whose delay and duration fit in a thousand,
placed in a window, is over by the window's end, with the rounding. -/
theorem inWindow_end (tr : Transition) (start slot : Nat) (h : tr.delay + tr.duration ≤ 1000) :
    (tr.inWindow start slot).delay + (tr.inWindow start slot).duration ≤ start + slot := by
  have h1 := Motion.scale_add_le tr.delay tr.duration 1000 slot 1000 h
  rw [Nat.mul_div_cancel_left slot (by decide : 0 < 1000)] at h1
  show start + tr.delay * slot / 1000 + tr.duration * slot / 1000 ≤ start + slot
  omega

/-- **An order inside a window is kept.** Where one transition is over before another starts,
the two placed in one window are so: a line drawn in the first part of a window is whole before
a box grows in a later part. -/
theorem inWindow_before {a b : Transition} (start slot : Nat)
    (h : a.delay + a.duration ≤ b.delay) :
    (a.inWindow start slot).delay + (a.inWindow start slot).duration ≤
      (b.inWindow start slot).delay := by
  have h1 := Motion.scale_add_le a.delay a.duration b.delay slot 1000 h
  show start + a.delay * slot / 1000 + a.duration * slot / 1000 ≤ start + b.delay * slot / 1000
  omega

/-- The transition that takes a whole window is the window: it starts at its start and lasts
as long. -/
theorem inWindow_whole (ease : Easing) (start slot : Nat) :
    ({ delay := 0, duration := 1000, ease := ease } : Transition).inWindow start slot =
      { delay := start, duration := slot, ease := ease } := by
  show ({ delay := start + 0 * slot / 1000, duration := 1000 * slot / 1000, ease := ease } :
    Transition) = _
  rw [Nat.zero_mul, Nat.zero_div, Nat.add_zero, Nat.mul_div_cancel_left slot (by decide)]

/-- A transition that is over by the step's end is held inside the step as it is: the cut at
the step's end changes nothing. -/
theorem within_of_le (tr : Transition) (h : tr.delay + tr.duration ≤ 1000) : tr.within = tr := by
  have e1 : min tr.delay 1000 = tr.delay := by omega
  have e2 : min tr.duration (1000 - min tr.delay 1000) = tr.duration := by omega
  exact congr (congrArg (fun d u => (⟨d, u, tr.ease⟩ : Transition)) e1) e2

/-- **The same share of a window, and no longer than `most`.** The duration, a share of a
window `slot` long, is cut to the least share that lasts `most`. Placed in such a window the
transition lasts `most` at most (`atMost_duration`). -/
def atMost (tr : Transition) (most slot : Nat) : Transition :=
  { tr with duration := min tr.duration ((most * 1000 + (slot - 1)) / slot) }

/-- The least share of a window that lasts `most` lasts `most` exactly, in a window of a
thousand at most: the two roundings undo each other. -/
theorem share_exact (most slot : Nat) (h0 : 0 < slot) (hs : slot ≤ 1000) :
    (most * 1000 + (slot - 1)) / slot * slot / 1000 = most := by
  have h1 := Nat.div_mul_le_self (most * 1000 + (slot - 1)) slot
  have h2 := Nat.lt_mul_div_succ (most * 1000 + (slot - 1)) h0
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm slot] at h2
  omega

/-- A transition cut to last `most` at most starts where it started. -/
theorem atMost_delay (tr : Transition) (most start slot : Nat) :
    ((tr.atMost most slot).inWindow start slot).delay = (tr.inWindow start slot).delay := rfl

/-- **A transition cut to last `most` at most lasts its share of the window, or `most` where
that is less.** A choreography's own duration is a cap: in a long window the thing is no slower
than the choreography says. -/
theorem atMost_duration (tr : Transition) (most start slot : Nat) (hs : slot ≤ 1000) :
    ((tr.atMost most slot).inWindow start slot).duration =
      min (tr.inWindow start slot).duration most := by
  show min tr.duration ((most * 1000 + (slot - 1)) / slot) * slot / 1000 =
    min (tr.duration * slot / 1000) most
  cases Nat.eq_zero_or_pos slot with
  | inl h0 =>
    rw [h0, Nat.mul_zero, Nat.mul_zero, Nat.zero_div]
    omega
  | inr h0 =>
    have he := share_exact most slot h0 hs
    generalize (most * 1000 + (slot - 1)) / slot = r at he ⊢
    rcases Nat.le_total tr.duration r with h | h
    · have hm := Nat.div_le_div_right (c := 1000) (Nat.mul_le_mul_right slot h)
      rw [Nat.min_eq_left h]
      omega
    · have hm := Nat.div_le_div_right (c := 1000) (Nat.mul_le_mul_right slot h)
      rw [Nat.min_eq_right h]
      omega

/-- A share of whole per cents, written in per mille, is the share in per cents: the two
roundings are one. -/
theorem per_cent (k slot : Nat) : 10 * k * slot / 1000 = slot * k / 100 := by
  have e : 10 * k * slot = 10 * (slot * k) := by rw [Nat.mul_assoc, Nat.mul_comm k slot]
  rw [e]
  omega

/-- **A part of a window in per cents, with a cap.** A transition that starts `a` per cent into
its window and takes `b` per cent of it, cut to last `most` at most, starts at
`start + slot * a / 100` and lasts `min (slot * b / 100) most`. With `a = 0` and `b = 45` this is
the draw of a new edge in lean4-effect4's sampler, and with `a = 40` and `b = 60` the growth of
the box at its end, each with the choreography's own duration as `most`. -/
theorem atMost_inWindow_cent (a b most start slot : Nat) (ease : Easing) (hs : slot ≤ 1000) :
    (({ delay := 10 * a, duration := 10 * b, ease := ease } : Transition).atMost most
      slot).inWindow start slot =
      { delay := start + slot * a / 100, duration := min (slot * b / 100) most, ease := ease } := by
  have hd := atMost_duration ({ delay := 10 * a, duration := 10 * b, ease := ease } : Transition)
    most start slot hs
  have e1 : start + 10 * a * slot / 1000 = start + slot * a / 100 := by rw [per_cent]
  have e2 : min (10 * b) ((most * 1000 + (slot - 1)) / slot) * slot / 1000 =
      min (slot * b / 100) most := hd.trans (by rw [← per_cent]; rfl)
  exact congr (congrArg (fun d u => (⟨d, u, ease⟩ : Transition)) e1) e2

end Transition

/-! ## Tracks apart from their times -/

/-- What a track says apart from its times: its key, its change and its easing. -/
def Track.untimed (tr : Track κ) : κ × Change × Easing := (tr.key, tr.change, tr.timing.ease)

/-- A track of a motion that ends at `finish`, retimed so that the motion ends by `budget`: as
it is where the motion ends by then, and with its delay and its duration scaled by the budget
over the finish where it does not. -/
def Track.endBy (budget finish : Nat) (tr : Track κ) : Track κ :=
  if finish ≤ budget then tr
  else { tr with timing := { tr.timing with
    delay := tr.timing.delay * budget / finish,
    duration := tr.timing.duration * budget / finish } }

/-- A retimed track is of the same thing, with the same change and the same easing. -/
theorem Track.endBy_untimed (budget finish : Nat) (tr : Track κ) :
    (tr.endBy budget finish).untimed = tr.untimed := by
  unfold Track.endBy
  rcases Decidable.em (finish ≤ budget) with h | h
  · rw [if_pos h]
  · rw [if_neg h]
    rfl

namespace Motion

/-! ## Tracks in the windows of their ranks -/

/-- **The motion with each track in the window of its key's rank.** The windows are `slot` long
and follow one another from `start`: the rank `r` has the window from `start + r * slot`. -/
def slotted (m : Motion κ) (start slot : Nat) (rank : κ → Nat) : Motion κ :=
  m.map fun tr => { tr with timing := tr.timing.inWindow (start + rank tr.key * slot) slot }

/-- A slotted motion has as many tracks. -/
theorem length_slotted (m : Motion κ) (start slot : Nat) (rank : κ → Nat) :
    (m.slotted start slot rank).length = m.length := List.length_map _

/-- **A slotted motion moves the same things in the same way**: track by track it has the same
keys, changes and easings. -/
theorem slotted_untimed (m : Motion κ) (start slot : Nat) (rank : κ → Nat) :
    (m.slotted start slot rank).map Track.untimed = m.map Track.untimed :=
  List.map_map.trans (List.map_congr_left fun _ _ => rfl)

/-- A track of a slotted motion is a track of the motion, placed in the window of its rank. -/
theorem mem_slotted (m : Motion κ) (start slot : Nat) (rank : κ → Nat) {tr : Track κ}
    (h : tr ∈ m.slotted start slot rank) : ∃ tr0 ∈ m,
      tr = { tr0 with timing := tr0.timing.inWindow (start + rank tr0.key * slot) slot } := by
  obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp h
  exact ⟨tr0, h0, rfl⟩

/-- No track of a slotted motion starts before the window of its rank. -/
theorem slotted_starts (m : Motion κ) (start slot : Nat) (rank : κ → Nat) :
    ∀ tr ∈ m.slotted start slot rank, start + rank tr.key * slot ≤ tr.timing.delay := by
  intro tr h
  obtain ⟨tr0, _, rfl⟩ := mem_slotted m start slot rank h
  exact Transition.inWindow_start _ _ _

/-- **Each track of a slotted motion is over by the end of its rank's window**, where the
tracks of the motion fit in a thousand each. -/
theorem slotted_ends (m : Motion κ) (start slot : Nat) (rank : κ → Nat)
    (hm : ∀ tr ∈ m, tr.timing.delay + tr.timing.duration ≤ 1000) :
    ∀ tr ∈ m.slotted start slot rank,
      tr.timing.delay + tr.timing.duration ≤ start + (rank tr.key + 1) * slot := by
  intro tr h
  obtain ⟨tr0, h0, rfl⟩ := mem_slotted m start slot rank h
  have h1 := Transition.inWindow_end tr0.timing (start + rank tr0.key * slot) slot (hm tr0 h0)
  have e : (rank tr0.key + 1) * slot = rank tr0.key * slot + slot := by
    rw [Nat.add_mul, Nat.one_mul]
  show (tr0.timing.inWindow (start + rank tr0.key * slot) slot).delay +
    (tr0.timing.inWindow (start + rank tr0.key * slot) slot).duration ≤
      start + (rank tr0.key + 1) * slot
  rw [e]
  omega

/-- **Tracks placed by rank keep every order that the rank follows.** Where `before a b` gives
`rank a < rank b`, the thing `a` is done before the thing `b` starts: with the rank the depth in
a tree, no child appears before its parent is whole. -/
theorem slotted_respects (before : κ → κ → Prop) (m : Motion κ) (start slot : Nat)
    (rank : κ → Nat) (hr : ∀ a b, before a b → rank a < rank b)
    (hm : ∀ tr ∈ m, tr.timing.delay + tr.timing.duration ≤ 1000) :
    (m.slotted start slot rank).Respects before := by
  intro a ha b hb hab
  have h1 := slotted_ends m start slot rank hm a ha
  have h2 := slotted_starts m start slot rank b hb
  have h3 : (rank a.key + 1) * slot ≤ rank b.key * slot :=
    Nat.mul_le_mul_right slot (hr _ _ hab)
  omega

/-- **A slotted motion ends with its last window**: with every rank below `levels`, it is over
by `start + levels * slot`. -/
theorem slotted_finish (m : Motion κ) (start slot levels : Nat) (rank : κ → Nat)
    (hr : ∀ tr ∈ m, rank tr.key < levels)
    (hm : ∀ tr ∈ m, tr.timing.delay + tr.timing.duration ≤ 1000) :
    (m.slotted start slot rank).finish ≤ start + levels * slot := by
  refine finish_le_of _ _ fun tr h => ?_
  have h1 := slotted_ends m start slot rank hm tr h
  obtain ⟨tr0, h0, rfl⟩ := mem_slotted m start slot rank h
  have h2 : (rank tr0.key + 1) * slot ≤ levels * slot := Nat.mul_le_mul_right slot (hr tr0 h0)
  exact Nat.le_trans h1 (Nat.add_le_add_left h2 start)

/-- A motion whose every track is over by the step's end is held inside the step as it is. -/
theorem within_of_ends (m : Motion κ)
    (h : ∀ tr ∈ m, tr.timing.delay + tr.timing.duration ≤ 1000) : m.within = m :=
  (List.map_congr_left fun tr htr =>
    show ({ tr with timing := tr.timing.within } : Track κ) = id tr from
      congrArg (fun u => ({ tr with timing := u } : Track κ))
        (Transition.within_of_le tr.timing (h tr htr))).trans (List.map_id m)

/-! ## A motion that ends by a moment -/

/-- **The motion made to end by `budget`.** A motion that ends by then is left as it is. A
longer one is fitted: every delay and duration scaled by one factor, as `Motion.fit` does. It
is never stretched, so a quick motion stays quick. -/
def endBy (m : Motion κ) (budget : Nat) : Motion κ := m.map (Track.endBy budget m.finish)

/-- A motion that ends by the budget is left as it is. -/
theorem endBy_of_le (m : Motion κ) {budget : Nat} (h : m.finish ≤ budget) : m.endBy budget = m :=
  (List.map_congr_left fun _ _ => if_pos h).trans (List.map_id m)

/-- A motion that ends after the budget is fitted to it. -/
theorem endBy_of_lt (m : Motion κ) {budget : Nat} (h : budget < m.finish) :
    m.endBy budget = m.fit budget :=
  List.map_congr_left fun _ _ => if_neg (Nat.not_le_of_lt h)

/-- **A motion made to end by a moment ends by it.** -/
theorem endBy_finish (m : Motion κ) (budget : Nat) : (m.endBy budget).finish ≤ budget := by
  rcases Nat.lt_or_ge budget m.finish with h | h
  · rw [endBy_of_lt m h]
    exact fit_finish m budget
  · rw [endBy_of_le m h]
    exact h

/-- A motion made to end by a moment keeps the order that it had. -/
theorem endBy_respects (before : κ → κ → Prop) (m : Motion κ) (budget : Nat)
    (h : m.Respects before) : (m.endBy budget).Respects before := by
  rcases Nat.lt_or_ge budget m.finish with hlt | hge
  · rw [endBy_of_lt m hlt]
    exact fit_respects before m budget h
  · rw [endBy_of_le m hge]
    exact h

/-- A motion made to end by a moment moves the same things in the same way, track by track. -/
theorem endBy_untimed (m : Motion κ) (budget : Nat) :
    (m.endBy budget).map Track.untimed = m.map Track.untimed :=
  List.map_map.trans (List.map_congr_left fun tr _ => Track.endBy_untimed budget m.finish tr)

/-! ## A step in stages -/

/-- How long the window of one level is: the room after `enterFrom`, shared among the levels
and rounded down. With no level it is `0`. -/
def slot (enterFrom levels : Nat) : Nat := (1000 - enterFrom) / levels

/-- The windows of the levels end by the step's end: the window of a rank below `levels` ends
by `1000`, where the new things enter by then. -/
theorem slot_window_le {enterFrom levels r : Nat} (he : enterFrom ≤ 1000) (hr : r < levels) :
    enterFrom + (r + 1) * slot enterFrom levels ≤ 1000 := by
  have h1 : (r + 1) * slot enterFrom levels ≤ levels * slot enterFrom levels :=
    Nat.mul_le_mul_right _ hr
  have h2 : levels * slot enterFrom levels ≤ 1000 - enterFrom := Nat.mul_div_le _ _
  omega

/-- A slot is no longer than the step, so the laws of a window of a thousand at most hold of
it. -/
theorem slot_le (enterFrom levels : Nat) : slot enterFrom levels ≤ 1000 :=
  Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)

/-- The tracks of the kept things of a join, as the plan times them. -/
def keeping (key : α → κ) (j : Join α) (p : Plan α) : Motion κ :=
  j.update.flatMap fun q => tracks (key q.2) (p.kept q.1 q.2)

/-- The tracks of the new things of a join, as the plan times them. -/
def entering (key : α → κ) (j : Join α) (p : Plan α) : Motion κ :=
  j.enter.flatMap fun n => tracks (key n) (p.enter n)

/-- The tracks of the things of the new picture are those of the kept things, then those of the
new things. -/
theorem staying_eq (key : α → κ) (j : Join α) (p : Plan α) :
    staying key j p = keeping key j p ++ entering key j p := rfl

/-- The tracks of the first stage of a step, as the plan times them: those of the kept things
and those of the things that leave. -/
def firstStage (key : α → κ) (j : Join α) (p : Plan α) : Motion κ :=
  keeping key j p ++ leaving key j p

/-- The first stage, made to end by a moment, is the kept things' tracks and then the leaving
things' tracks, each retimed by the one factor of the whole stage: the two keep their pace
against each other. -/
theorem firstStage_endBy (key : α → κ) (j : Join α) (p : Plan α) (budget : Nat) :
    (firstStage key j p).endBy budget =
      (keeping key j p).map (Track.endBy budget (firstStage key j p).finish) ++
        (leaving key j p).map (Track.endBy budget (firstStage key j p).finish) :=
  List.map_append

/-- The tracks of one new thing in a staged step: those that the plan's `enter` gives it, in
the window of its level. -/
def stagedOf (key : α → κ) (p : Plan α) (enterFrom levels : Nat) (rank : α → Nat) (n : α) :
    Motion κ :=
  (tracks (key n) (p.enter n)).slotted enterFrom (slot enterFrom levels) fun _ => rank n

/-- **A step in stages.** The kept things and the things that leave come first, made to end by
`enterFrom` (`Motion.endBy`, with one factor for the two). Then the new things enter level by
level: the level `rank n` of a new thing `n` has the window that starts at
`enterFrom + rank n * slot`, with `slot = (1000 - enterFrom) / levels`, and the transitions that
the plan's `enter` gives count in per mille of that window. The tracks stand in the order of
`Motion.ofJoin`: the kept things, the new things, the things that leave. -/
def staged (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat) (rank : α → Nat) :
    Motion κ :=
  (keeping key j p).map (Track.endBy enterFrom (firstStage key j p).finish) ++
    j.enter.flatMap (stagedOf key p enterFrom levels rank) ++
    (leaving key j p).map (Track.endBy enterFrom (firstStage key j p).finish)

/-- A track of a staged step is a track of the first stage, retimed, or a track of a new thing
in its level's window. -/
theorem mem_staged (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) {tr : Track κ} :
    tr ∈ staged key j p enterFrom levels rank ↔
      (∃ tr0 ∈ firstStage key j p, tr = tr0.endBy enterFrom (firstStage key j p).finish) ∨
        ∃ n ∈ j.enter, tr ∈ stagedOf key p enterFrom levels rank n := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h1 | h3
    · rcases List.mem_append.mp h1 with h1 | h2
      · obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp h1
        exact Or.inl ⟨tr0, List.mem_append_left _ h0, rfl⟩
      · exact Or.inr (List.mem_flatMap.mp h2)
    · obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp h3
      exact Or.inl ⟨tr0, List.mem_append_right _ h0, rfl⟩
  · rintro (⟨tr0, h0, rfl⟩ | h2)
    · have h0' : tr0 ∈ keeping key j p ++ leaving key j p := h0
      rcases List.mem_append.mp h0' with hk | hl
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hk))
      · exact List.mem_append_right _ (List.mem_map_of_mem hl)
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr h2))

/-- A track of a new thing in a staged step is a change that the plan's `enter` gives the
thing, with its key, its transition placed in the window of its level. -/
theorem mem_stagedOf (key : α → κ) (p : Plan α) (enterFrom levels : Nat) (rank : α → Nat) (n : α)
    {tr : Track κ} :
    tr ∈ stagedOf key p enterFrom levels rank n ↔ ∃ c ∈ p.enter n,
      tr = ⟨key n, c.1, c.2.inWindow (enterFrom + rank n * slot enterFrom levels)
        (slot enterFrom levels)⟩ := by
  constructor
  · intro h
    obtain ⟨tr0, h0, rfl⟩ := mem_slotted _ _ _ _ h
    obtain ⟨c, hc, rfl⟩ := mem_tracks.mp h0
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact List.mem_map.mpr ⟨⟨key n, c.1, c.2⟩, mem_tracks.mpr ⟨c, hc, rfl⟩, rfl⟩

/-- **The same things, the same changes.** A staged step has the tracks of `Motion.ofJoin`, one
for one and in the same order, each with its key, its change and its easing. Staging changes
when a thing moves, and never what moves or how. -/
theorem staged_untimed (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) :
    (staged key j p enterFrom levels rank).map Track.untimed =
      (ofJoin key j p).map Track.untimed := by
  have hk : ∀ m : Motion κ,
      (m.map (Track.endBy enterFrom (firstStage key j p).finish)).map Track.untimed =
        m.map Track.untimed := fun m =>
    List.map_map.trans (List.map_congr_left fun tr _ => Track.endBy_untimed _ _ tr)
  have hn : (j.enter.flatMap (stagedOf key p enterFrom levels rank)).map Track.untimed =
      (entering key j p).map Track.untimed :=
    map_flatMap_congr Track.untimed _ _ (fun _ => slotted_untimed _ _ _ _) j.enter
  show ((keeping key j p).map _ ++ j.enter.flatMap _ ++ (leaving key j p).map _).map
      Track.untimed =
    (keeping key j p ++ entering key j p ++ leaving key j p).map Track.untimed
  rw [List.map_append, List.map_append, List.map_append, List.map_append, hk, hk, hn]

/-- A staged step has as many tracks as the step has. -/
theorem length_staged (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) : (staged key j p enterFrom levels rank).length = (ofJoin key j p).length := by
  have h := congrArg List.length (staged_untimed key j p enterFrom levels rank)
  rw [List.length_map, List.length_map] at h
  exact h

/-- A track of a staged step is a track of the step with other times: the same key, the same
change and the same easing. -/
theorem mem_staged_ofJoin (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) {tr : Track κ} (h : tr ∈ staged key j p enterFrom levels rank) :
    ∃ tr0 ∈ ofJoin key j p, tr0.untimed = tr.untimed := by
  have h1 : tr.untimed ∈ (staged key j p enterFrom levels rank).map Track.untimed :=
    List.mem_map_of_mem h
  rw [staged_untimed] at h1
  exact List.mem_map.mp h1

/-- Every track of the step is in the staged step, with other times. -/
theorem mem_ofJoin_staged (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) {tr0 : Track κ} (h : tr0 ∈ ofJoin key j p) :
    ∃ tr ∈ staged key j p enterFrom levels rank, tr.untimed = tr0.untimed := by
  have h1 : tr0.untimed ∈ (ofJoin key j p).map Track.untimed := List.mem_map_of_mem h
  rw [← staged_untimed key j p enterFrom levels rank] at h1
  exact List.mem_map.mp h1

/-! ### The order of a staged step -/

/-- **The first stage is over by `enterFrom`**: every track of a kept thing and of a thing that
leaves, whatever the plan gives them. -/
theorem staged_first_ends (key : α → κ) (j : Join α) (p : Plan α) (enterFrom : Nat) :
    ∀ tr0 ∈ firstStage key j p,
      (tr0.endBy enterFrom (firstStage key j p).finish).timing.delay +
        (tr0.endBy enterFrom (firstStage key j p).finish).timing.duration ≤ enterFrom :=
  fun _ h0 =>
    Nat.le_trans (finish_le ((firstStage key j p).endBy enterFrom) _ (List.mem_map_of_mem h0))
      (endBy_finish _ _)

/-- No track of a new thing starts before the window of its level. -/
theorem stagedOf_starts (key : α → κ) (p : Plan α) (enterFrom levels : Nat) (rank : α → Nat)
    (n : α) : ∀ tr ∈ stagedOf key p enterFrom levels rank n,
      enterFrom + rank n * slot enterFrom levels ≤ tr.timing.delay :=
  slotted_starts _ _ _ _

/-- Each track of a new thing is over by the end of the window of its level, where the
transitions that the plan gives the thing fit in a thousand each. -/
theorem stagedOf_ends (key : α → κ) (p : Plan α) (enterFrom levels : Nat) (rank : α → Nat) (n : α)
    (ht : ∀ c ∈ p.enter n, c.2.delay + c.2.duration ≤ 1000) :
    ∀ tr ∈ stagedOf key p enterFrom levels rank n,
      tr.timing.delay + tr.timing.duration ≤ enterFrom + (rank n + 1) * slot enterFrom levels :=
  slotted_ends _ _ _ _ fun tr h => by
    obtain ⟨c, hc, rfl⟩ := mem_tracks.mp h
    exact ht c hc

/-- **The kept things first.** Every track of the first stage is over before any track of a new
thing starts: no new thing appears before the kept things are at rest and the old things are
gone. It asks nothing of the plan or of the ranks. -/
theorem staged_kept_first (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) {tr0 y : Track κ} {n : α} (h0 : tr0 ∈ firstStage key j p)
    (hy : y ∈ stagedOf key p enterFrom levels rank n) :
    (tr0.endBy enterFrom (firstStage key j p).finish).timing.delay +
      (tr0.endBy enterFrom (firstStage key j p).finish).timing.duration ≤ y.timing.delay :=
  Nat.le_trans (staged_first_ends key j p enterFrom tr0 h0)
    (Nat.le_trans (Nat.le_add_right _ _) (stagedOf_starts key p enterFrom levels rank n y hy))

/-- **Level by level.** A track of a new thing of one level is over before a track of a new
thing of a deeper level starts: nothing appears before the level above it is done. It asks that
the transitions of the thing of the earlier level fit in a thousand. -/
theorem staged_levels (key : α → κ) (p : Plan α) (enterFrom levels : Nat) (rank : α → Nat)
    {n n' : α} (hr : rank n < rank n')
    (ht : ∀ c ∈ p.enter n, c.2.delay + c.2.duration ≤ 1000) {x y : Track κ}
    (hx : x ∈ stagedOf key p enterFrom levels rank n)
    (hy : y ∈ stagedOf key p enterFrom levels rank n') :
    x.timing.delay + x.timing.duration ≤ y.timing.delay := by
  have h1 := stagedOf_ends key p enterFrom levels rank n ht x hx
  have h2 := stagedOf_starts key p enterFrom levels rank n' y hy
  have h3 : (rank n + 1) * slot enterFrom levels ≤ rank n' * slot enterFrom levels :=
    Nat.mul_le_mul_right _ hr
  omega

/-- **The kept things are at rest from `enterFrom` on**, with a plan that settles and is proper:
each stands on its place, in its shape, when the first new thing may appear. -/
theorem staged_kept_rest (key : α → κ) (j : Join α) (p : Plan α) (enterFrom : Nat)
    (hs : p.Settles) (hp : p.Proper) {tr0 : Track κ} (h0 : tr0 ∈ keeping key j p) {t : Nat}
    (ht : enterFrom ≤ t) :
    ((tr0.endBy enterFrom (firstStage key j p).finish).at t).AtRest := by
  have eu := Track.endBy_untimed enterFrom (firstStage key j p).finish tr0
  have hst : tr0 ∈ staying key j p := List.mem_append_left _ h0
  have e1 : (tr0.endBy enterFrom (firstStage key j p).finish).timing.ease = tr0.timing.ease :=
    congrArg (fun u => u.2.2) eu
  have e2 : (tr0.endBy enterFrom (firstStage key j p).finish).change = tr0.change :=
    congrArg (fun u => u.2.1) eu
  refine Track.atRest_of_done _ t ⟨?_, Nat.le_trans
    (staged_first_ends key j p enterFrom tr0 (List.mem_append_left _ h0)) ht⟩ ?_
  · rw [e1]
    exact staying_proper key j p hp tr0 hst
  · show (tr0.endBy enterFrom (firstStage key j p).finish).change.stop.AtRest
    rw [e2]
    exact staying_settles key j p hs tr0 hst

/-- **A staged step respects an order in time.** Let the plan's first stage respect `before`,
let `before` put no new thing before a thing of the first stage, and let it follow the rank
among the new things. Then no thing starts before a thing that is before it is done: with
`before` the edges of a tree and the rank the depth, no child appears before its parent. -/
theorem staged_respects (before : κ → κ → Prop) (key : α → κ) (j : Join α) (p : Plan α)
    (enterFrom levels : Nat) (rank : α → Nat) (h1 : (firstStage key j p).Respects before)
    (h2 : ∀ n ∈ j.enter, ∀ tr0 ∈ firstStage key j p, ¬ before (key n) tr0.key)
    (hr : ∀ n ∈ j.enter, ∀ n' ∈ j.enter, before (key n) (key n') → rank n < rank n')
    (ht : ∀ n ∈ j.enter, ∀ c ∈ p.enter n, c.2.delay + c.2.duration ≤ 1000) :
    (staged key j p enterFrom levels rank).Respects before := by
  intro a ha b hb hab
  rcases (mem_staged key j p enterFrom levels rank).mp hb with ⟨tr0, h0, rfl⟩ | ⟨n', hn', hy⟩
  · rcases (mem_staged key j p enterFrom levels rank).mp ha with ⟨tr1, h1', rfl⟩ | ⟨n, hn, hx⟩
    · exact endBy_respects before (firstStage key j p) enterFrom h1 _ (List.mem_map_of_mem h1')
        _ (List.mem_map_of_mem h0) hab
    · obtain ⟨c, _, rfl⟩ := (mem_stagedOf key p enterFrom levels rank n).mp hx
      have ek : (tr0.endBy enterFrom (firstStage key j p).finish).key = tr0.key :=
        congrArg Prod.fst (Track.endBy_untimed _ _ tr0)
      rw [ek] at hab
      exact absurd hab (h2 n hn tr0 h0)
  · rcases (mem_staged key j p enterFrom levels rank).mp ha with ⟨tr1, h1', rfl⟩ | ⟨n, hn, hx⟩
    · exact staged_kept_first key j p enterFrom levels rank h1' hy
    · obtain ⟨c, _, rfl⟩ := (mem_stagedOf key p enterFrom levels rank n).mp hx
      obtain ⟨c', _, rfl⟩ := (mem_stagedOf key p enterFrom levels rank n').mp hy
      exact staged_levels key p enterFrom levels rank (hr n hn n' hn' hab) (ht n hn) hx hy
/-! ### The end of a staged step -/

/-- **Every track of a staged step is over by the step's end**, where the new things enter by
then, each has a rank below `levels`, and the transitions that the plan gives it fit in a
thousand. -/
theorem staged_ends (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) (he : enterFrom ≤ 1000) (hl : ∀ n ∈ j.enter, rank n < levels)
    (ht : ∀ n ∈ j.enter, ∀ c ∈ p.enter n, c.2.delay + c.2.duration ≤ 1000) :
    ∀ tr ∈ staged key j p enterFrom levels rank, tr.timing.delay + tr.timing.duration ≤ 1000 := by
  intro tr h
  rcases (mem_staged key j p enterFrom levels rank).mp h with ⟨tr0, h0, rfl⟩ | ⟨n, hn, hm⟩
  · exact Nat.le_trans (staged_first_ends key j p enterFrom tr0 h0) he
  · exact Nat.le_trans (stagedOf_ends key p enterFrom levels rank n (ht n hn) tr hm)
      (slot_window_le he (hl n hn))

/-- A staged step is over by the step's end, on the same three terms. -/
theorem staged_finish (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) (he : enterFrom ≤ 1000) (hl : ∀ n ∈ j.enter, rank n < levels)
    (ht : ∀ n ∈ j.enter, ∀ c ∈ p.enter n, c.2.delay + c.2.duration ≤ 1000) :
    (staged key j p enterFrom levels rank).finish ≤ 1000 :=
  finish_le_of _ 1000 (staged_ends key j p enterFrom levels rank he hl ht)

/-- **A staged step needs no cut at the step's end**: held inside the step it is itself, on the
same three terms. -/
theorem staged_within (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) (he : enterFrom ≤ 1000) (hl : ∀ n ∈ j.enter, rank n < levels)
    (ht : ∀ n ∈ j.enter, ∀ c ∈ p.enter n, c.2.delay + c.2.duration ≤ 1000) :
    (staged key j p enterFrom levels rank).within = staged key j p enterFrom levels rank :=
  within_of_ends _ (staged_ends key j p enterFrom levels rank he hl ht)

/-- Every track of a staged step has a proper easing, where the plan is proper. -/
theorem staged_proper (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) (hp : p.Proper) :
    ∀ tr ∈ staged key j p enterFrom levels rank, tr.timing.ease.Proper := by
  intro tr h
  obtain ⟨tr0, h0, e⟩ := mem_staged_ofJoin key j p enterFrom levels rank h
  have ee : tr0.timing.ease = tr.timing.ease := congrArg (fun u => u.2.2) e
  rw [← ee]
  exact ofJoin_proper key j p hp tr0 h0

/-- **Every track of a staged step is done at the step's end**, with a proper plan and on the
same three terms: each thing stands at the end of its change, the things that leave too. -/
theorem staged_done (key : α → κ) (j : Join α) (p : Plan α) (enterFrom levels : Nat)
    (rank : α → Nat) (hp : p.Proper) (he : enterFrom ≤ 1000)
    (hl : ∀ n ∈ j.enter, rank n < levels)
    (ht : ∀ n ∈ j.enter, ∀ c ∈ p.enter n, c.2.delay + c.2.duration ≤ 1000) :
    ∀ tr ∈ staged key j p enterFrom levels rank, tr.Done 1000 := fun tr h =>
  ⟨staged_proper key j p enterFrom levels rank hp tr h,
    staged_ends key j p enterFrom levels rank he hl ht tr h⟩

/-- Every track of a staged step ends at rest, with a plan that settles, or is of a thing that
leaves: its key is of no thing of the new list. -/
theorem staged_settles [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (enterFrom levels : Nat) (rank : α → Nat) (hs : p.Settles) :
    ∀ tr ∈ staged key (join key old new) p enterFrom levels rank,
      tr.Settles ∨ ∀ n ∈ new, key n ≠ tr.key := by
  intro tr htr
  rcases (mem_staged key (join key old new) p enterFrom levels rank).mp htr with
    ⟨tr0, h0, rfl⟩ | ⟨n', _, hm⟩
  · have eu := Track.endBy_untimed enterFrom (firstStage key (join key old new) p).finish tr0
    have h0' : tr0 ∈ keeping key (join key old new) p ++ leaving key (join key old new) p := h0
    rcases List.mem_append.mp h0' with hkp | hlv
    · have e2 : (tr0.endBy enterFrom (firstStage key (join key old new) p).finish).change =
          tr0.change := congrArg (fun u => u.2.1) eu
      refine Or.inl ?_
      show (tr0.endBy enterFrom (firstStage key (join key old new) p).finish).change.stop.AtRest
      rw [e2]
      exact staying_settles key (join key old new) p hs tr0 (List.mem_append_left _ hkp)
    · obtain ⟨_, _, _, hne⟩ := mem_leaving_key key old new p hlv
      have ek : (tr0.endBy enterFrom (firstStage key (join key old new) p).finish).key =
          tr0.key := congrArg Prod.fst eu
      refine Or.inr fun n hn => ?_
      rw [ek]
      exact hne n hn
  · obtain ⟨c, hc, rfl⟩ := (mem_stagedOf key p enterFrom levels rank n').mp hm
    exact Or.inl (hs.2 n' c hc)

/-- **The last picture of a staged step.** At the step's end and after, every pose that the
step sets on a thing of the new list is at rest, with a plan that settles and is proper and on
the same three terms. With `Join.drawn_end`, the things drawn then are the new list, each as the
still picture has it. -/
theorem staged_end [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (enterFrom levels : Nat) (rank : α → Nat) (hs : p.Settles) (hp : p.Proper)
    (he : enterFrom ≤ 1000) (hl : ∀ n ∈ (join key old new).enter, rank n < levels)
    (ht : ∀ n ∈ (join key old new).enter, ∀ c ∈ p.enter n, c.2.delay + c.2.duration ≤ 1000)
    {n : α} (hn : n ∈ new) {t : Nat} (h1000 : 1000 ≤ t) :
    ∀ q ∈ (staged key (join key old new) p enterFrom levels rank).posesOf (key n) t,
      q.AtRest := by
  intro q hq
  obtain ⟨tr, htr, hk, rfl⟩ := mem_posesOf _ _ _ hq
  have hd : tr.Done t :=
    ⟨staged_proper key (join key old new) p enterFrom levels rank hp tr htr, Nat.le_trans
      (staged_ends key (join key old new) p enterFrom levels rank he hl ht tr htr) h1000⟩
  rcases staged_settles key old new p enterFrom levels rank hs tr htr with hst | hne
  · exact Track.atRest_of_done tr t hd hst
  · exact absurd (beq_iff_eq.mp hk).symm (hne n hn)

/-- **The last picture, with no term on the stages.** Held inside its step, a staged step has
every pose on a thing of the new list at rest at the step's end and after, with a plan that
settles and is proper: whatever the ranks and however long the entrances. A caller that cannot
show the three terms cuts the step, and its last picture is still the next picture. -/
theorem staged_within_end [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (enterFrom levels : Nat) (rank : α → Nat) (hs : p.Settles) (hp : p.Proper) {n : α}
    (hn : n ∈ new) {t : Nat} (h1000 : 1000 ≤ t) :
    ∀ q ∈ (staged key (join key old new) p enterFrom levels rank).within.posesOf (key n) t,
      q.AtRest := by
  intro q hq
  obtain ⟨tr, htr, hk, rfl⟩ := mem_posesOf _ _ _ hq
  have hd : tr.Done t := Track.done_of_le (within_done _
    (staged_proper key (join key old new) p enterFrom levels rank hp) tr htr) h1000
  obtain ⟨tr0, h0, rfl⟩ := mem_within _ htr
  rcases staged_settles key old new p enterFrom levels rank hs tr0 h0 with hst | hne
  · exact Track.atRest_of_done _ t hd hst
  · exact absurd (beq_iff_eq.mp hk).symm (hne n hn)
end Motion

/-! ## The two entrances of lean4-effect4's viewer

Its sampler starts a new edge at the start of its level's slot and draws it for 45 per cent of
the slot, or for the choreography's own duration where that is less. It starts the box at the
edge's end 40 per cent into the slot and grows it for 60 per cent of the slot, or for its own
duration. Each is a part of a window with a cap, for every slot, every start and every cap. -/

/-- The draw of a new edge: `{ c.draw with duration := min c.draw.duration (slot * 45 / 100) }`
started at the level's start. -/
example (ease : Easing) (most start slot : Nat) (hs : slot ≤ 1000) :
    (({ delay := 0, duration := 450, ease := ease } : Transition).atMost most slot).inWindow
      start slot = { delay := start, duration := min (slot * 45 / 100) most, ease := ease } :=
  (Transition.atMost_inWindow_cent 0 45 most start slot ease hs).trans
    (by rw [Nat.mul_zero, Nat.zero_div, Nat.add_zero])

/-- The growth of the box at an edge's end:
`{ c.expand with duration := min c.expand.duration (slot * 60 / 100) }` started
`slot * 40 / 100` after the level's start. -/
example (ease : Easing) (most start slot : Nat) (hs : slot ≤ 1000) :
    (({ delay := 400, duration := 600, ease := ease } : Transition).atMost most slot).inWindow
      start slot =
      { delay := start + slot * 40 / 100, duration := min (slot * 60 / 100) most, ease := ease } :=
  Transition.atMost_inWindow_cent 40 60 most start slot ease hs
/-! ## Finite evaluations

A thing is a key, a place across, a level, and whether it is an edge. The step is the one of
five things that the port of lean4-effect4's motion draws
(`WhatwgTest/Html/SvgMotion.lean`): the box `1` moves, the box `2` leaves, and the box `3`, the
edge `4` that ends at it and the box `5` one level down are new. The plan has the consumer's
default numbers in per mille of its step, with the entrances as shares of a window: an edge
draws in the first 45 per cent, and a box grows from 40 per cent on.

With the new things from the moment `300`, as the consumer has it, the three new things have
the consumer's delays and durations: `(440, 210)`, `(300, 157)` and `(790, 210)`. The first
stage differs. The consumer's kept box moves for `450` and its old box shrinks for `250`, past
the moment `300`. Here the two are fitted to end by `300`. With the new things from `450`, the
first stage is as the consumer has it. -/

#guard
  let key : Nat × Int × Nat × Bool → Nat := fun a => a.1
  let old : List (Nat × Int × Nat × Bool) := [(1, 40, 0, false), (2, 40, 0, false)]
  let new : List (Nat × Int × Nat × Bool) :=
    [(1, 100, 0, false), (3, 100, 0, false), (4, 100, 0, true), (5, 100, 1, false)]
  let p : Plan (Nat × Int × Nat × Bool) :=
    { kept := Plan.moving (fun a => ⟨a.2.1, 0⟩) { duration := 450 }
      enter := fun a =>
        if a.2.2.2 then [(.reveal 0 1000, { delay := 0, duration := 450 })]
        else [(.grow 0 1000, { delay := 400, duration := 600 })]
      leave := fun _ => [(.grow 1000 0, { duration := 250 })] }
  let times (enterFrom : Nat) : List (Nat × Nat × Nat) :=
    (Motion.staged key (join key old new) p enterFrom 2 fun a => a.2.2.1).map
      fun tr => (tr.key, tr.timing.delay, tr.timing.duration)
  times 300 == [(1, 0, 300), (3, 440, 210), (4, 300, 157), (5, 790, 210), (2, 0, 166)] &&
    times 450 == [(1, 0, 450), (3, 560, 165), (4, 450, 123), (5, 835, 165), (2, 0, 250)]

-- With one level the window is `700` long. The consumer's own durations are then the shorter:
-- its edge draws for `220` and its box grows for `360`. The plain shares are `315` and `420`,
-- and the shares with a cap are the consumer's.
#guard
  let slot := Motion.slot 300 1
  let plain (tr : Transition) := (tr.inWindow 300 slot).duration
  let capped (tr : Transition) (most : Nat) := ((tr.atMost most slot).inWindow 300 slot).duration
  (plain { delay := 0, duration := 450 }, plain { delay := 400, duration := 600 }) == (315, 420) &&
    (capped { delay := 0, duration := 450 } 220, capped { delay := 400, duration := 600 } 360) ==
      (220, 360)

-- A control of `Motion.slotted_respects`, which needs a rank that follows the order. A parent
-- `0` and its child `1`, each for a whole window: ranked by their keys the child waits for the
-- parent, and with the child ranked above its parent it does not.
#guard decide (Motion.Respects (fun a b : Nat => a < b)
  (Motion.slotted [⟨0, .grow 0 1000, {}⟩, ⟨1, .grow 0 1000, {}⟩] 0 500 fun k => k))
#guard !decide (Motion.Respects (fun a b : Nat => a < b)
  (Motion.slotted [⟨0, .grow 0 1000, {}⟩, ⟨1, .grow 0 1000, {}⟩] 0 500 fun k => 1 - k))

-- A control of `Motion.staged_ends`, which needs transitions that fit in a thousand. A new
-- thing whose entrance is one and a half windows long, in the last of two levels, is not over
-- at the step's end: it ends at `1175`.
#guard
  let p : Plan (Nat × Nat) :=
    { kept := fun _ _ => [], enter := fun _ => [(.grow 0 1000, { duration := 1500 })],
      leave := fun _ => [] }
  (Motion.staged Prod.fst (join Prod.fst [] [(1, 0), (2, 1)]) p 300 2 Prod.snd).finish == 1175

end Whatwg.Svg.Scene
