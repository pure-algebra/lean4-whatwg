import Whatwg.Svg.Scene.Stage
import Whatwg.Svg.Scene.Resume

/-!
# Whatwg.Svg.Scene.Step

Owner: a step from one picture to the next, as one value (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`).

A step is made of pieces that other modules own: the join of two pictures by key
(`Whatwg/Svg/Scene/Join.lean`), a plan of what each thing does (`Plan.lean`), the tracks of the
join under the plan, held inside the step (`Motion.ofJoin`, `Motion.within`), the same tracks in
stages (`Stage.lean`), the things drawn at a moment (`Join.drawn`), what each looks like then
(`Frame.lean`), and the plan of a step that begins before the last one has ended
(`Resume.lean`). A caller that puts the pieces together by hand names its key five times, joins
its two pictures three times and has to remember the cut at the step's end. Here the pieces are
put together once.

- `Step α κ`: the key, the picture before, the picture after, the plan, and how the step is
  timed. A caller writes it once, as a structure.
- `Stages α`: the three numbers of a step in stages, as one value: the moment the new things
  enter from, the number of levels, and the level of each new thing. A step with no stages is
  timed as its plan says.
- `Step.planned key old new plan`: a step whose plan is made from its join, for a look whose
  entrances depend on what enters. `Step.staged s enterFrom levels rank`: the step, in stages.
- `Step.join`: the join of the two pictures. `Step.motion`: the tracks of the step, always held
  inside the step, so a caller never writes the cut. `Step.drawn t`: the things drawn at a
  moment, with the things that leave until the step's end. `Step.frame a t`: what a thing looks
  like at a moment. `Step.sample t`: the things drawn at a moment, each with its frame.
- `Step.next s newer`: the step after `s`, from its new picture to the picture `newer`.
- `Step.interrupt s t newer settle shape`: **the step that begins while `s` is still moving.**
  It goes from the things that `s` draws at the moment `t` to the picture `newer`, and each old
  thing starts where `s` shows it at `t`. It is timed as its plan says. Where `s` was over at
  `t`, it shows what `Step.next s newer` shows (`Step.interrupt_of_rest` of the laws).

What a reader of pictures needs of a step is here: `Step.drawn 0` is the things to draw, each
with its key by `Step.key`, and `Step.motion` is their tracks.

The laws of a step are in `Whatwg/Svg/Scene/Step/Laws.lean`: the last picture, one track for
each property, kept things that keep their relations, the order of a step in stages, and what
holds across `interrupt`. This module has the readings that are true by definition.

One decision, and its reason. The stages are a field of the step and not a second function for
its motion. With a second function, each reader of a step needs a second form too: its frame,
its sample, the step that interrupts it. With a field there is one of each, and three laws read
the same for both timings: the last picture (`Step.frame_end`), one track for each property
(`Step.single`) and the relations of kept things (`Step.together`).

What this module does not claim. `Step.motion` of a step in stages is the staged tracks held
inside the step: where a new thing's level is past the last or its entrance is longer than its
window, the cut shortens it, and `Step.motion_of_stages` of the laws says when there is no cut.
`Step.next` and `Step.interrupt` give a step with no stages, since the levels of a step depend
on what enters in it. The laws of the first moment of `interrupt` are of a step timed as its
plan says, and a caller that puts it in stages keeps the last picture and not those laws. A step
holds two lists and a plan and no proof: that the keys of a picture are distinct is a premise of
the laws that need it, and a program decides it of its own pictures.

The instance at the head of this module, which decides whether the keys of a list are distinct,
belongs in `Whatwg/Svg/Scene/Join.lean`, beside `Distinct`.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

variable {α κ : Type}

/-- Whether the keys of a list are distinct: a program can test its pictures. -/
instance [DecidableEq κ] (key : α → κ) (l : List α) : Decidable (Distinct key l) :=
  inferInstanceAs (Decidable (l.map key).Nodup)

/-- **The stages of a step**: the kept things and the things that leave come first, and then the
new things enter level by level (`Motion.staged`). -/
structure Stages (α : Type) where
  /-- The moment by which the kept things and the things that leave are over, and from which the
  new things enter. -/
  enterFrom : Nat
  /-- In how many levels the new things enter. -/
  levels : Nat
  /-- The level of a new thing, from `0`. -/
  rank : α → Nat

/-- **A step from one picture to the next.** The things of both pictures are of one type, and a
thing's key is the name of what it draws. -/
structure Step (α κ : Type) where
  /-- The name of what a thing draws. -/
  key : α → κ
  /-- The picture before. -/
  old : List α
  /-- The picture after. -/
  new : List α
  /-- What a kept thing, a new thing and a thing that leaves does. -/
  plan : Plan α
  /-- The stages of the step. With none, each thing moves when the plan says. -/
  stages : Option (Stages α) := none

namespace Step

/-- **A step whose plan is made from its join**: a look whose entrances depend on which things
enter, as where each level of new things has a share of the step. -/
def planned [BEq κ] (key : α → κ) (old new : List α) (plan : Join α → Plan α) : Step α κ :=
  { key, old, new, plan := plan (Scene.join key old new) }

/-- The step in stages: the kept things and the things that leave are over by `enterFrom`, and
the new things enter from then on in `levels` levels, each at the level that `rank` gives it. -/
def staged (s : Step α κ) (enterFrom levels : Nat) (rank : α → Nat) : Step α κ :=
  { s with stages := some ⟨enterFrom, levels, rank⟩ }

/-- The join of the two pictures of the step: the things that enter, the pairs that are kept and
the things that leave. -/
def join [BEq κ] (s : Step α κ) : Join α := Scene.join s.key s.old s.new

/-- **The tracks of the step**, held inside the step: no track starts after the step's end or
ends after it. With no stages they are the tracks of the join under the plan (`Motion.ofJoin`).
With stages they are those tracks in stages (`Motion.staged`). -/
def motion [BEq κ] (s : Step α κ) : Motion κ :=
  match s.stages with
  | none => (Motion.ofJoin s.key s.join s.plan).within
  | some g => (Motion.staged s.key s.join s.plan g.enterFrom g.levels g.rank).within

/-- **The things drawn at the moment `t`**: the old things that leave, until the step's end, and
then the things of the new picture. -/
def drawn [BEq κ] (s : Step α κ) (t : Nat) : List α := s.join.drawn s.new t

/-- **What a thing looks like at the moment `t`**: how far off its place it stands, its size, how
much of its line is drawn, its opacity and its shape. A thing with no track is the still
picture. -/
def frame [BEq κ] (s : Step α κ) (a : α) (t : Nat) : Frame := s.motion.frame (s.key a) t

/-- **The picture at the moment `t`**: the things drawn then, each with its frame. -/
def sample [BEq κ] (s : Step α κ) (t : Nat) : List (α × Frame) :=
  let m := s.motion
  (s.drawn t).map fun a => (a, m.frame (s.key a) t)

/-- **The step after this one**: from this step's new picture to the picture `newer`, under this
step's plan unless another is given. It is timed as its plan says. -/
def next (s : Step α κ) (newer : List α) (plan : Plan α := s.plan) : Step α κ :=
  { key := s.key, old := s.new, new := newer, plan }

/-- **The step that begins while this one is still moving.** At the moment `t` a request for
the picture `newer` arrives. The step that answers it goes from the things drawn at `t`, the
things that were leaving too, to `newer`. Each old thing starts where this step shows it at `t`
(`Plan.resumeFrom`), so nothing jumps. `settle n` brings to rest what the plan does not change of
a kept thing, and `shape n` is the thing's own shape, where it has one that a track can change.
The plan is this step's, unless another is given. -/
def interrupt [BEq κ] (s : Step α κ) (t : Nat) (newer : List α) (settle : α → Transition)
    (shape : α → Option (List ICubic) := fun _ => none) (plan : Plan α := s.plan) : Step α κ where
  key := s.key
  old := s.drawn t
  new := newer
  plan := plan.resumeFrom s.key s.motion t settle shape

/-! ## Readings that are true by definition -/

/-- A step with no stages has the tracks of its join under its plan, held inside the step. -/
theorem motion_of_none [BEq κ] (s : Step α κ) (h : s.stages = none) :
    s.motion = (Motion.ofJoin s.key s.join s.plan).within := by
  unfold motion
  rw [h]

/-- A step in stages has the staged tracks of its join under its plan, held inside the step. -/
theorem motion_of_some [BEq κ] (s : Step α κ) {g : Stages α} (h : s.stages = some g) :
    s.motion = (Motion.staged s.key s.join s.plan g.enterFrom g.levels g.rank).within := by
  unfold motion
  rw [h]

/-- Until the step's end the things that leave are drawn, under the things of the new
picture. -/
theorem drawn_before [BEq κ] (s : Step α κ) {t : Nat} (h : t < 1000) :
    s.drawn t = s.join.exit ++ s.new :=
  Join.drawn_before s.join s.new h

/-- **At the step's end and after, the things drawn are the new picture.** -/
theorem drawn_end [BEq κ] (s : Step α κ) {t : Nat} (h : 1000 ≤ t) : s.drawn t = s.new :=
  Join.drawn_end s.join s.new h

/-- The picture at a moment is each thing drawn then with its frame. -/
theorem sample_eq [BEq κ] (s : Step α κ) (t : Nat) :
    s.sample t = (s.drawn t).map fun a => (a, s.frame a t) := rfl

/-- The things of the picture at a moment are the things drawn then, in their order. -/
theorem sample_things [BEq κ] (s : Step α κ) (t : Nat) :
    (s.sample t).map Prod.fst = s.drawn t :=
  (List.map_map.trans (List.map_congr_left fun _ _ => rfl)).trans (List.map_id _)

/-- A step that interrupts another goes from the things drawn at the interruption. -/
theorem interrupt_old [BEq κ] (s : Step α κ) (t : Nat) (newer : List α)
    (settle : α → Transition) (shape : α → Option (List ICubic)) (p : Plan α) :
    (s.interrupt t newer settle shape p).old = s.drawn t := rfl

/-- The plan of a step that interrupts another is the plan resumed from where each thing is
seen. -/
theorem interrupt_plan [BEq κ] (s : Step α κ) (t : Nat) (newer : List α)
    (settle : α → Transition) (shape : α → Option (List ICubic)) (p : Plan α) :
    (s.interrupt t newer settle shape p).plan =
      p.resume (fun a => s.frame a t) settle shape := rfl

end Step

/-! ## Finite evaluations

A thing is a key and a place along one axis. The plan moves a kept thing whose place changed,
grows a new thing and shrinks an old one. In the step the thing `1` stays where it is, the thing
`2` moves by two, the thing `4` is new and the thing `3` leaves. -/

-- The tracks of a step are those of its join under its plan, held inside the step, and the
-- things drawn are the thing that leaves and then the new picture, until the step's end.
#guard
  let places : Plan (Nat × Int) :=
    ⟨Plan.moving (fun a => ⟨a.2, 0⟩) {}, fun _ => [(.grow 0 1000, {})],
      fun _ => [(.grow 1000 0, {})]⟩
  let s : Step (Nat × Int) Nat :=
    { key := Prod.fst, old := [(1, 0), (2, 5), (3, 9)], new := [(1, 0), (2, 7), (4, 1)],
      plan := places }
  s.motion.map (fun tr => (tr.key, tr.change)) ==
      [(2, Change.shift ⟨-2, 0⟩ 0), (4, Change.grow 0 1000), (3, Change.grow 1000 0)] &&
    s.drawn 0 == [(3, 9), (1, 0), (2, 7), (4, 1)] && s.drawn 1000 == [(1, 0), (2, 7), (4, 1)] &&
    (s.sample 500).map (fun x => (x.1.1, x.2.shift.x, x.2.size)) ==
      [(3, 0, 500), (1, 0, 1000), (2, -1, 1000), (4, 0, 500)]

-- A control of the cut at the step's end. A plan whose move is two steps long gives a track
-- that ends at the moment `2000`. The step holds it inside itself: it ends at `1000`, and the
-- thing is on its place there.
#guard
  let slow : Plan (Nat × Int) :=
    ⟨Plan.moving (fun a => ⟨a.2, 0⟩) { duration := 2000 }, fun _ => [], fun _ => []⟩
  let s : Step (Nat × Int) Nat :=
    { key := Prod.fst, old := [(2, 5)], new := [(2, 7)], plan := slow }
  (Motion.ofJoin s.key s.join s.plan).map (fun tr => tr.timing.duration) == [2000] &&
    s.motion.map (fun tr => tr.timing.duration) == [1000] && s.frame (2, 7) 1000 == {}

-- The same step in stages, and the step that interrupts it. In stages the kept thing is over
-- by the moment `300` and the new thing enters from then. Interrupted at the moment `150`, the
-- thing `2` is seen one unit off its place, and the next step starts it there: its new place is
-- `10`, three further, so it starts four off.
#guard
  let places : Plan (Nat × Int) :=
    ⟨Plan.moving (fun a => ⟨a.2, 0⟩) {}, fun _ => [(.grow 0 1000, {})],
      fun _ => [(.grow 1000 0, {})]⟩
  let s : Step (Nat × Int) Nat :=
    ({ key := Prod.fst, old := [(1, 0), (2, 5), (3, 9)], new := [(1, 0), (2, 7), (4, 1)],
       plan := places } : Step (Nat × Int) Nat).staged 300 1 fun _ => 0
  let r := s.interrupt 150 [(1, 0), (2, 10)] fun _ => {}
  s.motion.map (fun tr => (tr.key, tr.timing.delay, tr.timing.duration)) ==
      [(2, 0, 300), (4, 300, 700), (3, 0, 300)] &&
    (s.frame (2, 7) 150).shift == ⟨-1, 0⟩ && r.old == [(3, 9), (1, 0), (2, 7), (4, 1)] &&
    (r.frame (2, 10) 0).shift == ⟨-4, 0⟩ && r.frame (2, 10) 1000 == {}

end Whatwg.Svg.Scene
