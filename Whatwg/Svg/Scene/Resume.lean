import Whatwg.Svg.Scene.Plan
import Whatwg.Svg.Scene.Frame

/-!
# Whatwg.Svg.Scene.Resume

Owner: a step that is interrupted, and resumes from where things are seen (slice S16 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-87).

A picture of a program changes when the program does, and the program does not wait. A request
can arrive while the step before is still moving. A step that starts from the still picture
then makes every moving thing jump back to its place. Here the picture of every moment is data
(`Motion.frame` of `Whatwg/Svg/Scene/Frame.lean`), so the next step can start each thing exactly
where it is seen. This module is that step, and the law that nothing jumps.

How a caller uses it. The step before was `m`, the motion of a join `j` to the list `new`, and
it is interrupted at the moment `t`. The things drawn then are `olds := j.drawn new t`, and each
is seen at `seen o := m.frame (key o) t`. The next picture is `next`. The caller writes the plan
`p` of the step from `olds` to `next` as if every old thing stood still, and plays

```
(Motion.ofJoin key (join key olds next) (p.resume seen settle shape)).within
```

- The reader of this module is `Frame.Shows f p` of `Whatwg/Svg/Scene/Frame.lean`: the frame
  shows the pose. A law here says what a frame shows, one property at a time.
- `Change.stay`: the change that holds a thing at the start of a change. `Frame.hold`: the
  changes that hold a thing as it is seen, one for each of its place, its size, its line and its
  opacity that is not at rest. `Frame.reshape`: the change of shape from the shape that is seen
  to another, where both are known.
- `Frame.carry f fill tm cs`: the changes `cs` of a plan, each started where the thing is seen
  (`Change.from`), and after them the changes of `fill` whose property the plan does not change,
  by the transition `tm`.
- `Frame.resume`: `carry` for a kept thing. What the plan does not change goes to rest
  (`Frame.toRest`), and the shape that is seen goes to the thing's own, where that is given.
- `Frame.leaveFrom`: `carry` for a thing that leaves. What the plan does not change is held as
  it is seen, the shape too.
- `Plan.resume`: the plan with every answer for a kept thing and for a thing that leaves taken
  from where the old thing is seen. A new thing enters as the plan says. `Plan.resumeFrom` is
  `Plan.resume` with each old thing seen at its frame in a motion `m` at a moment `t`, so a
  caller writes `p.resumeFrom key m t settle shape` and no `seen`.
- `Plan.sprout`: how a new thing enters from the place of the thing it comes from.

What the laws say:

- The end. A resumed plan settles where the plan does, and is proper where the plan is and
  every `settle` has a proper easing (`Plan.resume_settles`, `Plan.resume_proper`). So the
  resumed step ends on the next picture (`Motion.resume_end`).
- **Nothing jumps**, for one thing. The frame of the starts of a resumed answer shows whatever
  the thing is seen with (`Frame.resume_shows`): its size, its line and its opacity in every
  case (`Frame.resume_size`, `Frame.resume_part`, `Frame.resume_shown`), its place where the
  plan does not move it, and its shape where the plan changes the shape or the thing's own
  shape is given (`Frame.resume_shape`). A thing that the plan moves starts where the plan's
  starts put it, moved by the shift at which it is seen (`Frame.resume_shift`). With
  `Plan.moving` that is where it is seen, in the places of the next picture: its new place and
  its shift are its old place and the shift it had (`Frame.resume_moving`).
- **Nothing jumps**, for the step. With distinct keys in the next list, the poses of a kept
  thing at the first moment of the resumed step are the starts of its resumed answer
  (`Motion.resume_kept_poses`, `Motion.resume_kept_frame`). So the thing shows whatever its old
  thing was seen with (`Motion.resume_kept_shows`) and stands where it stood
  (`Motion.resume_kept_shift`, `Motion.resume_kept_place`). `Motion.nothing_jumps` and
  `Motion.nothing_moves` say it of the caller's own step: the frames are those of the motion
  `m` at the moment `t`, and the resumed step is held inside its step.
  `Motion.nothing_jumps_from` and `Motion.nothing_moves_from` are the two said of
  `Plan.resumeFrom`. These ask that each transition reads `0` at the moment `0`. It does where
  its easing is proper and it has a delay or a duration (`Transition.at_zero` of
  `Whatwg/Svg/Scene/Motion/Laws.lean`), and holding it inside its step does not change that
  (`Transition.within_at_zero` there, and `Motion.within_frame_zero` of `Frame.lean`).
- A thing that leaves. The frame of the starts of `leaveFrom` shows whatever the thing is seen
  with, its shape too (`Frame.leaveFrom_shows`, `Frame.leaveFrom_shift`), and what the plan does
  not change is held at every moment (`Frame.leaveFrom_held`). For the step:
  `Motion.resume_leaving_shows` and `Motion.resume_leaving_held`, with distinct keys among the
  things drawn at the interruption (`Join.drawn_distinct` of `Whatwg/Svg/Scene/Plan.lean`).
- A thing seen at rest resumes as the plan says (`Frame.resume_of_rest`,
  `Frame.leaveFrom_of_rest`), where each change of the plan of a size, a line or an opacity
  starts at rest. So a step that is not interrupted is the plan's step
  (`Plan.resume_of_rest`).
- Holding. `Frame.mem_hold` lists the changes of `hold`. Each starts at what is seen, ends
  where it starts and reads its start at every eased progress (`Frame.hold_start`,
  `Frame.hold_stop`, `Frame.hold_at`, from `Change.stay_at`). They are of distinct properties,
  none is a change of shape, and there is none exactly when the frame is at rest
  (`Frame.hold_distinct`, `Frame.hold_not_shape`, `Frame.hold_eq_nil`).
- A new thing that comes from another ends at rest (`Plan.sprout_stop`), and starts on the
  thing it comes from, as nothing (`Plan.sprout_start`, `Plan.sprout_origin`). In a step it is
  drawn so at the first moment (`Motion.sprout_frame`).
- One change for each property. `Plan.Single` of `Plan.lean` says that no thing has two changes
  of one property in any answer of a plan. `Plan.sprout` gives one change for each property
  (`Plan.sprout_single`), and a resumed plan does where the plan does (`Plan.resume_single`,
  from `Frame.carry_distinct`). So a resumed step is `Motion.Single`, where the keys of each
  list are distinct (`Motion.resume_single`, by `Motion.single_ofJoin` of `Plan.lean`).

The reader. `Frame.shows_under` of `Frame.lean` says what a frame under a list of poses shows,
and `Frame.carry_shows` says it of `carry` under any reading of a change: its start, or its pose
at a moment. The laws of `resume` and of `leaveFrom` are cases of that one law.

What this module does not claim. Nothing jumps, and nothing is said of speed: a thing on its
way starts its new change by the new transition, from standing. Where the plan has no change of
shape and `shape` gives none, a kept thing that is seen with a shape is drawn with its own shape
at once (`Frame.resume_shape_own`): a caller that changes shapes gives `shape`. The laws of a
place ask that the plan's answer has one change for each property; a plan that gives a thing two
shifts is not covered. The laws of the first moment ask that each transition reads `0` there,
and a control at the end of this file is a transition that does not. `seen` is the caller's: the
laws hold of every `seen`, and `Motion.nothing_jumps` and `Motion.nothing_moves` are the two
that take it from the step before. A thing that leaves again takes the whole of the plan's
transition again, from where it is seen. No law here says that a gap of two pictures is kept
between two resumed things: `Whatwg/Svg/Scene/Between.lean` is of steps that start from the
still picture. The laws are of the kit's own reading of a motion, and what a host draws is an
observation of that host.

What this module holds, and what it cites. It holds the definitions above and the laws of a
resumed step, and nothing of a plan, of a frame or of a list that is not about resuming. The
laws that it was first written with and that another module owns are in that module since the
tidy of slice S16, under the same names, and this file is some five hundred lines shorter. It
cites:

- from `Whatwg/Svg/Scene/Frame.lean`: `Frame.Shows` with `Frame.shows_shift` and its four
  fellows, `Frame.shows_under`, `Frame.shows_ofPoses`, `Frame.shape_ne_none_of_shows`,
  `Pose.eq_of_shows`, and `Motion.within_frame_zero`;
- from `Whatwg/Svg/Scene/Plan.lean`: the poses of the things of a join (`Motion.posesOf_kept`,
  `Motion.posesOf_entering`, `Motion.posesOf_leaving`), on which the laws of a step rest;
  `Plan.Single`, `Plan.moving_single` and `Motion.single_ofJoin`; `Plan.moving_start_shift`; and
  `Join.drawn_distinct`;
- from `Whatwg/Svg/Scene/Motion/Laws.lean`: `Transition.at_zero`;
- from `Whatwg/Svg/Scene/Join/Laws.lean`: `nodup_append_of`.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

variable {α κ : Type}

/-- A step from `b` to `a` and then `s`, taken from `b`, ends at `a` moved by `s`. -/
private theorem IVec.add_sub_add (a b s : IVec) : b + (a - b + s) = a + s :=
  IVec.ext (by simp only [IVec.add_x, IVec.sub_x]; omega)
    (by simp only [IVec.add_y, IVec.sub_y]; omega)

/-! ## Holding a thing as it is seen -/

/-- The change that holds a thing at the start of a change: from that start to that start. -/
def Change.stay : Change → Change
  | .shift a _ => .shift a a
  | .grow a _ => .grow a a
  | .reveal a _ => .reveal a a
  | .fade a _ => .fade a a
  | .morph a _ => .morph a a

namespace Change

/-- A change that stays starts where the change starts. -/
theorem stay_start (c : Change) : c.stay.start = c.start := by
  cases c <;> rfl

/-- A change that stays ends where the change starts. -/
theorem stay_stop (c : Change) : c.stay.stop = c.start := by
  cases c <;> rfl

/-- A change that stays is of the change's property. -/
theorem stay_property (c : Change) : c.stay.property = c.property := by
  cases c <;> rfl

/-- **A change that stays reads the same pose at every eased progress**: the start of the
change. A thing under it does not move, whatever the easing does. -/
theorem stay_at (c : Change) (e : Int) : c.stay.at e = c.start := by
  cases c with
  | shift a _ => exact congrArg Pose.shift (IVec.ext (mix_self a.x e) (mix_self a.y e))
  | grow a _ => exact congrArg Pose.grow (mix_self a e)
  | reveal a _ => exact congrArg Pose.reveal (mix_self a e)
  | fade a _ => exact congrArg Pose.fade (mix_self a e)
  | morph a _ =>
    have hp : ∀ p : IVec, (⟨mix p.x p.x e, mix p.y p.y e⟩ : IVec) = p := fun p =>
      IVec.ext (mix_self p.x e) (mix_self p.y e)
    have hc : ∀ c : ICubic, ICubic.mix c c e = c := fun c =>
      congr (congr (congr (congrArg ICubic.mk (hp c.p0)) (hp c.p1)) (hp c.p2)) (hp c.p3)
    show (Change.morph a a).at e = Pose.shape a
    rw [Change.at_morph a a e rfl, List.zipWith_self]
    exact congrArg Pose.shape ((List.map_congr_left fun c _ => hc c).trans (List.map_id a))

end Change

/-- **The changes that hold a thing as it is seen**: one for each of its place, its size, its
line and its opacity that is not at rest, from the frame's value to the same value. -/
def Frame.hold (f : Frame) : List Change := f.toRest.map Change.stay

/-- The change of shape from the shape a thing is seen with to another shape, where the thing
is seen with a shape and the other shape is known. -/
def Frame.reshape (f : Frame) (own : Option (List ICubic)) : List Change :=
  match f.shape with
  | none => []
  | some seen =>
    match own with
    | none => []
    | some o => [.morph seen o]

namespace Frame

/-- **The changes of `hold`, one by one**: a shift, a size, a line and an opacity from what is
seen to what is seen, each only where the frame is not at rest. -/
theorem mem_hold {f : Frame} {c : Change} : c ∈ f.hold ↔
    (f.shift ≠ 0 ∧ c = .shift f.shift f.shift) ∨ (f.size ≠ 1000 ∧ c = .grow f.size f.size) ∨
      (f.part ≠ 1000 ∧ c = .reveal f.part f.part) ∨
      (f.shown ≠ 1000 ∧ c = .fade f.shown f.shown) := by
  constructor
  · intro h
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    rcases mem_toRest.mp hd with ⟨hne, rfl⟩ | ⟨hne, rfl⟩ | ⟨hne, rfl⟩ | ⟨hne, rfl⟩
    · exact Or.inl ⟨hne, rfl⟩
    · exact Or.inr (Or.inl ⟨hne, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hne, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hne, rfl⟩))
  · rintro (⟨hne, rfl⟩ | ⟨hne, rfl⟩ | ⟨hne, rfl⟩ | ⟨hne, rfl⟩)
    · exact List.mem_map.mpr ⟨.shift f.shift 0, mem_toRest.mpr (Or.inl ⟨hne, rfl⟩), rfl⟩
    · exact List.mem_map.mpr
        ⟨.grow f.size 1000, mem_toRest.mpr (Or.inr (Or.inl ⟨hne, rfl⟩)), rfl⟩
    · exact List.mem_map.mpr
        ⟨.reveal f.part 1000, mem_toRest.mpr (Or.inr (Or.inr (Or.inl ⟨hne, rfl⟩))), rfl⟩
    · exact List.mem_map.mpr
        ⟨.fade f.shown 1000, mem_toRest.mpr (Or.inr (Or.inr (Or.inr ⟨hne, rfl⟩))), rfl⟩

/-- **Every change of `hold` starts at what is seen.** -/
theorem hold_start (f : Frame) : ∀ c ∈ f.hold, f.Shows c.start := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  rw [Change.stay_start]
  exact toRest_start f d hd

/-- **Every change of `hold` ends where it starts.** -/
theorem hold_stop (f : Frame) : ∀ c ∈ f.hold, c.stop = c.start := by
  intro c hc
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
  rw [Change.stay_stop, Change.stay_start]

/-- **Every change of `hold` reads its start at every eased progress.** A thing under it is
drawn as it was seen for as long as the track runs. -/
theorem hold_at (f : Frame) : ∀ c ∈ f.hold, ∀ e : Int, c.at e = c.start := by
  intro c hc e
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
  rw [Change.stay_at, Change.stay_start]

/-- No change of `hold` is a change of shape. -/
theorem hold_not_shape (f : Frame) : ∀ c ∈ f.hold, c.property ≠ .shape := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  rw [Change.stay_property]
  exact toRest_not_shape f d hd

/-- The changes of `hold` are of the properties of the changes of `toRest`, in their order. -/
theorem hold_properties (f : Frame) :
    f.hold.map Change.property = f.toRest.map Change.property := by
  show (f.toRest.map Change.stay).map Change.property = f.toRest.map Change.property
  rw [List.map_map]
  exact List.map_congr_left fun c _ => Change.stay_property c

/-- The changes of `hold` are of distinct properties: one at most for each. -/
theorem hold_distinct (f : Frame) : (f.hold.map Change.property).Nodup := by
  rw [hold_properties]
  exact toRest_distinct f

/-- **A frame has nothing to hold exactly when it is at rest.** -/
theorem hold_eq_nil (f : Frame) : f.hold = [] ↔ f.AtRest :=
  ⟨fun h => (toRest_eq_nil f).mp (List.eq_nil_of_length_eq_zero
      ((List.length_map Change.stay).symm.trans (congrArg List.length h))),
    fun h => congrArg (List.map Change.stay) ((toRest_eq_nil f).mpr h)⟩

/-- **The change of `reshape`**: from the shape that is seen to the other shape, where both are
known. -/
theorem mem_reshape {f : Frame} {own : Option (List ICubic)} {c : Change} :
    c ∈ f.reshape own ↔ ∃ s o, f.shape = some s ∧ own = some o ∧ c = .morph s o := by
  unfold reshape
  cases f.shape with
  | none => exact ⟨fun h => absurd h List.not_mem_nil, fun ⟨_, _, h, _⟩ => nomatch h⟩
  | some s =>
    cases own with
    | none => exact ⟨fun h => absurd h List.not_mem_nil, fun ⟨_, _, _, h, _⟩ => nomatch h⟩
    | some o =>
      exact ⟨fun h => ⟨s, o, rfl, rfl, List.mem_singleton.mp h⟩,
        fun ⟨_, _, hs, ho, hc⟩ => by
          cases hs
          cases ho
          exact List.mem_singleton.mpr hc⟩

/-- **Whatever of a thing's place, size, line and opacity is not at rest has a change in
`toRest`.** -/
theorem toRest_covers {f : Frame} {q : Pose} (hq : f.Shows q) (hs : q.property ≠ .shape)
    (hr : ¬rest.Shows q) : ∃ d ∈ f.toRest, d.property = q.property := by
  cases q with
  | shift s =>
    have e : f.shift = s := shows_shift.mp hq
    subst e
    exact ⟨.shift f.shift 0,
      mem_toRest.mpr (Or.inl ⟨fun h => hr (shows_shift.mpr h.symm), rfl⟩), rfl⟩
  | grow s =>
    have e : f.size = s := shows_grow.mp hq
    subst e
    exact ⟨.grow f.size 1000,
      mem_toRest.mpr (Or.inr (Or.inl ⟨fun h => hr (shows_grow.mpr h.symm), rfl⟩)), rfl⟩
  | reveal s =>
    have e : f.part = s := shows_reveal.mp hq
    subst e
    exact ⟨.reveal f.part 1000,
      mem_toRest.mpr (Or.inr (Or.inr (Or.inl ⟨fun h => hr (shows_reveal.mpr h.symm), rfl⟩))),
      rfl⟩
  | fade s =>
    have e : f.shown = s := shows_fade.mp hq
    subst e
    exact ⟨.fade f.shown 1000,
      mem_toRest.mpr (Or.inr (Or.inr (Or.inr ⟨fun h => hr (shows_fade.mpr h.symm), rfl⟩))),
      rfl⟩
  | shape s => exact absurd rfl hs

/-- **Whatever of a thing's place, size, line and opacity is not at rest has a change in
`hold`.** -/
theorem hold_covers {f : Frame} {q : Pose} (hq : f.Shows q) (hs : q.property ≠ .shape)
    (hr : ¬rest.Shows q) : ∃ d ∈ f.hold, d.property = q.property := by
  obtain ⟨d, hd, e⟩ := toRest_covers hq hs hr
  exact ⟨d.stay, List.mem_map.mpr ⟨d, hd, rfl⟩, (Change.stay_property d).trans e⟩

end Frame

/-! ## The changes of a plan, from where a thing is seen -/

/-- **The changes of a plan for a thing that is seen at a frame.** Each change of the plan starts
where the thing is seen (`Change.from`). After them come the changes of `fill` whose property the
plan does not change, each by the transition `tm`. `Frame.resume` and `Frame.leaveFrom` are this
with two lists to fill with. -/
def Frame.carry (f : Frame) (fill : List Change) (tm : Transition)
    (cs : List (Change × Transition)) : List (Change × Transition) :=
  cs.map (fun c => (c.1.from f, c.2)) ++
    (fill.filter fun d => cs.all fun c => decide (c.1.property ≠ d.property)).map fun d =>
      (d, tm)

/-- **The answers of a plan for a kept thing that is seen at a frame.** Each change of the plan
starts where the thing is seen (`Change.from`). Each of its place, size, line and opacity that
the plan does not change and that is not at rest goes to rest by `settle`. Where the thing is
seen with a shape, the plan gives no change of shape and the thing's own shape `own` is known,
its shape goes to its own by `settle`. -/
def Frame.resume (f : Frame) (settle : Transition) (own : Option (List ICubic))
    (cs : List (Change × Transition)) : List (Change × Transition) :=
  f.carry (f.toRest ++ f.reshape own) settle cs

/-- **The answers of a plan for a thing that leaves from where it is seen.** Each change of the
plan starts where the thing is seen. Each other property that is not at rest is held as it is
seen, and so is the shape where the thing is seen with one. -/
def Frame.leaveFrom (f : Frame) (cs : List (Change × Transition)) :
    List (Change × Transition) :=
  f.carry (f.hold ++ f.reshape f.shape) {} cs

/-- **A plan resumed from where things are seen.** `seen o` is the frame of the old thing `o`
at the moment of the interruption, `settle n` brings to rest what the plan does not change, and
`shape n` is the new thing's own shape, where it has one that a track can change. -/
def Plan.resume (p : Plan α) (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic) := fun _ => none) : Plan α where
  kept := fun o n => (seen o).resume (settle n) (shape n) (p.kept o n)
  enter := p.enter
  leave := fun o => (seen o).leaveFrom (p.leave o)

/-- **A plan resumed from a step that is interrupted.** `m` is the step before and `t` the
moment of the interruption: each old thing is seen at its frame in `m` at `t`. It is
`Plan.resume` with that `seen`, so a caller does not write it. -/
def Plan.resumeFrom [BEq κ] (key : α → κ) (m : Motion κ) (t : Nat) (p : Plan α)
    (settle : α → Transition) (shape : α → Option (List ICubic) := fun _ => none) : Plan α :=
  p.resume (fun a => m.frame (key a) t) settle shape

namespace Frame

/-- **The changes of `carry`, one by one**: a change of the plan started where the thing is
seen, or a change of `fill` whose property the plan does not change. -/
theorem mem_carry {f : Frame} {fill : List Change} {tm : Transition}
    {cs : List (Change × Transition)} {x : Change × Transition} :
    x ∈ f.carry fill tm cs ↔ (∃ c ∈ cs, x = (c.1.from f, c.2)) ∨
      ∃ d ∈ fill, (∀ c ∈ cs, c.1.property ≠ d.property) ∧ x = (d, tm) := by
  unfold carry
  rw [List.mem_append, List.mem_map, List.mem_map]
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨d, hd, rfl⟩)
    · exact Or.inl ⟨c, hc, rfl⟩
    · have hf := List.mem_filter.mp hd
      exact Or.inr ⟨d, hf.1, fun c hc => of_decide_eq_true (List.all_eq_true.mp hf.2 c hc), rfl⟩
  · rintro (⟨c, hc, rfl⟩ | ⟨d, hd, hno, rfl⟩)
    · exact Or.inl ⟨c, hc, rfl⟩
    · exact Or.inr ⟨d, List.mem_filter.mpr
        ⟨hd, List.all_eq_true.mpr fun c hc => decide_eq_true (hno c hc)⟩, rfl⟩

/-- **What the frame of a reading of `carry` shows.** `r` reads a pose of each change: its start,
or its pose at a moment. The frame of those poses shows `q` where each change of the plan of
`q`'s property reads `q`, each change of `fill` of that property reads `q`, and one of them is
there unless the still picture shows `q`. The laws of `resume` and `leaveFrom` are cases of this
one. -/
theorem carry_shows {f : Frame} {fill : List Change} {tm : Transition}
    {cs : List (Change × Transition)} (r : Change × Transition → Pose)
    (hr : ∀ x, (r x).property = x.1.property) {q : Pose}
    (hcs : ∀ c ∈ cs, c.1.property = q.property → r (c.1.from f, c.2) = q)
    (hfill : ∀ d ∈ fill, (∀ c ∈ cs, c.1.property ≠ d.property) → d.property = q.property →
      r (d, tm) = q)
    (hcov : rest.Shows q ∨ (∃ c ∈ cs, c.1.property = q.property) ∨
      ∃ d ∈ fill, d.property = q.property) :
    (ofPoses ((f.carry fill tm cs).map r)).Shows q := by
  refine shows_ofPoses (fun p hp he => ?_) (fun hno => ?_)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    rcases mem_carry.mp hx with ⟨c, hc, rfl⟩ | ⟨d, hd, hnc, rfl⟩
    · exact hcs c hc
        ((Change.from_property c.1 f).symm.trans ((hr (c.1.from f, c.2)).symm.trans he))
    · exact hfill d hd hnc ((hr (d, tm)).symm.trans he)
  · cases hfind : cs.find? (fun c => decide (c.1.property = q.property)) with
    | some c =>
      have hc : c ∈ cs := List.mem_of_find?_eq_some hfind
      have he : c.1.property = q.property :=
        of_decide_eq_true (List.find?_some
          (p := fun c : Change × Transition => decide (c.1.property = q.property)) hfind)
      exact absurd ((hr (c.1.from f, c.2)).trans ((Change.from_property c.1 f).trans he))
        (hno _ (List.mem_map.mpr
          ⟨(c.1.from f, c.2), mem_carry.mpr (Or.inl ⟨c, hc, rfl⟩), rfl⟩))
    | none =>
      have hnc : ∀ c ∈ cs, c.1.property ≠ q.property := fun c hc e =>
        List.find?_eq_none.mp hfind c hc (decide_eq_true e)
      rcases hcov with h | ⟨c, hc, e⟩ | ⟨d, hd, e⟩
      · exact h
      · exact absurd e (hnc c hc)
      · exact absurd ((hr (d, tm)).trans e)
          (hno _ (List.mem_map.mpr ⟨(d, tm), mem_carry.mpr
            (Or.inr ⟨d, hd, fun c hc h => hnc c hc (h.trans e), rfl⟩), rfl⟩))

/-- The starts of a list of changes are of the properties of the changes. -/
private theorem starts_distinct {cs : List (Change × Transition)}
    (hd : (cs.map fun c => c.1.property).Nodup) :
    ((cs.map fun c => c.1.start).map Pose.property).Nodup := by
  have e : (cs.map fun c => c.1.start).map Pose.property = cs.map fun c => c.1.property := by
    rw [List.map_map]
    exact List.map_congr_left fun c _ => Change.start_property c.1
  rw [e]
  exact hd

/-- **The frame of the starts of `carry` shows what was seen**, of every property but the place:
a size, a line, an opacity or a shape that the frame shows. Each change of `fill` starts at what
is seen, and where the still picture does not show the pose, the plan or `fill` has a change of
its property. -/
theorem carry_start_shows {f : Frame} {fill : List Change} {tm : Transition}
    {cs : List (Change × Transition)} {q : Pose} (hq : f.Shows q) (hp : q.property ≠ .place)
    (hfill : ∀ d ∈ fill, f.Shows d.start)
    (hcov : rest.Shows q ∨ (∃ c ∈ cs, c.1.property = q.property) ∨
      ∃ d ∈ fill, d.property = q.property) :
    (ofPoses ((f.carry fill tm cs).map fun x => x.1.start)).Shows q := by
  refine carry_shows (fun x => x.1.start) (fun x => Change.start_property x.1)
    (fun c _ e => ?_) (fun d hd _ e => ?_) hcov
  · exact Pose.eq_of_shows
      (Change.from_start_onto (fun h => absurd (e.symm.trans h) hp)
        (fun h => shape_ne_none_of_shows hq (e.symm.trans h)))
      hq ((Change.start_property _).trans ((Change.from_property c.1 f).trans e))
  · exact Pose.eq_of_shows (hfill d hd) hq ((Change.start_property d).trans e)

/-- **Where the starts of `carry` put a thing**: where the starts of the plan put it, moved by
the shift at which it is seen. The changes of the plan are of distinct properties, each change
of `fill` starts at what is seen, and `fill` has a shift where the thing is seen off its
place. -/
theorem carry_start_shift {f : Frame} {fill : List Change} {tm : Transition}
    {cs : List (Change × Transition)} (hd : (cs.map fun c => c.1.property).Nodup)
    (hfill : ∀ d ∈ fill, f.Shows d.start)
    (hcov : f.shift ≠ 0 → ∃ d ∈ fill, d.property = .place) :
    (ofPoses ((f.carry fill tm cs).map fun x => x.1.start)).shift =
      (ofPoses (cs.map fun c => c.1.start)).shift + f.shift := by
  have hg0 : (∀ c ∈ cs, c.1.property ≠ .place) →
      (ofPoses (cs.map fun c => c.1.start)).shift = 0 := fun h =>
    shift_under_of_no (fun p hp e => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
      exact h c hc ((Change.start_property c.1).symm.trans e)) rest
  refine shows_shift.mp (carry_shows (fun x => x.1.start) (fun x => Change.start_property x.1)
    (fun c hc e => ?_) (fun d hdm hno e => ?_) ?_)
  · obtain ⟨c1, c2⟩ := c
    cases c1 with
    | shift a b =>
      have hg : (ofPoses (cs.map fun c => c.1.start)).shift = a :=
        shift_under (starts_distinct hd) (List.mem_map.mpr ⟨(.shift a b, c2), hc, rfl⟩) rest
      exact congrArg (fun s => Pose.shift (s + f.shift)) hg.symm
    | _ => cases e
  · have e' : d.property = .place := e
    have h0 := hg0 fun c hc h => hno c hc (h.trans e'.symm)
    have hs : d.start = Pose.shift f.shift :=
      Pose.eq_of_shows (hfill d hdm) (shows_shift.mpr rfl) ((Change.start_property d).trans e')
    exact hs.trans (congrArg Pose.shift
      ((congrArg (fun s => s + f.shift) h0).trans (IVec.zero_add f.shift)).symm)
  · cases hfind : cs.find? (fun c => decide (c.1.property = .place)) with
    | some c =>
      exact Or.inr (Or.inl ⟨c, List.mem_of_find?_eq_some hfind, of_decide_eq_true
        (List.find?_some
          (p := fun c : Change × Transition => decide (c.1.property = .place)) hfind)⟩)
    | none =>
      have hnc : ∀ c ∈ cs, c.1.property ≠ .place := fun c hc e =>
        List.find?_eq_none.mp hfind c hc (decide_eq_true e)
      cases Decidable.em (f.shift = 0) with
      | inl h =>
        exact Or.inl (shows_shift.mpr
          ((congrArg (fun s => s + f.shift) (hg0 hnc)).trans
            ((congrArg (fun s => (0 : IVec) + s) h).trans (IVec.add_zero 0))).symm)
      | inr h => exact Or.inr (Or.inr (hcov h))

/-- Where neither the plan nor `fill` has a change of shape, the starts of `carry` leave the
thing its own shape. -/
theorem carry_start_no_shape {f : Frame} {fill : List Change} {tm : Transition}
    {cs : List (Change × Transition)} (hc : ∀ c ∈ cs, c.1.property ≠ .shape)
    (hfill : ∀ d ∈ fill, d.property ≠ .shape) :
    (ofPoses ((f.carry fill tm cs).map fun x => x.1.start)).shape = none :=
  shape_under_of_no (fun p hp e => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    rcases mem_carry.mp hx with ⟨c, hcm, rfl⟩ | ⟨d, hdm, _, rfl⟩
    · exact hc c hcm
        ((Change.from_property c.1 f).symm.trans ((Change.start_property _).symm.trans e))
    · exact hfill d hdm ((Change.start_property d).symm.trans e)) rest

/-- **A thing seen with its own shape starts with the shape that the plan's starts give it.**
The changes of the plan are of distinct properties, and `fill` has no change of shape. -/
theorem carry_start_shape {f : Frame} {fill : List Change} {tm : Transition}
    {cs : List (Change × Transition)} (hd : (cs.map fun c => c.1.property).Nodup)
    (hf : f.shape = none) (hfill : ∀ d ∈ fill, d.property ≠ .shape) :
    (ofPoses ((f.carry fill tm cs).map fun x => x.1.start)).shape =
      (ofPoses (cs.map fun c => c.1.start)).shape := by
  cases hfind : cs.find? (fun c => decide (c.1.property = .shape)) with
  | none =>
    have hnc : ∀ c ∈ cs, c.1.property ≠ .shape := fun c hc e =>
      List.find?_eq_none.mp hfind c hc (decide_eq_true e)
    have hg : (ofPoses (cs.map fun c => c.1.start)).shape = none :=
      shape_under_of_no (fun p hp e => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
        exact hnc c hc ((Change.start_property c.1).symm.trans e)) rest
    exact (carry_start_no_shape hnc hfill).trans hg.symm
  | some c0 =>
    have hc0 : c0 ∈ cs := List.mem_of_find?_eq_some hfind
    have he0 : c0.1.property = .shape :=
      of_decide_eq_true (List.find?_some
        (p := fun c : Change × Transition => decide (c.1.property = .shape)) hfind)
    have hg : ∀ (a b : List ICubic) (t : Transition), (Change.morph a b, t) ∈ cs →
        (ofPoses (cs.map fun c => c.1.start)).shape = some a := fun a b t h =>
      shape_under (starts_distinct hd) (List.mem_map.mpr ⟨(.morph a b, t), h, rfl⟩) rest
    obtain ⟨c1, c2⟩ := c0
    cases c1 with
    | morph a b =>
      rw [hg a b c2 hc0]
      refine shows_shape.mp (carry_shows (fun x => x.1.start)
        (fun x => Change.start_property x.1) (fun c hc e => ?_) (fun d hdm _ e => ?_)
        (Or.inr (Or.inl ⟨_, hc0, rfl⟩)))
      · obtain ⟨d1, d2⟩ := c
        cases d1 with
        | morph a' b' =>
          have ea : a' = a := Option.some.inj ((hg a' b' d2 hc).symm.trans (hg a b c2 hc0))
          exact (congrArg (fun o : Option (List ICubic) => Pose.shape (o.getD a')) hf).trans
            (congrArg Pose.shape ea)
        | _ => cases e
      · exact absurd e (hfill d hdm)
    | _ => cases he0

/-- What holds of the transition of every change of the plan, and of the transition to fill
with, holds of the transition of every change of `carry`. -/
theorem carry_timing {f : Frame} {fill : List Change} {tm : Transition}
    {cs : List (Change × Transition)} (P : Transition → Prop) (h : ∀ c ∈ cs, P c.2)
    (ht : P tm) : ∀ c ∈ f.carry fill tm cs, P c.2 := by
  intro x hx
  rcases mem_carry.mp hx with ⟨c, hc, rfl⟩ | ⟨d, _, _, rfl⟩
  · exact h c hc
  · exact ht

/-! ### A kept thing -/

/-- **The changes of `resume`, one by one**: a change of the plan started where the thing is
seen; a change of `toRest` whose property the plan does not change, by `settle`; or the change
of the shape that is seen to the thing's own, by `settle`, where both are known and the plan has
no change of shape. -/
theorem mem_resume {f : Frame} {settle : Transition} {own : Option (List ICubic)}
    {cs : List (Change × Transition)} {x : Change × Transition} :
    x ∈ f.resume settle own cs ↔ (∃ c ∈ cs, x = (c.1.from f, c.2)) ∨
      (∃ d ∈ f.toRest, (∀ c ∈ cs, c.1.property ≠ d.property) ∧ x = (d, settle)) ∨
      ∃ s o, f.shape = some s ∧ own = some o ∧ (∀ c ∈ cs, c.1.property ≠ .shape) ∧
        x = (.morph s o, settle) := by
  constructor
  · intro h
    rcases mem_carry.mp h with hc | ⟨d, hd, hno, rfl⟩
    · exact Or.inl hc
    · rcases List.mem_append.mp hd with hr | hr
      · exact Or.inr (Or.inl ⟨d, hr, hno, rfl⟩)
      · obtain ⟨s, o, hs, ho, rfl⟩ := mem_reshape.mp hr
        exact Or.inr (Or.inr ⟨s, o, hs, ho, hno, rfl⟩)
  · rintro (hc | ⟨d, hd, hno, rfl⟩ | ⟨s, o, hs, ho, hno, rfl⟩)
    · exact mem_carry.mpr (Or.inl hc)
    · exact mem_carry.mpr (Or.inr ⟨d, List.mem_append_left _ hd, hno, rfl⟩)
    · exact mem_carry.mpr (Or.inr ⟨.morph s o,
        List.mem_append_right _ (mem_reshape.mpr ⟨s, o, hs, ho, rfl⟩), hno, rfl⟩)

/-- Each change that `resume` fills with starts at what is seen. -/
private theorem resume_fill_start (f : Frame) (own : Option (List ICubic)) :
    ∀ d ∈ f.toRest ++ f.reshape own, f.Shows d.start := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · exact toRest_start f d h
  · obtain ⟨s, o, hs, _, rfl⟩ := mem_reshape.mp h
    exact shows_shape.mpr hs

/-- **A resumed answer ends at rest where the plan's answer does.** -/
theorem resume_stop {f : Frame} {settle : Transition} {own : Option (List ICubic)}
    {cs : List (Change × Transition)} (h : ∀ c ∈ cs, c.1.stop.AtRest) :
    ∀ c ∈ f.resume settle own cs, c.1.stop.AtRest := by
  intro x hx
  rcases mem_resume.mp hx with ⟨c, hc, rfl⟩ | ⟨d, hd, _, rfl⟩ | ⟨s, o, _, _, _, rfl⟩
  · show (c.1.from f).stop.AtRest
    rw [Change.from_stop]
    exact h c hc
  · exact toRest_stop f d hd
  · exact True.intro

/-- **Nothing jumps.** Whatever a thing is seen with is what the starts of its resumed answer
show: its size, its line and its opacity in every case; its place where the plan does not move
it; and its shape where the plan changes the shape or the thing's own shape is known. So at the
first moment of the resumed step the thing is drawn as it was at the moment of the
interruption. `resume_shift` is the law of a thing that the plan moves. -/
theorem resume_shows {f : Frame} {q : Pose} (settle : Transition)
    {own : Option (List ICubic)} {cs : List (Change × Transition)} (hq : f.Shows q)
    (hp : q.property = .place → ∀ c ∈ cs, c.1.property ≠ .place)
    (hs : q.property = .shape → (∃ c ∈ cs, c.1.property = .shape) ∨ own ≠ none) :
    (ofPoses ((f.resume settle own cs).map fun c => c.1.start)).Shows q := by
  refine carry_shows (fun x => x.1.start) (fun x => Change.start_property x.1)
    (fun c hc e => ?_) (fun d hd _ e => ?_) ?_
  · exact Pose.eq_of_shows
      (Change.from_start_onto (fun h => absurd h (hp (e.symm.trans h) c hc))
        (fun h => shape_ne_none_of_shows hq (e.symm.trans h)))
      hq ((Change.start_property _).trans ((Change.from_property c.1 f).trans e))
  · exact Pose.eq_of_shows (resume_fill_start f own d hd) hq ((Change.start_property d).trans e)
  · cases Decidable.em (rest.Shows q) with
    | inl h => exact Or.inl h
    | inr h =>
      cases q with
      | shape s =>
        rcases hs rfl with hc | ho
        · exact Or.inr (Or.inl hc)
        · cases own with
          | none => exact absurd rfl ho
          | some o =>
            exact Or.inr (Or.inr ⟨.morph s o, List.mem_append_right _
              (mem_reshape.mpr ⟨s, o, shows_shape.mp hq, rfl, rfl⟩), rfl⟩)
      | shift s =>
        obtain ⟨d, hd, e⟩ := toRest_covers hq (fun e => nomatch e) h
        exact Or.inr (Or.inr ⟨d, List.mem_append_left _ hd, e⟩)
      | grow s =>
        obtain ⟨d, hd, e⟩ := toRest_covers hq (fun e => nomatch e) h
        exact Or.inr (Or.inr ⟨d, List.mem_append_left _ hd, e⟩)
      | reveal s =>
        obtain ⟨d, hd, e⟩ := toRest_covers hq (fun e => nomatch e) h
        exact Or.inr (Or.inr ⟨d, List.mem_append_left _ hd, e⟩)
      | fade s =>
        obtain ⟨d, hd, e⟩ := toRest_covers hq (fun e => nomatch e) h
        exact Or.inr (Or.inr ⟨d, List.mem_append_left _ hd, e⟩)

/-- **A resumed thing starts at the size it is seen at**, whatever the plan does. -/
theorem resume_size (f : Frame) (settle : Transition) (own : Option (List ICubic))
    (cs : List (Change × Transition)) :
    (ofPoses ((f.resume settle own cs).map fun c => c.1.start)).size = f.size :=
  shows_grow.mp (resume_shows settle (shows_grow.mpr rfl) (fun e => nomatch e)
    (fun e => nomatch e))

/-- **A resumed thing starts with as much of its line as is seen**, whatever the plan does. -/
theorem resume_part (f : Frame) (settle : Transition) (own : Option (List ICubic))
    (cs : List (Change × Transition)) :
    (ofPoses ((f.resume settle own cs).map fun c => c.1.start)).part = f.part :=
  shows_reveal.mp (resume_shows settle (shows_reveal.mpr rfl) (fun e => nomatch e)
    (fun e => nomatch e))

/-- **A resumed thing starts at the opacity it is seen with**, whatever the plan does. -/
theorem resume_shown (f : Frame) (settle : Transition) (own : Option (List ICubic))
    (cs : List (Change × Transition)) :
    (ofPoses ((f.resume settle own cs).map fun c => c.1.start)).shown = f.shown :=
  shows_fade.mp (resume_shows settle (shows_fade.mpr rfl) (fun e => nomatch e)
    (fun e => nomatch e))

/-- **A resumed thing starts with the shape it is seen with**, where the plan changes its shape
or its own shape is known. -/
theorem resume_shape {f : Frame} {s : List ICubic} (settle : Transition)
    {own : Option (List ICubic)} {cs : List (Change × Transition)} (h : f.shape = some s)
    (hs : (∃ c ∈ cs, c.1.property = .shape) ∨ own ≠ none) :
    (ofPoses ((f.resume settle own cs).map fun c => c.1.start)).shape = some s :=
  shows_shape.mp (resume_shows settle (shows_shape.mpr h) (fun e => nomatch e) (fun _ => hs))

/-- **Where a resumed thing starts**: where the plan's starts put it, moved by the shift at
which it is seen. The plan tells a shift from the thing's place in the next picture, as if the
thing stood at its place in the last one. The thing is seen off that place, and starts that
much further. The plan's changes are of distinct properties. -/
theorem resume_shift {f : Frame} (settle : Transition) (own : Option (List ICubic))
    {cs : List (Change × Transition)} (hd : (cs.map fun c => c.1.property).Nodup) :
    (ofPoses ((f.resume settle own cs).map fun c => c.1.start)).shift =
      (ofPoses (cs.map fun c => c.1.start)).shift + f.shift :=
  carry_start_shift hd (resume_fill_start f own) fun h =>
    ⟨.shift f.shift 0, List.mem_append_left _ (mem_toRest.mpr (Or.inl ⟨h, rfl⟩)), rfl⟩

/-- A thing seen with its own shape starts with the shape that the plan's starts give it. -/
theorem resume_shape_of_none {f : Frame} (settle : Transition) (own : Option (List ICubic))
    {cs : List (Change × Transition)} (hd : (cs.map fun c => c.1.property).Nodup)
    (hf : f.shape = none) :
    (ofPoses ((f.resume settle own cs).map fun c => c.1.start)).shape =
      (ofPoses (cs.map fun c => c.1.start)).shape :=
  carry_start_shape hd hf fun d hd' e => by
    rcases List.mem_append.mp hd' with h | h
    · exact toRest_not_shape f d h e
    · obtain ⟨s, _, hs, _, _⟩ := mem_reshape.mp h
      exact nomatch hs.symm.trans hf

/-- **The one jump that is left.** Where the plan has no change of shape and the thing's own
shape is not known, a resumed thing starts with its own shape, whatever shape it is seen
with. A caller that changes shapes gives `shape`. -/
theorem resume_shape_own {f : Frame} (settle : Transition)
    {cs : List (Change × Transition)} (hc : ∀ c ∈ cs, c.1.property ≠ .shape) :
    (ofPoses ((f.resume settle none cs).map fun c => c.1.start)).shape = none :=
  carry_start_no_shape hc fun d hd e => by
    rcases List.mem_append.mp hd with h | h
    · exact toRest_not_shape f d h e
    · obtain ⟨_, _, _, ho, _⟩ := mem_reshape.mp h
      exact nomatch ho

/-! ### A thing that leaves -/

/-- Each change that `leaveFrom` fills with starts at what is seen. -/
private theorem leave_fill_start (f : Frame) :
    ∀ d ∈ f.hold ++ f.reshape f.shape, f.Shows d.start := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · exact hold_start f d h
  · obtain ⟨s, o, hs, _, rfl⟩ := mem_reshape.mp h
    exact shows_shape.mpr hs

/-- Each change that `leaveFrom` fills with reads its start at every eased progress. -/
private theorem leave_fill_at (f : Frame) :
    ∀ d ∈ f.hold ++ f.reshape f.shape, ∀ e : Int, d.at e = d.start := by
  intro d hd e
  rcases List.mem_append.mp hd with h | h
  · exact hold_at f d h e
  · obtain ⟨s, o, hs, ho, rfl⟩ := mem_reshape.mp h
    have eo : o = s := Option.some.inj (ho.symm.trans hs)
    subst eo
    exact Change.stay_at (.morph o o) e

/-- Whatever a frame shows that the still picture does not has a change to hold it. -/
private theorem leave_fill_covers {f : Frame} {q : Pose} (hq : f.Shows q)
    (hr : ¬rest.Shows q) : ∃ d ∈ f.hold ++ f.reshape f.shape, d.property = q.property := by
  cases q with
  | shape s =>
    exact ⟨.morph s s, List.mem_append_right _
      (mem_reshape.mpr ⟨s, s, shows_shape.mp hq, shows_shape.mp hq, rfl⟩), rfl⟩
  | shift s =>
    obtain ⟨d, hd, e⟩ := hold_covers hq (fun e => nomatch e) hr
    exact ⟨d, List.mem_append_left _ hd, e⟩
  | grow s =>
    obtain ⟨d, hd, e⟩ := hold_covers hq (fun e => nomatch e) hr
    exact ⟨d, List.mem_append_left _ hd, e⟩
  | reveal s =>
    obtain ⟨d, hd, e⟩ := hold_covers hq (fun e => nomatch e) hr
    exact ⟨d, List.mem_append_left _ hd, e⟩
  | fade s =>
    obtain ⟨d, hd, e⟩ := hold_covers hq (fun e => nomatch e) hr
    exact ⟨d, List.mem_append_left _ hd, e⟩

/-- **The changes of `leaveFrom`, one by one**: a change of the plan started where the thing is
seen; a change of `hold` whose property the plan does not change; or the change that holds the
shape that is seen, where the plan has no change of shape. -/
theorem mem_leaveFrom {f : Frame} {cs : List (Change × Transition)}
    {x : Change × Transition} :
    x ∈ f.leaveFrom cs ↔ (∃ c ∈ cs, x = (c.1.from f, c.2)) ∨
      (∃ d ∈ f.hold, (∀ c ∈ cs, c.1.property ≠ d.property) ∧ x = (d, {})) ∨
      ∃ s, f.shape = some s ∧ (∀ c ∈ cs, c.1.property ≠ .shape) ∧ x = (.morph s s, {}) := by
  constructor
  · intro h
    rcases mem_carry.mp h with hc | ⟨d, hd, hno, rfl⟩
    · exact Or.inl hc
    · rcases List.mem_append.mp hd with hr | hr
      · exact Or.inr (Or.inl ⟨d, hr, hno, rfl⟩)
      · obtain ⟨s, o, hs, ho, rfl⟩ := mem_reshape.mp hr
        have eo : o = s := Option.some.inj (ho.symm.trans hs)
        subst eo
        exact Or.inr (Or.inr ⟨o, hs, hno, rfl⟩)
  · rintro (hc | ⟨d, hd, hno, rfl⟩ | ⟨s, hs, hno, rfl⟩)
    · exact mem_carry.mpr (Or.inl hc)
    · exact mem_carry.mpr (Or.inr ⟨d, List.mem_append_left _ hd, hno, rfl⟩)
    · exact mem_carry.mpr (Or.inr ⟨.morph s s,
        List.mem_append_right _ (mem_reshape.mpr ⟨s, s, hs, hs, rfl⟩), hno, rfl⟩)

/-- **A thing that leaves does not jump.** Whatever it is seen with is what the starts of
`leaveFrom` show: its size, its line, its opacity and its shape in every case, and its place
where the plan does not move it. `leaveFrom_shift` is the law of a thing that the plan
moves. -/
theorem leaveFrom_shows {f : Frame} {q : Pose} {cs : List (Change × Transition)}
    (hq : f.Shows q) (hp : q.property = .place → ∀ c ∈ cs, c.1.property ≠ .place) :
    (ofPoses ((f.leaveFrom cs).map fun c => c.1.start)).Shows q := by
  refine carry_shows (fun x => x.1.start) (fun x => Change.start_property x.1)
    (fun c hc e => ?_) (fun d hd _ e => ?_) ?_
  · exact Pose.eq_of_shows
      (Change.from_start_onto (fun h => absurd h (hp (e.symm.trans h) c hc))
        (fun h => shape_ne_none_of_shows hq (e.symm.trans h)))
      hq ((Change.start_property _).trans ((Change.from_property c.1 f).trans e))
  · exact Pose.eq_of_shows (leave_fill_start f d hd) hq ((Change.start_property d).trans e)
  · cases Decidable.em (rest.Shows q) with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (Or.inr (leave_fill_covers hq h))

/-- **What the plan does not change of a thing that leaves is held at every moment.** Whatever
the thing is seen with, of a property that the plan has no change of, is what its poses show at
every moment, whatever the transitions read: it is drawn so until it is dropped. -/
theorem leaveFrom_held {f : Frame} {q : Pose} {cs : List (Change × Transition)}
    (hq : f.Shows q) (hc : ∀ c ∈ cs, c.1.property ≠ q.property) (t : Nat) :
    (ofPoses ((f.leaveFrom cs).map fun c => c.1.at (c.2.at t))).Shows q := by
  refine carry_shows (fun x => x.1.at (x.2.at t)) (fun x => Change.at_property x.1 _)
    (fun c hcm e => absurd e (hc c hcm)) (fun d hd _ e => ?_) ?_
  · exact Pose.eq_of_shows ((leave_fill_at f d hd _).symm ▸ leave_fill_start f d hd) hq
      ((Change.at_property d _).trans e)
  · cases Decidable.em (rest.Shows q) with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (Or.inr (leave_fill_covers hq h))

/-- **Where a thing that leaves starts**: where the plan's starts put it, moved by the shift at
which it is seen. The plan's changes are of distinct properties. -/
theorem leaveFrom_shift {f : Frame} {cs : List (Change × Transition)}
    (hd : (cs.map fun c => c.1.property).Nodup) :
    (ofPoses ((f.leaveFrom cs).map fun c => c.1.start)).shift =
      (ofPoses (cs.map fun c => c.1.start)).shift + f.shift :=
  carry_start_shift hd (leave_fill_start f) fun h =>
    ⟨.shift f.shift f.shift, List.mem_append_left _ (mem_hold.mpr (Or.inl ⟨h, rfl⟩)), rfl⟩

/-- A thing that leaves with its own shape starts with the shape that the plan's starts give
it. -/
theorem leaveFrom_shape_of_none {f : Frame} {cs : List (Change × Transition)}
    (hd : (cs.map fun c => c.1.property).Nodup) (hf : f.shape = none) :
    (ofPoses ((f.leaveFrom cs).map fun c => c.1.start)).shape =
      (ofPoses (cs.map fun c => c.1.start)).shape :=
  carry_start_shape hd hf fun d hd' e => by
    rcases List.mem_append.mp hd' with h | h
    · exact hold_not_shape f d h e
    · obtain ⟨s, _, hs, _, _⟩ := mem_reshape.mp h
      exact nomatch hs.symm.trans hf

/-! ### A thing seen at rest -/

end Frame

/-- A change that starts at rest, or is a shift, is itself when it is started from the still
picture. -/
theorem Change.from_rest_of {c : Change} (h : c.property ≠ .place → c.start.AtRest) :
    c.from Frame.rest = c := by
  cases c with
  | shift a b => exact Change.from_rest_shift a b
  | grow a b => exact Change.from_rest (h fun e => nomatch e)
  | reveal a b => exact Change.from_rest (h fun e => nomatch e)
  | fade a b => exact Change.from_rest (h fun e => nomatch e)
  | morph a b => rfl

namespace Frame

/-- The changes of a plan started from the still picture are the changes of the plan, where
each that is not a shift starts at rest. -/
private theorem map_from_rest {cs : List (Change × Transition)}
    (hc : ∀ c ∈ cs, c.1.property ≠ .place → c.1.start.AtRest) :
    cs.map (fun c => (c.1.from rest, c.2)) = cs :=
  (List.map_congr_left fun c hcm =>
    congrArg (fun x : Change => (x, c.2)) (Change.from_rest_of (hc c hcm))).trans (List.map_id cs)

/-- **A thing seen at rest resumes as the plan says.** With the thing as the still picture has
it, its own shape too, the resumed answer is the plan's answer, where each change of the plan of
a size, a line or an opacity starts at rest. So a step that is not interrupted is the plan's
step. -/
theorem resume_of_rest {f : Frame} (hf : f.AtRest) (hs : f.shape = none) (settle : Transition)
    (own : Option (List ICubic)) {cs : List (Change × Transition)}
    (hc : ∀ c ∈ cs, c.1.property ≠ .place → c.1.start.AtRest) : f.resume settle own cs = cs := by
  have e : f = rest := ext hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hs
  subst e
  show cs.map (fun c => (c.1.from rest, c.2)) ++ [] = cs
  rw [List.append_nil]
  exact map_from_rest hc

/-- **A thing that leaves from rest leaves as the plan says.** -/
theorem leaveFrom_of_rest {f : Frame} (hf : f.AtRest) (hs : f.shape = none)
    {cs : List (Change × Transition)}
    (hc : ∀ c ∈ cs, c.1.property ≠ .place → c.1.start.AtRest) : f.leaveFrom cs = cs := by
  have e : f = rest := ext hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hs
  subst e
  show cs.map (fun c => (c.1.from rest, c.2)) ++ [] = cs
  rw [List.append_nil]
  exact map_from_rest hc

end Frame

/-! ## A resumed plan -/

namespace Plan

/-- **A resumed plan settles where the plan does.** Every change that it gives a kept thing or a
new thing ends at rest. -/
theorem resume_settles {p : Plan α} (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hp : p.Settles) : (p.resume seen settle shape).Settles :=
  ⟨fun o n => Frame.resume_stop (hp.1 o n), hp.2⟩

/-- **A resumed plan is proper where the plan is** and every `settle` has a proper easing. -/
theorem resume_proper {p : Plan α} (seen : α → Frame) {settle : α → Transition}
    (shape : α → Option (List ICubic)) (hp : p.Proper) (hs : ∀ n, (settle n).ease.Proper) :
    (p.resume seen settle shape).Proper :=
  ⟨fun o n => Frame.carry_timing (fun tm => tm.ease.Proper) (hp.1 o n) (hs n), hp.2.1,
    fun o => Frame.carry_timing (fun tm => tm.ease.Proper) (hp.2.2 o) Easing.proper_linear⟩

/-- **A step that is not interrupted is the plan's step.** Where every thing is seen as the
still picture has it, the resumed plan is the plan, where each change of the plan of a size, a
line or an opacity starts at rest. -/
theorem resume_of_rest (p : Plan α) {seen : α → Frame} (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hseen : ∀ o, (seen o).AtRest ∧ (seen o).shape = none)
    (hk : ∀ o n, ∀ c ∈ p.kept o n, c.1.property ≠ .place → c.1.start.AtRest)
    (hl : ∀ o, ∀ c ∈ p.leave o, c.1.property ≠ .place → c.1.start.AtRest) :
    p.resume seen settle shape = p := by
  have e1 : (fun o n => (seen o).resume (settle n) (shape n) (p.kept o n)) = p.kept :=
    funext fun o => funext fun n =>
      Frame.resume_of_rest (hseen o).1 (hseen o).2 (settle n) (shape n) (hk o n)
  have e2 : (fun o => (seen o).leaveFrom (p.leave o)) = p.leave :=
    funext fun o => Frame.leaveFrom_of_rest (hseen o).1 (hseen o).2 (hl o)
  show (⟨fun o n => (seen o).resume (settle n) (shape n) (p.kept o n), p.enter,
    fun o => (seen o).leaveFrom (p.leave o)⟩ : Plan α) = p
  rw [e1, e2]

end Plan

/-! ## The first moment of a step -/

namespace Motion

/-- A change by a transition that reads `0` stands at its start. -/
private theorem at_start_of (c : Change × Transition) (h : c.2.at 0 = 0) :
    c.1.at (c.2.at 0) = c.1.start :=
  (congrArg c.1.at h).trans (Change.at_start c.1)

/-- The transition with no delay, the whole step and the progress itself reads `0` at the
moment `0`. -/
private theorem default_at_zero : ({} : Transition).at 0 = 0 := by decide

/-! ### A kept thing -/

/-- **The poses of a kept thing at the first moment of a resumed step** are the starts of its
resumed answer, in order. The keys of the next list are distinct, and each transition of the
answer reads `0` at the moment `0` (`Transition.at_zero`). -/
theorem resume_kept_poses [BEq κ] [LawfulBEq κ] (key : α → κ) (olds next : List α)
    (p : Plan α) (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key next) {o n : α}
    (hu : (o, n) ∈ (join key olds next).update) (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0)
    (hs : (settle n).at 0 = 0) :
    (ofJoin key (join key olds next) (p.resume seen settle shape)).posesOf (key n) 0 =
      ((seen o).resume (settle n) (shape n) (p.kept o n)).map fun c => c.1.start :=
  (posesOf_kept key olds next (p.resume seen settle shape) hd hu 0).trans
    (List.map_congr_left fun c hc =>
      at_start_of c (Frame.carry_timing (fun tm => tm.at 0 = 0) hk hs c hc))

/-- **The frame of a kept thing at the first moment of a resumed step** is the frame of the
starts of its resumed answer. -/
theorem resume_kept_frame [BEq κ] [LawfulBEq κ] (key : α → κ) (olds next : List α)
    (p : Plan α) (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key next) {o n : α}
    (hu : (o, n) ∈ (join key olds next).update) (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0)
    (hs : (settle n).at 0 = 0) :
    (ofJoin key (join key olds next) (p.resume seen settle shape)).frame (key n) 0 =
      Frame.ofPoses (((seen o).resume (settle n) (shape n) (p.kept o n)).map fun c =>
        c.1.start) :=
  congrArg Frame.ofPoses (resume_kept_poses key olds next p seen settle shape hd hu hk hs)

/-- **Nothing jumps, in a step.** At the first moment of a resumed step a kept thing shows
whatever its old thing was seen with: its size, its line and its opacity in every case, its
place where the plan does not move it, and its shape where the plan changes the shape or the
thing's own shape is given. -/
theorem resume_kept_shows [BEq κ] [LawfulBEq κ] (key : α → κ) (olds next : List α)
    (p : Plan α) (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key next) {o n : α}
    (hu : (o, n) ∈ (join key olds next).update) (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0)
    (hs : (settle n).at 0 = 0) {q : Pose} (hq : (seen o).Shows q)
    (hp : q.property = .place → ∀ c ∈ p.kept o n, c.1.property ≠ .place)
    (hsh : q.property = .shape → (∃ c ∈ p.kept o n, c.1.property = .shape) ∨ shape n ≠ none) :
    ((ofJoin key (join key olds next) (p.resume seen settle shape)).frame (key n) 0).Shows q := by
  rw [resume_kept_frame key olds next p seen settle shape hd hu hk hs]
  exact Frame.resume_shows (settle n) hq hp hsh

/-- **Where a kept thing starts in a resumed step**: where the plan's starts put it, moved by
the shift at which its old thing was seen. The plan's changes for the pair are of distinct
properties. -/
theorem resume_kept_shift [BEq κ] [LawfulBEq κ] (key : α → κ) (olds next : List α)
    (p : Plan α) (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key next) {o n : α}
    (hu : (o, n) ∈ (join key olds next).update) (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0)
    (hs : (settle n).at 0 = 0) (hdist : ((p.kept o n).map fun c => c.1.property).Nodup) :
    ((ofJoin key (join key olds next) (p.resume seen settle shape)).frame (key n) 0).shift =
      (Frame.ofPoses ((p.kept o n).map fun c => c.1.start)).shift + (seen o).shift := by
  rw [resume_kept_frame key olds next p seen settle shape hd hu hk hs]
  exact Frame.resume_shift (settle n) (shape n) hdist

/-- **A step that is interrupted resumes with nothing changed.** The step before was `m`, and
it is interrupted at the moment `t`. The next step is the join of the things drawn then to the
next list, under the plan resumed from the frames of `m` at `t`, held inside its step. At its
first moment a kept thing shows whatever it showed in `m` at `t`: its size, its line and its
opacity in every case, its place where the plan does not move it, and its shape where the plan
changes the shape or the thing's own shape is given. `resume_kept_place` is the law of a thing
that the plan moves. -/
theorem nothing_jumps [BEq κ] [LawfulBEq κ] (key : α → κ) (m : Motion κ) (t : Nat)
    (olds next : List α) (p : Plan α) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key next) {o n : α}
    (hu : (o, n) ∈ (join key olds next).update) (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0)
    (hs : (settle n).at 0 = 0) {q : Pose} (hq : (m.frame (key n) t).Shows q)
    (hp : q.property = .place → ∀ c ∈ p.kept o n, c.1.property ≠ .place)
    (hsh : q.property = .shape → (∃ c ∈ p.kept o n, c.1.property = .shape) ∨ shape n ≠ none) :
    ((ofJoin key (join key olds next)
      (p.resume (fun a => m.frame (key a) t) settle shape)).within.frame (key n) 0).Shows q := by
  have hkey : key o = key n := (mem_update key olds next hu).2.2
  rw [within_frame_zero]
  refine resume_kept_shows key olds next p (fun a => m.frame (key a) t) settle shape hd hu hk hs
    ?_ hp hsh
  show (m.frame (key o) t).Shows q
  rw [hkey]
  exact hq

/-- **A resumed step ends on the next picture.** With a plan that settles and is proper, and a
proper easing in every `settle`, each thing of the next list is drawn as the still picture has
it from the step's end on, whatever its shape. -/
theorem resume_end [BEq κ] [LawfulBEq κ] (key : α → κ) (olds next : List α) (p : Plan α)
    (seen : α → Frame) {settle : α → Transition} (shape : α → Option (List ICubic))
    (hs : p.Settles) (hp : p.Proper) (hset : ∀ n, (settle n).ease.Proper) {n : α}
    (hn : n ∈ next) {t : Nat} (ht : 1000 ≤ t) :
    ((ofJoin key (join key olds next) (p.resume seen settle shape)).within.frame
      (key n) t).AtRest :=
  frame_atRest (ofJoin_end key olds next (p.resume seen settle shape)
    (Plan.resume_settles seen settle shape hs) (Plan.resume_proper seen shape hp hset) hn ht)

/-! ### A thing that leaves -/

/-- **The poses of a thing that leaves in a resumed step** are the changes of `leaveFrom`, each
read at its moment. The keys of the things drawn at the interruption are distinct. -/
theorem resume_leaving_poses [BEq κ] [LawfulBEq κ] (key : α → κ) (olds next : List α)
    (p : Plan α) (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key olds) {o : α}
    (ho : o ∈ (join key olds next).exit) (t : Nat) :
    (ofJoin key (join key olds next) (p.resume seen settle shape)).posesOf (key o) t =
      ((seen o).leaveFrom (p.leave o)).map fun c => c.1.at (c.2.at t) :=
  posesOf_leaving key olds next (p.resume seen settle shape) hd ho t

/-- **A thing that leaves goes on from where it is seen.** At the first moment of a resumed step
it shows whatever it was seen with: its size, its line, its opacity and its shape in every case,
and its place where the plan does not move it. -/
theorem resume_leaving_shows [BEq κ] [LawfulBEq κ] (key : α → κ) (olds next : List α)
    (p : Plan α) (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key olds) {o : α}
    (ho : o ∈ (join key olds next).exit) (hl : ∀ c ∈ p.leave o, c.2.at 0 = 0) {q : Pose}
    (hq : (seen o).Shows q)
    (hp : q.property = .place → ∀ c ∈ p.leave o, c.1.property ≠ .place) :
    ((ofJoin key (join key olds next) (p.resume seen settle shape)).frame (key o) 0).Shows q := by
  have e : (ofJoin key (join key olds next) (p.resume seen settle shape)).posesOf (key o) 0 =
      ((seen o).leaveFrom (p.leave o)).map fun c => c.1.start :=
    (resume_leaving_poses key olds next p seen settle shape hd ho 0).trans
      (List.map_congr_left fun c hc =>
        at_start_of c (Frame.carry_timing (fun tm => tm.at 0 = 0) hl default_at_zero c hc))
  show (Frame.ofPoses
    ((ofJoin key (join key olds next) (p.resume seen settle shape)).posesOf (key o) 0)).Shows q
  rw [e]
  exact Frame.leaveFrom_shows hq hp

/-- **What the plan does not change of a thing that leaves is held for the whole step.** At
every moment the thing shows whatever it was seen with, of each property that the plan has no
change of. -/
theorem resume_leaving_held [BEq κ] [LawfulBEq κ] (key : α → κ) (olds next : List α)
    (p : Plan α) (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key olds) {o : α}
    (ho : o ∈ (join key olds next).exit) {q : Pose} (hq : (seen o).Shows q)
    (hc : ∀ c ∈ p.leave o, c.1.property ≠ q.property) (t : Nat) :
    ((ofJoin key (join key olds next) (p.resume seen settle shape)).frame (key o) t).Shows q := by
  show (Frame.ofPoses
    ((ofJoin key (join key olds next) (p.resume seen settle shape)).posesOf (key o) t)).Shows q
  rw [resume_leaving_poses key olds next p seen settle shape hd ho t]
  exact Frame.leaveFrom_held hq hc t

end Motion

/-! ## A thing that the plan moves -/

/-- **A resumed thing that the plan moves starts where it is seen**, in the places of the next
picture: its new place and the shift of its start are its old place and the shift it is seen
at. The plan moves the thing by `Plan.moving`, and may give it more changes that are not of its
place. -/
theorem Frame.resume_moving (place : α → IVec) (move : Transition) (o n : α) (f : Frame)
    (settle : Transition) (own : Option (List ICubic)) {more : List (Change × Transition)}
    (hm : ∀ c ∈ more, c.1.property ≠ .place) (hd : (more.map fun c => c.1.property).Nodup) :
    place n + (Frame.ofPoses ((f.resume settle own (Plan.moving place move o n ++ more)).map
      fun c => c.1.start)).shift = place o + f.shift := by
  have hdist : ((Plan.moving place move o n ++ more).map fun c => c.1.property).Nodup := by
    rw [List.map_append]
    refine nodup_append_of (Plan.moving_single place move o n) hd fun a ha hb => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c', hc', e⟩ := List.mem_map.mp hb
    rw [Plan.mem_moving place move hc] at e
    exact hm c' hc' e
  have hno : ∀ p ∈ more.map (fun c => c.1.start), p.property ≠ .place := fun p hp e => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact hm c hc ((Change.start_property c.1).symm.trans e)
  have hg : (Frame.ofPoses ((Plan.moving place move o n ++ more).map fun c => c.1.start)).shift =
      place o - place n := by
    rw [List.map_append, Frame.ofPoses_append, Frame.shift_under_of_no hno]
    exact Plan.moving_start_shift place move o n
  rw [Frame.resume_shift settle own hdist, hg]
  exact IVec.add_sub_add (place o) (place n) f.shift

namespace Motion

/-- **A kept thing that the plan moves starts where its old thing was seen.** At the first
moment of a resumed step, its new place and its shift are its old place and the shift its old
thing was seen at. -/
theorem resume_kept_place [BEq κ] [LawfulBEq κ] (key : α → κ) (olds next : List α)
    (p : Plan α) (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key next) {o n : α}
    (hu : (o, n) ∈ (join key olds next).update) (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0)
    (hs : (settle n).at 0 = 0) (place : α → IVec) (move : Transition)
    {more : List (Change × Transition)} (hkept : p.kept o n = Plan.moving place move o n ++ more)
    (hm : ∀ c ∈ more, c.1.property ≠ .place) (hdm : (more.map fun c => c.1.property).Nodup) :
    place n +
        ((ofJoin key (join key olds next) (p.resume seen settle shape)).frame (key n) 0).shift =
      place o + (seen o).shift := by
  rw [resume_kept_frame key olds next p seen settle shape hd hu hk hs, hkept]
  exact Frame.resume_moving place move o n (seen o) (settle n) (shape n) hm hdm

/-- **A thing on its way stands still at the interruption.** The step before was `m`, and it is
interrupted at the moment `t`. At the first moment of the resumed step, held inside its step, a
kept thing that the plan moves stands where it stood in `m` at `t`: its new place and its shift
are its old place and the shift it had. -/
theorem nothing_moves [BEq κ] [LawfulBEq κ] (key : α → κ) (m : Motion κ) (t : Nat)
    (olds next : List α) (p : Plan α) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key next) {o n : α}
    (hu : (o, n) ∈ (join key olds next).update) (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0)
    (hs : (settle n).at 0 = 0) (place : α → IVec) (move : Transition)
    {more : List (Change × Transition)} (hkept : p.kept o n = Plan.moving place move o n ++ more)
    (hm : ∀ c ∈ more, c.1.property ≠ .place) (hdm : (more.map fun c => c.1.property).Nodup) :
    place n + ((ofJoin key (join key olds next)
        (p.resume (fun a => m.frame (key a) t) settle shape)).within.frame (key n) 0).shift =
      place o + (m.frame (key n) t).shift := by
  have hkey : key o = key n := (mem_update key olds next hu).2.2
  rw [within_frame_zero, resume_kept_place key olds next p (fun a => m.frame (key a) t) settle
    shape hd hu hk hs place move hkept hm hdm]
  show place o + (m.frame (key o) t).shift = place o + (m.frame (key n) t).shift
  rw [hkey]

/-- **A step that is interrupted resumes with nothing changed**: `nothing_jumps`, said of the
plan that `Plan.resumeFrom` gives. A caller that resumes by `p.resumeFrom key m t settle shape`
has this law of its own step, as it writes it. -/
theorem nothing_jumps_from [BEq κ] [LawfulBEq κ] (key : α → κ) (m : Motion κ) (t : Nat)
    (olds next : List α) (p : Plan α) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key next) {o n : α}
    (hu : (o, n) ∈ (join key olds next).update) (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0)
    (hs : (settle n).at 0 = 0) {q : Pose} (hq : (m.frame (key n) t).Shows q)
    (hp : q.property = .place → ∀ c ∈ p.kept o n, c.1.property ≠ .place)
    (hsh : q.property = .shape → (∃ c ∈ p.kept o n, c.1.property = .shape) ∨ shape n ≠ none) :
    ((ofJoin key (join key olds next)
      (p.resumeFrom key m t settle shape)).within.frame (key n) 0).Shows q :=
  nothing_jumps key m t olds next p settle shape hd hu hk hs hq hp hsh

/-- **A thing on its way stands still at the interruption**: `nothing_moves`, said of the plan
that `Plan.resumeFrom` gives. -/
theorem nothing_moves_from [BEq κ] [LawfulBEq κ] (key : α → κ) (m : Motion κ) (t : Nat)
    (olds next : List α) (p : Plan α) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hd : Distinct key next) {o n : α}
    (hu : (o, n) ∈ (join key olds next).update) (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0)
    (hs : (settle n).at 0 = 0) (place : α → IVec) (move : Transition)
    {more : List (Change × Transition)} (hkept : p.kept o n = Plan.moving place move o n ++ more)
    (hm : ∀ c ∈ more, c.1.property ≠ .place) (hdm : (more.map fun c => c.1.property).Nodup) :
    place n + ((ofJoin key (join key olds next)
        (p.resumeFrom key m t settle shape)).within.frame (key n) 0).shift =
      place o + (m.frame (key n) t).shift :=
  nothing_moves key m t olds next p settle shape hd hu hk hs place move hkept hm hdm

end Motion

/-! ## A new thing that comes from another -/

/-- **How a new thing enters from the place of the thing it comes from**: it shifts from there
to its own place and grows from nothing, by one transition. A thing with no origin grows where
it stands. -/
def Plan.sprout (place : α → IVec) (origin : α → Option IVec) (enter : α → Transition)
    (n : α) : List (Change × Transition) :=
  ((origin n).map fun source => (Change.shift (source - place n) 0, enter n)).toList ++
    [(.grow 0 1000, enter n)]

namespace Plan

/-- A thing with an origin shifts from it and grows. -/
theorem sprout_of_some {place : α → IVec} {origin : α → Option IVec} {enter : α → Transition}
    {n : α} {s : IVec} (h : origin n = some s) :
    sprout place origin enter n = [(.shift (s - place n) 0, enter n), (.grow 0 1000, enter n)] :=
  congrArg (fun x : Option IVec =>
    (x.map fun source => (Change.shift (source - place n) 0, enter n)).toList ++
      [(Change.grow 0 1000, enter n)]) h

/-- A thing with no origin grows where it stands. -/
theorem sprout_of_none {place : α → IVec} {origin : α → Option IVec} {enter : α → Transition}
    {n : α} (h : origin n = none) : sprout place origin enter n = [(.grow 0 1000, enter n)] :=
  congrArg (fun x : Option IVec =>
    (x.map fun source => (Change.shift (source - place n) 0, enter n)).toList ++
      [(Change.grow 0 1000, enter n)]) h

/-- **Every change of `sprout` ends at rest**: the new thing ends on its place at its size. A
plan whose `enter` is `sprout` has the half of `Settles` that is about new things. -/
theorem sprout_stop (place : α → IVec) (origin : α → Option IVec) (enter : α → Transition)
    (n : α) : ∀ c ∈ sprout place origin enter n, c.1.stop.AtRest := by
  intro c hc
  cases h : origin n with
  | none =>
    rw [sprout_of_none h] at hc
    rw [List.mem_singleton.mp hc]
    exact rfl
  | some s =>
    rw [sprout_of_some h] at hc
    rcases List.mem_cons.mp hc with e | e
    · rw [e]
      exact rfl
    · rw [List.mem_singleton.mp e]
      exact rfl

/-- Every easing of `sprout` is that of the thing's transition. -/
theorem sprout_ease (place : α → IVec) (origin : α → Option IVec) {enter : α → Transition}
    {n : α} (hp : (enter n).ease.Proper) : ∀ c ∈ sprout place origin enter n, c.2.ease.Proper := by
  intro c hc
  cases h : origin n with
  | none =>
    rw [sprout_of_none h] at hc
    rw [List.mem_singleton.mp hc]
    exact hp
  | some s =>
    rw [sprout_of_some h] at hc
    rcases List.mem_cons.mp hc with e | e
    · rw [e]
      exact hp
    · rw [List.mem_singleton.mp e]
      exact hp

/-- The changes of `sprout` are of distinct properties: a shift at most, and a size. -/
theorem sprout_single (place : α → IVec) (origin : α → Option IVec) (enter : α → Transition)
    (n : α) : ((sprout place origin enter n).map fun c => c.1.property).Nodup := by
  cases h : origin n with
  | none =>
    rw [sprout_of_none h]
    exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | some s =>
    rw [sprout_of_some h]
    show ([Property.place, Property.size]).Nodup
    decide

/-- **A new thing with an origin starts on it, as nothing.** The frame of the starts of
`sprout` has the step from the thing's place to its origin and the size `0`. -/
theorem sprout_start {place : α → IVec} {origin : α → Option IVec} (enter : α → Transition)
    {n : α} {s : IVec} (h : origin n = some s) :
    Frame.ofPoses ((sprout place origin enter n).map fun c => c.1.start) =
      { shift := s - place n, size := 0 } := by
  rw [sprout_of_some h]
  rfl

/-- A new thing with no origin starts on its own place, as nothing. -/
theorem sprout_start_of_none {place : α → IVec} {origin : α → Option IVec}
    (enter : α → Transition) {n : α} (h : origin n = none) :
    Frame.ofPoses ((sprout place origin enter n).map fun c => c.1.start) = { size := 0 } := by
  rw [sprout_of_none h]
  rfl

/-- **A new thing starts on the thing it comes from**: its place and the shift of its start are
its origin. -/
theorem sprout_origin {place : α → IVec} {origin : α → Option IVec} (enter : α → Transition)
    {n : α} {s : IVec} (h : origin n = some s) :
    place n + (Frame.ofPoses ((sprout place origin enter n).map fun c => c.1.start)).shift =
      s := by
  rw [sprout_start enter h]
  show place n + (s - place n) = s
  exact IVec.ext (by simp only [IVec.add_x, IVec.sub_x]; omega)
    (by simp only [IVec.add_y, IVec.sub_y]; omega)

end Plan

/-! ## One change for each property of a thing -/

namespace Frame

/-- The properties of the changes of `carry`: those of the plan's changes, then those of the
changes of `fill` that the plan does not change. -/
theorem carry_properties (f : Frame) (fill : List Change) (tm : Transition)
    (cs : List (Change × Transition)) :
    (f.carry fill tm cs).map (fun c => c.1.property) = cs.map (fun c => c.1.property) ++
      (fill.filter fun d => cs.all fun c => decide (c.1.property ≠ d.property)).map
        Change.property := by
  unfold carry
  rw [List.map_append, List.map_map, List.map_map]
  exact congrArg (fun l : List Property => l ++
      (fill.filter fun d => cs.all fun c => decide (c.1.property ≠ d.property)).map
        Change.property)
    (List.map_congr_left fun c _ => Change.from_property c.1 f)

/-- **The changes of `carry` are of distinct properties**, where the plan's are and those of
`fill` are. -/
theorem carry_distinct {f : Frame} {fill : List Change} {tm : Transition}
    {cs : List (Change × Transition)} (hc : (cs.map fun c => c.1.property).Nodup)
    (hf : (fill.map Change.property).Nodup) :
    ((f.carry fill tm cs).map fun c => c.1.property).Nodup := by
  rw [carry_properties]
  refine nodup_append_of hc
    (List.Nodup.sublist (List.Sublist.map Change.property List.filter_sublist) hf)
    fun a ha hb => ?_
  obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp ha
  obtain ⟨d, hd, e⟩ := List.mem_map.mp hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.mem_filter.mp hd).2 c hcm) e.symm

/-- `reshape` gives one change at most. -/
theorem reshape_distinct (f : Frame) (own : Option (List ICubic)) :
    ((f.reshape own).map Change.property).Nodup := by
  unfold reshape
  cases f.shape with
  | none => exact List.nodup_nil
  | some s =>
    cases own with
    | none => exact List.nodup_nil
    | some o => exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

/-- **A resumed answer has one change for each property**, where the plan's answer has. -/
theorem resume_distinct {f : Frame} (settle : Transition) (own : Option (List ICubic))
    {cs : List (Change × Transition)} (hc : (cs.map fun c => c.1.property).Nodup) :
    ((f.resume settle own cs).map fun c => c.1.property).Nodup := by
  refine carry_distinct hc ?_
  rw [List.map_append]
  refine nodup_append_of (toRest_distinct f) (reshape_distinct f own) fun a ha hb => ?_
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  obtain ⟨d', hd', e⟩ := List.mem_map.mp hb
  obtain ⟨s, o, _, _, rfl⟩ := mem_reshape.mp hd'
  exact toRest_not_shape f d hd e.symm

/-- **The answer of a thing that leaves from where it is seen has one change for each
property**, where the plan's answer has. -/
theorem leaveFrom_distinct {f : Frame} {cs : List (Change × Transition)}
    (hc : (cs.map fun c => c.1.property).Nodup) :
    ((f.leaveFrom cs).map fun c => c.1.property).Nodup := by
  refine carry_distinct hc ?_
  rw [List.map_append]
  refine nodup_append_of (hold_distinct f) (reshape_distinct f f.shape) fun a ha hb => ?_
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  obtain ⟨d', hd', e⟩ := List.mem_map.mp hb
  obtain ⟨s, o, _, _, rfl⟩ := mem_reshape.mp hd'
  exact hold_not_shape f d hd e.symm

end Frame

namespace Plan

/-- **A resumed plan has one change for each property of a thing**, where the plan has. -/
theorem resume_single {p : Plan α} (seen : α → Frame) (settle : α → Transition)
    (shape : α → Option (List ICubic)) (hp : p.Single) : (p.resume seen settle shape).Single :=
  ⟨fun o n => Frame.resume_distinct (settle n) (shape n) (hp.1 o n), hp.2.1,
    fun o => Frame.leaveFrom_distinct (hp.2.2 o)⟩

end Plan

namespace Motion

/-- **A resumed step is `Single`**, where the plan has one change for each property of a thing
and the keys of the things drawn and of the next list are distinct. -/
theorem resume_single [BEq κ] [LawfulBEq κ] (key : α → κ) (olds next : List α) (p : Plan α)
    (seen : α → Frame) (settle : α → Transition) (shape : α → Option (List ICubic))
    (hp : p.Single) (hdo : Distinct key olds) (hdn : Distinct key next) :
    (ofJoin key (join key olds next) (p.resume seen settle shape)).Single :=
  single_ofJoin key olds next _ (Plan.resume_single seen settle shape hp) hdo hdn

/-- **A new thing that comes from another is drawn on it at the first moment of the step**, as
nothing: its frame has the step from its place to its origin and the size `0`. The plan's
`enter` gives the thing `Plan.sprout`, and its transition reads `0` at the moment `0`. -/
theorem sprout_frame [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (hd : Distinct key new) {n : α} (hn : n ∈ (join key old new).enter) (place : α → IVec)
    (origin : α → Option IVec) (enter : α → Transition)
    (hp : p.enter n = Plan.sprout place origin enter n) (h0 : (enter n).at 0 = 0) {s : IVec}
    (ho : origin n = some s) :
    (ofJoin key (join key old new) p).frame (key n) 0 = { shift := s - place n, size := 0 } := by
  show Frame.ofPoses ((ofJoin key (join key old new) p).posesOf (key n) 0) = _
  rw [posesOf_entering key old new p hd hn 0, hp, Plan.sprout_of_some ho]
  show Frame.ofPoses [(Change.shift (s - place n) 0).at ((enter n).at 0),
    (Change.grow 0 1000).at ((enter n).at 0)] = _
  rw [h0, Change.at_start, Change.at_start]
  rfl

end Motion

/-! ## Finite evaluations and controls

A thing is a key and its left edge, as a box of a rank is. The plan moves a kept box whose place
changed, fades a new box in and fades an old one out, each over the whole step by the progress
itself. Lean computes each one. -/

-- A rank of three boxes. The first step moves the second box by forty and the third by fifty,
-- and it is interrupted at the moment 400 by a step to a third picture. The second box is then
-- drawn at 176 and the third at 356. At the first moment of the resumed step each box is drawn
-- where it was. Without `resume` each starts from its place in the second picture: the second
-- box jumps by 24 pixels and the third by 30. The resumed step is `Single`.
#guard
  let key : String × Int → String := Prod.fst
  let place : String × Int → IVec := fun a => ⟨a.2, 0⟩
  let plan : Plan (String × Int) :=
    ⟨Plan.moving place {}, fun _ => [(.fade 0 1000, {})], fun _ => [(.fade 1000 0, {})]⟩
  let first : List (String × Int) := [("a", 24), ("b", 160), ("c", 336)]
  let second : List (String × Int) := [("a", 24), ("b", 200), ("c", 386)]
  let third : List (String × Int) := [("a", 24), ("b", 300), ("c", 500)]
  let m := (Motion.ofJoin key (join key first second) plan).within
  let olds := (join key first second).drawn second 400
  let seen : String × Int → Frame := fun o => m.frame (key o) 400
  let resumed := Motion.ofJoin key (join key olds third) (plan.resume seen fun _ => {})
  let jumped := Motion.ofJoin key (join key olds third) plan
  olds.map (fun o => (place o + (seen o).shift).x) == [24, 176, 356] &&
    third.map (fun n => (place n + (resumed.within.frame (key n) 0).shift).x) ==
      [24, 176, 356] &&
    third.map (fun n => (place n + (jumped.within.frame (key n) 0).shift).x) ==
      [24, 200, 386] &&
    third.map (fun n => resumed.within.frame (key n) 1000) == [{}, {}, {}] &&
    decide resumed.Single

-- What the resumed plan gives the second box: the plan's shift from its place in the second
-- picture, started 24 further off, where the box is seen.
#guard
  let place : String × Int → IVec := fun a => ⟨a.2, 0⟩
  ({ shift := ⟨-24, 0⟩ } : Frame).resume {} none (Plan.moving place {} ("b", 200) ("b", 300)) ==
    [(.shift ⟨-124, 0⟩ 0, {})]

-- A box that was leaving and is wanted again. It fades out, and at the moment 400 it is drawn
-- at 600 per mille of its opacity. The next picture has it again, and its plan gives it nothing
-- to do, since its place is the same. Resumed, it comes back from 600 to the whole by `settle`,
-- and ends as the still picture has it. Without `resume` it has no track, and jumps to the
-- whole at once.
#guard
  let key : String × Int → String := Prod.fst
  let plan : Plan (String × Int) :=
    ⟨Plan.moving (fun a => ⟨a.2, 0⟩) {}, fun _ => [(.fade 0 1000, {})],
      fun _ => [(.fade 1000 0, {})]⟩
  let first : List (String × Int) := [("a", 24), ("b", 160)]
  let second : List (String × Int) := [("a", 24)]
  let m := (Motion.ofJoin key (join key first second) plan).within
  let olds := (join key first second).drawn second 400
  let seen : String × Int → Frame := fun o => m.frame (key o) 400
  let resumed := (Motion.ofJoin key (join key olds first) (plan.resume seen fun _ => {})).within
  let jumped := (Motion.ofJoin key (join key olds first) plan).within
  olds == [("b", 160), ("a", 24)] && (seen ("b", 160)).shown == 600 &&
    (plan.resume seen fun _ => {}).kept ("b", 160) ("b", 160) == [(.fade 600 1000, {})] &&
    (resumed.frame "b" 0).shown == 600 && resumed.frame "b" 1000 == ({} : Frame) &&
    (jumped.frame "b" 0).shown == 1000

-- A box that leaves and goes on leaving. It is seen 24 off its place and at 600 per mille. The
-- plan fades it out: the fade starts at 600, and its shift is held for the whole step.
#guard
  let seen : Frame := { shift := ⟨-24, 0⟩, shown := 600 }
  seen.leaveFrom [(.fade 1000 0, {})] ==
      [(.fade 600 0, {}), (.shift ⟨-24, 0⟩ ⟨-24, 0⟩, {})] &&
    [0, 500, 1000].map (fun t => Frame.ofPoses
      ((seen.leaveFrom [(.fade 1000 0, {})]).map fun c => c.1.at (c.2.at t))) ==
      [{ shift := ⟨-24, 0⟩, shown := 600 }, { shift := ⟨-24, 0⟩, shown := 300 },
        { shift := ⟨-24, 0⟩, shown := 0 }]

-- An edge in the middle of a change of shape. At the moment 400 its last two points are 40
-- down. A plan that changes its shape again starts from the shape that is seen. A plan with no
-- change of shape takes it to its own shape where that is given. Where it is not given the edge
-- has no track, and it is drawn with its own shape at once: the one jump that is left. An edge
-- that leaves holds the shape it is seen with.
#guard
  let s0 : List ICubic := [⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨100, 0⟩, ⟨100, 0⟩⟩]
  let s1 : List ICubic := [⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨100, 100⟩, ⟨100, 100⟩⟩]
  let s2 : List ICubic := [⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨200, 100⟩, ⟨200, 100⟩⟩]
  let mid : List ICubic := [⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨100, 40⟩, ⟨100, 40⟩⟩]
  let m : Motion String := [⟨"edge", .morph s0 s1, {}⟩]
  let seen := m.frame "edge" 400
  seen.shape == some mid &&
    seen.resume {} none [(.morph s1 s2, {})] == [(.morph mid s2, {})] &&
    seen.resume {} (some s1) [] == [(.morph mid s1, {})] &&
    seen.resume {} none [] == [] &&
    (Frame.ofPoses ((seen.resume {} none []).map fun c => c.1.start)).shape == none &&
    seen.leaveFrom [(.fade 1000 0, {})] == [(.fade 1000 0, {}), (.morph mid mid, {})]

-- The laws of the first moment ask that each transition reads `0` there. A transition with no
-- delay and no duration is over at the moment `0` and reads `1000`: a box that it moves is at
-- its new place at once, resumed or not.
#guard ({ duration := 0 } : Transition).at 0 == 1000 && ({} : Transition).at 0 == 0
#guard
  let place : String × Int → IVec := fun a => ⟨a.2, 0⟩
  let quick : Plan (String × Int) := ⟨Plan.moving place { duration := 0 }, fun _ => [], fun _ => []⟩
  let seen : String × Int → Frame := fun _ => { shift := ⟨-24, 0⟩ }
  ((Motion.ofJoin Prod.fst (join Prod.fst [("b", 200)] [("b", 300)])
    (quick.resume seen fun _ => {})).frame "b" 0).shift == 0

-- A thing seen at rest resumes as the plan says, and a new thing that comes from another
-- starts on it, as nothing.
#guard
  let place : String × Int → IVec := fun a => ⟨a.2, 0⟩
  Frame.rest.resume {} none (Plan.moving place {} ("b", 200) ("b", 300)) ==
      Plan.moving place {} ("b", 200) ("b", 300) &&
    Frame.ofPoses ((Plan.sprout place (fun _ => some ⟨200, 0⟩) (fun _ => {}) ("d", 300)).map
      fun c => c.1.start) == { shift := ⟨-100, 0⟩, size := 0 }

end Whatwg.Svg.Scene
