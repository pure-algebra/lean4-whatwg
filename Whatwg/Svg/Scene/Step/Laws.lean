import Whatwg.Svg.Scene.Step
import Whatwg.Svg.Scene.Together

/-!
# Whatwg.Svg.Scene.Step.Laws

Owner: the laws of a step as one value (slice S17 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Step.lean` puts the pieces of a step together. The laws of the pieces are in
the modules that own them, each said of `Motion.ofJoin` or of `Motion.staged` with the key, the
two lists and the plan as arguments. Here each is said of a `Step`, in the words of a caller:
`s.motion`, `s.frame`, `s.sample`, `s.interrupt`. A premise is a fact about the caller's plan
that it shows once (`Plan.Settles`, `Plan.Proper`, `Plan.Single`, `Plan.MovesBy`), or a fact of
its own pictures that Lean decides (`Distinct`).

What the laws say of a step `s`:

- **The last picture** (`Step.frame_end`, `Step.sample_end`): with a plan that settles and is
  proper, from the step's end on the things drawn are the new picture, each with a frame at
  rest. It holds of a step in stages on no further term, since the step is held inside itself.
  With a plan that changes no shape of a thing that stays (`Plan.KeepsShapes`), each frame is the
  still picture itself (`Step.frame_end_rest`), and the picture is the new one with every thing
  at rest (`Step.sample_end_rest`). A thing of the new picture has its own shape at every moment
  under such a plan (`Step.frame_shape`).
- `Step.mem_motion`: a track of a step is a track of its join under its plan, with other times:
  the same thing, the same change, the same easing. It is the one reading of `Step.motion` that
  holds for both timings.
- **One track for each property** (`Step.single`): with a plan that gives each thing one change
  for each property and distinct keys in both pictures.
- `Step.drawn_distinct`: the things drawn at a moment have distinct keys, where both pictures
  have. So the step that interrupts has distinct keys in the picture it starts from.
- **Kept things keep their relations** (`Step.together`): with a plan that moves each kept
  thing by one transition whose easing passes `Easing.bounded`, and distinct keys in the new
  picture, a kept relation that the places of two kept things have in both pictures holds of
  where they stand at every moment. `Step.leftOf` and `Step.above` are the law for a gap.
- **A step in stages.** It needs no cut where the stages have room (`Step.motion_of_stages`).
  It respects an order in time on the terms of `Motion.staged_respects` (`Step.respects`), and
  on terms that a caller can show of its own order: nothing is before an old thing, and among
  the new things the rank follows the order (`Step.order`). So the tracks of the kept things are
  over before a track of a new thing starts, and a level is over before the next starts. **The
  kept things are at rest when the new things enter** (`Step.kept_rest`): each kept thing has a
  frame at rest from the moment `enterFrom` on.
- **Across `interrupt`.** The step that interrupts ends on the next picture
  (`Step.interrupt_frame_end`, `Step.interrupt_sample_end`), at rest where the plan changes no
  shape (`Step.interrupt_sample_end_rest`), and has one track for each property
  (`Step.interrupt_single`). **Nothing jumps** (`Step.nothing_jumps`): at its first moment a
  kept thing shows whatever the old thing showed at the interruption. **Nothing moves**
  (`Step.nothing_moves`): a kept thing that the plan moves stands where the old thing stood. A
  thing that leaves goes on from where it is seen (`Step.leaving_goes_on`).
- **An interruption at the step's end is an ordinary step** (`Step.interrupt_of_rest`,
  `Step.interrupt_of_rest_sample`): where the step was over, the step that interrupts has the
  tracks, and so the samples, of the step from the new picture under the plan as written.

Some declarations here belong to other modules, and are stated in the namespaces they belong
to. `Plan.KeepsShapes` and `Plan.FromRest`, with what `Plan.moving` gives them
(`Plan.moving_keepsShape`, `Plan.moving_fromRest`), and `Motion.ofJoin_congr`, two plans that
agree on the things of a join, belong in `Whatwg/Svg/Scene/Plan.lean`. `Plan.resume_keepsShapes`
belongs in `Whatwg/Svg/Scene/Resume.lean`. `Motion.firstStage_key`, the key of a track of the
first stage, belongs in `Whatwg/Svg/Scene/Stage.lean`. `Transition.within_end_le` belongs in
`Whatwg/Svg/Scene/Motion/Laws.lean`.

Which laws are an existing law said of a `Step`, and which are not. A line or two over the law
of the piece: `single`, `drawn_distinct`, `frame_end`, `together`, `leftOf`, `above`,
`motion_of_stages`, `respects`, the three of the end of `interrupt`, `interrupt_single`,
`nothing_jumps`, `nothing_moves` and `leaving_goes_on`. Proved here, since the law of the piece
does not give it: `frame_shape` and the two laws of the still picture itself, `order`,
`kept_rest`, and `interrupt_of_rest`. The last rests on `Frame.resume_of_rest` and
`Frame.leaveFrom_of_rest`, the laws of one thing. `Plan.resume_of_rest` asks that every value of
the type is seen at rest, and a step cannot show that: a thing that has left is seen as its
leaving left it.

What this module does not claim. Of a step in stages that interrupts another, nothing is said
of the first moment: `Track.endBy` scales a duration and rounds it down, a short one to nothing,
and a transition with no delay and no duration reads its end at the moment `0`. A control at
the end of this file is such a step. The order laws are of the tracks, as `Motion.Respects` says
them. No law here says that a new thing is not seen before its level: `Motion.staged_levels` is
of single tracks named through `Motion.stagedOf`, and a law of frames needs the poses of one new
thing in a staged step, which `Stage.lean` does not have. `Step.together` is of a step that
starts from the still picture: the plan of a step that interrupts is resumed, and does not pass
`Plan.MovesBy`. `Motion.resume_leaving_held`, a thing that leaves holds what the plan does not
change, is of the step before the cut at its end, and is not said here of the step that is
played. `Step.interrupt_of_rest` asks that the plan of the step that is over changes no shape of
a thing that stays: a frame at rest may have a shape that a track gave it, and a plan that
changes shapes resumes from that shape.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

variable {α κ : Type}

/-! ## What belongs in other modules -/

namespace Plan

/-- **The plan changes no shape of a thing that stays**: no change that `kept` or `enter` gives
is a change of shape. Under such a plan a thing of the new picture is drawn with its own shape
at every moment, and at rest it is the still picture itself. -/
def KeepsShapes (p : Plan α) : Prop :=
  (∀ o n, ∀ c ∈ p.kept o n, c.1.property ≠ .shape) ∧ ∀ n, ∀ c ∈ p.enter n, c.1.property ≠ .shape

/-- **The plan is written from rest**: each change of a size, a line or an opacity that it gives
a kept thing or a thing that leaves starts at rest. A plan is written so when it is written as
if every old thing stood still, which is how `Plan.resume` asks for it. -/
def FromRest (p : Plan α) : Prop :=
  (∀ o n, ∀ c ∈ p.kept o n, c.1.property ≠ .place → c.1.start.AtRest) ∧
    ∀ o, ∀ c ∈ p.leave o, c.1.property ≠ .place → c.1.start.AtRest

/-- `moving` gives no change of shape. It is the part of `KeepsShapes` that is about
`moving`. -/
theorem moving_keepsShape (place : α → IVec) (move : Transition) (o n : α) :
    ∀ c ∈ moving place move o n, c.1.property ≠ .shape := by
  intro c h
  rw [mem_moving place move h]
  exact fun e => nomatch e

/-- `moving` gives a change of the place only. It is the part of `FromRest` that is about
`moving`. -/
theorem moving_fromRest (place : α → IVec) (move : Transition) (o n : α) :
    ∀ c ∈ moving place move o n, c.1.property ≠ .place → c.1.start.AtRest := by
  intro c h hne
  rw [mem_moving place move h] at hne
  exact absurd rfl hne

/-- **A resumed plan changes no shape of a thing that stays**, where the plan changes none and no
thing's own shape is given: what a kept thing is given to bring it to rest is of its place, its
size, its line or its opacity. So a step that interrupts ends on the still picture itself, and
the step after it may interrupt it in turn. -/
theorem resume_keepsShapes {p : Plan α} (seen : α → Frame) (settle : α → Transition)
    {shape : α → Option (List ICubic)} (hsh : ∀ n, shape n = none) (hp : p.KeepsShapes) :
    (p.resume seen settle shape).KeepsShapes :=
  ⟨fun o n x hx => by
    rcases Frame.mem_resume.mp hx with ⟨c, hc, rfl⟩ | ⟨d, hd, _, rfl⟩ | ⟨_, own, _, ho, _, _⟩
    · show (c.1.from (seen o)).property ≠ .shape
      rw [Change.from_property]
      exact hp.1 o n c hc
    · exact Frame.toRest_not_shape (seen o) d hd
    · exact absurd ((hsh n).symm.trans ho) (fun e => nomatch e), hp.2⟩

end Plan

namespace Motion

/-- Two functions that agree on the members of a list give the same tracks over it. -/
private theorem flatMap_congr_mem {β γ : Type} {f g : β → List γ} : ∀ {l : List β},
    (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr_mem fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- **Two plans that agree on the things of a join give it the same tracks.** A plan is three
functions, and a join asks each of them about its own things only: `kept` about its pairs,
`enter` about its new things and `leave` about the things that exit. -/
theorem ofJoin_congr (key : α → κ) (j : Join α) {p q : Plan α}
    (hk : ∀ x ∈ j.update, p.kept x.1 x.2 = q.kept x.1 x.2)
    (he : ∀ n ∈ j.enter, p.enter n = q.enter n) (hl : ∀ o ∈ j.exit, p.leave o = q.leave o) :
    ofJoin key j p = ofJoin key j q := by
  have e1 : j.update.flatMap (fun x => tracks (key x.2) (p.kept x.1 x.2)) =
      j.update.flatMap (fun x => tracks (key x.2) (q.kept x.1 x.2)) :=
    flatMap_congr_mem fun x hx => congrArg (tracks (key x.2)) (hk x hx)
  have e2 : j.enter.flatMap (fun n => tracks (key n) (p.enter n)) =
      j.enter.flatMap (fun n => tracks (key n) (q.enter n)) :=
    flatMap_congr_mem fun n hn => congrArg (tracks (key n)) (he n hn)
  have e3 : j.exit.flatMap (fun o => tracks (key o) (p.leave o)) =
      j.exit.flatMap (fun o => tracks (key o) (q.leave o)) :=
    flatMap_congr_mem fun o ho => congrArg (tracks (key o)) (hl o ho)
  show j.update.flatMap (fun x => tracks (key x.2) (p.kept x.1 x.2)) ++
      j.enter.flatMap (fun n => tracks (key n) (p.enter n)) ++
      j.exit.flatMap (fun o => tracks (key o) (p.leave o)) =
    j.update.flatMap (fun x => tracks (key x.2) (q.kept x.1 x.2)) ++
      j.enter.flatMap (fun n => tracks (key n) (q.enter n)) ++
      j.exit.flatMap (fun o => tracks (key o) (q.leave o))
  rw [e1, e2, e3]

/-- **A track of the first stage has the key of a thing of the old list**: a kept thing has the
key of its old thing, and a thing that leaves is old. -/
theorem firstStage_key [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    {tr : Track κ} (h : tr ∈ firstStage key (join key old new) p) : ∃ o ∈ old, key o = tr.key := by
  have h' : tr ∈ keeping key (join key old new) p ++ leaving key (join key old new) p := h
  rcases List.mem_append.mp h' with hk | hl
  · obtain ⟨⟨o, n⟩, hq, htr⟩ := List.mem_flatMap.mp hk
    obtain ⟨c, _, rfl⟩ := mem_tracks.mp htr
    exact ⟨o, (mem_update key old new hq).1, (mem_update key old new hq).2.2⟩
  · obtain ⟨o, ho, hko, _⟩ := mem_leaving_key key old new p hl
    exact ⟨o, ho, hko⟩

end Motion

/-- A transition held inside its step ends no later than it ended. -/
theorem Transition.within_end_le (tr : Transition) :
    tr.within.delay + tr.within.duration ≤ tr.delay + tr.duration := by
  show min tr.delay 1000 + min tr.duration (1000 - min tr.delay 1000) ≤ tr.delay + tr.duration
  omega

namespace Step

/-! ## The tracks of a step -/

/-- **A track of a step is a track of its join under its plan, with other times**: the same
thing, the same change and the same easing. The cut at the step's end and the stages change when
a thing moves, and never what moves or how. -/
theorem mem_motion [BEq κ] (s : Step α κ) {tr : Track κ} (h : tr ∈ s.motion) :
    ∃ tr0 ∈ Motion.ofJoin s.key s.join s.plan, tr0.untimed = tr.untimed := by
  obtain ⟨key, old, new, plan, stages⟩ := s
  cases stages with
  | none =>
    have h' : tr ∈ (Motion.ofJoin key (Scene.join key old new) plan).within := h
    obtain ⟨tr0, h0, rfl⟩ := Motion.mem_within _ h'
    exact ⟨tr0, h0, rfl⟩
  | some g =>
    have h' : tr ∈ (Motion.staged key (Scene.join key old new) plan g.enterFrom g.levels
      g.rank).within := h
    obtain ⟨tr1, h1, rfl⟩ := Motion.mem_within _ h'
    obtain ⟨tr0, h0, e⟩ := Motion.mem_staged_ofJoin key _ plan g.enterFrom g.levels g.rank h1
    exact ⟨tr0, h0, e⟩

/-- **One track for each property.** With a plan that gives each thing one change for each
property and distinct keys in both pictures, no thing of the step has two tracks of one
property, in stages or not. So the frame of a thing shows the pose of each of its tracks
(`Motion.frame_has`). -/
theorem single [BEq κ] [LawfulBEq κ] (s : Step α κ) (hp : s.plan.Single)
    (ho : Distinct s.key s.old) (hn : Distinct s.key s.new) : s.motion.Single := by
  obtain ⟨key, old, new, plan, stages⟩ := s
  cases stages with
  | none => exact (Motion.single_ofJoin key old new plan hp ho hn).within
  | some g =>
    exact (Motion.staged_single key old new plan g.enterFrom g.levels g.rank hp ho hn).within

/-- **The things drawn at a moment have distinct keys**, where both pictures have. So the step
that interrupts this one starts from a picture with distinct keys. -/
theorem drawn_distinct [BEq κ] [LawfulBEq κ] (s : Step α κ) (ho : Distinct s.key s.old)
    (hn : Distinct s.key s.new) (t : Nat) : Distinct s.key (s.drawn t) :=
  Join.drawn_distinct s.key s.old s.new ho hn t

/-! ## The last picture -/

/-- **The last picture.** With a plan that settles and is proper, each thing of the new picture
is drawn as the still picture has it from the step's end on, whatever its shape. A step in
stages asks no more: it is held inside itself, whatever its levels. -/
theorem frame_end [BEq κ] [LawfulBEq κ] (s : Step α κ) (hs : s.plan.Settles)
    (hp : s.plan.Proper) {n : α} (hn : n ∈ s.new) {t : Nat} (ht : 1000 ≤ t) :
    (s.frame n t).AtRest := by
  obtain ⟨key, old, new, plan, stages⟩ := s
  cases stages with
  | none => exact Motion.frame_atRest (Motion.ofJoin_end key old new plan hs hp hn ht)
  | some g =>
    exact Motion.frame_atRest
      (Motion.staged_within_end key old new plan g.enterFrom g.levels g.rank hs hp hn ht)

/-- **The last moment of a step is the new picture.** From the step's end on, the things of the
sample are the things of the new picture and no other, each with a frame at rest. -/
theorem sample_end [BEq κ] [LawfulBEq κ] (s : Step α κ) (hs : s.plan.Settles)
    (hp : s.plan.Proper) {t : Nat} (ht : 1000 ≤ t) :
    (s.sample t).map Prod.fst = s.new ∧ ∀ x ∈ s.sample t, x.2.AtRest := by
  refine ⟨(s.sample_things t).trans (s.drawn_end ht), fun x hx => ?_⟩
  rw [sample_eq, s.drawn_end ht] at hx
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  exact s.frame_end hs hp hn ht

/-- **A thing of the new picture has its own shape at every moment**, under a plan that changes
no shape of a thing that stays: no track of the step gives it another. -/
theorem frame_shape [BEq κ] [LawfulBEq κ] (s : Step α κ) (hk : s.plan.KeepsShapes) {n : α}
    (hn : n ∈ s.new) (t : Nat) : (s.frame n t).shape = none :=
  Frame.shape_under_of_no (fun q hq => by
    obtain ⟨tr, htr, hkey, rfl⟩ := Motion.mem_posesOf _ _ _ hq
    obtain ⟨tr0, h0, e⟩ := s.mem_motion htr
    have ek : tr0.key = tr.key := congrArg Prod.fst e
    have ec : tr0.change = tr.change := congrArg (fun u => u.2.1) e
    rw [Track.at_property, ← ec]
    rcases List.mem_append.mp h0 with hst | hlv
    · rcases (Motion.mem_staying s.key s.join s.plan).mp hst with
        ⟨x, _, c, hc, rfl⟩ | ⟨n', _, c, hc, rfl⟩
      · exact hk.1 x.1 x.2 c hc
      · exact hk.2 n' c hc
    · obtain ⟨_, _, _, hne⟩ := Motion.mem_leaving_key s.key s.old s.new s.plan hlv
      exact absurd (ek.trans (beq_iff_eq.mp hkey)).symm (hne n hn)) Frame.rest

/-- **At the step's end a thing of the new picture is the still picture itself**, with a plan
that settles, is proper and changes no shape of a thing that stays. -/
theorem frame_end_rest [BEq κ] [LawfulBEq κ] (s : Step α κ) (hs : s.plan.Settles)
    (hp : s.plan.Proper) (hk : s.plan.KeepsShapes) {n : α} (hn : n ∈ s.new) {t : Nat}
    (ht : 1000 ≤ t) : s.frame n t = Frame.rest :=
  have h := s.frame_end hs hp hn ht
  Frame.ext h.1 h.2.1 h.2.2.1 h.2.2.2 (s.frame_shape hk hn t)

/-- **The last moment of a step is the new picture at rest**: the things of the new picture, each
as the still picture has it. -/
theorem sample_end_rest [BEq κ] [LawfulBEq κ] (s : Step α κ) (hs : s.plan.Settles)
    (hp : s.plan.Proper) (hk : s.plan.KeepsShapes) {t : Nat} (ht : 1000 ≤ t) :
    s.sample t = s.new.map fun n => (n, Frame.rest) := by
  rw [sample_eq, s.drawn_end ht]
  exact List.map_congr_left fun n hn => congrArg (Prod.mk n) (s.frame_end_rest hs hp hk hn ht)

/-! ## Kept things keep their relations -/

/-- **A relation of the places of two kept things in both pictures holds of where they stand at
every moment.** The plan moves each kept thing by the one transition `move`, whose easing passes
the test `Easing.bounded`, and the keys of the new picture are distinct. For two kept pairs and
a kept relation `R`: where the two old places have `R` and the two new places have `R`, where the
two things stand has `R` at every moment of the step, in stages or not. -/
theorem together [BEq κ] [LawfulBEq κ] (s : Step α κ) (place : α → IVec) (move : Transition)
    (hd : Distinct s.key s.new) (hp : s.plan.MovesBy place move) (hb : move.ease.bounded = true)
    {R : IVec → IVec → Prop} (hR : Kept R) {o₁ n₁ o₂ n₂ : α} (h₁ : (o₁, n₁) ∈ s.join.update)
    (h₂ : (o₂, n₂) ∈ s.join.update) (hold : R (place o₁) (place o₂))
    (hnew : R (place n₁) (place n₂)) (t : Nat) :
    R ((s.frame n₁ t).stand (place n₁)) ((s.frame n₂ t).stand (place n₂)) := by
  obtain ⟨key, old, new, plan, stages⟩ := s
  cases stages with
  | none =>
    exact Motion.ofJoin_within_together key place old new plan move hd hp hb hR h₁ h₂ hold hnew t
  | some g =>
    exact Motion.staged_within_together key place old new plan move g.enterFrom g.levels g.rank
      hd hp hb hR h₁ h₂ hold hnew t

/-- **Two kept boxes a gap `g` apart in both pictures are a gap `g` apart at every moment.** With
`g` the width of the first box and the gap of the layout, the two boxes never touch. -/
theorem leftOf [BEq κ] [LawfulBEq κ] (s : Step α κ) (place : α → IVec) (move : Transition)
    (hd : Distinct s.key s.new) (hp : s.plan.MovesBy place move) (hb : move.ease.bounded = true)
    (g : Int) {o₁ n₁ o₂ n₂ : α} (h₁ : (o₁, n₁) ∈ s.join.update) (h₂ : (o₂, n₂) ∈ s.join.update)
    (hold : (place o₁).x + g ≤ (place o₂).x) (hnew : (place n₁).x + g ≤ (place n₂).x) (t : Nat) :
    ((s.frame n₁ t).stand (place n₁)).x + g ≤ ((s.frame n₂ t).stand (place n₂)).x :=
  s.together (R := fun a b => a.x + g ≤ b.x) place move hd hp hb (Kept.leftOf g) h₁ h₂ hold
    hnew t

/-- **Two kept boxes a gap `g` apart, one above the other, in both pictures are so at every
moment.** -/
theorem above [BEq κ] [LawfulBEq κ] (s : Step α κ) (place : α → IVec) (move : Transition)
    (hd : Distinct s.key s.new) (hp : s.plan.MovesBy place move) (hb : move.ease.bounded = true)
    (g : Int) {o₁ n₁ o₂ n₂ : α} (h₁ : (o₁, n₁) ∈ s.join.update) (h₂ : (o₂, n₂) ∈ s.join.update)
    (hold : (place o₁).y + g ≤ (place o₂).y) (hnew : (place n₁).y + g ≤ (place n₂).y) (t : Nat) :
    ((s.frame n₁ t).stand (place n₁)).y + g ≤ ((s.frame n₂ t).stand (place n₂)).y :=
  s.together (R := fun a b => a.y + g ≤ b.y) place move hd hp hb (Kept.above g) h₁ h₂ hold
    hnew t

/-! ## A step in stages -/

/-- **A step in stages needs no cut where its stages have room**: the new things enter by the
step's end, each has a level below the number of levels, and each entrance that the plan gives
fits in a thousand. The tracks of the step are then the staged tracks as they are. -/
theorem motion_of_stages [BEq κ] (s : Step α κ) {g : Stages α} (hg : s.stages = some g)
    (he : g.enterFrom ≤ 1000) (hl : ∀ n ∈ s.join.enter, g.rank n < g.levels)
    (ht : ∀ n ∈ s.join.enter, ∀ c ∈ s.plan.enter n, c.2.delay + c.2.duration ≤ 1000) :
    s.motion = Motion.staged s.key s.join s.plan g.enterFrom g.levels g.rank :=
  (s.motion_of_some hg).trans
    (Motion.staged_within s.key s.join s.plan g.enterFrom g.levels g.rank he hl ht)

/-- **A step in stages respects an order in time**, on the terms of `Motion.staged_respects`: the
plan's first stage respects the order, the order puts no new thing before a thing of the first
stage, it follows the rank among the new things, and each entrance fits in a thousand. -/
theorem respects [BEq κ] (s : Step α κ) {g : Stages α} (hg : s.stages = some g)
    (before : κ → κ → Prop) (h1 : (Motion.firstStage s.key s.join s.plan).Respects before)
    (h2 : ∀ n ∈ s.join.enter, ∀ tr0 ∈ Motion.firstStage s.key s.join s.plan,
      ¬ before (s.key n) tr0.key)
    (hr : ∀ n ∈ s.join.enter, ∀ n' ∈ s.join.enter, before (s.key n) (s.key n') →
      g.rank n < g.rank n')
    (ht : ∀ n ∈ s.join.enter, ∀ c ∈ s.plan.enter n, c.2.delay + c.2.duration ≤ 1000) :
    s.motion.Respects before := by
  rw [s.motion_of_some hg]
  exact Motion.within_respects before _
    (Motion.staged_respects before s.key s.join s.plan g.enterFrom g.levels g.rank h1 h2 hr ht)

/-- **The order of a step in stages.** Let `before` be an order of keys in which nothing is
before an old thing, and which the rank follows among the new things. Then no thing starts
before a thing that is before it is over. With `before` "an old thing, then a new one" the kept
things and the things that leave are over before a new thing starts. With `before` the edges of
a tree and the rank the depth, no child appears before its parent is whole. Each entrance that
the plan gives fits in a thousand. -/
theorem order [BEq κ] [LawfulBEq κ] (s : Step α κ) {g : Stages α} (hg : s.stages = some g)
    (before : κ → κ → Prop) (h0 : ∀ k, ∀ a ∈ s.old, ¬ before k (s.key a))
    (hr : ∀ n ∈ s.join.enter, ∀ n' ∈ s.join.enter, before (s.key n) (s.key n') →
      g.rank n < g.rank n')
    (ht : ∀ n ∈ s.join.enter, ∀ c ∈ s.plan.enter n, c.2.delay + c.2.duration ≤ 1000) :
    s.motion.Respects before :=
  s.respects hg before
    (fun a _ b hb hab => by
      obtain ⟨o, ho, hk⟩ := Motion.firstStage_key s.key s.old s.new s.plan hb
      rw [← hk] at hab
      exact absurd hab (h0 a.key o ho))
    (fun n _ tr0 h0' hab => by
      obtain ⟨o, ho, hk⟩ := Motion.firstStage_key s.key s.old s.new s.plan h0'
      rw [← hk] at hab
      exact h0 (s.key n) o ho hab)
    hr ht

/-- **The kept things are at rest when the new things enter.** In a step in stages, with a plan
that settles and is proper, each kept thing is drawn as the still picture has it from the moment
`enterFrom` on, whatever its shape: no new thing appears beside a kept thing that is still on its
way. It asks nothing of the levels or of the entrances. -/
theorem kept_rest [BEq κ] [LawfulBEq κ] (s : Step α κ) {g : Stages α} (hg : s.stages = some g)
    (hs : s.plan.Settles) (hp : s.plan.Proper) {o n : α} (hu : (o, n) ∈ s.join.update) {t : Nat}
    (ht : g.enterFrom ≤ t) : (s.frame n t).AtRest := by
  obtain ⟨ho, hn, hon⟩ := mem_update s.key s.old s.new hu
  refine Motion.frame_atRest fun q hq => ?_
  obtain ⟨tr, htr, hkey, rfl⟩ := Motion.mem_posesOf _ _ _ hq
  rw [s.motion_of_some hg] at htr
  obtain ⟨tr1, h1, rfl⟩ := Motion.mem_within _ htr
  have hkey' : tr1.key = s.key n := beq_iff_eq.mp hkey
  have hprop := Motion.staged_proper s.key s.join s.plan g.enterFrom g.levels g.rank hp tr1 h1
  rcases (Motion.mem_staged s.key s.join s.plan g.enterFrom g.levels g.rank).mp h1 with
    ⟨tr0, h0, rfl⟩ | ⟨n', hn', hm⟩
  · have hend := Motion.staged_first_ends s.key s.join s.plan g.enterFrom tr0 h0
    rcases Motion.staged_settles s.key s.old s.new s.plan g.enterFrom g.levels g.rank hs _ h1 with
      hst | hne
    · exact Track.atRest_of_done _ t
        ⟨hprop, Nat.le_trans (Transition.within_end_le _) (Nat.le_trans hend ht)⟩ hst
    · exact absurd hkey'.symm (hne n hn)
  · obtain ⟨c, _, rfl⟩ :=
      (Motion.mem_stagedOf s.key s.plan g.enterFrom g.levels g.rank n').mp hm
    exact absurd (hon.trans hkey'.symm) (((mem_enter s.key s.old s.new).mp hn').2 o ho)

/-! ## Across an interruption -/

/-- **The step that interrupts ends on the next picture.** With a plan that settles and is
proper, and a proper easing in every `settle`, each thing of the next picture is drawn as the
still picture has it from the step's end on, wherever the step began. -/
theorem interrupt_frame_end [BEq κ] [LawfulBEq κ] (s : Step α κ) (t : Nat) (newer : List α)
    {settle : α → Transition} (shape : α → Option (List ICubic)) (p : Plan α) (hs : p.Settles)
    (hp : p.Proper) (hset : ∀ n, (settle n).ease.Proper) {n : α} (hn : n ∈ newer) {u : Nat}
    (hu : 1000 ≤ u) : ((s.interrupt t newer settle shape p).frame n u).AtRest :=
  (s.interrupt t newer settle shape p).frame_end
    (Plan.resume_settles (fun a => s.frame a t) settle shape hs)
    (Plan.resume_proper (fun a => s.frame a t) shape hp hset) hn hu

/-- **The last moment of the step that interrupts is the next picture**: its things and no
other, each with a frame at rest. -/
theorem interrupt_sample_end [BEq κ] [LawfulBEq κ] (s : Step α κ) (t : Nat) (newer : List α)
    {settle : α → Transition} (shape : α → Option (List ICubic)) (p : Plan α) (hs : p.Settles)
    (hp : p.Proper) (hset : ∀ n, (settle n).ease.Proper) {u : Nat} (hu : 1000 ≤ u) :
    ((s.interrupt t newer settle shape p).sample u).map Prod.fst = newer ∧
      ∀ x ∈ (s.interrupt t newer settle shape p).sample u, x.2.AtRest :=
  (s.interrupt t newer settle shape p).sample_end
    (Plan.resume_settles (fun a => s.frame a t) settle shape hs)
    (Plan.resume_proper (fun a => s.frame a t) shape hp hset) hu

/-- **The last moment of the step that interrupts is the next picture at rest**, with a plan that
also changes no shape of a thing that stays, where no thing's own shape is given: each thing of
the next picture is the still picture itself. So the step after it may interrupt it at its end
as it would any step (`Step.interrupt_of_rest`). -/
theorem interrupt_sample_end_rest [BEq κ] [LawfulBEq κ] (s : Step α κ) (t : Nat)
    (newer : List α) {settle : α → Transition} (p : Plan α) (hs : p.Settles) (hp : p.Proper)
    (hk : p.KeepsShapes) (hset : ∀ n, (settle n).ease.Proper) {u : Nat} (hu : 1000 ≤ u) :
    (s.interrupt t newer settle (plan := p)).sample u = newer.map fun n => (n, Frame.rest) :=
  (s.interrupt t newer settle (plan := p)).sample_end_rest
    (Plan.resume_settles (fun a => s.frame a t) settle (fun _ => none) hs)
    (Plan.resume_proper (fun a => s.frame a t) (fun _ => none) hp hset)
    (Plan.resume_keepsShapes (fun a => s.frame a t) settle (fun _ => rfl) hk) hu

/-- **The step that interrupts has one track for each property**, where the plan has one change
for each property and the keys of both pictures of the step before, and of the next picture, are
distinct. -/
theorem interrupt_single [BEq κ] [LawfulBEq κ] (s : Step α κ) (t : Nat) (newer : List α)
    (settle : α → Transition) (shape : α → Option (List ICubic)) (p : Plan α) (hp : p.Single)
    (ho : Distinct s.key s.old) (hn : Distinct s.key s.new) (hd : Distinct s.key newer) :
    (s.interrupt t newer settle shape p).motion.Single :=
  (s.interrupt t newer settle shape p).single
    (Plan.resume_single (fun a => s.frame a t) settle shape hp) (s.drawn_distinct ho hn t) hd

/-- **Nothing jumps.** At the first moment of the step that interrupts, a kept thing shows
whatever its old thing showed at the interruption: its size, its line and its opacity in every
case, its place where the plan does not move it, and its shape where the plan changes the shape
or the thing's own shape is given. The keys of the next picture are distinct, and each
transition of the thing reads `0` at the moment `0` (`Transition.at_zero`). `nothing_moves` is
the law of a thing that the plan moves. -/
theorem nothing_jumps [BEq κ] [LawfulBEq κ] (s : Step α κ) (t : Nat) (newer : List α)
    (settle : α → Transition) (shape : α → Option (List ICubic)) (p : Plan α)
    (hd : Distinct s.key newer) {o n : α}
    (hu : (o, n) ∈ (s.interrupt t newer settle shape p).join.update)
    (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0) (hs : (settle n).at 0 = 0) {q : Pose}
    (hq : (s.frame o t).Shows q)
    (hp : q.property = .place → ∀ c ∈ p.kept o n, c.1.property ≠ .place)
    (hsh : q.property = .shape → (∃ c ∈ p.kept o n, c.1.property = .shape) ∨ shape n ≠ none) :
    ((s.interrupt t newer settle shape p).frame n 0).Shows q := by
  show ((Motion.ofJoin s.key (Scene.join s.key (s.drawn t) newer)
    (p.resume (fun a => s.frame a t) settle shape)).within.frame (s.key n) 0).Shows q
  rw [Motion.within_frame_zero]
  exact Motion.resume_kept_shows s.key (s.drawn t) newer p (fun a => s.frame a t) settle shape hd
    hu hk hs hq hp hsh

/-- **Nothing moves.** At the first moment of the step that interrupts, a kept thing that the
plan moves stands where its old thing stood at the interruption. The plan moves the thing by
`Plan.moving`, and may give it more changes that are not of its place. -/
theorem nothing_moves [BEq κ] [LawfulBEq κ] (s : Step α κ) (t : Nat) (newer : List α)
    (settle : α → Transition) (shape : α → Option (List ICubic)) (p : Plan α)
    (hd : Distinct s.key newer) {o n : α}
    (hu : (o, n) ∈ (s.interrupt t newer settle shape p).join.update)
    (hk : ∀ c ∈ p.kept o n, c.2.at 0 = 0) (hs : (settle n).at 0 = 0) (place : α → IVec)
    (move : Transition) {more : List (Change × Transition)}
    (hkept : p.kept o n = Plan.moving place move o n ++ more)
    (hm : ∀ c ∈ more, c.1.property ≠ .place) (hdm : (more.map fun c => c.1.property).Nodup) :
    ((s.interrupt t newer settle shape p).frame n 0).stand (place n) =
      (s.frame o t).stand (place o) := by
  show place n + ((Motion.ofJoin s.key (Scene.join s.key (s.drawn t) newer)
    (p.resume (fun a => s.frame a t) settle shape)).within.frame (s.key n) 0).shift =
      place o + (s.frame o t).shift
  rw [Motion.within_frame_zero]
  exact Motion.resume_kept_place s.key (s.drawn t) newer p (fun a => s.frame a t) settle shape hd
    hu hk hs place move hkept hm hdm

/-- **A thing that leaves goes on from where it is seen.** At the first moment of the step that
interrupts, a thing that leaves shows whatever it showed at the interruption: its size, its
line, its opacity and its shape in every case, and its place where the plan does not move it.
The keys of the things drawn at the interruption are distinct (`Step.drawn_distinct`). -/
theorem leaving_goes_on [BEq κ] [LawfulBEq κ] (s : Step α κ) (t : Nat) (newer : List α)
    (settle : α → Transition) (shape : α → Option (List ICubic)) (p : Plan α)
    (hd : Distinct s.key (s.drawn t)) {o : α}
    (ho : o ∈ (s.interrupt t newer settle shape p).join.exit)
    (hl : ∀ c ∈ p.leave o, c.2.at 0 = 0) {q : Pose} (hq : (s.frame o t).Shows q)
    (hp : q.property = .place → ∀ c ∈ p.leave o, c.1.property ≠ .place) :
    ((s.interrupt t newer settle shape p).frame o 0).Shows q := by
  show ((Motion.ofJoin s.key (Scene.join s.key (s.drawn t) newer)
    (p.resume (fun a => s.frame a t) settle shape)).within.frame (s.key o) 0).Shows q
  rw [Motion.within_frame_zero]
  exact Motion.resume_leaving_shows s.key (s.drawn t) newer p (fun a => s.frame a t) settle shape
    hd ho hl hq hp

/-- **An interruption at the step's end is an ordinary step.** Where the step was over, the step
that interrupts has the tracks of `Step.next`: the step from the new picture to the next under
the plan as it is written. The plan of the step that is over settles, is proper and changes no
shape of a thing that stays, so each thing of its new picture is seen as the still picture has
it. The plan of the next step is written from rest. -/
theorem interrupt_of_rest [BEq κ] [LawfulBEq κ] (s : Step α κ) {t : Nat} (ht : 1000 ≤ t)
    (newer : List α) (settle : α → Transition) (shape : α → Option (List ICubic)) (p : Plan α)
    (hs : s.plan.Settles) (hp : s.plan.Proper) (hk : s.plan.KeepsShapes) (hr : p.FromRest) :
    (s.interrupt t newer settle shape p).motion = (s.next newer p).motion := by
  have hseen : ∀ o ∈ s.new, s.frame o t = Frame.rest := fun o ho =>
    s.frame_end_rest hs hp hk ho ht
  show (Motion.ofJoin s.key (Scene.join s.key (s.drawn t) newer)
      (p.resume (fun a => s.frame a t) settle shape)).within =
    (Motion.ofJoin s.key (Scene.join s.key s.new newer) p).within
  rw [s.drawn_end ht]
  refine congrArg Motion.within (Motion.ofJoin_congr s.key _ (fun x hx => ?_) (fun _ _ => rfl)
    (fun o ho => ?_))
  · have ho : x.1 ∈ s.new := (mem_update s.key s.new newer (o := x.1) (n := x.2) hx).1
    show (s.frame x.1 t).resume (settle x.2) (shape x.2) (p.kept x.1 x.2) = p.kept x.1 x.2
    rw [hseen x.1 ho]
    exact Frame.resume_of_rest Frame.rest_atRest rfl (settle x.2) (shape x.2) (hr.1 x.1 x.2)
  · have ho' : o ∈ s.new := ((mem_exit s.key s.new newer).mp ho).1
    show (s.frame o t).leaveFrom (p.leave o) = p.leave o
    rw [hseen o ho']
    exact Frame.leaveFrom_of_rest Frame.rest_atRest rfl (hr.2 o)

/-- **An interruption at the step's end shows what an ordinary step shows**: the same things
with the same frames, at every moment. -/
theorem interrupt_of_rest_sample [BEq κ] [LawfulBEq κ] (s : Step α κ) {t : Nat} (ht : 1000 ≤ t)
    (newer : List α) (settle : α → Transition) (shape : α → Option (List ICubic)) (p : Plan α)
    (hs : s.plan.Settles) (hp : s.plan.Proper) (hk : s.plan.KeepsShapes) (hr : p.FromRest)
    (u : Nat) :
    (s.interrupt t newer settle shape p).sample u = (s.next newer p).sample u := by
  have hm := s.interrupt_of_rest ht newer settle shape p hs hp hk hr
  show ((Scene.join s.key (s.drawn t) newer).drawn newer u).map
      (fun a => (a, (s.interrupt t newer settle shape p).motion.frame (s.key a) u)) =
    ((Scene.join s.key s.new newer).drawn newer u).map
      (fun a => (a, (s.next newer p).motion.frame (s.key a) u))
  rw [hm, s.drawn_end ht]

end Step

/-! ## Controls

A thing is a key and a place along one axis. -/

-- A control of `Step.frame_end_rest`, which asks that the plan changes no shape of a thing that
-- stays. A kept edge changes its shape. At the step's end its frame is at rest, and it is not
-- the still picture: it has the shape that its track gave it.
#guard
  let shape : List ICubic := [⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨9, 9⟩, ⟨9, 9⟩⟩]
  let p : Plan Nat := ⟨fun _ _ => [(.morph [] shape, {})], fun _ => [], fun _ => []⟩
  let s : Step Nat Nat := { key := id, old := [1], new := [1], plan := p }
  decide (s.frame 1 1000).AtRest && s.frame 1 1000 != Frame.rest &&
    (s.frame 1 1000).shape == some shape

-- Why `Step.interrupt_of_rest` is of the things of the new picture, and is not
-- `Plan.resume_of_rest`, which asks that every thing is seen at rest. A thing that has left is
-- not: at the step's end the thing `2` is seen with no opacity, as its leaving left it. The
-- thing `1`, of the new picture, is the still picture.
#guard
  let p : Plan Nat := ⟨fun _ _ => [], fun _ => [], fun _ => [(.fade 1000 0, {})]⟩
  let s : Step Nat Nat := { key := id, old := [1, 2], new := [1], plan := p }
  (s.frame 2 1000).shown == 0 && !decide (s.frame 2 1000).AtRest && s.frame 1 1000 == Frame.rest

-- A control of `Step.interrupt_of_rest`, which asks that the next plan is written from rest. A
-- plan that fades a kept thing in from nothing is not: the step that interrupts starts the fade
-- where the thing is seen, at its whole opacity, and the ordinary step starts it at nothing.
#guard
  let p : Plan Nat := ⟨fun _ _ => [(.fade 0 1000, {})], fun _ => [], fun _ => []⟩
  let s : Step Nat Nat := { key := id, old := [1], new := [1], plan := Plan.still }
  ((s.interrupt 1000 [1] (fun _ => {}) (plan := p)).frame 1 0).shown == 1000 &&
    ((s.next [1] p).frame 1 0).shown == 0

-- What is not claimed of a step in stages that interrupts. The thing `1` is seen four off its
-- place and the plan moves it over three thousandths of the step. Timed as the plan says, the
-- step that interrupts starts it where it is seen. In stages that end the first stage by the
-- moment `300`, the move is scaled to nothing, and the thing is on its new place at once.
#guard
  let place : Nat × Int → IVec := fun a => ⟨a.2, 0⟩
  let quick : Plan (Nat × Int) :=
    ⟨Plan.moving place { duration := 3 }, fun _ => [], fun _ => [(.fade 1000 0, {})]⟩
  let s : Step (Nat × Int) Nat :=
    { key := Prod.fst, old := [(1, 0), (2, 0)], new := [(1, 8)],
      plan := ⟨Plan.moving place {}, fun _ => [], fun _ => [(.fade 1000 0, {})]⟩ }
  let r := s.interrupt 500 [(1, 20)] (fun _ => {}) (plan := quick)
  (s.frame (1, 8) 500).shift == ⟨-4, 0⟩ && (r.frame (1, 20) 0).shift == ⟨-16, 0⟩ &&
    ((r.staged 300 1 fun _ => 0).frame (1, 20) 0).shift == ⟨0, 0⟩

end Whatwg.Svg.Scene
