import Whatwg.Svg.Scene.Frame
import Whatwg.Svg.Scene.Stage
import Whatwg.Svg.Scene.Between

/-!
# Whatwg.Svg.Scene.Together

Owner: the kept things of a step keep, at every moment, each relation that both pictures have
(slice S16 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-90).

`Kept.moment` of `Whatwg/Svg/Scene/Between.lean` is a law of `mix` on two pairs of places. A
program has a step, `Motion.ofJoin` of a `Plan` or `Motion.staged`, and reads its frames with
`Motion.frame`. This module joins the two. A program checks its look once: the easing of the
move passes `Easing.bounded`, and every kept thing takes that one timing. Then one theorem says
that a relation that `Kept` names, held by the places of two kept things in both pictures, is
held by where the two stand at every moment.

- `Frame.stand f p` of `Whatwg/Svg/Scene/Frame.lean`: where a thing stands at a frame, its place
  and the frame's shift. The laws here are said of it.
- `Motion.MovesFrom m k a tr`: the thing `k` comes to its place from the step `a` off it, by the
  transition `tr`, and its place changes in no other way. A thing with a track of its place in a
  `Single` motion moves so (`MovesFrom.of_track`). A thing that no track moves comes from
  nothing, by any transition (`MovesFrom.of_still`). A motion held in its step moves the same
  things from the same places (`MovesFrom.within`).
- Where one thing stands. `Motion.stand_of_movesFrom`: at the straight mix from `p + a` to `p`,
  at the eased progress of its transition. `Motion.stand_shift` says it of a track in a `Single`
  motion, and `Motion.stand_still` of a thing that no track moves: it stands at `p`.
- **The law of the module** is `Motion.together`. Two things come to their places by one
  transition, and its easing passes the test. They keep at every moment each kept relation that
  both pictures have. `Motion.together_tracks`, `Motion.together_one_still` and
  `Motion.together_still` are its three plain cases.
- `Plan.MovesBy p place move` of `Whatwg/Svg/Scene/Plan.lean`: the plan moves each kept thing by
  the one transition `move`, and in no other way. A plan whose `kept` is
  `Plan.moving place move` passes (`Plan.movesBy_moving`), and so does such a plan together
  with a plan that changes no place (`Plan.MovesBy.and`).
- The step of a plan. With distinct keys in the new list, every track of a kept thing is a
  change that `kept` gave its pair (`Motion.ofJoin_of_kept` of `Plan.lean`). So a kept thing
  comes to its new place from its old one by `move` (`Motion.ofJoin_movesFrom`), and in a step
  in stages by one transition with the easing of `move` (`Motion.staged_movesFrom`).
  `Motion.ofJoin_together` is the law for the step, `Motion.ofJoin_within_together` for the step
  held inside itself, and `Motion.staged_together` and `Motion.staged_within_together` for a
  step in stages.
- A gap at every moment. Two kept boxes a gap `g` apart in both pictures are a gap `g` apart at
  every moment (`Motion.ofJoin_within_leftOf`, `Motion.staged_leftOf`), and so for one above the
  other (`Motion.ofJoin_within_above`, `Motion.staged_above`).

What the laws of a step ask, and what they do not. They ask for distinct keys in the new list,
for `Plan.MovesBy`, and for an easing that passes the test. They do not ask that the step is
`Single`, and they ask nothing of the keys of the old list, of the plan's `enter` and `leave`,
or of the stages. No track of a new thing or of a thing that leaves has the key of a kept
thing, and of the tracks of a kept thing only those of its place are read.

What this module does not claim. The laws of a step are of two kept things. A kept thing and a
new one, or one that leaves, are a case of `Motion.together` where the other thing has no track
of its place, and no law of a step says it. The relation is one that `Kept` names: a gap along
an axis, a fixed step, and such relations together. "Beside or above" is not one. A size that
grows past its end is `grow_clear` of `Between.lean`. A moment is a whole thousandth of the
step. The times between two of them are `Whatwg/Svg/Geometry/Moment.lean`, and no law here joins
the two. `Plan.MovesBy` is a property of the plan's functions, and a program shows it by how it
builds its plan. No law here shows that a step is `Single`, and none asks for it:
`Motion.single_ofJoin` of `Plan.lean` and `Motion.staged_single` of `Stage.lean` are the laws
for a program that wants it.

What this module holds, and what it cites. It holds `Motion.MovesFrom`, where one thing stands,
the law `Motion.together` and its forms for the step of a plan and for a step in stages. Since
the tidy of slice S16 it is shorter by what three other modules own: `Frame.stand` is in
`Frame.lean`, and `Plan.MovesBy`, `Plan.movesBy_moving`, `Plan.MovesBy.and` and
`Motion.ofJoin_of_kept` are in `Plan.lean`, each under the same name. It cites `Motion.keeping`
of `Plan.lean`, `Motion.staged`, `Motion.mem_staged` and `Track.endBy` of `Stage.lean`, and
`Kept` with `Kept.moment`, `Kept.leftOf` and `Kept.above` of `Between.lean`.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

variable {α κ : Type}

namespace Frame

/-- Where every pose of the place in a list is one shift, the frame under the list stands off
its place by that shift, or where it stood. -/
private theorem shift_under_of_all {s : IVec} : ∀ {ps : List Pose},
    (∀ p ∈ ps, p.property = .place → p = .shift s) → ∀ f : Frame,
      (f.under ps).shift = s ∨ (f.under ps).shift = f.shift
  | [], _, _ => Or.inr rfl
  | p :: ps, h, f => by
    rcases shift_under_of_all (fun r hr => h r (List.mem_cons_of_mem p hr)) (p.onto f) with e | e
    · exact Or.inl e
    · cases p with
      | shift a =>
        have ea : a = s := Pose.shift.inj (h _ List.mem_cons_self rfl)
        exact Or.inl (e.trans ea)
      | grow a => exact Or.inr e
      | reveal a => exact Or.inr e
      | fade a => exact Or.inr e
      | shape a => exact Or.inr e

end Frame

namespace Motion

/-! ## Where one thing stands -/

/-- **The thing `k` comes to its place from the step `a` off it, by the transition `tr`, and its
place changes in no other way.** Every track of `k` that changes the place is the shift from `a`
to nothing by `tr`, and the motion has that track unless `a` is nothing. A thing that no track
moves comes from nothing, by any transition: it stands still whatever the timing. -/
def MovesFrom (m : Motion κ) (k : κ) (a : IVec) (tr : Transition) : Prop :=
  (∀ tr' ∈ m, tr'.key = k → tr'.change.property = .place → tr' = ⟨k, .shift a 0, tr⟩) ∧
    (a = 0 ∨ (⟨k, .shift a 0, tr⟩ : Track κ) ∈ m)

/-- A thing with a track of its place, in a motion where no thing has two tracks of one
property, moves from where the track says, by the track's transition. -/
theorem MovesFrom.of_track {m : Motion κ} (hs : m.Single) {k : κ} {a : IVec} {tr : Transition}
    (htr : (⟨k, .shift a 0, tr⟩ : Track κ) ∈ m) : m.MovesFrom k a tr :=
  ⟨fun tr' htr' hk hp =>
    eq_of_distinct (fun x : Track κ => (x.key, x.change.property)) m hs tr' _ htr' htr (by
      show (tr'.key, tr'.change.property) = (k, Property.place)
      rw [hk, hp]),
    Or.inr htr⟩

/-- A thing that no track moves comes from nothing, by any transition. -/
theorem MovesFrom.of_still {m : Motion κ} {k : κ}
    (h : ∀ tr' ∈ m, tr'.key = k → tr'.change.property ≠ .place) (tr : Transition) :
    m.MovesFrom k 0 tr :=
  ⟨fun tr' htr' hk hp => absurd hp (h tr' htr' hk), Or.inl rfl⟩

/-- **A motion whose transitions are all changed by one rule moves the same things from the
same places**, by the changed transition. -/
theorem MovesFrom.retime {m : Motion κ} {k : κ} {a : IVec} {tr : Transition}
    (h : m.MovesFrom k a tr) (f : Transition → Transition) :
    MovesFrom (m.map fun x => { x with timing := f x.timing }) k a (f tr) := by
  refine ⟨fun tr' htr' hk hp => ?_, h.2.imp id fun hm => ?_⟩
  · obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp htr'
    have e := h.1 tr0 h0 hk hp
    subst e
    rfl
  · exact List.mem_map.mpr ⟨_, hm, rfl⟩

/-- A motion held inside its step moves the same things from the same places, each by its
transition held inside the step. -/
theorem MovesFrom.within {m : Motion κ} {k : κ} {a : IVec} {tr : Transition}
    (h : m.MovesFrom k a tr) : m.within.MovesFrom k a tr.within :=
  h.retime Transition.within

/-- How far off its place a thing that moves from `a` stands: the step from `a` to nothing at
the eased progress of its transition. -/
theorem shift_of_movesFrom [BEq κ] [LawfulBEq κ] {m : Motion κ} {k : κ} {a : IVec}
    {tr : Transition} (h : m.MovesFrom k a tr) (t : Nat) :
    (m.frame k t).shift = ⟨mix a.x 0 (tr.at t), mix a.y 0 (tr.at t)⟩ := by
  have hall : ∀ p ∈ m.posesOf k t, p.property = .place →
      p = .shift ⟨mix a.x 0 (tr.at t), mix a.y 0 (tr.at t)⟩ := by
    intro p hp hprop
    obtain ⟨tr', htr', hk, rfl⟩ := mem_posesOf m k t hp
    rw [Track.at_property] at hprop
    have e := h.1 tr' htr' (beq_iff_eq.mp hk) hprop
    subst e
    rfl
  rcases h.2 with e | hmem
  · rcases Frame.shift_under_of_all hall Frame.rest with e1 | e1
    · exact e1
    · subst e
      exact e1.trans (IVec.ext (mix_self _ _).symm (mix_self _ _).symm)
  · exact (congrArg Frame.shift
      (Frame.under_has (posesOf_of_mem hmem (beq_iff_eq.mpr rfl) t)
        (fun p hp e => hall p hp e) Frame.rest)).symm

/-- **Where a thing that moves stands.** A thing whose place in the new picture is `p`, and that
comes to it from `a` off it, stands at the straight mix from `p + a` to `p` at the eased progress
of its transition. A thing that no track moves stands at `p`. -/
theorem stand_of_movesFrom [BEq κ] [LawfulBEq κ] {m : Motion κ} {k : κ} {a : IVec}
    {tr : Transition} (h : m.MovesFrom k a tr) (p : IVec) (t : Nat) :
    (m.frame k t).stand p = ⟨mix (p + a).x p.x (tr.at t), mix (p + a).y p.y (tr.at t)⟩ := by
  show p + (m.frame k t).shift = _
  rw [shift_of_movesFrom h t]
  exact IVec.ext (mix_add p.x a.x (tr.at t)).symm (mix_add p.y a.y (tr.at t)).symm

/-- **Where a thing with a track of its place stands**, in a motion where no thing has two
tracks of one property: at the straight mix from `p + a` to `p` at the eased progress of the
track. -/
theorem stand_shift [BEq κ] [LawfulBEq κ] {m : Motion κ} (hs : m.Single) {k : κ} {a : IVec}
    {tr : Transition} (htr : (⟨k, .shift a 0, tr⟩ : Track κ) ∈ m) (p : IVec) (t : Nat) :
    (m.frame k t).stand p = ⟨mix (p + a).x p.x (tr.at t), mix (p + a).y p.y (tr.at t)⟩ :=
  stand_of_movesFrom (MovesFrom.of_track hs htr) p t

/-- The same for a shift that does not end on the place: the thing stands at the straight mix
from `p + a` to `p + b`. -/
theorem stand_shift_to [BEq κ] [LawfulBEq κ] {m : Motion κ} (hs : m.Single) {k : κ} {a b : IVec}
    {tr : Transition} (htr : (⟨k, .shift a b, tr⟩ : Track κ) ∈ m) (p : IVec) (t : Nat) :
    (m.frame k t).stand p =
      ⟨mix (p + a).x (p + b).x (tr.at t), mix (p + a).y (p + b).y (tr.at t)⟩ := by
  show p + (m.frame k t).shift = _
  rw [frame_shift hs htr t]
  refine IVec.ext ?_ ?_
  · show p.x + mix a.x b.x (tr.at t) = mix (p.x + a.x) (p.x + b.x) (tr.at t)
    rw [Int.add_comm p.x a.x, Int.add_comm p.x b.x, mix_add_right, Int.add_comm]
  · show p.y + mix a.y b.y (tr.at t) = mix (p.y + a.y) (p.y + b.y) (tr.at t)
    rw [Int.add_comm p.y a.y, Int.add_comm p.y b.y, mix_add_right, Int.add_comm]

/-- **A thing that no track moves stands at its place at every moment**, whatever its other
tracks do. -/
theorem stand_still [BEq κ] [LawfulBEq κ] {m : Motion κ} {k : κ}
    (h : ∀ tr ∈ m, tr.key = k → tr.change.property ≠ .place) (p : IVec) (t : Nat) :
    (m.frame k t).stand p = p := by
  have e : (m.frame k t).shift = 0 := Frame.shift_under_of_no (fun q hq => by
    obtain ⟨tr, htr, hk, rfl⟩ := mem_posesOf m k t hq
    rw [Track.at_property]
    exact h tr htr (beq_iff_eq.mp hk)) Frame.rest
  show p + (m.frame k t).shift = p
  rw [e]
  exact IVec.add_zero p

/-! ## Together -/

/-- **The law of the module: things that move together keep what both pictures have.** Two
things come to their places by one transition, and its easing passes the test
`Easing.bounded`. Where their places have a kept relation in the old picture and in the new
one, where they stand has it at every moment. A thing that no track moves is one of them: it
comes from nothing, by any transition. -/
theorem together [BEq κ] [LawfulBEq κ] {m : Motion κ} {k₁ k₂ : κ} {a₁ a₂ : IVec}
    {tr : Transition} (h₁ : m.MovesFrom k₁ a₁ tr) (h₂ : m.MovesFrom k₂ a₂ tr)
    (hb : tr.ease.bounded = true) {R : IVec → IVec → Prop} (hR : Kept R) {p₁ p₂ : IVec}
    (hold : R (p₁ + a₁) (p₂ + a₂)) (hnew : R p₁ p₂) (t : Nat) :
    R ((m.frame k₁ t).stand p₁) ((m.frame k₂ t).stand p₂) := by
  rw [stand_of_movesFrom h₁, stand_of_movesFrom h₂]
  exact hR.moment tr t hb hold hnew

/-- The same law with the two places of each thing: `x` in the old picture and `y` in the new
one. -/
theorem together_between [BEq κ] [LawfulBEq κ] {m : Motion κ} {k₁ k₂ : κ} {x₁ y₁ x₂ y₂ : IVec}
    {tr : Transition} (h₁ : m.MovesFrom k₁ (x₁ - y₁) tr) (h₂ : m.MovesFrom k₂ (x₂ - y₂) tr)
    (hb : tr.ease.bounded = true) {R : IVec → IVec → Prop} (hR : Kept R) (hold : R x₁ x₂)
    (hnew : R y₁ y₂) (t : Nat) : R ((m.frame k₁ t).stand y₁) ((m.frame k₂ t).stand y₂) := by
  have e₁ : y₁ + (x₁ - y₁) = x₁ := (IVec.add_comm _ _).trans (IVec.sub_add_cancel x₁ y₁)
  have e₂ : y₂ + (x₂ - y₂) = x₂ := (IVec.add_comm _ _).trans (IVec.sub_add_cancel x₂ y₂)
  refine together h₁ h₂ hb hR ?_ hnew t
  rw [e₁, e₂]
  exact hold

/-- **Two things with tracks of their places, by one transition.** In a motion where no thing
has two tracks of one property, two things that shift to their places by one transition whose
easing passes the test keep, at every moment, each kept relation that both pictures have. -/
theorem together_tracks [BEq κ] [LawfulBEq κ] {m : Motion κ} (hs : m.Single) {k₁ k₂ : κ}
    {a₁ a₂ : IVec} {tr : Transition} (h₁ : (⟨k₁, .shift a₁ 0, tr⟩ : Track κ) ∈ m)
    (h₂ : (⟨k₂, .shift a₂ 0, tr⟩ : Track κ) ∈ m) (hb : tr.ease.bounded = true)
    {R : IVec → IVec → Prop} (hR : Kept R) {p₁ p₂ : IVec} (hold : R (p₁ + a₁) (p₂ + a₂))
    (hnew : R p₁ p₂) (t : Nat) : R ((m.frame k₁ t).stand p₁) ((m.frame k₂ t).stand p₂) :=
  together (MovesFrom.of_track hs h₁) (MovesFrom.of_track hs h₂) hb hR hold hnew t

/-- **One thing moves and the other stands still.** The first has a track of its place, and no
track moves the second. They keep at every moment each kept relation that both pictures have,
where the easing of the one transition passes the test. -/
theorem together_one_still [BEq κ] [LawfulBEq κ] {m : Motion κ} (hs : m.Single) {k₁ k₂ : κ}
    {a₁ : IVec} {tr : Transition} (h₁ : (⟨k₁, .shift a₁ 0, tr⟩ : Track κ) ∈ m)
    (h₂ : ∀ tr' ∈ m, tr'.key = k₂ → tr'.change.property ≠ .place)
    (hb : tr.ease.bounded = true) {R : IVec → IVec → Prop} (hR : Kept R) {p₁ p₂ : IVec}
    (hold : R (p₁ + a₁) p₂) (hnew : R p₁ p₂) (t : Nat) :
    R ((m.frame k₁ t).stand p₁) ((m.frame k₂ t).stand p₂) := by
  refine together (MovesFrom.of_track hs h₁) (MovesFrom.of_still h₂ tr) hb hR ?_ hnew t
  rw [IVec.add_zero]
  exact hold

/-- **Two things that no track moves keep what the new picture has**, at every moment and with
no premise on any easing: both stand at their places. -/
theorem together_still [BEq κ] [LawfulBEq κ] {m : Motion κ} {k₁ k₂ : κ}
    (h₁ : ∀ tr' ∈ m, tr'.key = k₁ → tr'.change.property ≠ .place)
    (h₂ : ∀ tr' ∈ m, tr'.key = k₂ → tr'.change.property ≠ .place)
    {R : IVec → IVec → Prop} {p₁ p₂ : IVec} (hnew : R p₁ p₂) (t : Nat) :
    R ((m.frame k₁ t).stand p₁) ((m.frame k₂ t).stand p₂) := by
  rw [stand_still h₁, stand_still h₂]
  exact hnew

end Motion

/-! ## The step of a plan -/

namespace Motion

/-- The track of a kept thing whose place changed is one of the tracks of the kept things, in
a plan that moves each kept thing by `move`. -/
private theorem keeping_has (key : α → κ) (place : α → IVec) (j : Join α) (p : Plan α)
    (move : Transition) (hp : p.MovesBy place move) {o n : α} (hu : (o, n) ∈ j.update)
    (hne : place o ≠ place n) :
    (⟨key n, .shift (place o - place n) 0, move⟩ : Track κ) ∈ keeping key j p := by
  have hc : (Change.shift (place o - place n) 0, move) ∈ p.kept o n :=
    (hp o n _ rfl).mpr (by
      rw [Plan.moving_of_ne place move hne]
      exact List.mem_singleton.mpr rfl)
  exact List.mem_flatMap.mpr ⟨(o, n), hu, mem_tracks.mpr ⟨_, hc, rfl⟩⟩

/-- **A kept thing of a step comes to its new place from its old one, by `move`.** The plan
moves each kept thing by `move`, and the keys of the new list are distinct. Nothing is asked of
what the plan gives the new things and the things that leave, and the step need not be
`Single`. -/
theorem ofJoin_movesFrom [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec)
    (old new : List α) (p : Plan α) (move : Transition) (hd : Distinct key new)
    (hp : p.MovesBy place move) {o n : α} (hu : (o, n) ∈ (join key old new).update) :
    (ofJoin key (join key old new) p).MovesFrom (key n) (place o - place n) move := by
  refine ⟨fun tr htr hk hprop => ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := ofJoin_of_kept key old new p hd hu htr hk
    have e := Plan.mem_moving place move ((hp o n c hprop).mp hc)
    subst e
    rfl
  · rcases Decidable.em (place o = place n) with e | e
    · refine Or.inl ?_
      rw [e]
      exact IVec.sub_self _
    · exact Or.inr (List.mem_append_left _ (List.mem_append_left _
        (keeping_has key place (join key old new) p move hp hu e)))

/-- The transition of a track retimed by `Track.endBy`. -/
private def endByT (budget finish : Nat) (tr : Transition) : Transition :=
  if finish ≤ budget then tr
  else { tr with delay := tr.delay * budget / finish, duration := tr.duration * budget / finish }

/-- A retimed track is the track with its transition retimed. -/
private theorem endBy_eq (budget finish : Nat) (tr : Track κ) :
    tr.endBy budget finish = { tr with timing := endByT budget finish tr.timing } := by
  unfold Track.endBy endByT
  rcases Decidable.em (finish ≤ budget) with h | h
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- A retimed transition keeps its easing. -/
private theorem endByT_ease (budget finish : Nat) (tr : Transition) :
    (endByT budget finish tr).ease = tr.ease := by
  unfold endByT
  rcases Decidable.em (finish ≤ budget) with h | h
  · rw [if_pos h]
  · rw [if_neg h]

/-- **The kept things of a staged step come to their new places by one transition, with the
easing of `move`.** The first stage is retimed with one budget and one finish, so two tracks
that had one transition have one after, and the easing is not changed. -/
theorem staged_movesFrom [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec)
    (old new : List α) (p : Plan α) (move : Transition) (enterFrom levels : Nat) (rank : α → Nat)
    (hd : Distinct key new) (hp : p.MovesBy place move) :
    ∃ tr : Transition, tr.ease = move.ease ∧ ∀ {o n : α}, (o, n) ∈ (join key old new).update →
      (staged key (join key old new) p enterFrom levels rank).MovesFrom (key n)
        (place o - place n) tr := by
  refine ⟨endByT enterFrom (firstStage key (join key old new) p).finish move,
    endByT_ease _ _ _, fun {o n} hu => ⟨fun tr htr hk hprop => ?_, ?_⟩⟩
  · rcases (mem_staged key (join key old new) p enterFrom levels rank).mp htr with
      ⟨tr0, h0, rfl⟩ | ⟨n', hn', hm⟩
    · rw [endBy_eq] at hk hprop ⊢
      have h0' : tr0 ∈ keeping key (join key old new) p ++ leaving key (join key old new) p := h0
      have h1 : tr0 ∈ ofJoin key (join key old new) p := by
        rcases List.mem_append.mp h0' with hkp | hlv
        · exact List.mem_append_left _ (List.mem_append_left _ hkp)
        · exact List.mem_append_right _ hlv
      have e := (ofJoin_movesFrom key place old new p move hd hp hu).1 tr0 h1 hk hprop
      subst e
      rfl
    · obtain ⟨c, _, rfl⟩ := (mem_stagedOf key p enterFrom levels rank n').mp hm
      obtain ⟨ho, _, hon⟩ := mem_update key old new hu
      exact absurd (hon.trans hk.symm) (((mem_enter key old new).mp hn').2 o ho)
  · rcases Decidable.em (place o = place n) with e | e
    · refine Or.inl ?_
      rw [e]
      exact IVec.sub_self _
    · refine Or.inr ?_
      have h := (mem_staged key (join key old new) p enterFrom levels rank).mpr (Or.inl
        ⟨_, List.mem_append_left _ (keeping_has key place (join key old new) p move hp hu e),
          rfl⟩)
      rw [endBy_eq] at h
      exact h

/-! ### Every moment of a step -/

/-- **A relation of the places of two kept things in both pictures holds of where they stand at
every moment of the step.** The step is `Motion.ofJoin` of a plan that moves each kept thing by
the one transition `move`, whose easing passes the test `Easing.bounded`, and the keys of the
new list are distinct. For two kept pairs and a kept relation `R`: where the two old places have
`R` and the two new places have `R`, where the two things stand has `R` at every moment. -/
theorem ofJoin_together [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec) (old new : List α)
    (p : Plan α) (move : Transition) (hd : Distinct key new) (hp : p.MovesBy place move)
    (hb : move.ease.bounded = true) {R : IVec → IVec → Prop} (hR : Kept R) {o₁ n₁ o₂ n₂ : α}
    (h₁ : (o₁, n₁) ∈ (join key old new).update) (h₂ : (o₂, n₂) ∈ (join key old new).update)
    (hold : R (place o₁) (place o₂)) (hnew : R (place n₁) (place n₂)) (t : Nat) :
    R (((ofJoin key (join key old new) p).frame (key n₁) t).stand (place n₁))
      (((ofJoin key (join key old new) p).frame (key n₂) t).stand (place n₂)) :=
  together_between (ofJoin_movesFrom key place old new p move hd hp h₁)
    (ofJoin_movesFrom key place old new p move hd hp h₂) hb hR hold hnew t

/-- **The same law for the step held inside itself**, as a reader draws it: the cut at the
step's end changes no easing. -/
theorem ofJoin_within_together [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec)
    (old new : List α) (p : Plan α) (move : Transition) (hd : Distinct key new)
    (hp : p.MovesBy place move) (hb : move.ease.bounded = true) {R : IVec → IVec → Prop}
    (hR : Kept R) {o₁ n₁ o₂ n₂ : α} (h₁ : (o₁, n₁) ∈ (join key old new).update)
    (h₂ : (o₂, n₂) ∈ (join key old new).update) (hold : R (place o₁) (place o₂))
    (hnew : R (place n₁) (place n₂)) (t : Nat) :
    R (((ofJoin key (join key old new) p).within.frame (key n₁) t).stand (place n₁))
      (((ofJoin key (join key old new) p).within.frame (key n₂) t).stand (place n₂)) :=
  together_between (ofJoin_movesFrom key place old new p move hd hp h₁).within
    (ofJoin_movesFrom key place old new p move hd hp h₂).within hb hR hold hnew t

/-- **The same law for a step in stages.** The kept things of `Motion.staged` are retimed
together, so they still take one transition, with the easing of `move`. Nothing is asked of
`enterFrom`, of the levels or of the ranks. -/
theorem staged_together [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec) (old new : List α)
    (p : Plan α) (move : Transition) (enterFrom levels : Nat) (rank : α → Nat)
    (hd : Distinct key new) (hp : p.MovesBy place move) (hb : move.ease.bounded = true)
    {R : IVec → IVec → Prop} (hR : Kept R) {o₁ n₁ o₂ n₂ : α}
    (h₁ : (o₁, n₁) ∈ (join key old new).update) (h₂ : (o₂, n₂) ∈ (join key old new).update)
    (hold : R (place o₁) (place o₂)) (hnew : R (place n₁) (place n₂)) (t : Nat) :
    R (((staged key (join key old new) p enterFrom levels rank).frame (key n₁) t).stand
        (place n₁))
      (((staged key (join key old new) p enterFrom levels rank).frame (key n₂) t).stand
        (place n₂)) := by
  obtain ⟨tr, he, hc⟩ := staged_movesFrom key place old new p move enterFrom levels rank hd hp
  exact together_between (hc h₁) (hc h₂) (by rw [he]; exact hb) hR hold hnew t

/-- **The same law for a step in stages, held inside itself.** -/
theorem staged_within_together [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec)
    (old new : List α) (p : Plan α) (move : Transition) (enterFrom levels : Nat) (rank : α → Nat)
    (hd : Distinct key new) (hp : p.MovesBy place move) (hb : move.ease.bounded = true)
    {R : IVec → IVec → Prop} (hR : Kept R) {o₁ n₁ o₂ n₂ : α}
    (h₁ : (o₁, n₁) ∈ (join key old new).update) (h₂ : (o₂, n₂) ∈ (join key old new).update)
    (hold : R (place o₁) (place o₂)) (hnew : R (place n₁) (place n₂)) (t : Nat) :
    R (((staged key (join key old new) p enterFrom levels rank).within.frame (key n₁) t).stand
        (place n₁))
      (((staged key (join key old new) p enterFrom levels rank).within.frame (key n₂) t).stand
        (place n₂)) := by
  obtain ⟨tr, he, hc⟩ := staged_movesFrom key place old new p move enterFrom levels rank hd hp
  exact together_between (hc h₁).within (hc h₂).within (by
    show tr.ease.bounded = true
    rw [he]
    exact hb) hR hold hnew t

/-! ### A gap at every moment -/

/-- **Two kept boxes a gap `g` apart in both pictures are a gap `g` apart at every moment.**
The second is `g` or more to the right of the first in the old picture and in the new one, so
it is where the two stand at every moment of the step, held inside itself. With `g` the width
of the first box and the gap of the layout, the two boxes never touch. -/
theorem ofJoin_within_leftOf [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec)
    (old new : List α) (p : Plan α) (move : Transition) (hd : Distinct key new)
    (hp : p.MovesBy place move) (hb : move.ease.bounded = true) (g : Int) {o₁ n₁ o₂ n₂ : α}
    (h₁ : (o₁, n₁) ∈ (join key old new).update) (h₂ : (o₂, n₂) ∈ (join key old new).update)
    (hold : (place o₁).x + g ≤ (place o₂).x) (hnew : (place n₁).x + g ≤ (place n₂).x) (t : Nat) :
    (((ofJoin key (join key old new) p).within.frame (key n₁) t).stand (place n₁)).x + g ≤
      (((ofJoin key (join key old new) p).within.frame (key n₂) t).stand (place n₂)).x :=
  ofJoin_within_together (R := fun a b => a.x + g ≤ b.x) key place old new p move hd hp hb
    (Kept.leftOf g) h₁ h₂ hold hnew t

/-- **Two kept boxes a gap `g` apart, one above the other, in both pictures are so at every
moment** of the step, held inside itself. -/
theorem ofJoin_within_above [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec)
    (old new : List α) (p : Plan α) (move : Transition) (hd : Distinct key new)
    (hp : p.MovesBy place move) (hb : move.ease.bounded = true) (g : Int) {o₁ n₁ o₂ n₂ : α}
    (h₁ : (o₁, n₁) ∈ (join key old new).update) (h₂ : (o₂, n₂) ∈ (join key old new).update)
    (hold : (place o₁).y + g ≤ (place o₂).y) (hnew : (place n₁).y + g ≤ (place n₂).y) (t : Nat) :
    (((ofJoin key (join key old new) p).within.frame (key n₁) t).stand (place n₁)).y + g ≤
      (((ofJoin key (join key old new) p).within.frame (key n₂) t).stand (place n₂)).y :=
  ofJoin_within_together (R := fun a b => a.y + g ≤ b.y) key place old new p move hd hp hb
    (Kept.above g) h₁ h₂ hold hnew t

/-- **Two kept boxes a gap `g` apart in both pictures are a gap `g` apart at every moment of a
step in stages.** -/
theorem staged_leftOf [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec) (old new : List α)
    (p : Plan α) (move : Transition) (enterFrom levels : Nat) (rank : α → Nat)
    (hd : Distinct key new) (hp : p.MovesBy place move) (hb : move.ease.bounded = true) (g : Int)
    {o₁ n₁ o₂ n₂ : α} (h₁ : (o₁, n₁) ∈ (join key old new).update)
    (h₂ : (o₂, n₂) ∈ (join key old new).update) (hold : (place o₁).x + g ≤ (place o₂).x)
    (hnew : (place n₁).x + g ≤ (place n₂).x) (t : Nat) :
    (((staged key (join key old new) p enterFrom levels rank).frame (key n₁) t).stand
        (place n₁)).x + g ≤
      (((staged key (join key old new) p enterFrom levels rank).frame (key n₂) t).stand
        (place n₂)).x :=
  staged_together (R := fun a b => a.x + g ≤ b.x) key place old new p move enterFrom levels rank
    hd hp hb (Kept.leftOf g) h₁ h₂ hold hnew t

/-- **Two kept boxes a gap `g` apart, one above the other, in both pictures are so at every
moment of a step in stages.** -/
theorem staged_above [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec) (old new : List α)
    (p : Plan α) (move : Transition) (enterFrom levels : Nat) (rank : α → Nat)
    (hd : Distinct key new) (hp : p.MovesBy place move) (hb : move.ease.bounded = true) (g : Int)
    {o₁ n₁ o₂ n₂ : α} (h₁ : (o₁, n₁) ∈ (join key old new).update)
    (h₂ : (o₂, n₂) ∈ (join key old new).update) (hold : (place o₁).y + g ≤ (place o₂).y)
    (hnew : (place n₁).y + g ≤ (place n₂).y) (t : Nat) :
    (((staged key (join key old new) p enterFrom levels rank).frame (key n₁) t).stand
        (place n₁)).y + g ≤
      (((staged key (join key old new) p enterFrom levels rank).frame (key n₂) t).stand
        (place n₂)).y :=
  staged_together (R := fun a b => a.y + g ≤ b.y) key place old new p move enterFrom levels rank
    hd hp hb (Kept.above g) h₁ h₂ hold hnew t

end Motion

/-! ## Controls and finite evaluations

The data is that of `workshop/BetweenProbe.lean`: a rank of four boxes, with the widths and the
gap of sixteen of lean4-effect4's flow layout. A box is its key, its left edge and its width.
The box `fiber 1` leaves, and the two boxes to its right move left to close the room. Both
pictures have a gap of sixteen between every two neighbours. Each number below is the least gap
between two neighbours of the new rank over the moments 0, 10, …, 1000, read through
`Motion.frame` and `Frame.stand`.

1. One timing for the kept boxes, and an easing that passes the test: the least gap is `16`, as
   `Motion.ofJoin_within_leftOf` says.
2. The same easing, and the farther box started first: the premise "one transition" fails, and
   the least gap is `-141`.
3. One timing, and `Easing.backOut`, which fails the test: the least gap is `-2`.

The last three numbers are the same three steps in stages (`Motion.staged`, the new things from
the moment `300`, one level): `16`, as `Motion.staged_leftOf` says, then `-138` and `-2`. -/

#guard
  let key : String × Int × Int → String := fun i => i.1
  let place : String × Int × Int → IVec := fun i => ⟨i.2.1, 0⟩
  let before : List (String × Int × Int) :=
    [("fiber 0", 24, 120), ("fiber 1", 160, 160), ("fiber 2", 336, 216), ("fiber 3", 568, 120)]
  let after : List (String × Int × Int) :=
    [("fiber 0", 24, 120), ("fiber 2", 160, 216), ("fiber 3", 392, 120)]
  let settle : Easing :=
    .stops [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992,
      995, 998, 1000]
  let plan (timing : String → Transition) : Plan (String × Int × Int) :=
    { kept := fun o n => Plan.moving place (timing n.1) o n
      enter := fun _ => [(.fade 0 1000, {})]
      leave := fun _ => [(.fade 1000 0, { duration := 250, ease := Easing.cubicIn })] }
  let step (timing : String → Transition) : Motion String :=
    (Motion.ofJoin key (join key before after) (plan timing)).within
  let staged (timing : String → Transition) : Motion String :=
    Motion.staged key (join key before after) (plan timing) 300 1 fun _ => 0
  let left (m : Motion String) (t : Nat) (i : String × Int × Int) : Int :=
    ((m.frame i.1 t).stand (place i)).x
  let gapAt (m : Motion String) (t : Nat) : Int :=
    ((after.zip (after.drop 1)).map fun q => left m t q.2 - (left m t q.1 + q.1.2.2)).foldl min
      1000
  let least (m : Motion String) : Int :=
    ((List.range 101).map fun i => gapAt m (10 * i)).foldl min 1000
  let one : String → Transition := fun _ => { delay := 250, duration := 600, ease := settle }
  let two : String → Transition := fun k =>
    { delay := if k == "fiber 3" then 150 else 400, duration := 500, ease := settle }
  let past : String → Transition := fun _ =>
    { delay := 250, duration := 600, ease := Easing.backOut }
  (settle.bounded, Easing.backOut.bounded) == (true, false) &&
    [least (step one), least (step two), least (step past)] == [16, -141, -2] &&
    [least (staged one), least (staged two), least (staged past)] == [16, -138, -2]

-- `Plan.MovesBy` asks that the plan gives no second change of the place. The box `b` goes
-- from `100` to `50`, and the box `a` stays at `0`: `b` is `20` or more to the right of `a` in
-- both pictures. The plan gives `b` a second shift, from `80` to the left. The later track is
-- the one shown, and at the start `b` stands at `-30`, behind `a`.
#guard
  let key : String × Int → String := Prod.fst
  let place : String × Int → IVec := fun i => ⟨i.2, 0⟩
  let p : Plan (String × Int) :=
    { kept := fun o n => Plan.moving place {} o n ++
        (if n.1 == "b" then [(.shift ⟨-80, 0⟩ 0, {})] else [])
      enter := fun _ => []
      leave := fun _ => [] }
  let m : Motion String :=
    Motion.ofJoin key (join key [("a", 0), ("b", 100)] [("a", 0), ("b", 50)]) p
  ((m.frame "a" 0).stand ⟨0, 0⟩, (m.frame "b" 0).stand ⟨50, 0⟩) == ((⟨0, 0⟩ : IVec), ⟨-30, 0⟩)

-- The laws of a step ask for distinct keys in the new list. Two new things have the key `a`,
-- one at `0`, where the old `a` stood, and one at `100`. The track of the second moves the
-- first too: at the start it stands at `-100`, behind the box `b` at `-50`, which is before it
-- in both pictures.
#guard
  let key : String × Int → String := Prod.fst
  let place : String × Int → IVec := fun i => ⟨i.2, 0⟩
  let m : Motion String :=
    Motion.ofJoin key (join key [("b", -50), ("a", 0)] [("b", -50), ("a", 0), ("a", 100)])
      ⟨Plan.moving place {}, fun _ => [], fun _ => []⟩
  ((m.frame "b" 0).stand ⟨-50, 0⟩, (m.frame "a" 0).stand ⟨0, 0⟩) == ((⟨-50, 0⟩ : IVec), ⟨-100, 0⟩)

end Whatwg.Svg.Scene
