import Whatwg.Svg.Scene.Motion.Laws
import Whatwg.Svg.Scene.Frame

/-!
# Whatwg.Svg.Scene.Plan

Owner: how the things of a join move, as one value (slice S14 of `docs/SVG-PACKAGE-PLAN.md`;
ruling SV-77).

A step from one picture to the next has three kinds of thing: the kept, the new and the old
(`Whatwg/Svg/Scene/Join.lean`). A `Plan` says what each of them does, and `Motion.ofJoin` gives a
join its tracks from a plan. It is the one way to do so. A law of a step asks one thing of the
plan, so a caller states it once.

- `Plan α`: what a kept thing does, how a new thing enters and how an old thing leaves. Each
  answer is a list of changes, each with its transition, since one change is often too few: a
  kept box moves and changes its shape, and a new thing comes from its parent's place and fades
  in. The empty list is "does nothing", and a thing that does nothing has no track.
- `Plan.moving place move o n`: what a kept thing does when its place alone can change. It is
  one shift from the old place, and nothing where the place is the same (`Plan.moving_nil`).
- `Plan.still`: the plan in which no thing does anything. `Plan.and p q`: each thing does what
  `p` gives it and what `q` gives it. A plan for places and a plan for shapes or for opacity
  are put together so.
- `Motion.tracks k cs`: the tracks of one thing, one for each of its changes.
  `Motion.staying`: the tracks of the things of the new picture. `Motion.leaving`: the tracks of
  the things that leave. `Motion.ofJoin`: the two in a row (`Motion.ofJoin_eq`).
  `Motion.keeping` and `Motion.entering`: the tracks of the kept things and of the new things,
  which are `staying` in a row (`Motion.staying_eq`).
- `Plan.Settles`: every change that `kept` and `enter` give ends at rest. `Plan.Proper`: every
  easing of the plan starts at `0` and ends at `1000`.
- `Plan.Single`: no thing has two changes of one property in any answer of the plan.
  `Plan.MovesBy p place move`: the plan moves each kept thing by the one transition `move`, and
  in no other way.
- `Join.drawn`: the things that a reader draws at a moment.

A plan is a structure of three functions, and a caller may write one directly:

```
{ kept := fun o n => Plan.moving place (timing n) o n ++ shapes o n
  enter := fun n => [(.fade 0 1000, fadeIn)]
  leave := fun _ => [(.grow 1000 0, shrink)] }
```

`Plan.moving_settles` and `Plan.moving_proper` give the part of `Settles` and of `Proper` that
is about `Plan.moving`. Two plans that settle make one that settles (`Plan.and_settles`), and
so for `Proper` (`Plan.and_proper`).

What the laws say of a step:

- `Motion.mem_staying`, `Motion.mem_leaving`: a track is what the plan gives a thing, with the
  thing's key. So a staying track has the key of a thing of the new list
  (`Motion.mem_staying_key`), and a leaving track has the key of an old thing whose key no new
  thing has (`Motion.mem_leaving_key`). No key has a track of both kinds.
- `Motion.length_staying_le`: where the plan gives each kept thing and each new thing `k`
  changes at most, there are `k` staying tracks at most for each new thing.
- **The end law of a step** (`Motion.staying_end`): with a plan that settles and is proper, every
  staying track held inside the step is at rest at the step's end, and after it
  (`Motion.staying_after`). Every track of the step, staying or leaving, is over by then
  (`Motion.ofJoin_done`).
- **The poses of one thing** (`Motion.posesOf_kept`, `Motion.posesOf_entering`,
  `Motion.posesOf_leaving`): with distinct keys, the poses of a kept thing, of a new thing and
  of a thing that leaves are the changes that the plan gives it, in the plan's order, each read
  at its moment. No other track of the step has the thing's key (`Motion.ofJoin_of_kept` says it
  of the tracks of a kept thing). They rest on `Motion.posesOf_tracks`, the poses of a thing
  among its own tracks, and on `Motion.update_distinct`: with distinct keys in the new list, no
  two kept pairs have one key.
- `Motion.staying_still`: a kept thing that the plan gives no change has no pose at any moment,
  where the keys of the new list are distinct. A reader draws it as it is. It is
  `Motion.posesOf_kept` of a pair with no change.
- **The last picture** (`Motion.ofJoin_end`): at the step's end and after, every pose that the
  step sets on a thing of the new list is at rest. With `Join.drawn_end`, the things drawn then
  are the new list, each as the still picture has it.
- **One track for each property** (`Motion.single_ofJoin`): under a plan with one change for
  each property of a thing (`Plan.Single`), with distinct keys in the old list and in the new
  one, the step is `Motion.Single`. So the reader of `Whatwg/Svg/Scene/Frame.lean` reads it:
  each track is in the frame of its thing. `Plan.moving` and `Plan.still` give one change for
  each property (`Plan.moving_single`, `Plan.still_single`), and the tracks of one such thing
  are `Single` (`Motion.single_tracks`).
- `Plan.movesBy_moving`, `Plan.MovesBy.and`: a plan whose `kept` is `Plan.moving place move`
  moves each kept thing by `move`, and so does such a plan together with a plan that changes no
  place. `Plan.moving_start_shift`: the start of `moving` puts the thing at its old place.
- `Join.drawn_distinct`: the things drawn at a moment have distinct keys, where the old list
  and the new list have.
- `Motion.ofJoin_still`: the plan in which nothing happens gives no track.
  `Motion.mem_ofJoin_and`: a track of two plans together is a track of one or of the other.

How a reader draws a moment `t`. It draws the things of `Join.drawn`: the old things that leave,
until the step's end, and then the things of the new list. It puts on each the poses of its key
(`Motion.posesOf`) in `(Motion.ofJoin key j p).within`. From the moment `1000` on it drops the
leaving things, and the poses of the others change nothing.

What this module does not claim: that a thing that leaves ends as nothing, since the plan's
`leave` may be any changes and a caller chooses some that end so; that two changes of one kind
on one thing agree, since the later one wins in a reader that sets a property once, and
`Plan.Single` is the plan that gives no two; an order in time among the tracks, which is
`Whatwg/Svg/Scene/Score.lean`; what holds between the two pictures, which is
`Whatwg/Svg/Scene/Between.lean`.

What came here in the tidy of slice S16, each under the name it had, and what the module now
cites. It imports `Whatwg/Svg/Scene/Frame.lean`, for `Motion.Single`, `Motion.posesOf_append`
and `Frame.ofPoses`. From `Whatwg/Svg/Scene/Resume.lean` came `Plan.Single` with
`Plan.moving_single` and `Plan.still_single`, `Motion.single_tracks`, `Motion.single_ofJoin`,
the laws of the poses of one thing with `Motion.posesOf_tracks`, `Motion.posesOf_tracks_of_ne`
and `Motion.update_distinct`, `Plan.moving_start_shift` and `Join.drawn_distinct`. From
`Whatwg/Svg/Scene/Together.lean` came `Plan.MovesBy`, `Plan.movesBy_moving`, `Plan.MovesBy.and`
and `Motion.ofJoin_of_kept`. From `Whatwg/Svg/Scene/Stage.lean` came `Motion.keeping`,
`Motion.entering` and `Motion.staying_eq`. It cites `nodup_append_of` and `nodup_pair` of
`Whatwg/Svg/Scene/Join/Laws.lean`.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- How the things of a join move: what a kept thing does, how a new thing enters and how an
old one leaves. Each answer is a list of changes with their transitions, and the empty list is
"does nothing". -/
structure Plan (α : Type) where
  /-- What a kept thing does, from its old thing to its new one. -/
  kept : α → α → List (Change × Transition)
  /-- How a new thing enters. -/
  enter : α → List (Change × Transition)
  /-- How an old thing leaves. -/
  leave : α → List (Change × Transition)

variable {α κ : Type}

/-! ## A plan -/

namespace Plan

/-- **The plan settles**: every change that `kept` and `enter` give ends at rest, so each thing
of the new picture ends as the still picture has it. -/
def Settles (p : Plan α) : Prop :=
  (∀ o n, ∀ c ∈ p.kept o n, c.1.stop.AtRest) ∧ ∀ n, ∀ c ∈ p.enter n, c.1.stop.AtRest

/-- **The plan is proper**: every easing of the plan starts at `0` and ends at `1000`. -/
def Proper (p : Plan α) : Prop :=
  (∀ o n, ∀ c ∈ p.kept o n, c.2.ease.Proper) ∧ (∀ n, ∀ c ∈ p.enter n, c.2.ease.Proper) ∧
    ∀ o, ∀ c ∈ p.leave o, c.2.ease.Proper

/-! ### A thing whose place alone can change -/

/-- What a kept thing does when only its place can change: one shift from its old place where
the place changed, and nothing where it did not. -/
def moving (place : α → IVec) (move : Transition) (o n : α) : List (Change × Transition) :=
  if place o = place n then [] else [(.shift (place o - place n) 0, move)]

/-- **A thing that does not move has no track.** `moving` gives nothing exactly where the old
place is the new one. -/
theorem moving_nil (place : α → IVec) (move : Transition) (o n : α) :
    moving place move o n = [] ↔ place o = place n := by
  unfold moving
  rcases Decidable.em (place o = place n) with h | h
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun e => (nomatch e), fun e => absurd e h⟩

/-- Where the place changed, `moving` gives the one shift from the old place, by `move`. -/
theorem moving_of_ne (place : α → IVec) (move : Transition) {o n : α} (h : place o ≠ place n) :
    moving place move o n = [(.shift (place o - place n) 0, move)] := if_neg h

/-- `moving` gives one change at most. -/
theorem length_moving_le (place : α → IVec) (move : Transition) (o n : α) :
    (moving place move o n).length ≤ 1 := by
  unfold moving
  rcases Decidable.em (place o = place n) with h | h
  · rw [if_pos h]
    exact Nat.zero_le 1
  · rw [if_neg h]
    exact Nat.le_refl 1

/-- What `moving` gives is the shift from the old place, by `move`. -/
theorem mem_moving (place : α → IVec) (move : Transition) {o n : α} {c : Change × Transition}
    (h : c ∈ moving place move o n) : c = (.shift (place o - place n) 0, move) := by
  rcases Decidable.em (place o = place n) with he | he
  · rw [(moving_nil place move o n).mpr he] at h
    exact nomatch h
  · rw [moving_of_ne place move he] at h
    exact List.mem_singleton.mp h

/-- Every change that `moving` gives ends at rest: a kept thing ends on its place. It is the
part of `Settles` that is about `moving`. -/
theorem moving_settles (place : α → IVec) (move : Transition) (o n : α) :
    ∀ c ∈ moving place move o n, c.1.stop.AtRest := by
  intro c h
  rw [mem_moving place move h]
  exact rfl

/-- Every easing that `moving` gives is that of `move`. It is the part of `Proper` that is
about `moving`. -/
theorem moving_proper (place : α → IVec) (move : Transition) (hm : move.ease.Proper) (o n : α) :
    ∀ c ∈ moving place move o n, c.2.ease.Proper := by
  intro c h
  rw [mem_moving place move h]
  exact hm

/-- `moving` gives changes of distinct properties: one shift at most. -/
theorem moving_single (place : α → IVec) (move : Transition) (o n : α) :
    ((moving place move o n).map fun c => c.1.property).Nodup := by
  rcases Decidable.em (place o = place n) with h | h
  · rw [(moving_nil place move o n).mpr h]
    exact List.nodup_nil
  · rw [moving_of_ne place move h]
    exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

/-- **The start of `moving` puts the thing at its old place**: the step from its new place to
its old one, and no step where the two are one. -/
theorem moving_start_shift (place : α → IVec) (move : Transition) (o n : α) :
    (Frame.ofPoses ((moving place move o n).map fun c => c.1.start)).shift =
      place o - place n := by
  rcases Decidable.em (place o = place n) with h | h
  · rw [(moving_nil place move o n).mpr h, h]
    exact (IVec.sub_self (place n)).symm
  · rw [moving_of_ne place move h]
    rfl

/-! ### No plan, and two plans together -/

/-- The plan in which no thing does anything. -/
def still : Plan α := ⟨fun _ _ => [], fun _ => [], fun _ => []⟩

/-- The plan in which nothing happens settles. -/
theorem still_settles : (still : Plan α).Settles :=
  ⟨fun _ _ _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil⟩

/-- The plan in which nothing happens is proper. -/
theorem still_proper : (still : Plan α).Proper :=
  ⟨fun _ _ _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil,
    fun _ _ h => absurd h List.not_mem_nil⟩

/-- **Two plans together**: each thing does what the first plan gives it, and what the second
gives it. A plan for places and a plan for shapes or for opacity make one plan so. -/
def and (p q : Plan α) : Plan α where
  kept o n := p.kept o n ++ q.kept o n
  enter n := p.enter n ++ q.enter n
  leave o := p.leave o ++ q.leave o

/-- Two plans that settle make a plan that settles. -/
theorem and_settles {p q : Plan α} (hp : p.Settles) (hq : q.Settles) : (p.and q).Settles :=
  ⟨fun o n c h => (List.mem_append.mp h).elim (hp.1 o n c) (hq.1 o n c),
    fun n c h => (List.mem_append.mp h).elim (hp.2 n c) (hq.2 n c)⟩

/-- Two proper plans make a proper plan. -/
theorem and_proper {p q : Plan α} (hp : p.Proper) (hq : q.Proper) : (p.and q).Proper :=
  ⟨fun o n c h => (List.mem_append.mp h).elim (hp.1 o n c) (hq.1 o n c),
    fun n c h => (List.mem_append.mp h).elim (hp.2.1 n c) (hq.2.1 n c),
    fun o c h => (List.mem_append.mp h).elim (hp.2.2 o c) (hq.2.2 o c)⟩

/-! ### One change for each property of a thing -/

/-- **No thing has two changes of one property in any answer of the plan.** The tracks of a join
under such a plan are `Motion.Single`, where the keys of each list are distinct
(`Motion.single_ofJoin`). -/
def Single (p : Plan α) : Prop :=
  (∀ o n, ((p.kept o n).map fun c => c.1.property).Nodup) ∧
    (∀ n, ((p.enter n).map fun c => c.1.property).Nodup) ∧
    ∀ o, ((p.leave o).map fun c => c.1.property).Nodup

/-- The plan in which nothing happens has one change for each property: none. -/
theorem still_single : (still : Plan α).Single :=
  ⟨fun _ _ => List.nodup_nil, fun _ => List.nodup_nil, fun _ => List.nodup_nil⟩

/-! ### A plan that moves each kept thing by one transition -/

/-- **The plan moves each kept thing by the one transition `move`, and in no other way.** The
changes of the place that `kept` gives a pair are those of `Plan.moving place move`: the one
shift from the old place where the place changed, and none where it did not. What else `kept`
gives, a change of shape or of opacity, is not asked about. This is the check on a look that
every kept thing takes one timing. -/
def MovesBy (p : Plan α) (place : α → IVec) (move : Transition) : Prop :=
  ∀ o n, ∀ c : Change × Transition, c.1.property = .place →
    (c ∈ p.kept o n ↔ c ∈ Plan.moving place move o n)

/-- A plan whose `kept` is `Plan.moving place move` moves each kept thing by `move`. -/
theorem movesBy_moving (place : α → IVec) (move : Transition)
    (enter leave : α → List (Change × Transition)) :
    (⟨Plan.moving place move, enter, leave⟩ : Plan α).MovesBy place move :=
  fun _ _ _ _ => Iff.rfl

/-- A plan that moves each kept thing by `move`, together with a plan that gives a kept thing
no change of its place, moves each kept thing by `move`: a plan for places and a plan for
shapes or for opacity. -/
theorem MovesBy.and {p q : Plan α} {place : α → IVec} {move : Transition}
    (hp : p.MovesBy place move) (hq : ∀ o n, ∀ c ∈ q.kept o n, c.1.property ≠ .place) :
    (p.and q).MovesBy place move := by
  intro o n c hc
  constructor
  · intro h
    rcases List.mem_append.mp h with h1 | h2
    · exact (hp o n c hc).mp h1
    · exact absurd hc (hq o n c h2)
  · intro h
    exact List.mem_append_left _ ((hp o n c hc).mpr h)

end Plan

/-- **The things that a reader draws at the moment `t`** of the step of a join to the list
`new`: the old things that leave, until the step's end, and then the things of the new list. A
join does not keep the order of the new list, so the list is given. -/
def Join.drawn (j : Join α) (new : List α) (t : Nat) : List α :=
  (if t < 1000 then j.exit else []) ++ new

/-- Until the step's end the things that leave are drawn, under the things of the new list. -/
theorem Join.drawn_before (j : Join α) (new : List α) {t : Nat} (h : t < 1000) :
    j.drawn new t = j.exit ++ new :=
  congrArg (· ++ new) (if_pos h)

/-- **At the step's end and after, the things drawn are the things of the new list.** -/
theorem Join.drawn_end (j : Join α) (new : List α) {t : Nat} (h : 1000 ≤ t) :
    j.drawn new t = new :=
  congrArg (· ++ new) (if_neg (Nat.not_lt_of_le h))

/-- **The things drawn at a moment of a step have distinct keys**, where the old list and the
new list have. So the things drawn at an interruption can be the old list of the next join. -/
theorem Join.drawn_distinct [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α)
    (ho : Distinct key old) (hn : Distinct key new) (t : Nat) :
    Distinct key ((join key old new).drawn new t) := by
  unfold Join.drawn
  rcases Decidable.em (t < 1000) with h | h
  · rw [if_pos h]
    show (((join key old new).exit ++ new).map key).Nodup
    rw [List.map_append]
    refine nodup_append_of (distinct_exit key old new ho) hn fun a ha hb => ?_
    obtain ⟨o, hom, rfl⟩ := List.mem_map.mp ha
    obtain ⟨n, hnm, e⟩ := List.mem_map.mp hb
    exact ((mem_exit key old new).mp hom).2 n hnm e
  · rw [if_neg h]
    exact hn

/-! ## The tracks of a join -/

namespace Motion

/-- The tracks of one thing: one for each of its changes, each with the thing's key. -/
def tracks (k : κ) (cs : List (Change × Transition)) : Motion κ := cs.map fun c => ⟨k, c.1, c.2⟩

/-- A thing has as many tracks as changes. -/
theorem length_tracks (k : κ) (cs : List (Change × Transition)) :
    (tracks k cs).length = cs.length := List.length_map _

/-- A track of a thing is one of its changes, with its key. -/
theorem mem_tracks {k : κ} {cs : List (Change × Transition)} {tr : Track κ} :
    tr ∈ tracks k cs ↔ ∃ c ∈ cs, tr = ⟨k, c.1, c.2⟩ := by
  constructor
  · intro h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact ⟨c, hc, rfl⟩
  · intro ⟨c, hc, e⟩
    exact List.mem_map.mpr ⟨c, hc, e.symm⟩

/-- The tracks of the things that are in the new picture: `ofJoin` without the things that
leave. A kept thing has a track for each change that `kept` gives it, and none where `kept`
gives nothing. A new thing has a track for each change that `enter` gives it. -/
def staying (key : α → κ) (j : Join α) (p : Plan α) : Motion κ :=
  j.update.flatMap (fun q => tracks (key q.2) (p.kept q.1 q.2)) ++
    j.enter.flatMap (fun n => tracks (key n) (p.enter n))

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

/-- The tracks of the things that leave: one for each change that `leave` gives an old thing
that exits. -/
def leaving (key : α → κ) (j : Join α) (p : Plan α) : Motion κ :=
  j.exit.flatMap fun o => tracks (key o) (p.leave o)

/-- **The tracks of a join under a plan**: those of the kept things that do something, then
those of the new things, then those of the old ones. -/
def ofJoin (key : α → κ) (j : Join α) (p : Plan α) : Motion κ :=
  staying key j p ++ leaving key j p

/-- The tracks of a join are those of the things that stay, then those of the things that
leave. -/
theorem ofJoin_eq (key : α → κ) (j : Join α) (p : Plan α) :
    ofJoin key j p = staying key j p ++ leaving key j p := rfl

/-- The tracks of a join held inside a step are those of the things that stay, held, then those
of the things that leave, held. -/
theorem ofJoin_within (key : α → κ) (j : Join α) (p : Plan α) :
    (ofJoin key j p).within = (staying key j p).within ++ (leaving key j p).within :=
  List.map_append

/-- A staying track is a change that `kept` gives a kept pair, or one that `enter` gives a new
thing, with the key of the new thing. -/
theorem mem_staying (key : α → κ) (j : Join α) (p : Plan α) {tr : Track κ} :
    tr ∈ staying key j p ↔
      (∃ q ∈ j.update, ∃ c ∈ p.kept q.1 q.2, tr = ⟨key q.2, c.1, c.2⟩) ∨
        ∃ n ∈ j.enter, ∃ c ∈ p.enter n, tr = ⟨key n, c.1, c.2⟩ := by
  unfold staying
  rw [List.mem_append, List.mem_flatMap, List.mem_flatMap]
  constructor
  · rintro (⟨q, hq, h⟩ | ⟨n, hn, h⟩)
    · exact Or.inl ⟨q, hq, mem_tracks.mp h⟩
    · exact Or.inr ⟨n, hn, mem_tracks.mp h⟩
  · rintro (⟨q, hq, h⟩ | ⟨n, hn, h⟩)
    · exact Or.inl ⟨q, hq, mem_tracks.mpr h⟩
    · exact Or.inr ⟨n, hn, mem_tracks.mpr h⟩

/-- A leaving track is a change that `leave` gives an old thing that exits, with its key. -/
theorem mem_leaving (key : α → κ) (j : Join α) (p : Plan α) {tr : Track κ} :
    tr ∈ leaving key j p ↔ ∃ o ∈ j.exit, ∃ c ∈ p.leave o, tr = ⟨key o, c.1, c.2⟩ := by
  unfold leaving
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨o, ho, h⟩
    exact ⟨o, ho, mem_tracks.mp h⟩
  · rintro ⟨o, ho, h⟩
    exact ⟨o, ho, mem_tracks.mpr h⟩

/-- A staying track has the key of a thing of the new list. -/
theorem mem_staying_key [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    {tr : Track κ} (h : tr ∈ staying key (join key old new) p) : ∃ n ∈ new, key n = tr.key := by
  rcases (mem_staying key (join key old new) p).mp h with
    ⟨⟨_, n⟩, hq, _, _, rfl⟩ | ⟨n, hn, _, _, rfl⟩
  · exact ⟨n, (mem_update key old new hq).2.1, rfl⟩
  · exact ⟨n, ((mem_enter key old new).mp hn).1, rfl⟩

/-- A leaving track has the key of a thing of the old list whose key no thing of the new list
has. -/
theorem mem_leaving_key [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    {tr : Track κ} (h : tr ∈ leaving key (join key old new) p) :
    ∃ o ∈ old, key o = tr.key ∧ ∀ n ∈ new, key n ≠ tr.key := by
  obtain ⟨o, ho, _, _, rfl⟩ := (mem_leaving key (join key old new) p).mp h
  exact ⟨o, ((mem_exit key old new).mp ho).1, rfl, ((mem_exit key old new).mp ho).2⟩

/-- **There are `k` staying tracks at most for each thing of the new list**, where the plan
gives each kept thing and each new thing `k` changes at most. With `k = 1`, a thing of the new
picture has one track at most. -/
theorem length_staying_le [BEq κ] (key : α → κ) (old new : List α) (p : Plan α) (k : Nat)
    (hk : ∀ o n, (p.kept o n).length ≤ k) (he : ∀ n, (p.enter n).length ≤ k) :
    (staying key (join key old new) p).length ≤ k * new.length := by
  have h := length_enter_add_update key old new
  have h1 := length_flatMap_le (fun q : α × α => tracks (key q.2) (p.kept q.1 q.2)) k
    (join key old new).update fun q _ =>
      Nat.le_trans (Nat.le_of_eq (length_tracks _ _)) (hk q.1 q.2)
  have h2 := length_flatMap_le (fun n : α => tracks (key n) (p.enter n)) k
    (join key old new).enter fun n _ => Nat.le_trans (Nat.le_of_eq (length_tracks _ _)) (he n)
  rw [staying, List.length_append, ← h, Nat.mul_add]
  omega

/-! ### No plan, and two plans together -/

/-- **The plan in which nothing happens gives no track.** -/
theorem ofJoin_still (key : α → κ) (j : Join α) : ofJoin key j (Plan.still : Plan α) = [] :=
  eq_nil_of_no_mem fun tr h => by
    rcases List.mem_append.mp h with hs | hl
    · rcases (mem_staying key j Plan.still).mp hs with ⟨_, _, _, hc, _⟩ | ⟨_, _, _, hc, _⟩
      · exact absurd hc List.not_mem_nil
      · exact absurd hc List.not_mem_nil
    · obtain ⟨_, _, _, hc, _⟩ := (mem_leaving key j Plan.still).mp hl
      exact absurd hc List.not_mem_nil

/-- A staying track of two plans together is a staying track of one or of the other. -/
theorem mem_staying_and (key : α → κ) (j : Join α) (p q : Plan α) {tr : Track κ} :
    tr ∈ staying key j (p.and q) ↔ tr ∈ staying key j p ∨ tr ∈ staying key j q := by
  rw [mem_staying, mem_staying, mem_staying]
  constructor
  · rintro (⟨x, hx, c, hc, rfl⟩ | ⟨n, hn, c, hc, rfl⟩)
    · rcases List.mem_append.mp hc with h | h
      · exact Or.inl (Or.inl ⟨x, hx, c, h, rfl⟩)
      · exact Or.inr (Or.inl ⟨x, hx, c, h, rfl⟩)
    · rcases List.mem_append.mp hc with h | h
      · exact Or.inl (Or.inr ⟨n, hn, c, h, rfl⟩)
      · exact Or.inr (Or.inr ⟨n, hn, c, h, rfl⟩)
  · rintro ((⟨x, hx, c, hc, rfl⟩ | ⟨n, hn, c, hc, rfl⟩) |
      (⟨x, hx, c, hc, rfl⟩ | ⟨n, hn, c, hc, rfl⟩))
    · exact Or.inl ⟨x, hx, c, List.mem_append_left _ hc, rfl⟩
    · exact Or.inr ⟨n, hn, c, List.mem_append_left _ hc, rfl⟩
    · exact Or.inl ⟨x, hx, c, List.mem_append_right _ hc, rfl⟩
    · exact Or.inr ⟨n, hn, c, List.mem_append_right _ hc, rfl⟩

/-- A leaving track of two plans together is a leaving track of one or of the other. -/
theorem mem_leaving_and (key : α → κ) (j : Join α) (p q : Plan α) {tr : Track κ} :
    tr ∈ leaving key j (p.and q) ↔ tr ∈ leaving key j p ∨ tr ∈ leaving key j q := by
  rw [mem_leaving, mem_leaving, mem_leaving]
  constructor
  · rintro ⟨o, ho, c, hc, rfl⟩
    rcases List.mem_append.mp hc with h | h
    · exact Or.inl ⟨o, ho, c, h, rfl⟩
    · exact Or.inr ⟨o, ho, c, h, rfl⟩
  · rintro (⟨o, ho, c, hc, rfl⟩ | ⟨o, ho, c, hc, rfl⟩)
    · exact ⟨o, ho, c, List.mem_append_left _ hc, rfl⟩
    · exact ⟨o, ho, c, List.mem_append_right _ hc, rfl⟩

/-- **A track of two plans together is a track of one or of the other**, and each track of
either is a track of the two together. The order of the tracks is not that of the two motions
in a row: the tracks of one thing stand together. -/
theorem mem_ofJoin_and (key : α → κ) (j : Join α) (p q : Plan α) {tr : Track κ} :
    tr ∈ ofJoin key j (p.and q) ↔ tr ∈ ofJoin key j p ∨ tr ∈ ofJoin key j q := by
  rw [ofJoin, ofJoin, ofJoin, List.mem_append, List.mem_append, List.mem_append,
    mem_staying_and, mem_leaving_and]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

/-! ### The end of a step -/

/-- Every staying track settles, where the plan does. -/
theorem staying_settles (key : α → κ) (j : Join α) (p : Plan α) (hs : p.Settles) :
    ∀ tr ∈ staying key j p, tr.Settles := by
  intro tr htr
  rcases (mem_staying key j p).mp htr with ⟨q, _, c, hc, rfl⟩ | ⟨n, _, c, hc, rfl⟩
  · exact hs.1 q.1 q.2 c hc
  · exact hs.2 n c hc

/-- Every track of a join has a proper easing, where the plan is proper. -/
theorem ofJoin_proper (key : α → κ) (j : Join α) (p : Plan α) (hp : p.Proper) :
    ∀ tr ∈ ofJoin key j p, tr.timing.ease.Proper := by
  intro tr htr
  rcases List.mem_append.mp htr with hst | hlv
  · rcases (mem_staying key j p).mp hst with ⟨q, _, c, hc, rfl⟩ | ⟨n, _, c, hc, rfl⟩
    · exact hp.1 q.1 q.2 c hc
    · exact hp.2.1 n c hc
  · obtain ⟨o, _, c, hc, rfl⟩ := (mem_leaving key j p).mp hlv
    exact hp.2.2 o c hc

/-- Every staying track has a proper easing, where the plan is proper. -/
theorem staying_proper (key : α → κ) (j : Join α) (p : Plan α) (hp : p.Proper) :
    ∀ tr ∈ staying key j p, tr.timing.ease.Proper := fun tr h =>
  ofJoin_proper key j p hp tr (List.mem_append_left _ h)

/-- With a proper plan, every track of a join held inside a step is over at the step's end:
each stands at the end of its change (`Track.at_done`), the things that leave too. -/
theorem ofJoin_done (key : α → κ) (j : Join α) (p : Plan α) (hp : p.Proper) :
    ∀ tr ∈ (ofJoin key j p).within, tr.Done 1000 :=
  within_done (ofJoin key j p) (ofJoin_proper key j p hp)

/-- **At the step's end and after, every staying thing is at rest**, with a plan that settles
and is proper. -/
theorem staying_after (key : α → κ) (j : Join α) (p : Plan α) (hs : p.Settles) (hp : p.Proper)
    {t : Nat} (ht : 1000 ≤ t) : ∀ tr ∈ (staying key j p).within, (tr.at t).AtRest :=
  within_after (staying key j p) (staying_proper key j p hp) (staying_settles key j p hs) ht

/-- **The end law of a step.** With a plan that settles and is proper, every track of a thing
of the new picture is at rest at the step's end: the step's last moment is the next picture. -/
theorem staying_end (key : α → κ) (j : Join α) (p : Plan α) (hs : p.Settles) (hp : p.Proper) :
    ∀ tr ∈ (staying key j p).within, (tr.at 1000).AtRest :=
  staying_after key j p hs hp (Nat.le_refl 1000)

/-! ### The poses of the things of a join

These laws are of `Motion.ofJoin` of every plan. They say what the poses of one thing are, as a
list: the changes that the plan gives the thing, in the plan's order, each read at its
moment. -/

/-- The poses of a thing among its own tracks are its changes, each read at its moment. -/
theorem posesOf_tracks [BEq κ] [LawfulBEq κ] (k : κ) (cs : List (Change × Transition))
    (t : Nat) : (tracks k cs).posesOf k t = cs.map fun c => c.1.at (c.2.at t) := by
  have hf : (tracks k cs).filter (fun tr => tr.key == k) = tracks k cs :=
    List.filter_eq_self.mpr fun tr htr => by
      obtain ⟨c, _, rfl⟩ := mem_tracks.mp htr
      exact beq_iff_eq.mpr rfl
  show ((tracks k cs).filter fun tr => tr.key == k).map (fun tr => tr.at t) = _
  rw [hf]
  exact List.map_map

/-- The tracks of one thing set no pose on another. -/
theorem posesOf_tracks_of_ne [BEq κ] [LawfulBEq κ] {k k' : κ} (h : k ≠ k')
    (cs : List (Change × Transition)) (t : Nat) : (tracks k cs).posesOf k' t = [] :=
  still_of_no_track _ k' t fun tr htr he => by
    obtain ⟨c, _, rfl⟩ := mem_tracks.mp htr
    exact h he

/-- Among the tracks of things with distinct keys, the poses of one thing are its own
changes. -/
private theorem posesOf_flatMap [BEq κ] [LawfulBEq κ] {β : Type} (k : β → κ)
    (g : β → List (Change × Transition)) : ∀ (l : List β), Distinct k l → ∀ (x : β), x ∈ l →
      ∀ (t : Nat), Motion.posesOf (l.flatMap fun y => tracks (k y) (g y)) (k x) t =
        (g x).map fun c => c.1.at (c.2.at t)
  | [], _, _, hx, _ => nomatch hx
  | y :: rest, hd, x, hx, t => by
    have hd' : k y ∉ rest.map k ∧ (rest.map k).Nodup := List.nodup_cons.mp hd
    have hsplit : Motion.posesOf ((y :: rest).flatMap fun y => tracks (k y) (g y)) (k x) t =
        Motion.posesOf (tracks (k y) (g y)) (k x) t ++
          Motion.posesOf (rest.flatMap fun y => tracks (k y) (g y)) (k x) t := by
      rw [List.flatMap_cons]
      exact posesOf_append _ _ _ _
    rw [hsplit]
    cases hb : k y == k x with
    | true =>
      have hk : k y = k x := beq_iff_eq.mp hb
      have hxy : x = y := by
        rcases List.mem_cons.mp hx with e | hr
        · exact e
        · exact absurd (List.mem_map.mpr ⟨x, hr, hk.symm⟩) hd'.1
      subst hxy
      have hrest : Motion.posesOf (rest.flatMap fun y => tracks (k y) (g y)) (k x) t = [] :=
        still_of_no_track _ (k x) t fun tr htr he => by
          obtain ⟨z, hz, htz⟩ := List.mem_flatMap.mp htr
          obtain ⟨c, _, rfl⟩ := mem_tracks.mp htz
          exact hd'.1 (List.mem_map.mpr ⟨z, hz, he⟩)
      rw [posesOf_tracks, hrest, List.append_nil]
    | false =>
      have hne : k y ≠ k x := fun e => Bool.false_ne_true (hb.symm.trans (beq_iff_eq.mpr e))
      have hr : x ∈ rest := by
        rcases List.mem_cons.mp hx with e | hr
        · exact absurd (congrArg k e).symm hne
        · exact hr
      rw [posesOf_tracks_of_ne hne, List.nil_append]
      exact posesOf_flatMap k g rest hd'.2 x hr t

/-- The keys of the new things of the kept pairs are among the keys of the new list, in its
order. -/
private theorem update_keys_sublist [BEq κ] (key : α → κ) (old : List α) : ∀ new : List α,
    List.Sublist ((join key old new).update.map fun q => key q.2) (new.map key)
  | [] => List.Sublist.slnil
  | n :: new => by
    have ih := update_keys_sublist key old new
    show List.Sublist (((n :: new).filterMap fun n =>
      (old.find? fun o => key o == key n).map (·, n)).map fun q => key q.2) ((n :: new).map key)
    cases hf : old.find? (fun o => key o == key n) with
    | none =>
      have h1 : (fun n => (old.find? fun o => key o == key n).map (·, n)) n = none :=
        congrArg (Option.map (·, n)) hf
      rw [List.filterMap_cons_none
        (f := fun n => (old.find? fun o => key o == key n).map (·, n)) h1]
      exact ih.cons (key n)
    | some o =>
      have h1 : (fun n => (old.find? fun o => key o == key n).map (·, n)) n = some (o, n) :=
        congrArg (Option.map (·, n)) hf
      rw [List.filterMap_cons_some
        (f := fun n => (old.find? fun o => key o == key n).map (·, n)) h1]
      exact ih.cons_cons (key n)

/-- **With distinct keys in the new list, no two kept pairs have one key.** -/
theorem update_distinct [BEq κ] (key : α → κ) (old new : List α) (hd : Distinct key new) :
    Distinct (fun q : α × α => key q.2) (join key old new).update :=
  List.Nodup.sublist (update_keys_sublist key old new) hd

/-- **The poses of a kept thing are the changes that the plan gives its pair**, in the plan's
order, each read at its moment. The keys of the new list are distinct. No other track of the
step has the thing's key. -/
theorem posesOf_kept [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (hd : Distinct key new) {o n : α} (hu : (o, n) ∈ (join key old new).update) (t : Nat) :
    (ofJoin key (join key old new) p).posesOf (key n) t =
      (p.kept o n).map fun c => c.1.at (c.2.at t) := by
  obtain ⟨ho, hn, hon⟩ := mem_update key old new hu
  have h1 : Motion.posesOf ((join key old new).update.flatMap fun q =>
      tracks (key q.2) (p.kept q.1 q.2)) (key n) t =
      (p.kept o n).map fun c => c.1.at (c.2.at t) :=
    posesOf_flatMap (fun q : α × α => key q.2) (fun q => p.kept q.1 q.2) _
      (update_distinct key old new hd) (o, n) hu t
  have h2 : Motion.posesOf ((join key old new).enter.flatMap fun n =>
      tracks (key n) (p.enter n)) (key n) t = [] :=
    still_of_no_track _ (key n) t fun tr htr he => by
      obtain ⟨n', hn', htr'⟩ := List.mem_flatMap.mp htr
      obtain ⟨c, _, rfl⟩ := mem_tracks.mp htr'
      exact ((mem_enter key old new).mp hn').2 o ho (hon.trans he.symm)
  have h3 : (leaving key (join key old new) p).posesOf (key n) t = [] :=
    still_of_no_track _ (key n) t fun tr htr he => by
      obtain ⟨_, _, _, hne⟩ := mem_leaving_key key old new p htr
      exact hne n hn he.symm
  show Motion.posesOf (((join key old new).update.flatMap fun q =>
      tracks (key q.2) (p.kept q.1 q.2)) ++
    ((join key old new).enter.flatMap fun n => tracks (key n) (p.enter n)) ++
    leaving key (join key old new) p) (key n) t = _
  rw [posesOf_append, posesOf_append, h1, h2, h3, List.append_nil, List.append_nil]

/-- **The poses of a new thing are the changes that the plan gives it to enter**, in the plan's
order, each read at its moment. The keys of the new list are distinct. -/
theorem posesOf_entering [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (hd : Distinct key new) {n : α} (hn : n ∈ (join key old new).enter) (t : Nat) :
    (ofJoin key (join key old new) p).posesOf (key n) t =
      (p.enter n).map fun c => c.1.at (c.2.at t) := by
  have hn' := (mem_enter key old new).mp hn
  have h1 : Motion.posesOf ((join key old new).update.flatMap fun q =>
      tracks (key q.2) (p.kept q.1 q.2)) (key n) t = [] :=
    still_of_no_track _ (key n) t fun tr htr he => by
      obtain ⟨⟨o', n''⟩, hq, htr'⟩ := List.mem_flatMap.mp htr
      obtain ⟨c, _, rfl⟩ := mem_tracks.mp htr'
      obtain ⟨ho', _, hk⟩ := mem_update key old new hq
      exact hn'.2 o' ho' (hk.trans he)
  have h2 : Motion.posesOf ((join key old new).enter.flatMap fun n =>
      tracks (key n) (p.enter n)) (key n) t = (p.enter n).map fun c => c.1.at (c.2.at t) :=
    posesOf_flatMap key p.enter _ (distinct_enter key old new hd) n hn t
  have h3 : (leaving key (join key old new) p).posesOf (key n) t = [] :=
    still_of_no_track _ (key n) t fun tr htr he => by
      obtain ⟨_, _, _, hne⟩ := mem_leaving_key key old new p htr
      exact hne n hn'.1 he.symm
  show Motion.posesOf (((join key old new).update.flatMap fun q =>
      tracks (key q.2) (p.kept q.1 q.2)) ++
    ((join key old new).enter.flatMap fun n => tracks (key n) (p.enter n)) ++
    leaving key (join key old new) p) (key n) t = _
  rw [posesOf_append, posesOf_append, h1, h2, h3, List.append_nil, List.nil_append]

/-- **The poses of a thing that leaves are the changes that the plan gives it to leave**, in
the plan's order, each read at its moment. The keys of the old list are distinct. -/
theorem posesOf_leaving [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (hd : Distinct key old) {o : α} (ho : o ∈ (join key old new).exit) (t : Nat) :
    (ofJoin key (join key old new) p).posesOf (key o) t =
      (p.leave o).map fun c => c.1.at (c.2.at t) := by
  have h1 : (staying key (join key old new) p).posesOf (key o) t = [] :=
    still_of_no_track _ (key o) t fun tr htr he => by
      obtain ⟨n, hn, hk⟩ := mem_staying_key key old new p htr
      exact ((mem_exit key old new).mp ho).2 n hn (hk.trans he)
  have h2 : Motion.posesOf ((join key old new).exit.flatMap fun o =>
      tracks (key o) (p.leave o)) (key o) t = (p.leave o).map fun c => c.1.at (c.2.at t) :=
    posesOf_flatMap key p.leave _ (distinct_exit key old new hd) o ho t
  show Motion.posesOf (staying key (join key old new) p ++
    ((join key old new).exit.flatMap fun o => tracks (key o) (p.leave o))) (key o) t = _
  rw [posesOf_append, h1, h2, List.nil_append]

/-- **A kept thing that the plan gives no change has no pose**, at any moment, where the keys
of the new list are distinct. With `Plan.moving`, that is a thing whose place did not change
(`Plan.moving_nil`). -/
theorem staying_still [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (hd : Distinct key new) {o n : α} (hu : (o, n) ∈ (join key old new).update)
    (hk : p.kept o n = []) (t : Nat) :
    (staying key (join key old new) p).posesOf (key n) t = [] := by
  have h : (staying key (join key old new) p).posesOf (key n) t ++
      (leaving key (join key old new) p).posesOf (key n) t = [] := by
    rw [← posesOf_append]
    exact (posesOf_kept key old new p hd hu t).trans
      (congrArg (List.map fun c : Change × Transition => c.1.at (c.2.at t)) hk)
  refine eq_nil_of_no_mem fun q hq => ?_
  have hm : q ∈ (staying key (join key old new) p).posesOf (key n) t ++
      (leaving key (join key old new) p).posesOf (key n) t := List.mem_append_left _ hq
  rw [h] at hm
  exact absurd hm List.not_mem_nil

/-- **Every track of a kept thing in a step is a change that the plan's `kept` gives its
pair**, where the keys of the new list are distinct. No track of a new thing or of a thing that
leaves has its key. -/
theorem ofJoin_of_kept [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (hd : Distinct key new) {o n : α} (hu : (o, n) ∈ (join key old new).update) {tr : Track κ}
    (htr : tr ∈ ofJoin key (join key old new) p) (hk : tr.key = key n) :
    ∃ c ∈ p.kept o n, tr = ⟨key n, c.1, c.2⟩ := by
  obtain ⟨ho, hn, hon⟩ := mem_update key old new hu
  rcases List.mem_append.mp htr with hst | hlv
  · rcases (mem_staying key (join key old new) p).mp hst with
      ⟨⟨o', n'⟩, hq, c, hc, rfl⟩ | ⟨n', hn', _, _, rfl⟩
    · have e : n' = n := eq_of_distinct key new hd n' n (mem_update key old new hq).2.1 hn hk
      subst e
      have e2 : o' = o := Option.some.inj
        (((mem_update_find key old new).mp hq).2.symm.trans
          ((mem_update_find key old new).mp hu).2)
      subst e2
      exact ⟨c, hc, rfl⟩
    · exact absurd (hon.trans hk.symm) (((mem_enter key old new).mp hn').2 o ho)
  · obtain ⟨_, _, _, hne⟩ := mem_leaving_key key old new p hlv
    exact absurd hk.symm (hne n hn)

/-- **The last picture.** At the step's end and after, every pose that the tracks of a join
set on a thing of the new list is at rest, with a plan that settles and is proper. A track of a
thing that leaves has another key, so it sets nothing on a thing of the new list. -/
theorem ofJoin_end [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (hs : p.Settles) (hp : p.Proper) {n : α} (hn : n ∈ new) {t : Nat} (ht : 1000 ≤ t) :
    ∀ q ∈ (ofJoin key (join key old new) p).within.posesOf (key n) t, q.AtRest := by
  intro q hq
  obtain ⟨tr, htr, hk, rfl⟩ := mem_posesOf _ _ _ hq
  rw [ofJoin_within] at htr
  rcases List.mem_append.mp htr with hst | hlv
  · exact staying_after key (join key old new) p hs hp ht tr hst
  · obtain ⟨tr0, h0, rfl⟩ := mem_within _ hlv
    obtain ⟨_, _, _, hne⟩ := mem_leaving_key key old new p h0
    exact absurd (beq_iff_eq.mp hk).symm (hne n hn)

/-! ### One track for each property of a thing -/

/-- The tracks of one thing with one change for each property are `Single`. -/
theorem single_tracks (k : κ) {cs : List (Change × Transition)}
    (h : (cs.map fun c => c.1.property).Nodup) : (tracks k cs).Single := by
  show ((cs.map fun c => (⟨k, c.1, c.2⟩ : Track κ)).map fun tr : Track κ =>
    (tr.key, tr.change.property)).Nodup
  rw [List.map_map]
  exact nodup_pair k (fun c : Change × Transition => c.1.property) cs h

/-- The tracks of things with distinct keys, each with one change for each property, are
`Single`. -/
private theorem single_flatMap {β : Type} (k : β → κ) (g : β → List (Change × Transition)) :
    ∀ (l : List β), Distinct k l → (∀ y ∈ l, ((g y).map fun c => c.1.property).Nodup) →
      Motion.Single (l.flatMap fun y => tracks (k y) (g y))
  | [], _, _ => List.nodup_nil
  | y :: rest, hd, hg => by
    have hd' : k y ∉ rest.map k ∧ (rest.map k).Nodup := List.nodup_cons.mp hd
    show (((y :: rest).flatMap fun y => tracks (k y) (g y)).map fun tr : Track κ =>
      (tr.key, tr.change.property)).Nodup
    rw [List.flatMap_cons, List.map_append]
    refine nodup_append_of (single_tracks (k y) (hg y List.mem_cons_self))
      (single_flatMap k g rest hd'.2 fun z hz => hg z (List.mem_cons_of_mem y hz))
      fun a ha hb => ?_
    obtain ⟨tr, htr, rfl⟩ := List.mem_map.mp ha
    obtain ⟨tr', htr', e⟩ := List.mem_map.mp hb
    obtain ⟨c, _, rfl⟩ := mem_tracks.mp htr
    obtain ⟨z, hz, htz⟩ := List.mem_flatMap.mp htr'
    obtain ⟨c', _, rfl⟩ := mem_tracks.mp htz
    exact hd'.1 (List.mem_map.mpr ⟨z, hz, congrArg Prod.fst e⟩)

/-- **The tracks of a join under a plan with one change for each property are `Single`**, where
the keys of the old list and of the new list are distinct. So every law of a `Single` motion
holds of the step: each track is in the frame of its thing (`Motion.frame_has`). -/
theorem single_ofJoin [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (hp : p.Single) (hdo : Distinct key old) (hdn : Distinct key new) :
    (ofJoin key (join key old new) p).Single := by
  have hU : Motion.Single ((join key old new).update.flatMap fun q =>
      tracks (key q.2) (p.kept q.1 q.2)) :=
    single_flatMap (fun q : α × α => key q.2) (fun q => p.kept q.1 q.2) _
      (update_distinct key old new hdn) fun q _ => hp.1 q.1 q.2
  have hE : Motion.Single ((join key old new).enter.flatMap fun n =>
      tracks (key n) (p.enter n)) :=
    single_flatMap key p.enter _ (distinct_enter key old new hdn) fun n _ => hp.2.1 n
  have hL : Motion.Single ((join key old new).exit.flatMap fun o =>
      tracks (key o) (p.leave o)) :=
    single_flatMap key p.leave _ (distinct_exit key old new hdo) fun o _ => hp.2.2 o
  show ((((join key old new).update.flatMap fun q => tracks (key q.2) (p.kept q.1 q.2)) ++
      ((join key old new).enter.flatMap fun n => tracks (key n) (p.enter n)) ++
      ((join key old new).exit.flatMap fun o => tracks (key o) (p.leave o))).map
    fun tr : Track κ => (tr.key, tr.change.property)).Nodup
  rw [List.map_append, List.map_append]
  refine nodup_append_of (nodup_append_of hU hE fun a ha hb => ?_) hL fun a ha hb => ?_
  · obtain ⟨tr, htr, rfl⟩ := List.mem_map.mp ha
    obtain ⟨tr', htr', e⟩ := List.mem_map.mp hb
    obtain ⟨⟨o', n'⟩, hq, htq⟩ := List.mem_flatMap.mp htr
    obtain ⟨c, _, rfl⟩ := mem_tracks.mp htq
    obtain ⟨n, hn, htn⟩ := List.mem_flatMap.mp htr'
    obtain ⟨c', _, rfl⟩ := mem_tracks.mp htn
    obtain ⟨ho', _, hk⟩ := mem_update key old new hq
    exact ((mem_enter key old new).mp hn).2 o' ho' (hk.trans (congrArg Prod.fst e).symm)
  · obtain ⟨tr', htr', e⟩ := List.mem_map.mp hb
    have hst : ∃ tr ∈ staying key (join key old new) p,
        (tr.key, tr.change.property) = a := by
      rcases List.mem_append.mp ha with h | h
      · obtain ⟨tr, htr, e'⟩ := List.mem_map.mp h
        exact ⟨tr, List.mem_append_left _ htr, e'⟩
      · obtain ⟨tr, htr, e'⟩ := List.mem_map.mp h
        exact ⟨tr, List.mem_append_right _ htr, e'⟩
    obtain ⟨tr, htr, e'⟩ := hst
    obtain ⟨n, hn, hk⟩ := mem_staying_key key old new p htr
    obtain ⟨_, _, _, hne⟩ := mem_leaving_key key old new p htr'
    exact hne n hn (hk.trans (congrArg Prod.fst (e'.trans e.symm)))

end Motion

/-! ## Finite evaluations

A thing is a key and a place along one axis. The plan `places` moves a kept thing whose place
changed, grows a new thing and shrinks an old one. In the first step the thing `1` stays where
it is and has no track, the thing `2` moves, the thing `4` is new and the thing `3` leaves. -/

#guard
  let key : Nat × Int → Nat := Prod.fst
  let places : Plan (Nat × Int) :=
    ⟨Plan.moving (fun a => ⟨a.2, 0⟩) {}, fun _ => [(.grow 0 1000, {})],
      fun _ => [(.grow 1000 0, {})]⟩
  (Motion.ofJoin key (join key [(1, 0), (2, 5), (3, 9)] [(1, 0), (2, 7), (4, 1)]) places).map
      (fun tr => (tr.key, tr.change)) ==
    [(2, Change.shift ⟨-2, 0⟩ 0), (4, Change.grow 0 1000), (3, Change.grow 1000 0)]

-- The same step with a second plan for opacity: a new thing fades in, and an old one fades
-- out. The tracks of one thing stand together.
#guard
  let key : Nat × Int → Nat := Prod.fst
  let places : Plan (Nat × Int) :=
    ⟨Plan.moving (fun a => ⟨a.2, 0⟩) {}, fun _ => [(.grow 0 1000, {})],
      fun _ => [(.grow 1000 0, {})]⟩
  let fades : Plan (Nat × Int) :=
    ⟨fun _ _ => [], fun _ => [(.fade 0 1000, {})], fun _ => [(.fade 1000 0, {})]⟩
  (Motion.ofJoin key (join key [(1, 0), (2, 5), (3, 9)] [(1, 0), (2, 7), (4, 1)])
      (places.and fades)).map (fun tr => (tr.key, tr.change)) ==
    [(2, Change.shift ⟨-2, 0⟩ 0), (4, Change.grow 0 1000), (4, Change.fade 0 1000),
      (3, Change.grow 1000 0), (3, Change.fade 1000 0)]

-- A plan written directly: a kept thing moves where its place changed, and its shape changes
-- in every case. The thing `1`, which has not moved, has the one track of its shape.
#guard
  let key : Nat × Int → Nat := Prod.fst
  let p : Plan (Nat × Int) :=
    { kept := fun o n => Plan.moving (fun a => ⟨a.2, 0⟩) {} o n ++ [(.morph [] [], {})]
      enter := fun _ => []
      leave := fun _ => [] }
  (Motion.ofJoin key (join key [(1, 0), (2, 5)] [(1, 0), (2, 7)]) p).map
      (fun tr => (tr.key, tr.change)) ==
    [(1, Change.morph [] []), (2, Change.shift ⟨-2, 0⟩ 0), (2, Change.morph [] [])]

-- A control of `Motion.staying_still`, which needs distinct keys in the new list. Two new
-- things have the key `1`. The first stands where the old thing stood, and the second does not:
-- the key has a pose.
#guard
  let key : Nat × Int → Nat := Prod.fst
  let places : Plan (Nat × Int) :=
    ⟨Plan.moving (fun a => ⟨a.2, 0⟩) {}, fun _ => [(.grow 0 1000, {})],
      fun _ => [(.grow 1000 0, {})]⟩
  (Motion.staying key (join key [(1, 0)] [(1, 0), (1, 4)]) places).posesOf 1 0 ==
    [Pose.shift ⟨-4, 0⟩]

-- A control of `Motion.staying_end`, which needs a plan that settles. A new thing that grows to
-- half its size is over at the step's end, and it is not at rest there.
#guard
  let p : Plan Nat := ⟨fun _ _ => [], fun _ => [(.grow 0 500, {})], fun _ => []⟩
  (Motion.staying id (join id [] [7]) p).within.map (fun tr => decide (tr.at 1000).AtRest) ==
    [false]

end Whatwg.Svg.Scene
