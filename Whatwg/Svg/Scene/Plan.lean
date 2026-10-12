import Whatwg.Svg.Scene.Motion.Laws

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
- `Plan.Settles`: every change that `kept` and `enter` give ends at rest. `Plan.Proper`: every
  easing of the plan starts at `0` and ends at `1000`.
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
- `Motion.staying_still`: a kept thing that the plan gives no change has no pose at any moment,
  where the keys of the new list are distinct. A reader draws it as it is.
- **The last picture** (`Motion.ofJoin_end`): at the step's end and after, every pose that the
  step sets on a thing of the new list is at rest. With `Join.drawn_end`, the things drawn then
  are the new list, each as the still picture has it.
- `Motion.ofJoin_still`: the plan in which nothing happens gives no track.
  `Motion.mem_ofJoin_and`: a track of two plans together is a track of one or of the other.

How a reader draws a moment `t`. It draws the things of `Join.drawn`: the old things that leave,
until the step's end, and then the things of the new list. It puts on each the poses of its key
(`Motion.posesOf`) in `(Motion.ofJoin key j p).within`. From the moment `1000` on it drops the
leaving things, and the poses of the others change nothing.

What this module does not claim: that a thing that leaves ends as nothing, since the plan's
`leave` may be any changes and a caller chooses some that end so; that two changes of one kind
on one thing agree, since the later one wins in a reader that sets a property once; an order in
time among the tracks, which is `Whatwg/Svg/Scene/Score.lean`; what holds between the two
pictures, which is `Whatwg/Svg/Scene/Between.lean`.

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

/-- **A kept thing that the plan gives no change has no pose**, at any moment, where the keys
of the new list are distinct. With `Plan.moving`, that is a thing whose place did not change
(`Plan.moving_nil`). -/
theorem staying_still [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (p : Plan α)
    (hd : Distinct key new) {o n : α} (hu : (o, n) ∈ (join key old new).update)
    (hk : p.kept o n = []) (t : Nat) :
    (staying key (join key old new) p).posesOf (key n) t = [] := by
  refine still_of_no_track _ (key n) t fun tr htr he => ?_
  obtain ⟨ho, hn, hon⟩ := mem_update key old new hu
  rcases (mem_staying key (join key old new) p).mp htr with
    ⟨⟨o', n'⟩, hq, c, hc, rfl⟩ | ⟨n', hn', _, _, rfl⟩
  · have hc' : c ∈ p.kept o' n' := hc
    have e : n' = n := eq_of_distinct key new hd n' n (mem_update key old new hq).2.1 hn he
    subst e
    have e2 : o' = o := Option.some.inj
      (((mem_update_find key old new).mp hq).2.symm.trans ((mem_update_find key old new).mp hu).2)
    subst e2
    rw [hk] at hc'
    exact absurd hc' List.not_mem_nil
  · exact ((mem_enter key old new).mp hn').2 o ho (hon.trans he.symm)

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
