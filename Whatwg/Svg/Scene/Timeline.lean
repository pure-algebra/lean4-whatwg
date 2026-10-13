import Whatwg.Svg.Scene.Plan
import Whatwg.Svg.Scene.Score

/-!
# Whatwg.Svg.Scene.Timeline

Owner: motions put together in time, and what the result shows (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Motion.lean` starts tracks later (`Motion.delayed`), and
`Whatwg/Svg/Scene/Score.lean` puts one motion after another (`Motion.andThen`) and says which
orders in time such a motion respects. Neither says what the result shows at a moment or how
long it lasts, so a caller that composes two motions has to read the tracks again. lean4-effect4
composes by hand: its sampler adds a delay for each line (`c.write.after (i * c.stagger)` of its
`tools/Tools/View/Motion.lean`) and starts each level at `enterFrom + level * slot`. This
module has the laws of the composite. No definition of another module changes.

- `Transition.later`, `Track.later`, `Motion.later m d`: the same thing, started `d` later. It
  is `Motion.delayed` with one delay for every key (`Motion.later_eq_delayed`), and
  `Transition.after` is it held inside the step (`Transition.after_eq_later`).
- **A motion started later shows the same, later** (`Motion.poses_later`,
  `Motion.posesOf_later`, `Motion.frame_later`): at the moment `t + d` it shows what the motion
  shows at `t`. No premise: it holds of every easing and every timing. Before `d` it shows the
  start of each easing (`Motion.poses_later_before`).
- **Time is one more way to move** (the instances of `Moves`): a transition, a track and so a
  motion move by a number of thousandths, as a point moves by a step. Starting later by nothing
  changes nothing, and two delays are their sum (`Motion.later_zero`, `Motion.later_later`). So
  the laws of `Whatwg/Svg/Scene/Moves.lean` are laws of time: a result computed for a motion
  stands for the motion started later (`Commutes.stored`). `Motion.reduced_commutes` is the
  first function that commutes: less motion, started later, is the later motion with less.
- **How long a composite lasts.** Two motions together end when the later one ends
  (`Motion.finish_append`). A motion started later ends that much later (`Motion.finish_later`).
  One motion after another lasts the two lengths together (`Motion.finish_andThen`), and a row
  of them the sum (`Motion.finish_inOrder`).
- **One after another is a monoid** (`Motion.nil_andThen`, `Motion.andThen_nil`,
  `Motion.andThen_assoc`): no motion is its unit, and three in a row are one row whichever two
  are joined first. `Motion.inOrder` is a row of motions, and a row of two rows is the row of
  the first after the row of the second (`Motion.inOrder_append`).
- **What a row shows** (`Motion.andThen_poses`): at the moment `t` after the first motion has
  ended, the first shows what it shows then and the second what it shows at `t`. With proper
  easings the first is at the end of each change (`Motion.andThen_poses_done`). Until the first
  has ended the second is at its start (`Motion.andThen_poses_before`). For one thing: a thing
  that the second motion alone moves has the frame of the second at `t`
  (`Motion.andThen_frame_second`), and a thing that the first alone moves has the frame of the
  first at every moment (`Motion.andThen_frame_first`).
- **An order in time does not depend on when the motion starts** (`Motion.later_respects`).
- **A plan started later** (`Plan.later`): each thing does what the plan says, `d` later. The
  tracks of a join under it are the tracks under the plan, started later
  (`Motion.ofJoin_later`), and it settles, is proper and gives one change for each property
  where the plan does. With `Plan.and`, `p.and (q.later d)` is the plan in which each thing
  does what `p` says and then, from `d` on, what `q` says. A `Step` takes it as any plan.

What this module does not claim: anything for `Motion.andThen` with an overlap, where the
second motion starts before the first has ended; that `Motion.within` commutes with a later
start, since the cut at the step's end does not; that a row of motions fits in a step, which
`Motion.fit` and `Motion.endBy` are for; a run of several steps as one value.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

variable {α κ : Type}

/-! ## Started later -/

/-- The transition, started `d` later. -/
def Transition.later (tr : Transition) (d : Nat) : Transition := { tr with delay := tr.delay + d }

/-- The track, started `d` later. -/
def Track.later (tr : Track κ) (d : Nat) : Track κ := { tr with timing := tr.timing.later d }

/-- **The motion, started `d` later**: every track with the same key, the same change and the
same easing, `d` thousandths later. -/
def Motion.later (m : Motion κ) (d : Nat) : Motion κ := m.map fun tr => tr.later d

namespace Transition

/-- Started later by nothing, a transition is itself. -/
theorem later_zero (tr : Transition) : tr.later 0 = tr := rfl

/-- Two delays are their sum. -/
theorem later_later (tr : Transition) (d e : Nat) : (tr.later d).later e = tr.later (d + e) := by
  show ({ tr with delay := tr.delay + d + e } : Transition) =
    { tr with delay := tr.delay + (d + e) }
  rw [Nat.add_assoc]

/-- **A transition started later reads the same, later**: at the moment `t + d` it reads what
the transition reads at `t`. -/
theorem later_at (tr : Transition) (d t : Nat) : (tr.later d).at (t + d) = tr.at t := by
  show (if tr.delay + d + tr.duration ≤ t + d then tr.ease.at 1000
      else if t + d ≤ tr.delay + d then tr.ease.at 0
      else tr.ease.of (t + d - (tr.delay + d)) tr.duration) =
    (if tr.delay + tr.duration ≤ t then tr.ease.at 1000
      else if t ≤ tr.delay then tr.ease.at 0 else tr.ease.of (t - tr.delay) tr.duration)
  by_cases h1 : tr.delay + tr.duration ≤ t
  · rw [if_pos h1, if_pos (show tr.delay + d + tr.duration ≤ t + d by omega)]
  · rw [if_neg h1, if_neg (show ¬ tr.delay + d + tr.duration ≤ t + d by omega)]
    by_cases h2 : t ≤ tr.delay
    · rw [if_pos h2, if_pos (show t + d ≤ tr.delay + d by omega)]
    · rw [if_neg h2, if_neg (show ¬ t + d ≤ tr.delay + d by omega),
        show t + d - (tr.delay + d) = t - tr.delay by omega]

/-- **`Transition.after` is a later start, held inside the step**: the consumer's stagger. -/
theorem after_eq_later (tr : Transition) (d : Nat) : tr.after d = (tr.later d).within := rfl

/-- Before its new start, a transition started later reads the start of its easing. -/
theorem later_before (tr : Transition) {d t : Nat} (h : t < d) :
    (tr.later d).at t = tr.ease.at 0 := by
  show (if tr.delay + d + tr.duration ≤ t then tr.ease.at 1000
      else if t ≤ tr.delay + d then tr.ease.at 0
      else tr.ease.of (t - (tr.delay + d)) tr.duration) = tr.ease.at 0
  rw [if_neg (show ¬ tr.delay + d + tr.duration ≤ t by omega),
    if_pos (show t ≤ tr.delay + d by omega)]

end Transition

namespace Track

/-- Started later by nothing, a track is itself. -/
theorem later_zero (tr : Track κ) : tr.later 0 = tr := rfl

/-- Two delays are their sum. -/
theorem later_later (tr : Track κ) (d e : Nat) : (tr.later d).later e = tr.later (d + e) := by
  show ({ tr with timing := (tr.timing.later d).later e } : Track κ) =
    { tr with timing := tr.timing.later (d + e) }
  rw [Transition.later_later]

/-- **A track started later shows the same, later.** -/
theorem later_at (tr : Track κ) (d t : Nat) : (tr.later d).at (t + d) = tr.at t :=
  congrArg tr.change.at (Transition.later_at tr.timing d t)

/-- Before its new start, a track started later is where its easing starts. -/
theorem later_before (tr : Track κ) {d t : Nat} (h : t < d) :
    (tr.later d).at t = tr.change.at (tr.timing.ease.at 0) :=
  congrArg tr.change.at (Transition.later_before tr.timing h)

end Track

/-- A transition moves in time: by a number of thousandths. -/
instance : Moves Nat Transition where
  move d tr := tr.later d
  move_zero := Transition.later_zero
  move_move d e tr := Transition.later_later tr d e

/-- A track moves in time, and so does a motion, which is a list of tracks. -/
instance : Moves Nat (Track κ) where
  move d tr := tr.later d
  move_zero := Track.later_zero
  move_move d e tr := Track.later_later tr d e

namespace Motion

/-! ## A motion started later -/

/-- A motion started later is the motion with one delay for every key. -/
theorem later_eq_delayed (m : Motion κ) (d : Nat) : m.later d = m.delayed fun _ => d := rfl

/-- A motion started later is the motion, moved in time. -/
theorem later_eq_move (m : Motion κ) (d : Nat) : m.later d = Moves.move d m := rfl

theorem later_nil (d : Nat) : later ([] : Motion κ) d = [] := rfl

/-- Started later by nothing, a motion is itself. -/
theorem later_zero (m : Motion κ) : m.later 0 = m :=
  (List.map_congr_left fun _ _ => rfl).trans (List.map_id m)

/-- Two delays are their sum. -/
theorem later_later (m : Motion κ) (d e : Nat) : (m.later d).later e = m.later (d + e) := by
  show (m.map fun tr => tr.later d).map (fun tr => tr.later e) = m.map fun tr => tr.later (d + e)
  rw [List.map_map]
  exact List.map_congr_left fun tr _ => Track.later_later tr d e

/-- Two motions together, started later, are the two started later, together. -/
theorem later_append (a b : Motion κ) (d : Nat) : (a ++ b).later d = a.later d ++ b.later d :=
  List.map_append

/-- The tracks of each member of a list in a row, started later. -/
theorem later_flatMap {β : Type} (l : List β) (f : β → Motion κ) (d : Nat) :
    later (l.flatMap f) d = l.flatMap fun a => later (f a) d :=
  List.map_flatMap

/-- A motion started later has as many tracks. -/
theorem length_later (m : Motion κ) (d : Nat) : (m.later d).length = m.length := List.length_map _

/-- A track of a motion started later is a track of the motion, started later. -/
theorem mem_later {m : Motion κ} {d : Nat} {tr : Track κ} (h : tr ∈ m.later d) :
    ∃ tr0 ∈ m, tr = tr0.later d := by
  obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp h
  exact ⟨tr0, h0, rfl⟩

/-- **A motion started later shows the same, later**: every key with its pose, track by track,
at the moment `t + d`, is what the motion shows at `t`. -/
theorem poses_later (m : Motion κ) (d t : Nat) : (m.later d).poses (t + d) = m.poses t := by
  show (m.map fun tr => tr.later d).map (fun tr => (tr.key, tr.at (t + d))) =
    m.map fun tr => (tr.key, tr.at t)
  rw [List.map_map]
  exact List.map_congr_left fun tr _ => congrArg (Prod.mk tr.key) (Track.later_at tr d t)

/-- Before its new start, a motion started later has each track where its easing starts. -/
theorem poses_later_before (m : Motion κ) {d t : Nat} (h : t < d) :
    (m.later d).poses t = m.map fun tr => (tr.key, tr.change.at (tr.timing.ease.at 0)) := by
  show (m.map fun tr => tr.later d).map (fun tr => (tr.key, tr.at t)) =
    m.map fun tr => (tr.key, tr.change.at (tr.timing.ease.at 0))
  rw [List.map_map]
  exact List.map_congr_left fun tr _ => congrArg (Prod.mk tr.key) (Track.later_before tr h)

/-- The tracks of one key in a motion started later are its tracks in the motion, started
later. -/
theorem filter_later [BEq κ] (key : κ) (d : Nat) : ∀ m : Motion κ,
    (m.later d).filter (fun tr => tr.key == key) = later (m.filter fun tr => tr.key == key) d
  | [] => rfl
  | x :: rest => by
    show ((x.later d) :: later rest d).filter (fun tr => tr.key == key) =
      later ((x :: rest).filter fun tr => tr.key == key) d
    rw [List.filter_cons, List.filter_cons, filter_later key d rest]
    show (if (x.key == key) = true then
          x.later d :: later (rest.filter fun tr => tr.key == key) d
        else later (rest.filter fun tr => tr.key == key) d) =
      later (if (x.key == key) = true then x :: rest.filter (fun tr => tr.key == key)
        else rest.filter fun tr => tr.key == key) d
    cases x.key == key with
    | true => rfl
    | false => rfl

/-- **The poses of one key in a motion started later are its poses in the motion, later.** -/
theorem posesOf_later [BEq κ] (m : Motion κ) (key : κ) (d t : Nat) :
    (m.later d).posesOf key (t + d) = m.posesOf key t := by
  show ((m.later d).filter fun tr => tr.key == key).map (fun tr => tr.at (t + d)) =
    (m.filter fun tr => tr.key == key).map fun tr => tr.at t
  rw [filter_later]
  show ((m.filter fun tr => tr.key == key).map fun tr => tr.later d).map
    (fun tr => tr.at (t + d)) = (m.filter fun tr => tr.key == key).map fun tr => tr.at t
  rw [List.map_map]
  exact List.map_congr_left fun tr _ => Track.later_at tr d t

/-- **What a thing looks like under a motion started later is what it looks like under the
motion, later.** -/
theorem frame_later [BEq κ] (m : Motion κ) (key : κ) (d t : Nat) :
    (m.later d).frame key (t + d) = m.frame key t :=
  congrArg Frame.ofPoses (posesOf_later m key d t)

/-- Less motion, started later, is the later motion with less: `Motion.reduced` commutes with a
move in time. -/
theorem reduced_commutes : Commutes (Motion.reduced : Motion κ → Motion κ) :=
  Commutes.map fun _ _ => rfl

/-- **An order in time does not depend on when the motion starts.** -/
theorem later_respects (before : κ → κ → Prop) (m : Motion κ) (d : Nat)
    (h : m.Respects before) : (m.later d).Respects before := by
  intro a ha b hb hab
  obtain ⟨a0, ha0, rfl⟩ := mem_later ha
  obtain ⟨b0, hb0, rfl⟩ := mem_later hb
  have h1 := h a0 ha0 b0 hb0 hab
  show a0.timing.delay + d + a0.timing.duration ≤ b0.timing.delay + d
  omega

/-! ## How long a composite lasts -/

/-- **Two motions together end when the later one ends.** -/
theorem finish_append : ∀ a b : Motion κ, (a ++ b).finish = max a.finish b.finish
  | [], b => (Nat.zero_max _).symm
  | x :: rest, b => by
    show max (x.timing.delay + x.timing.duration) (finish (rest ++ b)) =
      max (max (x.timing.delay + x.timing.duration) (finish rest)) b.finish
    rw [finish_append rest b, Nat.max_assoc]

/-- **A motion started later ends that much later**, where it has a track. -/
theorem finish_later : ∀ (m : Motion κ) (d : Nat), m ≠ [] → (m.later d).finish = m.finish + d
  | [], _, h => absurd rfl h
  | [x], d, _ => by
    show max (x.timing.delay + d + x.timing.duration) 0 =
      max (x.timing.delay + x.timing.duration) 0 + d
    omega
  | x :: y :: rest, d, _ => by
    have ih := finish_later (y :: rest) d (List.cons_ne_nil y rest)
    show max (x.timing.delay + d + x.timing.duration) (finish (later (y :: rest) d)) =
      max (x.timing.delay + x.timing.duration) (finish (y :: rest)) + d
    rw [ih]
    omega

/-- A motion started later ends by that much later, with a track or with none. -/
theorem finish_later_le (m : Motion κ) (d : Nat) : (m.later d).finish ≤ m.finish + d := by
  cases m with
  | nil => exact Nat.zero_le _
  | cons x rest => exact Nat.le_of_eq (finish_later (x :: rest) d (List.cons_ne_nil x rest))

/-- **One motion after another lasts the two lengths together.** -/
theorem finish_andThen (a b : Motion κ) : (a.andThen b).finish = a.finish + b.finish := by
  show (a ++ b.later a.finish).finish = a.finish + b.finish
  rw [finish_append]
  cases b with
  | nil =>
    show max a.finish 0 = a.finish + 0
    omega
  | cons x rest =>
    rw [finish_later (x :: rest) a.finish (List.cons_ne_nil x rest)]
    omega

/-! ## One after another is a monoid -/

/-- One motion after another is the first, then the second started when the first ends. -/
theorem andThen_eq_later (a b : Motion κ) : a.andThen b = a ++ b.later a.finish := rfl

/-- After no motion, a motion is itself. -/
theorem nil_andThen (b : Motion κ) : andThen ([] : Motion κ) b = b := later_zero b

/-- A motion with no motion after it is itself. -/
theorem andThen_nil (a : Motion κ) : a.andThen [] = a := List.append_nil a

/-- **Three motions in a row are one row**, whichever two are joined first. -/
theorem andThen_assoc (a b c : Motion κ) :
    (a.andThen b).andThen c = a.andThen (b.andThen c) := by
  show (a ++ b.later a.finish) ++ c.later (a.andThen b).finish =
    a ++ (b ++ c.later b.finish).later a.finish
  rw [finish_andThen, later_append, later_later, List.append_assoc,
    Nat.add_comm b.finish a.finish]

/-- **A row of motions**: each starts when the one before it has ended. -/
def inOrder : List (Motion κ) → Motion κ
  | [] => []
  | m :: rest => m.andThen (inOrder rest)

/-- **A row of motions lasts the sum of their lengths.** -/
theorem finish_inOrder : ∀ ms : List (Motion κ), (inOrder ms).finish = (ms.map finish).sum
  | [] => rfl
  | m :: rest => by
    show (m.andThen (inOrder rest)).finish = m.finish + (rest.map finish).sum
    rw [finish_andThen, finish_inOrder rest]

/-- **A row of two rows is the row of the first, and after it the row of the second.** -/
theorem inOrder_append : ∀ xs ys : List (Motion κ),
    inOrder (xs ++ ys) = (inOrder xs).andThen (inOrder ys)
  | [], ys => (nil_andThen (inOrder ys)).symm
  | m :: rest, ys => by
    show m.andThen (inOrder (rest ++ ys)) = (m.andThen (inOrder rest)).andThen (inOrder ys)
    rw [inOrder_append rest ys, andThen_assoc]

/-! ## What a row shows -/

/-- Two motions together show what each shows. -/
theorem poses_append (a b : Motion κ) (t : Nat) : (a ++ b).poses t = a.poses t ++ b.poses t :=
  List.map_append

/-- **What a row shows after its first motion has ended**: at the moment `t` after that end,
the first motion shows what it shows then, and the second what it shows at `t`. -/
theorem andThen_poses (a b : Motion κ) (t : Nat) :
    (a.andThen b).poses (t + a.finish) = a.poses (t + a.finish) ++ b.poses t := by
  show (a ++ b.later a.finish).poses (t + a.finish) = a.poses (t + a.finish) ++ b.poses t
  rw [poses_append, poses_later]

/-- **After the first motion of a row has ended, each of its tracks is at the end of its
change**, with proper easings, and the second motion shows what it shows by itself. -/
theorem andThen_poses_done (a b : Motion κ) (hp : ∀ tr ∈ a, tr.timing.ease.Proper) (t : Nat) :
    (a.andThen b).poses (t + a.finish) =
      (a.map fun tr => (tr.key, tr.change.stop)) ++ b.poses t := by
  rw [andThen_poses, poses_done a (t + a.finish) fun tr h =>
    ⟨hp tr h, Nat.le_trans (finish_le a tr h) (Nat.le_add_left _ _)⟩]

/-- **Until the first motion of a row has ended, the second is at its start**: each of its
tracks is where its easing starts. -/
theorem andThen_poses_before (a b : Motion κ) {t : Nat} (h : t < a.finish) :
    (a.andThen b).poses t =
      a.poses t ++ b.map fun tr => (tr.key, tr.change.at (tr.timing.ease.at 0)) := by
  show (a ++ b.later a.finish).poses t = _
  rw [poses_append, poses_later_before b h]

/-- **A thing that the second motion of a row alone moves** looks, at the moment `t` after the
first has ended, as the second motion shows it at `t`. -/
theorem andThen_frame_second [BEq κ] [LawfulBEq κ] (a b : Motion κ) (key : κ) (t : Nat)
    (h : ∀ tr ∈ a, tr.key ≠ key) : (a.andThen b).frame key (t + a.finish) = b.frame key t := by
  show (a ++ b.later a.finish).frame key (t + a.finish) = b.frame key t
  rw [frame_append, frame_of_no_track a key _ h]
  exact congrArg Frame.ofPoses (posesOf_later b key a.finish t)

/-- **A thing that the first motion of a row alone moves** looks at every moment as the first
motion shows it. -/
theorem andThen_frame_first [BEq κ] [LawfulBEq κ] (a b : Motion κ) (key : κ) (t : Nat)
    (h : ∀ tr ∈ b, tr.key ≠ key) : (a.andThen b).frame key t = a.frame key t := by
  have hb : ∀ tr ∈ b.later a.finish, tr.key ≠ key := fun tr htr => by
    obtain ⟨tr0, h0, rfl⟩ := mem_later htr
    exact h tr0 h0
  show (a ++ b.later a.finish).frame key t = a.frame key t
  rw [frame_append, still_of_no_track _ key t hb]
  rfl

end Motion

/-! ## A plan started later -/

/-- **The plan, started `d` later**: each thing does what the plan gives it, `d` thousandths
later. With `Plan.and`, `p.and (q.later d)` is one plan in which each thing does what `p` says
and, from `d` on, what `q` says. -/
def Plan.later (p : Plan α) (d : Nat) : Plan α where
  kept o n := (p.kept o n).map fun c => (c.1, c.2.later d)
  enter n := (p.enter n).map fun c => (c.1, c.2.later d)
  leave o := (p.leave o).map fun c => (c.1, c.2.later d)

namespace Plan

/-- A plan that settles, started later, settles. -/
theorem later_settles {p : Plan α} (h : p.Settles) (d : Nat) : (p.later d).Settles :=
  ⟨fun o n c hc => by
      obtain ⟨c0, h0, rfl⟩ := List.mem_map.mp hc
      exact h.1 o n c0 h0,
    fun n c hc => by
      obtain ⟨c0, h0, rfl⟩ := List.mem_map.mp hc
      exact h.2 n c0 h0⟩

/-- A proper plan, started later, is proper. -/
theorem later_proper {p : Plan α} (h : p.Proper) (d : Nat) : (p.later d).Proper :=
  ⟨fun o n c hc => by
      obtain ⟨c0, h0, rfl⟩ := List.mem_map.mp hc
      exact h.1 o n c0 h0,
    fun n c hc => by
      obtain ⟨c0, h0, rfl⟩ := List.mem_map.mp hc
      exact h.2.1 n c0 h0,
    fun o c hc => by
      obtain ⟨c0, h0, rfl⟩ := List.mem_map.mp hc
      exact h.2.2 o c0 h0⟩

/-- A plan with one change for each property, started later, has one for each. -/
theorem later_single {p : Plan α} (h : p.Single) (d : Nat) : (p.later d).Single := by
  have e : ∀ cs : List (Change × Transition),
      (cs.map fun c => (c.1, c.2.later d)).map (fun c => c.1.property) =
        cs.map fun c => c.1.property := fun cs =>
    List.map_map.trans (List.map_congr_left fun _ _ => rfl)
  refine ⟨fun o n => ?_, fun n => ?_, fun o => ?_⟩
  · show (((p.kept o n).map fun c => (c.1, c.2.later d)).map fun c => c.1.property).Nodup
    rw [e]
    exact h.1 o n
  · show (((p.enter n).map fun c => (c.1, c.2.later d)).map fun c => c.1.property).Nodup
    rw [e]
    exact h.2.1 n
  · show (((p.leave o).map fun c => (c.1, c.2.later d)).map fun c => c.1.property).Nodup
    rw [e]
    exact h.2.2 o

end Plan

namespace Motion

/-- The tracks of one thing whose changes start later are its tracks, started later. -/
theorem tracks_later (k : κ) (cs : List (Change × Transition)) (d : Nat) :
    tracks k (cs.map fun c => (c.1, c.2.later d)) = (tracks k cs).later d := by
  show (cs.map fun c => (c.1, c.2.later d)).map (fun c => (⟨k, c.1, c.2⟩ : Track κ)) =
    (cs.map fun c => (⟨k, c.1, c.2⟩ : Track κ)).map fun tr => tr.later d
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun _ _ => rfl

/-- **The tracks of a join under a plan started later are its tracks under the plan, started
later.** So every law of this module about a motion started later is a law of a step under such
a plan. -/
theorem ofJoin_later (key : α → κ) (j : Join α) (p : Plan α) (d : Nat) :
    ofJoin key j (p.later d) = (ofJoin key j p).later d := by
  show (j.update.flatMap (fun q => tracks (key q.2) ((p.later d).kept q.1 q.2)) ++
      j.enter.flatMap (fun n => tracks (key n) ((p.later d).enter n))) ++
      j.exit.flatMap (fun o => tracks (key o) ((p.later d).leave o)) =
    later ((j.update.flatMap (fun q => tracks (key q.2) (p.kept q.1 q.2)) ++
      j.enter.flatMap (fun n => tracks (key n) (p.enter n))) ++
      j.exit.flatMap (fun o => tracks (key o) (p.leave o))) d
  rw [later_append, later_append, later_flatMap, later_flatMap, later_flatMap]
  simp only [Plan.later, tracks_later]

end Motion

end Whatwg.Svg.Scene
