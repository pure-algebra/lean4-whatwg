import Whatwg.Svg.Scene.Step.Laws
import Whatwg.Svg.Scene.Timeline

/-!
# Whatwg.Svg.Scene.Reel

Owner: a run of steps, as one value (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Step.lean` has one step from a picture to the next, and `Step.next` for the
step after it. A program that shows a run has a list of pictures and plays the steps between
them one after another. lean4-effect4 does so by hand: `Run.framesBuilt` of its
`tools/Tools/View/Run.lean` makes the pictures, and `writeFrames` of its
`tools/Drivers/View.lean` loops over them, writes some moments of each step and then the
picture itself. Here the run is a value, and a moment of the run is a function of it.

- `Reel α κ`: the key, the plan, the first picture and the pictures after it. `stages` gives
  the stages of the step between two pictures, and none unless given.
- `Reel.picture k`: the picture `k`, and the last picture from the end on. `Reel.step k`: the
  step from the picture `k` to the next. `Reel.span`: the length of the run, a thousand for
  each step.
- `Reel.at T`: **the run at the moment `T`**: the things drawn then, each with its frame.
- `Reel.moments per` and `Reel.frames per`: the moments that a player shows, `per` of each step,
  and the run at each. It is the consumer's loop.
- `Reel.extend newer`: the run with one more picture.
- `Reel.motions` and `Reel.playtime`: the motions of the steps, and how long the run lasts when
  each step begins as soon as the one before it is over (`Motion.inOrder` of
  `Whatwg/Svg/Scene/Timeline.lean`).

**One decision, and its reasons.** Two steps meet at a joint, the moment `1000 k`. It is the
last moment of the step before and the first moment of the step after, and the two show
different things: the step before shows the picture `k` at rest, and the step after shows, with
the things of the picture `k`, each thing that is about to enter, at the start of its entrance.
The run reads a joint as the last moment of the step before. So **a thing that is about to
enter is not drawn at the joint**: the step `k` is read at the moments after `1000 k`, up to
`1000 (k + 1)` and with it, and its own first moment is passed over. The reasons:

1. A joint is where a player rests. The picture it rests on is a picture of the run, and a
   thing that enters in the next step is no part of it, whatever its entrance starts from.
2. The law of the joint is then an equation with no premise on the entrances: the run at
   `1000 k` is the picture `k`, every thing at rest (`Reel.at_joint`). Read the other way, it
   would hold only of plans whose entrances start from nothing, and only as "looks like".
3. It is what the consumer does. `writeFrames` writes the moments `k * 1000 / motion` of a
   step for `k` from `1` on, and then the picture itself, by its law `sample_end`.

What the laws say:

- `Reel.at_zero`, `Reel.at_inside`, `Reel.at_joint`, `Reel.at_end`: the run starts on its first
  picture at rest; between two joints it is the step, sampled; **at every joint it is the
  picture at rest**; from its end on it is the last picture at rest.
- **The step after starts from the joint** (`Reel.joint_stands`, `Reel.joint_whole`): at its
  first moment, which the run passes over, a kept thing stands where the joint has it, with its
  whole size, its whole line and its whole opacity. So from the joint to the first moment that
  is played a kept thing does what one moment of its transition does, and nothing jumps. They
  are `Step.nothing_moves` and `Step.nothing_jumps` at the end of the step before, where an
  interruption is an ordinary step (`Step.interrupt_of_rest`).
- `Reel.step_old`: each step starts from the picture that the step before ended on.
  `Reel.step_next`: with no stages it is `Step.next` of the step before.
- `Reel.at_extend`: a run with one more picture is the same run up to its old end.
- `Reel.length_moments`, `Reel.joint_mem_moments`: a player that shows `per` moments of each
  step shows one picture and `per` for each step, and every picture of the run at rest is among
  them.
- `Reel.playtime_eq`, `Reel.playtime_le`: played with no waiting, the run lasts the lengths of
  its steps together, which is the span at the most.

What this module does not claim. A plan that is made from the join of a step (`Step.planned`)
is not a field of a reel: the plan is one for the run. The two joint laws are of a step after
that has no stages, as the laws of `Step.interrupt` are. `Reel.playtime` is a length, and the
motion it is the length of is not a motion to read frames from: a thing has tracks in several
steps under one key, and a reader sets a property once. Nothing is said of a run that is
interrupted, which is `Step.interrupt` of the step it is in.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

variable {α κ : Type}

/-- **A run of steps**: a first picture, and the pictures after it, each a step from the one
before under one plan. -/
structure Reel (α κ : Type) where
  /-- The name of what a thing draws. -/
  key : α → κ
  /-- What a kept thing, a new thing and a thing that leaves does, in every step. -/
  plan : Plan α
  /-- The first picture. -/
  first : List α
  /-- The pictures after the first, in order. -/
  rest : List (List α) := []
  /-- The stages of the step from one picture to another. With none, each thing moves when the
  plan says. -/
  stages : List α → List α → Option (Stages α) := fun _ _ => none

namespace Reel

/-- The picture `k` of a first picture and the pictures after it: the last from the end on. -/
def pictureOf : Nat → List α → List (List α) → List α
  | 0, first, _ => first
  | _ + 1, first, [] => first
  | k + 1, _, next :: rest => pictureOf k next rest

/-- A run of the pictures of a list, and of the empty picture for no picture. -/
def ofPictures (key : α → κ) (plan : Plan α) : List (List α) → Reel α κ
  | [] => { key, plan, first := [] }
  | first :: rest => { key, plan, first, rest }

/-- **The picture `k` of the run**, from `0`. From the end of the run on it is the last
picture. -/
def picture (r : Reel α κ) (k : Nat) : List α := pictureOf k r.first r.rest

/-- **The length of the run**: a thousand for each step. -/
def span (r : Reel α κ) : Nat := 1000 * r.rest.length

/-- **The step `k` of the run**: from the picture `k` to the next. -/
def step (r : Reel α κ) (k : Nat) : Step α κ :=
  { key := r.key, old := r.picture k, new := r.picture (k + 1), plan := r.plan,
    stages := r.stages (r.picture k) (r.picture (k + 1)) }

/-- **The run with one more picture** at its end. -/
def extend (r : Reel α κ) (newer : List α) : Reel α κ := { r with rest := r.rest ++ [newer] }

/-- **The moments that a player shows**: the start, and `per` moments of each step, evenly
spaced, the last of them the joint at the step's end. -/
def moments (r : Reel α κ) (per : Nat) : List Nat :=
  0 :: (List.range r.rest.length).flatMap fun k =>
    (List.range per).map fun j => 1000 * k + (j + 1) * 1000 / per

end Reel

/-- **The run at the moment `T`**: the things drawn then, each with its frame. At `0` it is the
first picture at rest. After that it is the step that the moment falls in, sampled: the step
`k` at the moments after `1000 k`, up to `1000 (k + 1)` and with it. A moment past the end reads
as the end. -/
def Reel.at [BEq κ] (r : Reel α κ) (T : Nat) : List (α × Frame) :=
  if min T r.span = 0 then r.first.map fun a => (a, Frame.rest)
  else (r.step ((min T r.span - 1) / 1000)).sample
    (min T r.span - 1000 * ((min T r.span - 1) / 1000))

namespace Reel

/-- **The run at each moment that a player shows**, `per` of each step. -/
def frames [BEq κ] (r : Reel α κ) (per : Nat) : List (List (α × Frame)) :=
  (r.moments per).map fun T => r.at T

/-- The motions of the steps of the run, in order. -/
def motions [BEq κ] (r : Reel α κ) : List (Motion κ) :=
  (List.range r.rest.length).map fun k => (r.step k).motion

/-- **How long the run lasts with no waiting**: each step begins as soon as the one before it
is over. A step in which nothing changes takes no time. -/
def playtime [BEq κ] (r : Reel α κ) : Nat := (Motion.inOrder r.motions).finish

/-! ## The pictures and the steps -/

/-- The first picture of the run is its picture `0`. -/
theorem picture_zero (r : Reel α κ) : r.picture 0 = r.first := rfl

/-- A run of the pictures of a list has the plan it was given. -/
theorem ofPictures_plan (key : α → κ) (plan : Plan α) (pictures : List (List α)) :
    (ofPictures key plan pictures).plan = plan := by
  cases pictures <;> rfl

/-- A run of the pictures of a list has the key it was given. -/
theorem ofPictures_key (key : α → κ) (plan : Plan α) (pictures : List (List α)) :
    (ofPictures key plan pictures).key = key := by
  cases pictures <;> rfl

/-- A run of the pictures of a list has a step for each picture but the first. -/
theorem ofPictures_length (key : α → κ) (plan : Plan α) (pictures : List (List α)) :
    (ofPictures key plan pictures).rest.length = pictures.length - 1 := by
  cases pictures <;> rfl

/-- **Each step starts from the picture that the step before ended on.** -/
theorem step_old (r : Reel α κ) (k : Nat) : (r.step (k + 1)).old = (r.step k).new := rfl

/-- **A step with no stages is `Step.next` of the step before.** -/
theorem step_next (r : Reel α κ) (k : Nat)
    (h : r.stages (r.picture (k + 1)) (r.picture (k + 2)) = none) :
    r.step (k + 1) = (r.step k).next (r.picture (k + 2)) r.plan := by
  show (⟨r.key, r.picture (k + 1), r.picture (k + 2), r.plan,
      r.stages (r.picture (k + 1)) (r.picture (k + 2))⟩ : Step α κ) =
    ⟨r.key, r.picture (k + 1), r.picture (k + 2), r.plan, none⟩
  rw [h]

/-- A picture of a list with one more picture at its end is the picture of the list, up to its
last. -/
theorem pictureOf_append (newer : List α) : ∀ (rest : List (List α)) (first : List α) (k : Nat),
    k ≤ rest.length → pictureOf k first (rest ++ [newer]) = pictureOf k first rest
  | _, _, 0, _ => rfl
  | [], _, k + 1, h => absurd h (Nat.not_succ_le_zero k)
  | next :: rest, _, k + 1, h => pictureOf_append newer rest next k (Nat.le_of_succ_le_succ h)

/-- The picture after the last of a list with one more picture is that picture. -/
theorem pictureOf_last (newer : List α) : ∀ (rest : List (List α)) (first : List α),
    pictureOf (rest.length + 1) first (rest ++ [newer]) = newer
  | [], _ => rfl
  | next :: rest, _ => pictureOf_last newer rest next

/-- The pictures of a run with one more picture are the pictures of the run, up to its last. -/
theorem picture_extend (r : Reel α κ) (newer : List α) {k : Nat} (h : k ≤ r.rest.length) :
    (r.extend newer).picture k = r.picture k :=
  pictureOf_append newer r.rest r.first k h

/-- The last picture of a run with one more picture is that picture. -/
theorem picture_extend_last (r : Reel α κ) (newer : List α) :
    (r.extend newer).picture (r.rest.length + 1) = newer :=
  pictureOf_last newer r.rest r.first

/-- The steps of a run with one more picture are the steps of the run. -/
theorem step_extend (r : Reel α κ) (newer : List α) {k : Nat} (h : k < r.rest.length) :
    (r.extend newer).step k = r.step k := by
  show (⟨r.key, (r.extend newer).picture k, (r.extend newer).picture (k + 1), r.plan,
      r.stages ((r.extend newer).picture k) ((r.extend newer).picture (k + 1))⟩ : Step α κ) =
    r.step k
  rw [picture_extend r newer (Nat.le_of_lt h), picture_extend r newer h]
  rfl

/-! ## The run at a moment -/

/-- **The run starts on its first picture, at rest.** -/
theorem at_zero [BEq κ] (r : Reel α κ) : r.at 0 = r.first.map fun a => (a, Frame.rest) := by
  show (if min 0 r.span = 0 then r.first.map fun a => (a, Frame.rest)
    else (r.step ((min 0 r.span - 1) / 1000)).sample
      (min 0 r.span - 1000 * ((min 0 r.span - 1) / 1000))) = _
  rw [if_pos (Nat.zero_min _)]

/-- A moment past the end reads as the end. -/
theorem at_clamp [BEq κ] (r : Reel α κ) (T : Nat) : r.at T = r.at (min T r.span) := by
  show (if min T r.span = 0 then r.first.map fun a => (a, Frame.rest)
      else (r.step ((min T r.span - 1) / 1000)).sample
        (min T r.span - 1000 * ((min T r.span - 1) / 1000))) =
    (if min (min T r.span) r.span = 0 then r.first.map fun a => (a, Frame.rest)
      else (r.step ((min (min T r.span) r.span - 1) / 1000)).sample
        (min (min T r.span) r.span - 1000 * ((min (min T r.span) r.span - 1) / 1000)))
  rw [Nat.min_assoc, Nat.min_self]

/-- **Between two joints the run is the step, sampled**: at the moment `t` of the step `k`,
after its first moment and up to its end, it is that step at `t`. -/
theorem at_inside [BEq κ] (r : Reel α κ) {k t : Nat} (hk : k < r.rest.length) (h0 : 0 < t)
    (h1 : t ≤ 1000) : r.at (1000 * k + t) = (r.step k).sample t := by
  have hm : min (1000 * k + t) r.span = 1000 * k + t := by
    show min (1000 * k + t) (1000 * r.rest.length) = 1000 * k + t
    omega
  have hq : (1000 * k + t - 1) / 1000 = k := by omega
  have ht : 1000 * k + t - 1000 * k = t := by omega
  have hne : ¬ 1000 * k + t = 0 := by omega
  show (if min (1000 * k + t) r.span = 0 then r.first.map fun a => (a, Frame.rest)
    else (r.step ((min (1000 * k + t) r.span - 1) / 1000)).sample
      (min (1000 * k + t) r.span - 1000 * ((min (1000 * k + t) r.span - 1) / 1000))) = _
  rw [hm, if_neg hne, hq, ht]

/-- The things of the run between two joints are the things that the step draws then. -/
theorem at_things [BEq κ] (r : Reel α κ) {k t : Nat} (hk : k < r.rest.length) (h0 : 0 < t)
    (h1 : t ≤ 1000) : (r.at (1000 * k + t)).map Prod.fst = (r.step k).drawn t := by
  rw [at_inside r hk h0 h1]
  exact (r.step k).sample_things t

/-- **At every joint the run is the picture, at rest**: at the moment `1000 k` its things are
the things of the picture `k` and no other, each as the still picture has it. The plan settles,
is proper and changes no shape of a thing that stays. No thing that is about to enter is
drawn. -/
theorem at_joint [BEq κ] [LawfulBEq κ] (r : Reel α κ) (hs : r.plan.Settles) (hp : r.plan.Proper)
    (hk : r.plan.KeepsShapes) {k : Nat} (h : k ≤ r.rest.length) :
    r.at (1000 * k) = (r.picture k).map fun a => (a, Frame.rest) := by
  cases k with
  | zero =>
    rw [picture_zero]
    exact r.at_zero
  | succ j =>
    have e : 1000 * (j + 1) = 1000 * j + 1000 := Nat.mul_succ 1000 j
    rw [e, at_inside r (Nat.lt_of_succ_le h) (by decide) (Nat.le_refl 1000)]
    exact (r.step j).sample_end_rest hs hp hk (Nat.le_refl 1000)

/-- **From its end on the run is its last picture, at rest.** -/
theorem at_end [BEq κ] [LawfulBEq κ] (r : Reel α κ) (hs : r.plan.Settles) (hp : r.plan.Proper)
    (hk : r.plan.KeepsShapes) {T : Nat} (h : r.span ≤ T) :
    r.at T = (r.picture r.rest.length).map fun a => (a, Frame.rest) := by
  rw [at_clamp, Nat.min_eq_right h]
  exact at_joint r hs hp hk (Nat.le_refl _)

/-- **A run with one more picture is the same run up to its old end.** What a run has shown
does not change when it goes on. -/
theorem at_extend [BEq κ] (r : Reel α κ) (newer : List α) {T : Nat} (h : T ≤ r.span) :
    (r.extend newer).at T = r.at T := by
  have hn : (r.extend newer).rest.length = r.rest.length + 1 := by
    show (r.rest ++ [newer]).length = r.rest.length + 1
    rw [List.length_append]
    rfl
  have hspan : r.span = 1000 * r.rest.length := rfl
  have hm1 : min T (r.extend newer).span = T := by
    show min T (1000 * (r.extend newer).rest.length) = T
    rw [hn]
    omega
  have hm2 : min T r.span = T := Nat.min_eq_left h
  show (if min T (r.extend newer).span = 0 then r.first.map fun a => (a, Frame.rest)
      else ((r.extend newer).step ((min T (r.extend newer).span - 1) / 1000)).sample
        (min T (r.extend newer).span - 1000 * ((min T (r.extend newer).span - 1) / 1000))) =
    (if min T r.span = 0 then r.first.map fun a => (a, Frame.rest)
      else (r.step ((min T r.span - 1) / 1000)).sample
        (min T r.span - 1000 * ((min T r.span - 1) / 1000)))
  rw [hm1, hm2]
  cases Nat.eq_zero_or_pos T with
  | inl h0 => rw [if_pos h0, if_pos h0]
  | inr hpos =>
    have hne : ¬ T = 0 := Nat.pos_iff_ne_zero.mp hpos
    have hlt : (T - 1) / 1000 < r.rest.length := by omega
    rw [if_neg hne, if_neg hne, step_extend r newer hlt]

/-! ## The step after starts from the joint -/

/-- The first moment of a step of the run is the first moment of the step that interrupts the
step before at its end. The plan settles, is proper, changes no shape of a thing that stays and
is written from rest, and the step has no stages. -/
theorem step_frame_zero [BEq κ] [LawfulBEq κ] (r : Reel α κ) (hs : r.plan.Settles)
    (hp : r.plan.Proper) (hk : r.plan.KeepsShapes) (hr : r.plan.FromRest) (k : Nat)
    (hst : r.stages (r.picture (k + 1)) (r.picture (k + 2)) = none) (a : α) :
    (r.step (k + 1)).frame a 0 =
      ((r.step k).interrupt 1000 (r.picture (k + 2)) (fun _ => {}) (plan := r.plan)).frame a 0 := by
  have e := (r.step k).interrupt_of_rest (Nat.le_refl 1000) (r.picture (k + 2)) (fun _ => {})
    (fun _ => none) r.plan hs hp hk hr
  rw [step_next r k hst]
  show ((r.step k).next (r.picture (k + 2)) r.plan).motion.frame (r.key a) 0 =
    ((r.step k).interrupt 1000 (r.picture (k + 2)) (fun _ => {}) (plan := r.plan)).motion.frame
      (r.key a) 0
  rw [e]

/-- The kept pairs of a step of the run are the kept pairs of the step that interrupts the step
before at its end. -/
theorem interrupt_join [BEq κ] (r : Reel α κ) (k : Nat) :
    ((r.step k).interrupt 1000 (r.picture (k + 2)) (fun _ => {}) (plan := r.plan)).join =
      Scene.join r.key (r.picture (k + 1)) (r.picture (k + 2)) := by
  show Scene.join r.key ((r.step k).drawn 1000) (r.picture (k + 2)) = _
  rw [(r.step k).drawn_end (Nat.le_refl 1000)]
  rfl

/-- **The step after starts each kept thing where the joint has it.** At the first moment of
the step `k + 1`, which the run passes over, a kept thing that the plan moves stands where its
old thing stands in the picture `k + 1`. The plan moves the thing by `Plan.moving`, and may give
it more changes that are not of its place. Each transition of the thing reads `0` at the moment
`0`, and the keys of the next picture are distinct. -/
theorem joint_stands [BEq κ] [LawfulBEq κ] (r : Reel α κ) (hs : r.plan.Settles)
    (hp : r.plan.Proper) (hk : r.plan.KeepsShapes) (hr : r.plan.FromRest) {k : Nat}
    (hst : r.stages (r.picture (k + 1)) (r.picture (k + 2)) = none)
    (hd : Distinct r.key (r.picture (k + 2))) {o n : α}
    (hu : (o, n) ∈ (Scene.join r.key (r.picture (k + 1)) (r.picture (k + 2))).update)
    (hz : ∀ c ∈ r.plan.kept o n, c.2.at 0 = 0) (place : α → IVec) (move : Transition)
    {more : List (Change × Transition)}
    (hkept : r.plan.kept o n = Plan.moving place move o n ++ more)
    (hm : ∀ c ∈ more, c.1.property ≠ .place) (hdm : (more.map fun c => c.1.property).Nodup) :
    ((r.step (k + 1)).frame n 0).stand (place n) = place o := by
  have hu' : (o, n) ∈ ((r.step k).interrupt 1000 (r.picture (k + 2)) (fun _ => {})
      (plan := r.plan)).join.update := by
    rw [interrupt_join]
    exact hu
  have ho : o ∈ (r.step k).new := (mem_update r.key _ _ hu).1
  rw [step_frame_zero r hs hp hk hr k hst n,
    (r.step k).nothing_moves 1000 (r.picture (k + 2)) (fun _ => {}) (fun _ => none) r.plan hd hu'
      hz rfl place move hkept hm hdm,
    (r.step k).frame_end_rest hs hp hk ho (Nat.le_refl 1000)]
  exact IVec.add_zero (place o)

/-- **The step after starts each kept thing whole.** At the first moment of the step `k + 1`,
which the run passes over, a kept thing has its whole size, its whole line and its whole
opacity, as the joint has it. Each transition of the thing reads `0` at the moment `0`, and the
keys of the next picture are distinct. -/
theorem joint_whole [BEq κ] [LawfulBEq κ] (r : Reel α κ) (hs : r.plan.Settles)
    (hp : r.plan.Proper) (hk : r.plan.KeepsShapes) (hr : r.plan.FromRest) {k : Nat}
    (hst : r.stages (r.picture (k + 1)) (r.picture (k + 2)) = none)
    (hd : Distinct r.key (r.picture (k + 2))) {o n : α}
    (hu : (o, n) ∈ (Scene.join r.key (r.picture (k + 1)) (r.picture (k + 2))).update)
    (hz : ∀ c ∈ r.plan.kept o n, c.2.at 0 = 0) :
    ((r.step (k + 1)).frame n 0).size = 1000 ∧ ((r.step (k + 1)).frame n 0).part = 1000 ∧
      ((r.step (k + 1)).frame n 0).shown = 1000 := by
  have hu' : (o, n) ∈ ((r.step k).interrupt 1000 (r.picture (k + 2)) (fun _ => {})
      (plan := r.plan)).join.update := by
    rw [interrupt_join]
    exact hu
  have ho : o ∈ (r.step k).new := (mem_update r.key _ _ hu).1
  have hrest := (r.step k).frame_end_rest hs hp hk ho (Nat.le_refl 1000)
  have shows : ∀ q : Pose, Frame.rest.Shows q → q.property ≠ .place → q.property ≠ .shape →
      ((r.step (k + 1)).frame n 0).Shows q := fun q hq h1 h2 => by
    rw [step_frame_zero r hs hp hk hr k hst n]
    exact (r.step k).nothing_jumps 1000 (r.picture (k + 2)) (fun _ => {}) (fun _ => none) r.plan
      hd hu' hz rfl (by rw [hrest]; exact hq) (fun e => absurd e h1) (fun e => absurd e h2)
  exact ⟨Frame.shows_grow.mp (shows (.grow 1000) rfl (fun e => nomatch e) (fun e => nomatch e)),
    Frame.shows_reveal.mp (shows (.reveal 1000) rfl (fun e => nomatch e) (fun e => nomatch e)),
    Frame.shows_fade.mp (shows (.fade 1000) rfl (fun e => nomatch e) (fun e => nomatch e))⟩

/-! ## What a player shows -/

/-- Rows of `per` moments each have `per` moments for each row. -/
theorem length_rows (per : Nat) (g : Nat → Nat → Nat) : ∀ l : List Nat,
    (l.flatMap fun k => (List.range per).map (g k)).length = l.length * per
  | [] => (Nat.zero_mul per).symm
  | k :: rest => by
    rw [List.flatMap_cons, List.length_append, List.length_map, List.length_range,
      length_rows per g rest, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- **A player shows one picture, and `per` for each step.** -/
theorem length_moments (r : Reel α κ) (per : Nat) :
    (r.moments per).length = 1 + r.rest.length * per := by
  show ((List.range r.rest.length).flatMap fun k =>
    (List.range per).map fun j => 1000 * k + (j + 1) * 1000 / per).length + 1 = _
  rw [length_rows per (fun k j => 1000 * k + (j + 1) * 1000 / per), List.length_range,
    Nat.add_comm]

/-- The player shows a picture of the run at each of its moments. -/
theorem length_frames [BEq κ] (r : Reel α κ) (per : Nat) :
    (r.frames per).length = 1 + r.rest.length * per :=
  (List.length_map _).trans (r.length_moments per)

/-- **Every joint is a moment that the player shows**, where it shows one moment or more of
each step. With `at_joint`, every picture of the run is shown at rest. -/
theorem joint_mem_moments (r : Reel α κ) {per : Nat} (hper : 0 < per) {k : Nat}
    (h : k ≤ r.rest.length) : 1000 * k ∈ r.moments per := by
  cases k with
  | zero => exact List.mem_cons_self
  | succ j =>
    refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr h, ?_⟩)
    refine List.mem_map.mpr ⟨per - 1, List.mem_range.mpr (Nat.sub_lt hper (by decide)), ?_⟩
    have e1 : per - 1 + 1 = per := Nat.sub_add_cancel hper
    rw [e1, Nat.mul_div_cancel_left 1000 hper]
    exact (Nat.mul_succ 1000 j).symm

/-! ## How long a run lasts with no waiting -/

/-- The tracks of a step are over by its end. -/
theorem step_finish_le [BEq κ] (s : Step α κ) : s.motion.finish ≤ 1000 := by
  refine Motion.finish_le_of _ 1000 fun tr h => ?_
  obtain ⟨key, old, new, plan, stages⟩ := s
  cases stages with
  | none =>
    have h' : tr ∈ (Motion.ofJoin key (Scene.join key old new) plan).within := h
    obtain ⟨tr0, _, rfl⟩ := Motion.mem_within _ h'
    exact Transition.within_end tr0.timing
  | some g =>
    have h' : tr ∈ (Motion.staged key (Scene.join key old new) plan g.enterFrom g.levels
      g.rank).within := h
    obtain ⟨tr0, _, rfl⟩ := Motion.mem_within _ h'
    exact Transition.within_end tr0.timing

/-- Numbers that are each `b` at the most add up to `b` for each at the most. -/
theorem sum_le (b : Nat) : ∀ l : List Nat, (∀ x ∈ l, x ≤ b) → l.sum ≤ b * l.length
  | [], _ => Nat.le_refl 0
  | x :: rest, h => by
    have ih := sum_le b rest fun y hy => h y (List.mem_cons_of_mem x hy)
    have hx := h x List.mem_cons_self
    rw [List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

/-- **Played with no waiting, a run lasts the lengths of its steps together.** -/
theorem playtime_eq [BEq κ] (r : Reel α κ) :
    r.playtime = (r.motions.map Motion.finish).sum :=
  Motion.finish_inOrder r.motions

/-- **Played with no waiting, a run lasts its span at the most.** -/
theorem playtime_le [BEq κ] (r : Reel α κ) : r.playtime ≤ r.span := by
  have h := sum_le 1000 (r.motions.map Motion.finish) fun x hx => by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hm
    exact step_finish_le (r.step k)
  have hl : (r.motions.map Motion.finish).length = r.rest.length := by
    show (((List.range r.rest.length).map fun k => (r.step k).motion).map Motion.finish).length =
      r.rest.length
    rw [List.length_map, List.length_map, List.length_range]
  rw [hl] at h
  exact Nat.le_trans (Nat.le_of_eq r.playtime_eq) h

end Reel

end Whatwg.Svg.Scene
