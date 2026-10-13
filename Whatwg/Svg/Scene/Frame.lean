import Whatwg.Svg.Scene.Motion.Laws
import Whatwg.Svg.Scene.Join

/-!
# Whatwg.Svg.Scene.Frame

Owner: what a thing looks like at a moment (slice S15 of `docs/SVG-PACKAGE-PLAN.md`; ruling
SV-85).

`Motion.posesOf` of `Whatwg/Svg/Scene/Motion.lean` gives the poses that the tracks of a motion
set on a thing at a moment, track by track. It does not say what the thing then looks like. Two
tracks may set one property, and a thing with no track of a property has that property at rest.
This module is the reader that says so.

- `Property`: what a pose sets. A thing has five: its place, its size, how much of its line is
  drawn, its opacity and its shape.
- `Frame`: a value for each property. `Frame.rest` is the still picture.
- `Pose.onto`: a pose put on a frame. It sets its own property and leaves the others. A later
  pose of one property replaces an earlier one. CSS does the same: of two animations of one
  property on one element, the later in the list is the one shown.
- `Frame.under`, `Frame.ofPoses`: the poses of a list put on a frame, or on the still picture,
  one after another. `Frame.poses`: the poses that take the still picture to a frame.
- `Frame.Shows f p`: the frame shows the pose. Putting the pose on the frame changes nothing. It
  is the reader for a caller: one statement for any pose, in place of five for the five values.
  `Frame.stand f p`: where a thing stands at a frame, its place and the frame's shift.
- `Motion.frame m key t`: the frame of a thing at a moment, its poses put on the still picture
  in the order of the tracks.
- `Motion.Single`: no thing has two tracks of one property. The frame of such a motion does not
  depend on the order of its tracks.
- `Motion.Same`: two motions that give every thing the same frame at every moment. A reader
  cannot tell them apart.
- `Change.from`: a change that starts where a thing is seen. `Frame.toRest`: the changes that
  take a thing from a frame to rest. A step that begins before the last one has ended starts
  each thing from its frame, and nothing jumps.

What the laws say:

- Poses on a frame. Poses of two different properties commute (`Pose.onto_comm`), and of two
  poses of one property the later wins (`Pose.onto_onto`). So a pose commutes past the poses of
  the other properties (`Frame.onto_under`), and a pose with no pose of its property after it is
  in the frame, whatever came before it (`Frame.under_last`). Two lists in a row are put on one
  after the other (`Frame.under_append`, `Frame.ofPoses_append`). A frame at rest stays at rest
  under poses that are each at rest (`Frame.atRest_under`, `Frame.ofPoses_atRest`).
- Reading a frame. With distinct properties, every pose of a list is in its frame
  (`Frame.ofPoses_has`). A shift of the list is then where the thing stands, and so for a size,
  a part, an opacity and a shape (`Frame.shift_under`, `Frame.size_under`, `Frame.part_under`,
  `Frame.shown_under`, `Frame.shape_under`). A property that no pose of the list sets is as it
  was, and so at rest from the still picture (`Frame.shift_under_of_no` and the four others).
  Two lists with the same members, the first with distinct properties, give the same frame
  (`Frame.ofPoses_congr`): the order of poses of different properties does not matter.
- What a frame shows. A frame shows a shift exactly when the thing stands that far off its
  place, and so for the four other poses (`Frame.shows_shift`, `Frame.shows_grow`,
  `Frame.shows_reveal`, `Frame.shows_fade`, `Frame.shows_shape`). It shows one pose of each
  property at most (`Pose.eq_of_shows`), and a frame that shows a shape has one
  (`Frame.shape_ne_none_of_shows`). A frame under a list of poses shows a pose where every pose
  of that property in the list is that pose, and where the frame showed it already if the list
  has none (`Frame.shows_under`, `Frame.shows_ofPoses`). This asks for no distinct properties.
- The poses of a frame. They give the frame back (`Frame.ofPoses_poses`). They are of distinct
  properties (`Frame.poses_distinct`), and there is none exactly when the frame is the still
  picture (`Frame.poses_eq_nil`).
- The frame of a motion. A change sets one property at every progress, and a track at every
  moment (`Change.at_property`, `Track.at_property`). A thing with no track is the still picture
  (`Motion.frame_of_no_track`), and the tracks of other things do not change its frame
  (`Motion.frame_append_left`, `Motion.frame_append_right`). The frame of two motions in a row
  is the frame of the first under the poses of the second (`Motion.frame_append`). Where every
  pose of a thing is at rest, its frame is at rest (`Motion.frame_atRest`,
  `Motion.frame_atRest_of_tracks`). This takes the end laws of
  `Whatwg/Svg/Scene/Motion/Laws.lean`, which are of poses, to what is seen
  (`Motion.within_frame_atRest`). Holding a motion inside its step does not change its first
  moment: every thing has the same poses and the same frame there
  (`Motion.within_posesOf_zero`, `Motion.within_frame_zero`).
- One track for each property. A motion whose tracks have distinct keys is `Single`
  (`Motion.single_of_keys`), and a motion held inside its step is `Single` where the motion is
  (`Motion.Single.within`). In a `Single` motion the poses of a thing are of distinct
  properties (`Motion.posesOf_distinct`), so the pose of every track is in the frame of its
  thing (`Motion.frame_has`). `Motion.frame_shift`, `Motion.frame_size`, `Motion.frame_part`,
  `Motion.frame_shown` and `Motion.frame_shape` say it value by value, and `Motion.frame_done`
  is the end law: a track that is over has left its thing at the end of its change. In every
  motion, `Single` or not, the later of two tracks of one property on one thing is the one shown
  (`Motion.frame_last`).
- Motions that a reader cannot tell apart. `Motion.Same` holds of a motion and itself, goes both
  ways and goes through a third motion (`Same.refl`, `Same.symm`, `Same.trans`). Two motions
  with the same tracks are the same where the first is `Single` (`Same.of_mem`), so the two
  parts of a `Single` motion may change places (`Same.append_comm`). The same tracks put after
  two motions that are the same give motions that are the same (`Same.append_right`). Two parts
  may both be replaced where both rows are `Single` (`Same.append`).
- Tracks that can be dropped. A track at the end of a motion can be dropped exactly where the
  frame of its thing already shows its pose at every moment (`Same.concat_iff`,
  `Same.of_shown`). Two cases: a track said twice in a `Single` motion (`Same.of_again`), and a
  track from rest to rest that is not a change of shape, where no earlier track of its thing is
  of its property (`Same.of_idle`, and `Same.of_idle_append` in the middle of a motion). Such a
  track is at rest at every moment (`Change.at_atRest`, `Track.at_atRest`).
- Starting where a thing is seen. `Change.from` keeps the end and the property of a change
  (`Change.from_stop`, `Change.from_property`). From the still picture, a change that starts at
  rest is itself (`Change.from_rest`), and so is every shift (`Change.from_rest_shift`). The
  start of the change that `Change.from` gives is what is seen, so the thing does not jump
  (`Change.from_start_onto`): this holds of a size, a line and an opacity, of a shift told from
  the thing's own place, and of a change of shape where the frame has a shape. A shift told
  from another place starts further off by the shift of the frame (`Change.from_start_shift`).
- Going to rest. `Frame.mem_toRest` lists the changes of `Frame.toRest`. Each ends at rest and
  starts at what is seen (`Frame.toRest_stop`, `Frame.toRest_start`). They are of distinct
  properties, and none is a change of shape (`Frame.toRest_distinct`,
  `Frame.toRest_not_shape`). There is none exactly when the frame is at rest
  (`Frame.toRest_eq_nil`). Their starts give the frame back, less its shape
  (`Frame.ofPoses_toRest`, and `Frame.toRest_shows` value by value), and their ends give the
  still picture (`Frame.toRest_stops`).

The controls at the end of this file are motions with numbers: two shifts on one box, where a
reader that adds them is wrong; a motion that is not `Single`, whose two orders give two frames;
a box read at three moments of its step; and the track that shows why `Same.append` and
`Same.of_idle` have their premises.

What this module does not claim. `Frame.AtRest` says nothing of the shape: a frame at rest may
have a shape that a track gave it, and that a change of shape ends at the shape of the next
picture is the caller's to see to. The frame is the kit's own reading of a motion. What a host
draws where two animations set one property on one element is an observation of that host, and
no law here is about it. Two shifts on one thing are not added: a caller that wants their sum
gives one track. `Motion.Same` is of frames from the still picture, so it does not hold of two
rows because it holds of their parts, unless both rows are `Single`. `Frame.toRest` gives
changes and no transition: when a thing goes to rest is the caller's. A frame knows no rest of
a shape, so `Frame.toRest` has no change of shape. The laws about keys ask for an equality test
on keys that is lawful, and say so.

What came here in the tidy of slice S16, each under the name it had. `Frame.Shows` with its
laws, `Motion.within_posesOf_zero` and `Motion.within_frame_zero` came from
`Whatwg/Svg/Scene/Resume.lean`, and `Frame.stand` from `Whatwg/Svg/Scene/Together.lean`: each is
of a frame alone. `Motion.single_of_keys` and `Motion.Single.within` came from the port
`WhatwgTest/Html/SvgMotion.lean`, which now cites them. That a step of a plan is `Single` is
`Motion.single_ofJoin` of `Whatwg/Svg/Scene/Plan.lean`. The proofs of this module still read a
frame through a private function, one property at a time; `Frame.Shows` is the public form of
the same reading.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- What a pose sets on a thing. -/
inductive Property where
  /-- Where the thing stands. -/
  | place
  /-- At what size it is drawn. -/
  | size
  /-- How much of its line is drawn. -/
  | line
  /-- How much of its opacity it has. -/
  | opacity
  /-- Its shape. -/
  | shape
  deriving DecidableEq, Repr, Inhabited

/-- The property that a pose sets. -/
def Pose.property : Pose → Property
  | .shift _ => .place
  | .grow _ => .size
  | .reveal _ => .line
  | .fade _ => .opacity
  | .shape _ => .shape

/-- The property that a change changes. -/
def Change.property : Change → Property
  | .shift _ _ => .place
  | .grow _ _ => .size
  | .reveal _ _ => .line
  | .fade _ _ => .opacity
  | .morph _ _ => .shape

/-- **What a thing looks like at a moment**: how far off its place it stands, at what size it is
drawn, how much of its line is drawn, how much of its opacity it has, in per mille, and its
shape where a track gave it one. -/
structure Frame where
  /-- How far off its place the thing stands. -/
  shift : IVec := 0
  /-- The size it is drawn at, in per mille of its own. -/
  size : Int := 1000
  /-- How much of its line is drawn, in per mille. -/
  part : Int := 1000
  /-- How much of its opacity it has, in per mille. -/
  shown : Int := 1000
  /-- The shape it is drawn with, in place of its own: `none` for its own. -/
  shape : Option (List ICubic) := none
  deriving DecidableEq, Repr, Inhabited

namespace Frame

/-- The still picture: every property at rest. -/
def rest : Frame := {}

/-- A frame that shows the thing as the still picture has it, whatever its shape. -/
def AtRest (f : Frame) : Prop := f.shift = 0 ∧ f.size = 1000 ∧ f.part = 1000 ∧ f.shown = 1000

instance (f : Frame) : Decidable f.AtRest := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end Frame

/-- **A pose put on a frame.** It sets its own property, and the others stay. -/
def Pose.onto : Pose → Frame → Frame
  | .shift step, f => { f with shift := step }
  | .grow size, f => { f with size := size }
  | .reveal part, f => { f with part := part }
  | .fade shown, f => { f with shown := shown }
  | .shape segments, f => { f with shape := some segments }

/-- **A frame shows a pose**: putting the pose on the frame changes nothing. The thing is drawn
as the pose says. -/
def Frame.Shows (f : Frame) (p : Pose) : Prop := p.onto f = f

instance (f : Frame) (p : Pose) : Decidable (f.Shows p) :=
  inferInstanceAs (Decidable (p.onto f = f))

/-- Where a thing stands at a frame: its place and the frame's shift. -/
def Frame.stand (f : Frame) (place : IVec) : IVec := place + f.shift

namespace Frame

/-- The poses of a list put on a frame, one after another. -/
def under (f : Frame) (ps : List Pose) : Frame := ps.foldl (fun g p => p.onto g) f

/-- The frame of a list of poses: each put on the still picture, one after another. -/
def ofPoses (ps : List Pose) : Frame := rest.under ps

/-- The poses that take the still picture to a frame: one for each property that is not at
rest. -/
def poses (f : Frame) : List Pose :=
  (if f.shift = 0 then [] else [.shift f.shift]) ++
    (if f.size = 1000 then [] else [.grow f.size]) ++
    (if f.part = 1000 then [] else [.reveal f.part]) ++
    (if f.shown = 1000 then [] else [.fade f.shown]) ++
    (match f.shape with
      | none => []
      | some segments => [.shape segments])

/-- **The changes that take a thing from a frame to rest**: one for each of its place, its
size, its line and its opacity that is not at rest. A shape has no rest that a frame knows: a
caller that changes a shape back gives the `morph`. -/
def toRest (f : Frame) : List Change :=
  (if f.shift = 0 then [] else [.shift f.shift 0]) ++
    (if f.size = 1000 then [] else [.grow f.size 1000]) ++
    (if f.part = 1000 then [] else [.reveal f.part 1000]) ++
    (if f.shown = 1000 then [] else [.fade f.shown 1000])

end Frame

/-- **A change that starts where a thing is seen.** The change keeps its end. A shift starts
further off by the shift of the frame; a size, a line and an opacity start at the frame's; a
change of shape starts at the frame's shape where it has one. -/
def Change.from (f : Frame) : Change → Change
  | .shift a b => .shift (a + f.shift) b
  | .grow _ b => .grow f.size b
  | .reveal _ b => .reveal f.part b
  | .fade _ b => .fade f.shown b
  | .morph a b => .morph (f.shape.getD a) b

namespace Motion

variable {κ : Type}

/-- **The frame of a thing at a moment**: its poses put on the still picture, in the order of
the tracks. A thing with no track is the still picture. -/
def frame [BEq κ] (m : Motion κ) (key : κ) (t : Nat) : Frame := Frame.ofPoses (m.posesOf key t)

/-- **No thing has two tracks of one property.** -/
def Single (m : Motion κ) : Prop := Distinct (fun tr : Track κ => (tr.key, tr.change.property)) m

/-- **Two motions that a reader cannot tell apart**: every thing has the same frame in both at
every moment. -/
def Same [BEq κ] (m n : Motion κ) : Prop := ∀ key t, m.frame key t = n.frame key t

end Motion

/-! ## Poses on a frame -/

namespace Pose

/-- **Poses of two different properties commute.** A thing that is moved and then faded looks as
one that is faded and then moved. -/
theorem onto_comm {p q : Pose} (h : p.property ≠ q.property) (f : Frame) :
    p.onto (q.onto f) = q.onto (p.onto f) := by
  cases p with
  | shift a =>
    cases q with
    | shift b => exact absurd rfl h
    | _ => rfl
  | grow a =>
    cases q with
    | grow b => exact absurd rfl h
    | _ => rfl
  | reveal a =>
    cases q with
    | reveal b => exact absurd rfl h
    | _ => rfl
  | fade a =>
    cases q with
    | fade b => exact absurd rfl h
    | _ => rfl
  | shape a =>
    cases q with
    | shape b => exact absurd rfl h
    | _ => rfl

/-- **Of two poses of one property the later wins.** A thing that is put at one place and then
at another stands at the second. -/
theorem onto_onto {p q : Pose} (h : p.property = q.property) (f : Frame) :
    p.onto (q.onto f) = p.onto f := by
  cases p <;> cases q <;> cases h <;> rfl

/-- A pose put twice is put once. -/
theorem onto_self (p : Pose) (f : Frame) : p.onto (p.onto f) = p.onto f := onto_onto rfl f

/-- A pose at rest, put on a frame at rest, gives a frame at rest. -/
theorem onto_atRest {p : Pose} {f : Frame} (hp : p.AtRest) (hf : f.AtRest) :
    (p.onto f).AtRest := by
  cases p with
  | shift s => exact ⟨hp, hf.2.1, hf.2.2.1, hf.2.2.2⟩
  | grow s => exact ⟨hf.1, hp, hf.2.2.1, hf.2.2.2⟩
  | reveal s => exact ⟨hf.1, hf.2.1, hp, hf.2.2.2⟩
  | fade s => exact ⟨hf.1, hf.2.1, hf.2.2.1, hp⟩
  | shape s => exact hf

/-- A pose at rest that is not a shape changes nothing of the still picture. A shape is not so:
the still picture has the thing's own shape, and a pose gives it another. -/
theorem onto_rest {p : Pose} (hp : p.AtRest) (hs : p.property ≠ .shape) :
    p.onto Frame.rest = Frame.rest := by
  cases p with
  | shift s =>
    have e : s = 0 := hp
    rw [e]
    rfl
  | grow s =>
    have e : s = 1000 := hp
    rw [e]
    rfl
  | reveal s =>
    have e : s = 1000 := hp
    rw [e]
    rfl
  | fade s =>
    have e : s = 1000 := hp
    rw [e]
    rfl
  | shape s => exact absurd rfl hs

end Pose

namespace Frame

/-- Two frames with the same five values are one frame. -/
theorem ext : ∀ {f g : Frame}, f.shift = g.shift → f.size = g.size → f.part = g.part →
    f.shown = g.shown → f.shape = g.shape → f = g
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, rfl, rfl, rfl, rfl, rfl => rfl

/-- The still picture is at rest. -/
theorem rest_atRest : rest.AtRest := ⟨rfl, rfl, rfl, rfl⟩

/-- **A frame is at rest exactly when it is the still picture but for its shape.** -/
theorem atRest_iff (f : Frame) : f.AtRest ↔ ({ f with shape := none } : Frame) = rest :=
  ⟨fun h => ext h.1 h.2.1 h.2.2.1 h.2.2.2 rfl, fun h =>
    ⟨congrArg Frame.shift h, congrArg Frame.size h, congrArg Frame.part h,
      congrArg Frame.shown h⟩⟩

/-! ### One property at a time -/

/-- The pose of a property that a frame shows. A frame with no shape of its own shows no pose of
the shape. The laws of this module read a frame through it, one property at a time, so that
each is proved once and not five times. -/
private def pose (f : Frame) : Property → Option Pose
  | .place => some (.shift f.shift)
  | .size => some (.grow f.size)
  | .line => some (.reveal f.part)
  | .opacity => some (.fade f.shown)
  | .shape => f.shape.map Pose.shape

/-- Two shapes that give the same pose, or both none, are one shape. -/
private theorem map_shape_inj : ∀ {a b : Option (List ICubic)},
    a.map Pose.shape = b.map Pose.shape → a = b
  | none, none, _ => rfl
  | none, some _, h => nomatch h
  | some _, none, h => nomatch h
  | some _, some _, h => congrArg some (Pose.shape.inj (Option.some.inj h))

/-- Two frames that show the same pose of every property are one frame. -/
private theorem ext_pose {f g : Frame} (h : ∀ π, f.pose π = g.pose π) : f = g := by
  have h1 : some (Pose.shift f.shift) = some (Pose.shift g.shift) := h .place
  have h2 : some (Pose.grow f.size) = some (Pose.grow g.size) := h .size
  have h3 : some (Pose.reveal f.part) = some (Pose.reveal g.part) := h .line
  have h4 : some (Pose.fade f.shown) = some (Pose.fade g.shown) := h .opacity
  have h5 : f.shape.map Pose.shape = g.shape.map Pose.shape := h .shape
  exact ext (Pose.shift.inj (Option.some.inj h1)) (Pose.grow.inj (Option.some.inj h2))
    (Pose.reveal.inj (Option.some.inj h3)) (Pose.fade.inj (Option.some.inj h4)) (map_shape_inj h5)

/-- A frame under a pose shows that pose of its property, and of every other property what it
showed. -/
private theorem pose_onto (p : Pose) (f : Frame) (π : Property) :
    (p.onto f).pose π = if p.property = π then some p else f.pose π := by
  cases p <;> cases π <;> rfl

/-- A frame under a pose shows that pose. -/
private theorem pose_onto_self (p : Pose) (f : Frame) : (p.onto f).pose p.property = some p :=
  (pose_onto p f p.property).trans (if_pos rfl)

/-- A pose leaves the other properties as they are. -/
private theorem pose_onto_of_ne {p : Pose} {π : Property} (h : p.property ≠ π) (f : Frame) :
    (p.onto f).pose π = f.pose π :=
  (pose_onto p f π).trans (if_neg h)

/-- A pose changes nothing of a frame exactly where the frame shows it. -/
private theorem onto_eq_iff (p : Pose) (f : Frame) :
    p.onto f = f ↔ f.pose p.property = some p := by
  constructor
  · intro h
    exact (congrArg (fun g : Frame => g.pose p.property) h).symm.trans (pose_onto_self p f)
  · intro h
    refine ext_pose fun π => ?_
    rw [pose_onto]
    cases Decidable.em (p.property = π) with
    | inl e =>
      rw [if_pos e, ← e, h]
    | inr e => rw [if_neg e]

/-! ### Poses, one after another -/

/-- No pose leaves a frame as it is. -/
theorem under_nil (f : Frame) : f.under [] = f := rfl

/-- The first pose of a list is put on first. -/
theorem under_cons (f : Frame) (p : Pose) (ps : List Pose) :
    f.under (p :: ps) = (p.onto f).under ps := rfl

/-- Two lists of poses in a row are put on one after the other. -/
theorem under_append (f : Frame) (ps qs : List Pose) :
    f.under (ps ++ qs) = (f.under ps).under qs := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih => exact ih (p.onto f)

/-- The last pose of a list is put on last. -/
theorem under_concat (f : Frame) (ps : List Pose) (p : Pose) :
    f.under (ps ++ [p]) = p.onto (f.under ps) := under_append f ps [p]

/-- No pose gives the still picture. -/
theorem ofPoses_nil : ofPoses [] = rest := rfl

/-- **The frame of two lists of poses in a row** is the frame of the first under the second. -/
theorem ofPoses_append (ps qs : List Pose) : ofPoses (ps ++ qs) = (ofPoses ps).under qs :=
  under_append rest ps qs

/-- **A frame at rest stays at rest under poses that are each at rest.** -/
theorem atRest_under {f : Frame} {ps : List Pose} (hf : f.AtRest) (h : ∀ p ∈ ps, p.AtRest) :
    (f.under ps).AtRest := by
  induction ps generalizing f with
  | nil => exact hf
  | cons p ps ih =>
    exact ih (Pose.onto_atRest (h p List.mem_cons_self) hf)
      (fun r hr => h r (List.mem_cons_of_mem p hr))

/-- **Poses that are each at rest give a frame at rest.** Where every pose of a thing is at rest,
the thing is drawn as the still picture has it, whatever its shape. -/
theorem ofPoses_atRest {ps : List Pose} (h : ∀ p ∈ ps, p.AtRest) : (ofPoses ps).AtRest :=
  atRest_under rest_atRest h

/-- **A pose commutes past the poses of the other properties.** It may be put on before them or
after them. -/
theorem onto_under {q : Pose} {ps : List Pose} (h : ∀ p ∈ ps, p.property ≠ q.property)
    (f : Frame) : q.onto (f.under ps) = (q.onto f).under ps := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    have hp : q.property ≠ p.property := fun e => h p List.mem_cons_self e.symm
    show q.onto ((p.onto f).under ps) = (p.onto (q.onto f)).under ps
    rw [ih (fun r hr => h r (List.mem_cons_of_mem p hr)) (p.onto f), Pose.onto_comm hp]

/-- **The later of the poses of one property is the one shown.** A pose with no pose of its
property after it is in the frame, whatever came before it. CSS does the same with two
animations of one property on one element. -/
theorem under_last {q : Pose} {qs : List Pose} (h : ∀ p ∈ qs, p.property ≠ q.property)
    (f : Frame) (ps : List Pose) :
    q.onto (f.under (ps ++ q :: qs)) = f.under (ps ++ q :: qs) := by
  rw [under_append, under_cons, onto_under h, Pose.onto_self]

/-- Where no pose of a list is of a property, the frame shows of that property what it showed
before. -/
private theorem pose_under_of_no {π : Property} : ∀ {ps : List Pose},
    (∀ p ∈ ps, p.property ≠ π) → ∀ f : Frame, (f.under ps).pose π = f.pose π
  | [], _, _ => rfl
  | p :: _, h, f =>
    (pose_under_of_no (fun r hr => h r (List.mem_cons_of_mem p hr)) (p.onto f)).trans
      (pose_onto_of_ne (h p List.mem_cons_self) f)

/-- A pose of a list that is the only pose of its property there is the one shown. -/
private theorem pose_under_of_mem {q : Pose} : ∀ {ps : List Pose}, q ∈ ps →
    (∀ p ∈ ps, p.property = q.property → p = q) → ∀ f : Frame,
      (f.under ps).pose q.property = some q
  | [], hq, _, _ => nomatch hq
  | p :: ps, hq, h, f => by
    cases Decidable.em (q ∈ ps) with
    | inl hin =>
      exact pose_under_of_mem hin (fun r hr => h r (List.mem_cons_of_mem p hr)) (p.onto f)
    | inr hout =>
      have hp : q = p := by
        rcases List.mem_cons.mp hq with e | e
        · exact e
        · exact absurd e hout
      subst hp
      have hno : ∀ r ∈ ps, r.property ≠ q.property := fun r hr e =>
        hout (h r (List.mem_cons_of_mem q hr) e ▸ hr)
      exact (pose_under_of_no hno (q.onto f)).trans (pose_onto_self q f)

/-- **A pose that is the only one of its property in a list is in the frame.** Putting it on
again changes nothing. The list may say it twice. -/
theorem under_has {ps : List Pose} {q : Pose} (hq : q ∈ ps)
    (h : ∀ p ∈ ps, p.property = q.property → p = q) (f : Frame) :
    q.onto (f.under ps) = f.under ps :=
  (onto_eq_iff q _).mpr (pose_under_of_mem hq h f)

/-- **With distinct properties, every pose of a list is in the frame.** -/
theorem under_has_of_distinct {ps : List Pose} (hd : (ps.map Pose.property).Nodup) {q : Pose}
    (hq : q ∈ ps) (f : Frame) : q.onto (f.under ps) = f.under ps :=
  under_has hq (fun p hp e => eq_of_distinct Pose.property ps hd p q hp hq e) f

/-- **With distinct properties, every pose of a list is in its frame.** -/
theorem ofPoses_has {ps : List Pose} (hd : (ps.map Pose.property).Nodup) {q : Pose}
    (hq : q ∈ ps) : q.onto (ofPoses ps) = ofPoses ps :=
  under_has_of_distinct hd hq rest

/-! ### Reading a frame

Each law is of `f.under ps`. The frame of a list, `ofPoses ps`, is the case where `f` is the
still picture, and its values at rest are `0`, `1000`, `1000`, `1000` and `none`. -/

/-- With distinct properties, a shift of the list is how far off its place the thing stands. -/
theorem shift_under {ps : List Pose} (hd : (ps.map Pose.property).Nodup) {s : IVec}
    (hs : Pose.shift s ∈ ps) (f : Frame) : (f.under ps).shift = s :=
  (congrArg Frame.shift (under_has_of_distinct hd hs f)).symm

/-- With distinct properties, a size of the list is the size the thing is drawn at. -/
theorem size_under {ps : List Pose} (hd : (ps.map Pose.property).Nodup) {s : Int}
    (hs : Pose.grow s ∈ ps) (f : Frame) : (f.under ps).size = s :=
  (congrArg Frame.size (under_has_of_distinct hd hs f)).symm

/-- With distinct properties, a part of the list is how much of the thing's line is drawn. -/
theorem part_under {ps : List Pose} (hd : (ps.map Pose.property).Nodup) {s : Int}
    (hs : Pose.reveal s ∈ ps) (f : Frame) : (f.under ps).part = s :=
  (congrArg Frame.part (under_has_of_distinct hd hs f)).symm

/-- With distinct properties, an opacity of the list is the opacity the thing has. -/
theorem shown_under {ps : List Pose} (hd : (ps.map Pose.property).Nodup) {s : Int}
    (hs : Pose.fade s ∈ ps) (f : Frame) : (f.under ps).shown = s :=
  (congrArg Frame.shown (under_has_of_distinct hd hs f)).symm

/-- With distinct properties, a shape of the list is the shape the thing is drawn with. -/
theorem shape_under {ps : List Pose} (hd : (ps.map Pose.property).Nodup) {s : List ICubic}
    (hs : Pose.shape s ∈ ps) (f : Frame) : (f.under ps).shape = some s :=
  (congrArg Frame.shape (under_has_of_distinct hd hs f)).symm

/-- With no shift in the list, the thing stands where it stood: at its place, from the still
picture. -/
theorem shift_under_of_no {ps : List Pose} (h : ∀ p ∈ ps, p.property ≠ .place) (f : Frame) :
    (f.under ps).shift = f.shift := by
  have e : some (Pose.shift (f.under ps).shift) = some (Pose.shift f.shift) :=
    pose_under_of_no h f
  exact Pose.shift.inj (Option.some.inj e)

/-- With no size in the list, the thing keeps its size: its own, from the still picture. -/
theorem size_under_of_no {ps : List Pose} (h : ∀ p ∈ ps, p.property ≠ .size) (f : Frame) :
    (f.under ps).size = f.size := by
  have e : some (Pose.grow (f.under ps).size) = some (Pose.grow f.size) := pose_under_of_no h f
  exact Pose.grow.inj (Option.some.inj e)

/-- With no part in the list, as much of the line is drawn as was: the whole, from the still
picture. -/
theorem part_under_of_no {ps : List Pose} (h : ∀ p ∈ ps, p.property ≠ .line) (f : Frame) :
    (f.under ps).part = f.part := by
  have e : some (Pose.reveal (f.under ps).part) = some (Pose.reveal f.part) :=
    pose_under_of_no h f
  exact Pose.reveal.inj (Option.some.inj e)

/-- With no opacity in the list, the thing keeps its opacity: the whole, from the still
picture. -/
theorem shown_under_of_no {ps : List Pose} (h : ∀ p ∈ ps, p.property ≠ .opacity) (f : Frame) :
    (f.under ps).shown = f.shown := by
  have e : some (Pose.fade (f.under ps).shown) = some (Pose.fade f.shown) :=
    pose_under_of_no h f
  exact Pose.fade.inj (Option.some.inj e)

/-- With no shape in the list, the thing keeps its shape: its own, from the still picture. -/
theorem shape_under_of_no {ps : List Pose} (h : ∀ p ∈ ps, p.property ≠ .shape) (f : Frame) :
    (f.under ps).shape = f.shape := by
  have e : (f.under ps).shape.map Pose.shape = f.shape.map Pose.shape := pose_under_of_no h f
  exact map_shape_inj e

/-- **The order of poses of different properties does not matter.** Two lists with the same
members, the first with distinct properties, put the same poses on a frame. The second may say a
pose twice. -/
theorem under_congr {ps qs : List Pose} (hd : (ps.map Pose.property).Nodup)
    (h : ∀ p, p ∈ ps ↔ p ∈ qs) (f : Frame) : f.under ps = f.under qs := by
  have hps : ∀ p ∈ ps, ∀ q ∈ ps, p.property = q.property → p = q := fun p hp q hq e =>
    eq_of_distinct Pose.property ps hd p q hp hq e
  refine ext_pose fun π => ?_
  cases hfind : ps.find? (fun p => decide (p.property = π)) with
  | none =>
    have hno : ∀ p ∈ ps, p.property ≠ π := fun p hp e =>
      List.find?_eq_none.mp hfind p hp (decide_eq_true e)
    rw [pose_under_of_no hno f, pose_under_of_no (fun p hp => hno p ((h p).mpr hp)) f]
  | some q =>
    have hq : q ∈ ps := List.mem_of_find?_eq_some hfind
    have hπ : q.property = π :=
      of_decide_eq_true (List.find?_some (p := fun p : Pose => decide (p.property = π)) hfind)
    subst hπ
    rw [pose_under_of_mem hq (fun p hp e => hps p hp q hq e) f,
      pose_under_of_mem ((h q).mp hq) (fun p hp e => hps p ((h p).mpr hp) q hq e) f]

/-- **Two lists with the same members, the first with distinct properties, give the same
frame.** -/
theorem ofPoses_congr {ps qs : List Pose} (hd : (ps.map Pose.property).Nodup)
    (h : ∀ p, p ∈ ps ↔ p ∈ qs) : ofPoses ps = ofPoses qs :=
  under_congr hd h rest

/-! ### What a frame shows

`Frame.Shows` is the reader of a frame for a caller: one statement for any pose, in place of
five for the five values. -/

/-- A frame shows a shift exactly when the thing stands that far off its place. -/
theorem shows_shift {f : Frame} {s : IVec} : f.Shows (.shift s) ↔ f.shift = s := by
  constructor
  · intro h
    exact (congrArg Frame.shift h).symm
  · intro h
    subst h
    exact (rfl : (Pose.shift f.shift).onto f = f)

/-- A frame shows a size exactly when the thing is drawn at that size. -/
theorem shows_grow {f : Frame} {s : Int} : f.Shows (.grow s) ↔ f.size = s := by
  constructor
  · intro h
    exact (congrArg Frame.size h).symm
  · intro h
    subst h
    exact (rfl : (Pose.grow f.size).onto f = f)

/-- A frame shows a part exactly when that much of the thing's line is drawn. -/
theorem shows_reveal {f : Frame} {s : Int} : f.Shows (.reveal s) ↔ f.part = s := by
  constructor
  · intro h
    exact (congrArg Frame.part h).symm
  · intro h
    subst h
    exact (rfl : (Pose.reveal f.part).onto f = f)

/-- A frame shows an opacity exactly when the thing has that much of its opacity. -/
theorem shows_fade {f : Frame} {s : Int} : f.Shows (.fade s) ↔ f.shown = s := by
  constructor
  · intro h
    exact (congrArg Frame.shown h).symm
  · intro h
    subst h
    exact (rfl : (Pose.fade f.shown).onto f = f)

/-- A frame shows a shape exactly when the thing is drawn with that shape in place of its
own. -/
theorem shows_shape {f : Frame} {s : List ICubic} : f.Shows (.shape s) ↔ f.shape = some s := by
  constructor
  · intro h
    exact (congrArg Frame.shape h).symm
  · intro h
    obtain ⟨shift, size, part, shown, shape⟩ := f
    have e : shape = some s := h
    subst e
    exact (rfl : (Pose.shape s).onto _ = _)

/-- A frame that shows a shape has one. The still picture shows none. -/
theorem shape_ne_none_of_shows {f : Frame} {q : Pose} (hq : f.Shows q)
    (hs : q.property = .shape) : f.shape ≠ none := by
  cases q with
  | shape s =>
    rw [shows_shape.mp hq]
    exact fun e => nomatch e
  | _ => cases hs

/-- **What a frame under a list of poses shows.** It shows a pose where every pose of that
property in the list is that pose, and where the frame showed it already if the list has no pose
of that property. -/
theorem shows_under {ps : List Pose} {q : Pose} (f : Frame)
    (ha : ∀ p ∈ ps, p.property = q.property → p = q)
    (hb : (∀ p ∈ ps, p.property ≠ q.property) → f.Shows q) : (f.under ps).Shows q := by
  cases hfind : ps.find? (fun p => decide (p.property = q.property)) with
  | none =>
    have hno : ∀ p ∈ ps, p.property ≠ q.property := fun p hp e =>
      List.find?_eq_none.mp hfind p hp (decide_eq_true e)
    exact (onto_under hno f).trans (congrArg (fun g : Frame => g.under ps) (hb hno))
  | some p =>
    have hp : p ∈ ps := List.mem_of_find?_eq_some hfind
    have he : p.property = q.property :=
      of_decide_eq_true
        (List.find?_some (p := fun p : Pose => decide (p.property = q.property)) hfind)
    have hpq : p = q := ha p hp he
    subst hpq
    exact under_has hp ha f

/-- What the frame of a list of poses shows: `shows_under` from the still picture. -/
theorem shows_ofPoses {ps : List Pose} {q : Pose}
    (ha : ∀ p ∈ ps, p.property = q.property → p = q)
    (hb : (∀ p ∈ ps, p.property ≠ q.property) → rest.Shows q) : (ofPoses ps).Shows q :=
  shows_under rest ha hb

end Frame

/-- **A frame shows one pose of each property at most.** Two poses of one property that a frame
shows are one pose. -/
theorem Pose.eq_of_shows {f : Frame} {p q : Pose} (hp : f.Shows p) (hq : f.Shows q)
    (h : p.property = q.property) : p = q := by
  cases p with
  | shift a =>
    cases q with
    | shift b =>
      exact congrArg Pose.shift ((Frame.shows_shift.mp hp).symm.trans (Frame.shows_shift.mp hq))
    | _ => cases h
  | grow a =>
    cases q with
    | grow b =>
      exact congrArg Pose.grow ((Frame.shows_grow.mp hp).symm.trans (Frame.shows_grow.mp hq))
    | _ => cases h
  | reveal a =>
    cases q with
    | reveal b =>
      exact congrArg Pose.reveal
        ((Frame.shows_reveal.mp hp).symm.trans (Frame.shows_reveal.mp hq))
    | _ => cases h
  | fade a =>
    cases q with
    | fade b =>
      exact congrArg Pose.fade ((Frame.shows_fade.mp hp).symm.trans (Frame.shows_fade.mp hq))
    | _ => cases h
  | shape a =>
    cases q with
    | shape b =>
      exact congrArg Pose.shape
        (Option.some.inj ((Frame.shows_shape.mp hp).symm.trans (Frame.shows_shape.mp hq)))
    | _ => cases h

namespace Frame

/-! ### The poses of a frame -/

/-- One pose, or none where it would change nothing: either way the frame is under the pose. -/
private theorem under_ite (f : Frame) (c : Prop) [Decidable c] (p : Pose)
    (h : c → p.onto f = f) : f.under (if c then [] else [p]) = p.onto f := by
  cases Decidable.em c with
  | inl hc =>
    rw [if_pos hc]
    exact (h hc).symm
  | inr hc =>
    rw [if_neg hc]
    rfl

/-- One member, or none, is a part of the list of that member. -/
private theorem ite_sublist {α : Type} (c : Prop) [Decidable c] (a : α) :
    List.Sublist (if c then [] else [a]) [a] := by
  cases Decidable.em c with
  | inl hc =>
    rw [if_pos hc]
    exact List.nil_sublist [a]
  | inr hc =>
    rw [if_neg hc]
    exact List.Sublist.refl [a]

/-- **The poses of a frame give the frame back.** A frame is the still picture under its
poses. -/
theorem ofPoses_poses (f : Frame) : ofPoses f.poses = f := by
  rw [ofPoses, poses, under_append, under_append, under_append, under_append,
    under_ite rest (f.shift = 0) (.shift f.shift) (fun h => by rw [h]; rfl),
    under_ite _ (f.size = 1000) (.grow f.size) (fun h => by rw [h]; rfl),
    under_ite _ (f.part = 1000) (.reveal f.part) (fun h => by rw [h]; rfl),
    under_ite _ (f.shown = 1000) (.fade f.shown) (fun h => by rw [h]; rfl)]
  obtain ⟨shift, size, part, shown, shape⟩ := f
  cases shape with
  | none => rfl
  | some segments => rfl

/-- The poses of a frame are of distinct properties: one at most for each. -/
theorem poses_distinct (f : Frame) : (f.poses.map Pose.property).Nodup := by
  have h : List.Sublist (f.poses.map Pose.property)
      ([.place] ++ [.size] ++ [.line] ++ [.opacity] ++ [.shape]) := by
    rw [poses, List.map_append, List.map_append, List.map_append, List.map_append]
    refine List.Sublist.append (List.Sublist.append (List.Sublist.append (List.Sublist.append
      ((ite_sublist _ _).map Pose.property) ((ite_sublist _ _).map Pose.property))
      ((ite_sublist _ _).map Pose.property)) ((ite_sublist _ _).map Pose.property)) ?_
    cases f.shape with
    | none => exact List.nil_sublist _
    | some segments => exact List.Sublist.refl _
  exact List.Nodup.sublist h (by decide)

/-- **A frame has no pose exactly when it is the still picture.** -/
theorem poses_eq_nil (f : Frame) : f.poses = [] ↔ f = rest :=
  ⟨fun h => (ofPoses_poses f).symm.trans (congrArg ofPoses h), fun h => by rw [h]; rfl⟩

/-! ### Two lists in a row, with distinct properties -/

/-- Where the keys of two lists in a row are distinct, no member of the first has the key of a
member of the second. -/
private theorem ne_of_distinct_append {α β : Type} (g : α → β) : ∀ {l r : List α},
    ((l ++ r).map g).Nodup → ∀ a ∈ l, ∀ b ∈ r, g a ≠ g b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: l, r, hd, a, ha, b, hb => by
    have hd' : g x ∉ (l ++ r).map g ∧ ((l ++ r).map g).Nodup := List.nodup_cons.mp hd
    rcases List.mem_cons.mp ha with e | e
    · intro he
      exact hd'.1 (List.mem_map.mpr ⟨b, List.mem_append_right l hb, (e ▸ he).symm⟩)
    · exact ne_of_distinct_append g hd'.2 a e b hb

/-- **What the frame of two lists in a row shows of a property**, where the properties of the
two together are distinct: what the frame of the second shows, and what the frame of the first
shows where the second has that property at rest. So the frame of the two is made of their two
frames, and of nothing else. -/
private theorem pose_merge {ps qs : List Pose} (hd : ((ps ++ qs).map Pose.property).Nodup)
    (π : Property) : (ofPoses (ps ++ qs)).pose π =
      if (ofPoses qs).pose π = rest.pose π then (ofPoses ps).pose π else (ofPoses qs).pose π := by
  rw [ofPoses_append]
  cases hfind : qs.find? (fun p => decide (p.property = π)) with
  | none =>
    have hno : ∀ p ∈ qs, p.property ≠ π := fun p hp e =>
      List.find?_eq_none.mp hfind p hp (decide_eq_true e)
    have e2 : (ofPoses qs).pose π = rest.pose π := pose_under_of_no hno rest
    rw [pose_under_of_no hno (ofPoses ps), if_pos e2]
  | some q =>
    have hq : q ∈ qs := List.mem_of_find?_eq_some hfind
    have hπ : q.property = π :=
      of_decide_eq_true (List.find?_some (p := fun p : Pose => decide (p.property = π)) hfind)
    subst hπ
    have hdq : (qs.map Pose.property).Nodup :=
      List.Nodup.sublist ((List.sublist_append_right ps qs).map Pose.property) hd
    have hqs : ∀ p ∈ qs, p.property = q.property → p = q := fun p hp e =>
      eq_of_distinct Pose.property qs hdq p q hp hq e
    have hps : ∀ p ∈ ps, p.property ≠ q.property := fun p hp =>
      ne_of_distinct_append Pose.property hd p hp q hq
    have e1 : ((ofPoses ps).under qs).pose q.property = some q := pose_under_of_mem hq hqs _
    have e2 : (ofPoses qs).pose q.property = some q := pose_under_of_mem hq hqs rest
    have e3 : (ofPoses ps).pose q.property = rest.pose q.property := pose_under_of_no hps rest
    rw [e1, e2, e3]
    cases Decidable.em (some q = rest.pose q.property) with
    | inl h =>
      rw [if_pos h]
      exact h
    | inr h => rw [if_neg h]

end Frame

/-! ## The frame of a motion -/

namespace Change

/-- **A change sets one property at every progress**: its own. -/
theorem at_property (c : Change) (e : Int) : (c.at e).property = c.property := by
  cases c with
  | morph a b =>
    show (if a.length = b.length then
        Pose.shape (List.zipWith (fun x y => ICubic.mix x y e) a b)
      else if e < 500 then Pose.shape a
      else Pose.shape b).property = Property.shape
    split
    · rfl
    · split
      · rfl
      · rfl
  | _ => rfl

/-- The start of a change is of the change's property. -/
theorem start_property (c : Change) : c.start.property = c.property := by
  cases c <;> rfl

/-- The end of a change is of the change's property. -/
theorem stop_property (c : Change) : c.stop.property = c.property := by
  cases c <;> rfl

/-- **A change from rest to rest is at rest at every progress.** A thing under it is drawn as
the still picture has it, whatever the easing does on the way. -/
theorem at_atRest {c : Change} (h0 : c.start.AtRest) (h1 : c.stop.AtRest) (e : Int) :
    (c.at e).AtRest := by
  cases c with
  | shift a b =>
    have ea : a = 0 := h0
    have eb : b = 0 := h1
    rw [ea, eb]
    show (⟨mix (0 : IVec).x (0 : IVec).x e, mix (0 : IVec).y (0 : IVec).y e⟩ : IVec) = 0
    exact IVec.ext (mix_self _ e) (mix_self _ e)
  | grow a b =>
    have ea : a = 1000 := h0
    have eb : b = 1000 := h1
    rw [ea, eb]
    exact mix_self 1000 e
  | reveal a b =>
    have ea : a = 1000 := h0
    have eb : b = 1000 := h1
    rw [ea, eb]
    exact mix_self 1000 e
  | fade a b =>
    have ea : a = 1000 := h0
    have eb : b = 1000 := h1
    rw [ea, eb]
    exact mix_self 1000 e
  | morph a b =>
    show Pose.AtRest (if a.length = b.length then
        Pose.shape (List.zipWith (fun x y => ICubic.mix x y e) a b)
      else if e < 500 then Pose.shape a
      else Pose.shape b)
    split
    · exact True.intro
    · split
      · exact True.intro
      · exact True.intro

end Change

namespace Track

/-- **A track sets one property at every moment**: its change's. -/
theorem at_property {κ : Type} (tr : Track κ) (t : Nat) :
    (tr.at t).property = tr.change.property :=
  Change.at_property tr.change (tr.timing.at t)

/-- **A track from rest to rest is at rest at every moment.** It does nothing that is seen,
unless it is a change of shape. -/
theorem at_atRest {κ : Type} {tr : Track κ} (h0 : tr.change.start.AtRest) (h1 : tr.Settles)
    (t : Nat) : (tr.at t).AtRest :=
  Change.at_atRest h0 h1 (tr.timing.at t)

end Track

namespace Motion

variable {κ : Type}

/-! ### The poses of a key -/

/-- The poses of a key in two motions in a row are its poses in the first and then its poses in
the second. -/
theorem posesOf_append [BEq κ] (m n : Motion κ) (key : κ) (t : Nat) :
    (m ++ n).posesOf key t = m.posesOf key t ++ n.posesOf key t := by
  show ((m ++ n).filter fun tr => tr.key == key).map (fun tr => tr.at t) =
    (m.filter fun tr => tr.key == key).map (fun tr => tr.at t) ++
      (n.filter fun tr => tr.key == key).map (fun tr => tr.at t)
  rw [List.filter_append, List.map_append]

/-- The pose of a track is one of the poses of its key. -/
theorem posesOf_of_mem [BEq κ] {m : Motion κ} {tr : Track κ} (htr : tr ∈ m) {key : κ}
    (hk : (tr.key == key) = true) (t : Nat) : tr.at t ∈ m.posesOf key t :=
  List.mem_map.mpr ⟨tr, List.mem_filter.mpr ⟨htr, hk⟩, rfl⟩

/-- A first track with the key gives the key its first pose. -/
private theorem posesOf_cons_pos [BEq κ] {tr : Track κ} {key : κ} (h : (tr.key == key) = true)
    (m : Motion κ) (t : Nat) : Motion.posesOf (tr :: m) key t = tr.at t :: m.posesOf key t := by
  show ((tr :: m).filter fun tr => tr.key == key).map (fun tr => tr.at t) =
    tr.at t :: (m.filter fun tr => tr.key == key).map (fun tr => tr.at t)
  rw [List.filter_cons_of_pos (p := fun tr : Track κ => tr.key == key) h, List.map_cons]

/-- A first track with another key gives the key no pose. -/
private theorem posesOf_cons_neg [BEq κ] {tr : Track κ} {key : κ} (h : (tr.key == key) = false)
    (m : Motion κ) (t : Nat) : Motion.posesOf (tr :: m) key t = m.posesOf key t := by
  have hn : ¬(tr.key == key) = true := fun e => Bool.false_ne_true (h.symm.trans e)
  show ((tr :: m).filter fun tr => tr.key == key).map (fun tr => tr.at t) =
    (m.filter fun tr => tr.key == key).map (fun tr => tr.at t)
  rw [List.filter_cons_of_neg (p := fun tr : Track κ => tr.key == key) hn]

/-! ### The frame of a thing -/

/-- A motion with no track gives every thing the still picture. -/
theorem frame_nil [BEq κ] (key : κ) (t : Nat) :
    Motion.frame ([] : Motion κ) key t = Frame.rest := rfl

/-- **A thing with no track is the still picture**, at every moment. -/
theorem frame_of_no_track [BEq κ] [LawfulBEq κ] (m : Motion κ) (key : κ) (t : Nat)
    (h : ∀ tr ∈ m, tr.key ≠ key) : m.frame key t = Frame.rest :=
  congrArg Frame.ofPoses (still_of_no_track m key t h)

/-- **The frame of two motions in a row** is the frame of the first under the poses of the
second. Tracks that are put after others are put on what the others left. -/
theorem frame_append [BEq κ] (m n : Motion κ) (key : κ) (t : Nat) :
    (m ++ n).frame key t = (m.frame key t).under (n.posesOf key t) :=
  (congrArg Frame.ofPoses (posesOf_append m n key t)).trans (Frame.ofPoses_append _ _)

/-- **The tracks of other things do not change the frame of a thing.** Tracks put after a motion,
none with the key of a thing, leave the frame of that thing as it is. -/
theorem frame_append_left [BEq κ] [LawfulBEq κ] (m : Motion κ) {n : Motion κ} {key : κ}
    (h : ∀ tr ∈ n, tr.key ≠ key) (t : Nat) : (m ++ n).frame key t = m.frame key t :=
  (frame_append m n key t).trans
    (congrArg (Frame.under (m.frame key t)) (still_of_no_track n key t h))

/-- Tracks put before a motion, none with the key of a thing, leave the frame of that thing as
it is. -/
theorem frame_append_right [BEq κ] [LawfulBEq κ] {m : Motion κ} (n : Motion κ) {key : κ}
    (h : ∀ tr ∈ m, tr.key ≠ key) (t : Nat) : (m ++ n).frame key t = n.frame key t :=
  (frame_append m n key t).trans
    (congrArg (fun g : Frame => g.under (n.posesOf key t)) (frame_of_no_track m key t h))

/-- One more track at the end of a motion puts its pose on the frame of its thing. -/
theorem frame_concat [BEq κ] [LawfulBEq κ] (m : Motion κ) (tr : Track κ) (t : Nat) :
    (m ++ [tr]).frame tr.key t = (tr.at t).onto (m.frame tr.key t) :=
  (frame_append m [tr] tr.key t).trans
    (congrArg (Frame.under (m.frame tr.key t)) (posesOf_cons_pos (beq_iff_eq.mpr rfl) [] t))

/-- **Where every pose of a thing is at rest, its frame is at rest.** The thing is drawn as the
still picture has it, whatever its shape. This takes the end laws of
`Whatwg/Svg/Scene/Motion/Laws.lean`, which are of poses, to what is seen. -/
theorem frame_atRest [BEq κ] {m : Motion κ} {key : κ} {t : Nat}
    (h : ∀ p ∈ m.posesOf key t, p.AtRest) : (m.frame key t).AtRest :=
  Frame.ofPoses_atRest h

/-- **Where every track is at rest at a moment, every thing is drawn as the still picture has
it** at that moment, whatever its shape. -/
theorem frame_atRest_of_tracks [BEq κ] {m : Motion κ} {t : Nat}
    (h : ∀ tr ∈ m, (tr.at t).AtRest) (key : κ) : (m.frame key t).AtRest :=
  frame_atRest fun p hp => by
    obtain ⟨tr, htr, _, rfl⟩ := mem_posesOf m key t hp
    exact h tr htr

/-- **At the end of a step every thing looks as the still picture has it.** A motion held in its
step, whose easings are proper and whose tracks settle, shows each thing at rest from the step's
end on. Its shape is whatever a track gave it last. -/
theorem within_frame_atRest [BEq κ] (m : Motion κ) (hp : ∀ tr ∈ m, tr.timing.ease.Proper)
    (hs : ∀ tr ∈ m, tr.Settles) {t : Nat} (ht : 1000 ≤ t) (key : κ) :
    (m.within.frame key t).AtRest :=
  frame_atRest_of_tracks (within_after m hp hs ht) key

/-- **Holding a motion inside its step does not change the poses of its first moment.** -/
theorem within_posesOf_zero [BEq κ] (m : Motion κ) (key : κ) :
    m.within.posesOf key 0 = m.posesOf key 0 := by
  show ((m.map fun tr => ({ tr with timing := tr.timing.within } : Track κ)).filter
      fun tr => tr.key == key).map (fun tr => tr.at 0) =
    (m.filter fun tr => tr.key == key).map fun tr => tr.at 0
  rw [List.filter_map, List.map_map]
  exact List.map_congr_left fun tr _ =>
    congrArg tr.change.at (Transition.within_at_zero tr.timing)

/-- **Holding a motion inside its step does not change its first moment**: every thing has the
same frame there. So a law of the moment `0` holds of the step that a caller plays. -/
theorem within_frame_zero [BEq κ] (m : Motion κ) (key : κ) :
    m.within.frame key 0 = m.frame key 0 :=
  congrArg Frame.ofPoses (within_posesOf_zero m key)

/-! ### One track for each property of a thing -/

/-- Whether no thing has two tracks of one property: a program can test its motion. -/
instance [DecidableEq κ] (m : Motion κ) : Decidable m.Single :=
  inferInstanceAs
    (Decidable (m.map fun tr : Track κ => (tr.key, tr.change.property)).Nodup)

/-- **A motion whose tracks have distinct keys is `Single`.** A thing with one track at most has
no two tracks of one property, so the frame of each thing shows the pose of its track. -/
theorem single_of_keys : ∀ {m : Motion κ}, Distinct (fun tr : Track κ => tr.key) m → m.Single
  | [], _ => List.nodup_nil
  | tr :: rest, h => by
    have hd : tr.key ∉ rest.map (fun tr : Track κ => tr.key) ∧
        (rest.map fun tr : Track κ => tr.key).Nodup := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, single_of_keys hd.2⟩
    obtain ⟨tr', htr', e⟩ := List.mem_map.mp hm
    exact hd.1 (List.mem_map.mpr ⟨tr', htr', congrArg Prod.fst e⟩)

/-- **A motion held inside its step is `Single` where the motion is.** The cut at the step's end
changes times only: each track keeps its thing and its property. So the reader reads the step
that a caller plays as it reads the step of the plan. -/
theorem Single.within {m : Motion κ} (h : m.Single) : m.within.Single := by
  have e : (m.within.map fun tr : Track κ => (tr.key, tr.change.property)) =
      m.map fun tr : Track κ => (tr.key, tr.change.property) :=
    List.map_map.trans (List.map_congr_left fun _ _ => rfl)
  show (m.within.map fun tr : Track κ => (tr.key, tr.change.property)).Nodup
  rw [e]
  exact h

/-- **In a motion where no thing has two tracks of one property, the poses of a thing are of
distinct properties** at every moment. -/
theorem posesOf_distinct [BEq κ] [LawfulBEq κ] {m : Motion κ} (h : m.Single) (key : κ)
    (t : Nat) : ((m.posesOf key t).map Pose.property).Nodup := by
  induction m with
  | nil => exact List.nodup_nil
  | cons tr rest ih =>
    have hd : (tr.key, tr.change.property) ∉
        rest.map (fun tr : Track κ => (tr.key, tr.change.property)) ∧
        (rest.map fun tr : Track κ => (tr.key, tr.change.property)).Nodup :=
      List.nodup_cons.mp h
    cases hb : tr.key == key with
    | false =>
      rw [posesOf_cons_neg hb]
      exact ih hd.2
    | true =>
      rw [posesOf_cons_pos hb, List.map_cons]
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih hd.2⟩
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hmem
      obtain ⟨tr', htr', hk', rfl⟩ := mem_posesOf rest key t hp
      have hkey : tr'.key = tr.key := (beq_iff_eq.mp hk').trans (beq_iff_eq.mp hb).symm
      have hprop : tr'.change.property = tr.change.property :=
        (Track.at_property tr' t).symm.trans (he.trans (Track.at_property tr t))
      refine hd.1 (List.mem_map.mpr ⟨tr', htr', ?_⟩)
      show (tr'.key, tr'.change.property) = (tr.key, tr.change.property)
      rw [hkey, hprop]

/-- **The pose of a track is in the frame of its thing**, in a motion where no thing has two
tracks of one property. Putting the pose on the frame again changes nothing: the thing is drawn
as the track says. -/
theorem frame_has [BEq κ] [LawfulBEq κ] {m : Motion κ} (h : m.Single) {tr : Track κ}
    (htr : tr ∈ m) (t : Nat) : (tr.at t).onto (m.frame tr.key t) = m.frame tr.key t :=
  Frame.ofPoses_has (posesOf_distinct h tr.key t) (posesOf_of_mem htr (beq_iff_eq.mpr rfl) t)

/-- **The later of two tracks of one property on one thing is the one shown.** A track with no
track of its thing and property after it is in the frame, whatever came before it. This holds of
every motion. -/
theorem frame_last [BEq κ] [LawfulBEq κ] (m : Motion κ) {tr : Track κ} {n : Motion κ}
    (h : ∀ tr' ∈ n, tr'.key = tr.key → tr'.change.property ≠ tr.change.property) (t : Nat) :
    (tr.at t).onto ((m ++ tr :: n).frame tr.key t) = (m ++ tr :: n).frame tr.key t := by
  have e : (m ++ tr :: n).posesOf tr.key t =
      m.posesOf tr.key t ++ tr.at t :: n.posesOf tr.key t := by
    rw [posesOf_append, posesOf_cons_pos (beq_iff_eq.mpr rfl)]
  show (tr.at t).onto (Frame.ofPoses ((m ++ tr :: n).posesOf tr.key t)) =
    Frame.ofPoses ((m ++ tr :: n).posesOf tr.key t)
  rw [e]
  refine Frame.under_last (fun p hp => ?_) Frame.rest _
  obtain ⟨tr', htr', hk', rfl⟩ := mem_posesOf n tr.key t hp
  rw [Track.at_property, Track.at_property]
  exact h tr' htr' (beq_iff_eq.mp hk')

/-- **Where a thing that shifts stands.** In a motion where no thing has two tracks of one
property, a thing with a shift from `a` to `b` stands off its place by the step between them at
the eased progress of the track. -/
theorem frame_shift [BEq κ] [LawfulBEq κ] {m : Motion κ} (h : m.Single) {k : κ} {a b : IVec}
    {tm : Transition} (htr : (⟨k, .shift a b, tm⟩ : Track κ) ∈ m) (t : Nat) :
    (m.frame k t).shift = ⟨mix a.x b.x (tm.at t), mix a.y b.y (tm.at t)⟩ :=
  (congrArg Frame.shift (frame_has h htr t)).symm

/-- **The size of a thing that grows**: the size between `a` and `b` at the eased progress of
the track. -/
theorem frame_size [BEq κ] [LawfulBEq κ] {m : Motion κ} (h : m.Single) {k : κ} {a b : Int}
    {tm : Transition} (htr : (⟨k, .grow a b, tm⟩ : Track κ) ∈ m) (t : Nat) :
    (m.frame k t).size = mix a b (tm.at t) :=
  (congrArg Frame.size (frame_has h htr t)).symm

/-- **How much of a line that is revealed is drawn**: the part between `a` and `b` at the eased
progress of the track. -/
theorem frame_part [BEq κ] [LawfulBEq κ] {m : Motion κ} (h : m.Single) {k : κ} {a b : Int}
    {tm : Transition} (htr : (⟨k, .reveal a b, tm⟩ : Track κ) ∈ m) (t : Nat) :
    (m.frame k t).part = mix a b (tm.at t) :=
  (congrArg Frame.part (frame_has h htr t)).symm

/-- **The opacity of a thing that fades**: the opacity between `a` and `b` at the eased progress
of the track. -/
theorem frame_shown [BEq κ] [LawfulBEq κ] {m : Motion κ} (h : m.Single) {k : κ} {a b : Int}
    {tm : Transition} (htr : (⟨k, .fade a b, tm⟩ : Track κ) ∈ m) (t : Nat) :
    (m.frame k t).shown = mix a b (tm.at t) :=
  (congrArg Frame.shown (frame_has h htr t)).symm

/-- **The shape of a thing that changes shape** between two lists of one length: the two mixed
segment by segment at the eased progress of the track. -/
theorem frame_shape [BEq κ] [LawfulBEq κ] {m : Motion κ} (h : m.Single) {k : κ}
    {a b : List ICubic} {tm : Transition} (htr : (⟨k, .morph a b, tm⟩ : Track κ) ∈ m)
    (hl : a.length = b.length) (t : Nat) :
    (m.frame k t).shape = some (List.zipWith (fun x y => ICubic.mix x y (tm.at t)) a b) := by
  have e : (Change.morph a b).at (tm.at t) =
      Pose.shape (List.zipWith (fun x y => ICubic.mix x y (tm.at t)) a b) :=
    Change.at_morph a b (tm.at t) hl
  have hf : ((Change.morph a b).at (tm.at t)).onto (m.frame k t) = m.frame k t :=
    frame_has h htr t
  rw [e] at hf
  exact (congrArg Frame.shape hf).symm

/-- **The end law of a frame.** In a motion where no thing has two tracks of one property, a
track that is over has left its thing at the end of its change. -/
theorem frame_done [BEq κ] [LawfulBEq κ] {m : Motion κ} (h : m.Single) {tr : Track κ}
    (htr : tr ∈ m) {t : Nat} (hd : tr.Done t) :
    tr.change.stop.onto (m.frame tr.key t) = m.frame tr.key t := by
  rw [← Track.at_done tr t hd]
  exact frame_has h htr t

/-! ### Motions that a reader cannot tell apart -/

/-- What the frame of two motions in a row shows of a property, where no thing has two tracks of
one property in the two together: what the frame of the second shows, and what the frame of the
first shows where the second has that property at rest. -/
private theorem pose_frame_append [BEq κ] [LawfulBEq κ] {m n : Motion κ} (hs : (m ++ n).Single)
    (key : κ) (t : Nat) (π : Property) : ((m ++ n).frame key t).pose π =
      if (n.frame key t).pose π = Frame.rest.pose π then (m.frame key t).pose π
      else (n.frame key t).pose π := by
  have hd : ((m.posesOf key t ++ n.posesOf key t).map Pose.property).Nodup := by
    rw [← posesOf_append]
    exact posesOf_distinct hs key t
  exact (congrArg (fun l => (Frame.ofPoses l).pose π) (posesOf_append m n key t)).trans
    (Frame.pose_merge hd π)

namespace Same

/-- A motion is the same as itself. -/
theorem refl [BEq κ] (m : Motion κ) : Same m m := fun _ _ => rfl

/-- Being the same to a reader goes both ways. -/
theorem symm [BEq κ] {m n : Motion κ} (h : Same m n) : Same n m := fun key t => (h key t).symm

/-- Two motions that are each the same as a third are the same. -/
theorem trans [BEq κ] {m n o : Motion κ} (h : Same m n) (h' : Same n o) : Same m o :=
  fun key t => (h key t).trans (h' key t)

/-- **The same tracks put after two motions that are the same give motions that are the
same.** What comes first may be replaced by what a reader cannot tell from it. -/
theorem append_right [BEq κ] {m m' : Motion κ} (h : Same m m') (n : Motion κ) :
    Same (m ++ n) (m' ++ n) := by
  intro key t
  rw [frame_append, frame_append, h key t]

/-- **Two motions with the same tracks are the same to a reader**, where no thing has two tracks
of one property in the first. The order of the tracks does not matter, and the second may say a
track twice. -/
theorem of_mem [BEq κ] [LawfulBEq κ] {m n : Motion κ} (hs : m.Single)
    (h : ∀ tr, tr ∈ m ↔ tr ∈ n) : Same m n := by
  intro key t
  refine Frame.ofPoses_congr (posesOf_distinct hs key t) fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨tr, htr, hk, rfl⟩ := mem_posesOf m key t hp
    exact posesOf_of_mem ((h tr).mp htr) hk t
  · obtain ⟨tr, htr, hk, rfl⟩ := mem_posesOf n key t hp
    exact posesOf_of_mem ((h tr).mpr htr) hk t

/-- **Two motions in a row may be put in the other order**, where no thing has two tracks of one
property in the two together. -/
theorem append_comm [BEq κ] [LawfulBEq κ] {m n : Motion κ} (hs : (m ++ n).Single) :
    Same (m ++ n) (n ++ m) :=
  of_mem hs fun tr => by
    rw [List.mem_append, List.mem_append]
    exact ⟨Or.symm, Or.symm⟩

/-- **A track that sets what is already seen can be dropped.** Where the frame of its thing
shows the pose of the track at every moment, the motion with the track at its end is the same to
a reader as the motion without it. -/
theorem of_shown [BEq κ] [LawfulBEq κ] {m : Motion κ} {tr : Track κ}
    (h : ∀ t, (tr.at t).onto (m.frame tr.key t) = m.frame tr.key t) : Same (m ++ [tr]) m := by
  intro key t
  cases hb : tr.key == key with
  | false =>
    exact (frame_append m [tr] key t).trans
      (congrArg (Frame.under (m.frame key t)) (posesOf_cons_neg hb [] t))
  | true =>
    have hk : tr.key = key := beq_iff_eq.mp hb
    subst hk
    exact (frame_concat m tr t).trans (h t)

/-- **A track that does nothing can be dropped.** The track goes from rest to rest and is not a
change of shape: a shift from nothing to nothing, or a size, a line or an opacity from the whole
to the whole. Where no earlier track of its thing is of its property, the motion with the track
at its end is the same to a reader as the motion without it. -/
theorem of_idle [BEq κ] [LawfulBEq κ] {m : Motion κ} {tr : Track κ}
    (h0 : tr.change.start.AtRest) (h1 : tr.Settles) (hs : tr.change.property ≠ .shape)
    (hm : ∀ tr' ∈ m, tr'.key = tr.key → tr'.change.property ≠ tr.change.property) :
    Same (m ++ [tr]) m := by
  refine of_shown fun t => ?_
  have hno : ∀ p ∈ m.posesOf tr.key t, p.property ≠ (tr.at t).property := by
    intro p hp
    obtain ⟨tr', htr', hk', rfl⟩ := mem_posesOf m tr.key t hp
    rw [Track.at_property, Track.at_property]
    exact hm tr' htr' (beq_iff_eq.mp hk')
  have hr : (tr.at t).onto Frame.rest = Frame.rest :=
    Pose.onto_rest (Track.at_atRest h0 h1 t) (fun e => hs ((Track.at_property tr t).symm.trans e))
  exact (Frame.onto_under hno Frame.rest).trans
    (congrArg (fun g : Frame => g.under (m.posesOf tr.key t)) hr)

/-- **A track at the end of a motion can be dropped exactly where its thing's frame already shows
its pose at every moment.** This is the premise that `of_shown` asks, and no weaker one will
do. -/
theorem concat_iff [BEq κ] [LawfulBEq κ] {m : Motion κ} {tr : Track κ} :
    Same (m ++ [tr]) m ↔ ∀ t, (tr.at t).onto (m.frame tr.key t) = m.frame tr.key t :=
  ⟨fun h t => (frame_concat m tr t).symm.trans (h tr.key t), of_shown⟩

/-- **A track that does nothing can be dropped from the middle of a motion.** Only the tracks
before it are asked for: none of its thing is of its property. -/
theorem of_idle_append [BEq κ] [LawfulBEq κ] {m : Motion κ} {tr : Track κ}
    (h0 : tr.change.start.AtRest) (h1 : tr.Settles) (hs : tr.change.property ≠ .shape)
    (hm : ∀ tr' ∈ m, tr'.key = tr.key → tr'.change.property ≠ tr.change.property)
    (n : Motion κ) : Same (m ++ tr :: n) (m ++ n) := by
  have h := (of_idle h0 h1 hs hm).append_right n
  rw [List.append_assoc] at h
  exact h

/-- **A track said twice is said once.** In a motion where no thing has two tracks of one
property, a track of the motion put at its end again changes nothing that is seen. -/
theorem of_again [BEq κ] [LawfulBEq κ] {m : Motion κ} (hs : m.Single) {tr : Track κ}
    (htr : tr ∈ m) : Same (m ++ [tr]) m :=
  of_shown fun t => frame_has hs htr t

/-- **Motions that are the same, put in a row, give motions that are the same**, where no thing
has two tracks of one property in either row. The frame of a row is then made of the frames of
its two parts and of nothing else. Without the two premises the law fails. A control at the end
of this file is a track that does nothing alone, so that a reader cannot tell it from no track,
and that wins over an earlier track of its thing. -/
theorem append [BEq κ] [LawfulBEq κ] {m m' n n' : Motion κ} (hs : (m ++ n).Single)
    (hs' : (m' ++ n').Single) (hm : Same m m') (hn : Same n n') : Same (m ++ n) (m' ++ n') := by
  intro key t
  refine Frame.ext_pose fun π => ?_
  rw [pose_frame_append hs key t π, pose_frame_append hs' key t π, hm key t, hn key t]

end Same

end Motion

/-! ## Starting where a thing is seen -/

namespace Change

/-- **A change that starts where a thing is seen keeps its end.** -/
theorem from_stop (c : Change) (f : Frame) : (c.from f).stop = c.stop := by
  cases c <;> rfl

/-- A change that starts where a thing is seen changes the same property. -/
theorem from_property (c : Change) (f : Frame) : (c.from f).property = c.property := by
  cases c <;> rfl

/-- A shift that starts from the still picture is the shift itself. -/
theorem from_rest_shift (a b : IVec) : (Change.shift a b).from Frame.rest = .shift a b :=
  congrArg (fun s => Change.shift s b) (IVec.add_zero a)

/-- **A change that starts at rest, started from the still picture, is the change itself.** A
thing that no earlier motion has left off its rest is where its change says. -/
theorem from_rest {c : Change} (h : c.start.AtRest) : c.from Frame.rest = c := by
  cases c with
  | shift a b => exact from_rest_shift a b
  | grow a b =>
    have e : a = 1000 := h
    subst e
    rfl
  | reveal a b =>
    have e : a = 1000 := h
    subst e
    rfl
  | fade a b =>
    have e : a = 1000 := h
    subst e
    rfl
  | morph a b => rfl

/-- **A shift that starts where a thing is seen starts further off by the shift of the frame.**
A shift is told from the thing's place in the next picture. A thing that an earlier motion left
off its place is that much further from it. -/
theorem from_start_shift (a b : IVec) (f : Frame) :
    ((Change.shift a b).from f).start = .shift (a + f.shift) := rfl

/-- **A change of shape that starts where a thing is seen starts at the shape of the frame**,
where the frame has one. -/
theorem from_start_morph {a b s : List ICubic} {f : Frame} (h : f.shape = some s) :
    ((Change.morph a b).from f).start = .shape s :=
  congrArg (fun o : Option (List ICubic) => Pose.shape (o.getD a)) h

/-- **The start of a change that starts where a thing is seen is what is seen.** Putting it on
the frame changes nothing, so the thing does not jump when the change begins. This holds of a
size, a line and an opacity, of a shift told from the thing's own place, and of a change of
shape where the frame has a shape. -/
theorem from_start_onto {c : Change} {f : Frame} (hp : c.property = .place → c.start.AtRest)
    (hs : c.property = .shape → f.shape ≠ none) : (c.from f).start.onto f = f := by
  cases c with
  | shift a b =>
    have e : a = 0 := hp rfl
    subst e
    exact congrArg (fun s => (Pose.shift s).onto f) (IVec.zero_add f.shift)
  | grow a b => rfl
  | reveal a b => rfl
  | fade a b => rfl
  | morph a b =>
    obtain ⟨shift, size, part, shown, shape⟩ := f
    cases shape with
    | none => exact absurd rfl (hs rfl)
    | some segments => rfl

end Change

/-! ## Going to rest -/

namespace Frame

/-- A member of a list of one member or none. -/
private theorem mem_ite {α : Type} {c : Prop} [Decidable c] {a x : α} :
    a ∈ (if c then [] else [x]) ↔ ¬c ∧ a = x := by
  cases Decidable.em c with
  | inl hc =>
    rw [if_pos hc]
    exact ⟨fun h => (nomatch h), fun h => absurd hc h.1⟩
  | inr hc =>
    rw [if_neg hc]
    exact ⟨fun h => ⟨hc, List.mem_singleton.mp h⟩, fun h => List.mem_singleton.mpr h.2⟩

/-- A function over a list of one member or none. -/
private theorem map_ite {α β : Type} (g : α → β) (c : Prop) [Decidable c] (x : α) :
    (if c then [] else [x]).map g = if c then [] else [g x] :=
  apply_ite (List.map g) c [] [x]

/-- **The changes that take a frame to rest, one by one**: a shift from where the thing stands
to its place, and a size, a line and an opacity from what is seen to the whole, each only where
the frame is not at rest. -/
theorem mem_toRest {f : Frame} {c : Change} : c ∈ f.toRest ↔
    (f.shift ≠ 0 ∧ c = .shift f.shift 0) ∨ (f.size ≠ 1000 ∧ c = .grow f.size 1000) ∨
      (f.part ≠ 1000 ∧ c = .reveal f.part 1000) ∨ (f.shown ≠ 1000 ∧ c = .fade f.shown 1000) := by
  rw [toRest, List.mem_append, List.mem_append, List.mem_append, mem_ite, mem_ite, mem_ite,
    mem_ite, or_assoc, or_assoc]

/-- **Every change of `toRest` ends at rest.** -/
theorem toRest_stop (f : Frame) : ∀ c ∈ f.toRest, c.stop.AtRest := by
  intro c hc
  rcases mem_toRest.mp hc with h | h | h | h
  · rw [h.2]
    exact rfl
  · rw [h.2]
    exact rfl
  · rw [h.2]
    exact rfl
  · rw [h.2]
    exact rfl

/-- **Every change of `toRest` starts at what is seen.** Putting its start on the frame changes
nothing, so the thing does not jump when it begins to go to rest. -/
theorem toRest_start (f : Frame) : ∀ c ∈ f.toRest, c.start.onto f = f := by
  intro c hc
  rcases mem_toRest.mp hc with h | h | h | h
  · rw [h.2]
    rfl
  · rw [h.2]
    rfl
  · rw [h.2]
    rfl
  · rw [h.2]
    rfl

/-- No change of `toRest` is a change of shape. -/
theorem toRest_not_shape (f : Frame) : ∀ c ∈ f.toRest, c.property ≠ .shape := by
  intro c hc
  rcases mem_toRest.mp hc with h | h | h | h
  · rw [h.2]
    exact fun e => nomatch e
  · rw [h.2]
    exact fun e => nomatch e
  · rw [h.2]
    exact fun e => nomatch e
  · rw [h.2]
    exact fun e => nomatch e

/-- The changes of `toRest` are of distinct properties: one at most for each. -/
theorem toRest_distinct (f : Frame) : (f.toRest.map Change.property).Nodup := by
  have h : List.Sublist (f.toRest.map Change.property)
      ([.place] ++ [.size] ++ [.line] ++ [.opacity]) := by
    rw [toRest, List.map_append, List.map_append, List.map_append]
    exact List.Sublist.append (List.Sublist.append (List.Sublist.append
      ((ite_sublist _ _).map Change.property) ((ite_sublist _ _).map Change.property))
      ((ite_sublist _ _).map Change.property)) ((ite_sublist _ _).map Change.property)
  exact List.Nodup.sublist h (by decide)

/-- **A frame has no change to rest exactly when it is at rest.** -/
theorem toRest_eq_nil (f : Frame) : f.toRest = [] ↔ f.AtRest := by
  constructor
  · intro h
    have hno : ∀ c, c ∉ f.toRest := fun c hc => by
      rw [h] at hc
      cases hc
    exact ⟨Decidable.byContradiction fun hne => hno _ (mem_toRest.mpr (Or.inl ⟨hne, rfl⟩)),
      Decidable.byContradiction fun hne =>
        hno _ (mem_toRest.mpr (Or.inr (Or.inl ⟨hne, rfl⟩))),
      Decidable.byContradiction fun hne =>
        hno _ (mem_toRest.mpr (Or.inr (Or.inr (Or.inl ⟨hne, rfl⟩)))),
      Decidable.byContradiction fun hne =>
        hno _ (mem_toRest.mpr (Or.inr (Or.inr (Or.inr ⟨hne, rfl⟩))))⟩
  · intro h
    refine eq_nil_of_no_mem fun c hc => ?_
    rcases mem_toRest.mp hc with e | e | e | e
    · exact e.1 h.1
    · exact e.1 h.2.1
    · exact e.1 h.2.2.1
    · exact e.1 h.2.2.2

/-- The starts of the changes of `toRest` are the poses of the frame, less its shape. -/
theorem toRest_starts (f : Frame) :
    f.toRest.map Change.start = ({ f with shape := none } : Frame).poses := by
  show ((((if f.shift = 0 then [] else [Change.shift f.shift 0]) ++
      (if f.size = 1000 then [] else [Change.grow f.size 1000])) ++
      (if f.part = 1000 then [] else [Change.reveal f.part 1000])) ++
      (if f.shown = 1000 then [] else [Change.fade f.shown 1000])).map Change.start =
    ((((if f.shift = 0 then [] else [Pose.shift f.shift]) ++
      (if f.size = 1000 then [] else [Pose.grow f.size])) ++
      (if f.part = 1000 then [] else [Pose.reveal f.part])) ++
      (if f.shown = 1000 then [] else [Pose.fade f.shown])) ++ []
  rw [List.append_nil, List.map_append, List.map_append, List.map_append, map_ite, map_ite,
    map_ite, map_ite]
  rfl

/-- **The starts of `toRest` give the frame back**, on its place, its size, its line and its
opacity: the thing begins to go to rest from where it is seen. The shape is the thing's own,
since a frame knows no rest of a shape. -/
theorem ofPoses_toRest (f : Frame) :
    ofPoses (f.toRest.map Change.start) = { f with shape := none } := by
  rw [toRest_starts]
  exact ofPoses_poses _

/-- **The starts of `toRest` show the thing where it is seen**: the frame of the starts has the
place, the size, the line and the opacity of the frame. This is `ofPoses_toRest`, value by
value. -/
theorem toRest_shows (f : Frame) :
    (ofPoses (f.toRest.map Change.start)).shift = f.shift ∧
      (ofPoses (f.toRest.map Change.start)).size = f.size ∧
      (ofPoses (f.toRest.map Change.start)).part = f.part ∧
      (ofPoses (f.toRest.map Change.start)).shown = f.shown := by
  rw [ofPoses_toRest]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Poses at rest that are not shapes give the still picture. -/
theorem ofPoses_of_atRest {ps : List Pose} (h : ∀ p ∈ ps, p.AtRest ∧ p.property ≠ .shape) :
    ofPoses ps = rest := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    show (p.onto rest).under ps = rest
    rw [Pose.onto_rest (h p List.mem_cons_self).1 (h p List.mem_cons_self).2]
    exact ih fun r hr => h r (List.mem_cons_of_mem p hr)

/-- **The ends of `toRest` give the still picture.** -/
theorem toRest_stops (f : Frame) : ofPoses (f.toRest.map Change.stop) = rest := by
  refine ofPoses_of_atRest fun p hp => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact ⟨toRest_stop f c hc, fun e =>
    toRest_not_shape f c hc ((Change.stop_property c).symm.trans e)⟩

end Frame

/-! ## Controls

Each is a motion or a frame with numbers. Lean computes each one. -/

-- Two shifts on one box, ten to the right and then twenty down, each from its end to its end.
-- The box has both poses, and its frame shows the later one. A reader that adds the two steps
-- draws the box at `⟨10, 20⟩`, where neither track puts it.
#guard Motion.posesOf ([⟨"box", .shift ⟨10, 0⟩ ⟨10, 0⟩, {}⟩,
    ⟨"box", .shift ⟨0, 20⟩ ⟨0, 20⟩, {}⟩] : Motion String) "box" 500 =
  [.shift ⟨10, 0⟩, .shift ⟨0, 20⟩]
#guard (Motion.frame ([⟨"box", .shift ⟨10, 0⟩ ⟨10, 0⟩, {}⟩,
    ⟨"box", .shift ⟨0, 20⟩ ⟨0, 20⟩, {}⟩] : Motion String) "box" 500).shift = ⟨0, 20⟩

-- That motion is not `Single`, and its two tracks in the other order give another frame. So
-- `Motion.Same.of_mem` and `Motion.Same.append_comm` need their premise.
#guard ¬Motion.Single ([⟨"box", .shift ⟨10, 0⟩ ⟨10, 0⟩, {}⟩,
    ⟨"box", .shift ⟨0, 20⟩ ⟨0, 20⟩, {}⟩] : Motion String)
#guard (Motion.frame ([⟨"box", .shift ⟨0, 20⟩ ⟨0, 20⟩, {}⟩,
    ⟨"box", .shift ⟨10, 0⟩ ⟨10, 0⟩, {}⟩] : Motion String) "box" 500).shift = ⟨10, 0⟩

-- A box that comes a hundred from the left and fades in, by the progress itself. Its frame at
-- the start, half way and at the end: a hundred off and not shown, fifty off and half shown,
-- and the still picture. A line that no track names is the still picture at every moment.
#guard [0, 500, 1000].map (Motion.frame ([⟨"box", .shift ⟨-100, 0⟩ 0, {}⟩,
    ⟨"box", .fade 0 1000, {}⟩] : Motion String) "box") =
  [{ shift := ⟨-100, 0⟩, shown := 0 }, { shift := ⟨-50, 0⟩, shown := 500 }, {}]
#guard [0, 500, 1000].map (Motion.frame ([⟨"box", .shift ⟨-100, 0⟩ 0, {}⟩,
    ⟨"box", .fade 0 1000, {}⟩] : Motion String) "line") = [{}, {}, {}]

-- `Motion.Same.append` needs its premises, and `Motion.Same.of_idle` its last one. A shift from
-- nothing to nothing does nothing alone: a reader cannot tell it from no track. Put after a
-- shift of ten on the same box it wins, and the box stands at its place. With no track after
-- the shift of ten the box stands ten off.
#guard [0, 500, 1000].map (Motion.frame ([⟨"box", .shift 0 0, {}⟩] : Motion String) "box") =
  [0, 500, 1000].map (Motion.frame ([] : Motion String) "box")
#guard (Motion.frame ([⟨"box", .shift ⟨10, 0⟩ ⟨10, 0⟩, {}⟩,
    ⟨"box", .shift 0 0, {}⟩] : Motion String) "box" 500).shift = 0
#guard (Motion.frame ([⟨"box", .shift ⟨10, 0⟩ ⟨10, 0⟩, {}⟩] : Motion String) "box" 500).shift =
  ⟨10, 0⟩

/-- So `Motion.Same.append` does not hold of every four motions. The thing `0` shifts by ten, and
after that a shift from nothing to nothing is put on it, or no track. The two last parts are the
same to a reader (`Motion.Same.of_idle`), and the two rows are not: half way the thing stands at
its place in one and ten off in the other. -/
example : ¬∀ m m' n n' : Motion Nat, Motion.Same m m' → Motion.Same n n' →
    Motion.Same (m ++ n) (m' ++ n') := fun h =>
  absurd
    (congrArg Frame.shift
      (h [⟨0, .shift ⟨10, 0⟩ ⟨10, 0⟩, {}⟩] [⟨0, .shift ⟨10, 0⟩ ⟨10, 0⟩, {}⟩]
        [⟨0, .shift 0 0, {}⟩] [] (Motion.Same.refl _)
        (Motion.Same.of_idle (m := []) rfl rfl (fun e => nomatch e) (fun _ hm => nomatch hm))
        0 500))
    (by decide)

-- `Motion.Same.of_idle` asks that the track is not a change of shape. A change from a shape to
-- itself is at rest at every moment, and it is seen all the same: the frame has a shape, and
-- the still picture has the thing's own.
#guard (Motion.frame ([⟨"box", .morph [] [], {}⟩] : Motion String) "box" 500).AtRest
#guard (Motion.frame ([⟨"box", .morph [] [], {}⟩] : Motion String) "box" 500).shape = some []

-- A box caught half way, fifty off its place and half shown. The changes that take it to rest
-- start there. A shift told from thirty off its next place starts at twenty off the other way,
-- and a fade starts at what is shown, whatever start it was told.
#guard ({ shift := ⟨-50, 0⟩, shown := 500 } : Frame).toRest =
  [.shift ⟨-50, 0⟩ 0, .fade 500 1000]
#guard (Change.shift ⟨30, 0⟩ 0).from { shift := ⟨-50, 0⟩, shown := 500 } = .shift ⟨-20, 0⟩ 0
#guard (Change.fade 0 1000).from { shift := ⟨-50, 0⟩, shown := 500 } = .fade 500 1000

end Whatwg.Svg.Scene
