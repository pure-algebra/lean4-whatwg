import Whatwg.Svg.Scene.Reel

/-!
# WhatwgTest.Svg.Reel

lean4-effect4's run of frames and its player's loop, written on `Reel` of
`Whatwg/Svg/Scene/Reel.lean`.

**Source.** lean4-effect4 at commit `6ad8f7b8d`. `Run.framesBuilt` of
`tools/Tools/View/Run.lean` (lines 149 to 168) makes the pictures of a run: one as the run
opens, and one after each control, `most` controls at the most. `writeFrames` of
`tools/Drivers/View.lean` (lines 339 to 365) plays them: for each picture after the first it
writes the moments `k * 1000 / motion` of the step from the picture before, `k` from `1` to
`motion - 1`, and then the picture itself, which is the step's last moment by its law
`sample_end`.

Both are below in outline, on the kit's `Step`, with a thing as a key and a place along one
axis: `framesOf` is the loop of `framesBuilt` over any machine, and `written` is the loop of
`writeFrames`. This file is a template for the consumer's port: its list of pages is
`Reel.ofPictures`, and its loop is `Reel.frames`.

## What the port shows

- **The kit's frames are the consumer's**: `Reel.frames motion` is what `written` writes, on a
  run of four pictures in which things move, enter and leave.
- **The laws, read at the consumer's plan.** `run_joint`: every joint of every run under the
  plan is the picture at rest, so the consumer's `sample_end` is a law of the run and not of one
  step. `run_stands`: the step after starts each kept thing where the joint has it.
- **The decision.** The run does not draw at a joint a thing that is about to enter. Two guards
  are a plan whose entrance starts in view: the step's own first moment draws the new thing off
  its place, and the run at the joint draws the picture and nothing else.
-/

namespace WhatwgTest.Svg.Reel

open Whatwg.Svg.Scene

/-- A thing: a key and a place along one axis. -/
abbrev Thing := Nat × Int

/-! ## The consumer's two loops, in outline -/

/-- The pictures after the first: one after each control, `most` at the most. It is `go` of the
consumer's `framesBuilt`. -/
def framesGo {σ : Type} (next : σ → Option σ) (page : σ → List Thing) : Nat → σ → List (List Thing)
  | 0, _ => []
  | k + 1, s =>
    match next s with
    | none => []
    | some s' => page s' :: framesGo next page k s'

/-- The consumer's `framesBuilt`, over any machine: the picture as the run opens, and the
picture after each control. -/
def framesOf {σ : Type} (next : σ → Option σ) (page : σ → List Thing) (most : Nat) (s0 : σ) :
    List (List Thing) :=
  page s0 :: framesGo next page most s0

/-- The consumer's `writeFrames` loop: for each picture after the first, `motion - 1` moments of
the step from the picture before, and then the picture itself, at rest. -/
def written (plan : Plan Thing) (motion : Nat) : Option (List Thing) → List (List Thing) →
    List (List (Thing × Frame))
  | _, [] => []
  | prev, g :: rest =>
    (match prev with
      | some g0 =>
        (List.range' 1 (motion - 1)).map fun k =>
          ({ key := Prod.fst, old := g0, new := g, plan } : Step Thing Nat).sample
            (k * 1000 / motion)
      | none => []) ++ [g.map fun a => (a, Frame.rest)] ++ written plan motion (some g) rest

/-! ## A machine, a plan and their run -/

/-- A machine of four states: a counter that stops at three. -/
def next (n : Nat) : Option Nat := if n < 3 then some (n + 1) else none

/-- The picture of a state. Things move, enter and leave from one to the next. -/
def page : Nat → List Thing
  | 0 => [(1, 0)]
  | 1 => [(1, 0), (2, 40)]
  | 2 => [(1, 20), (2, 60), (3, 0)]
  | _ => [(2, 0), (3, 40)]

/-- The place of a thing. -/
def place (a : Thing) : IVec := ⟨a.2, 0⟩

/-- The consumer's plan, in outline: a kept thing moves, a new thing grows and an old thing
shrinks. -/
def look : Plan Thing :=
  ⟨Plan.moving place {}, fun _ => [(.grow 0 1000, {})], fun _ => [(.grow 1000 0, {})]⟩

/-- The pictures of the machine, by the consumer's loop. -/
def pictures : List (List Thing) := framesOf next page 64 0

/-- The run of the machine. -/
def run : Reel Thing Nat := Reel.ofPictures Prod.fst look pictures

-- The loop of `framesBuilt` stops when the machine has no control left: four pictures.
#guard pictures == [page 0, page 1, page 2, page 3]

-- **The kit's frames are what the consumer's loop writes**, at four moments of each step.
#guard run.frames 4 == written look 4 none pictures

-- The count of the consumer's pictures: one for each frame, and `motion - 1` more for each
-- frame after the first.
#guard (run.frames 4).length == pictures.length + (pictures.length - 1) * (4 - 1)

/-! ## The laws, read at the consumer's plan -/

theorem look_settles : look.Settles :=
  ⟨fun o n => Plan.moving_settles place {} o n, fun _ c hc => by
    cases List.mem_singleton.mp hc
    exact rfl⟩

theorem look_proper : look.Proper :=
  ⟨fun o n => Plan.moving_proper place {} (by decide) o n,
    fun _ c hc => by
      cases List.mem_singleton.mp hc
      decide,
    fun _ c hc => by
      cases List.mem_singleton.mp hc
      decide⟩

theorem look_keepsShapes : look.KeepsShapes :=
  ⟨fun o n => Plan.moving_keepsShape place {} o n, fun _ c hc => by
    cases List.mem_singleton.mp hc
    exact fun e => nomatch e⟩

theorem look_fromRest : look.FromRest :=
  ⟨fun o n => Plan.moving_fromRest place {} o n, fun _ c hc _ => by
    cases List.mem_singleton.mp hc
    exact rfl⟩

/-- **Every joint of every run under the plan is the picture at rest**: `Reel.at_joint` at the
consumer's plan. It is the consumer's `sample_end`, of a run. -/
theorem run_joint (ps : List (List Thing)) {k : Nat}
    (h : k ≤ (Reel.ofPictures Prod.fst look ps).rest.length) :
    (Reel.ofPictures Prod.fst look ps).at (1000 * k) =
      ((Reel.ofPictures Prod.fst look ps).picture k).map fun a => (a, Frame.rest) :=
  Reel.at_joint _ (by rw [Reel.ofPictures_plan]; exact look_settles)
    (by rw [Reel.ofPictures_plan]; exact look_proper)
    (by rw [Reel.ofPictures_plan]; exact look_keepsShapes) h

/-- **The step after starts each kept thing where the joint has it**: `Reel.joint_stands` at
the consumer's plan, for a run of three pictures or more whose next picture has distinct keys. -/
theorem run_stands (p0 p1 p2 : List Thing) (rest : List (List Thing)) (hd : Distinct Prod.fst p2)
    {o n : Thing} (hu : (o, n) ∈ (Whatwg.Svg.Scene.join Prod.fst p1 p2).update) :
    (((Reel.ofPictures Prod.fst look (p0 :: p1 :: p2 :: rest)).step 1).frame n 0).stand (place n) =
      place o :=
  Reel.joint_stands (Reel.ofPictures Prod.fst look (p0 :: p1 :: p2 :: rest)) look_settles
    look_proper look_keepsShapes look_fromRest (k := 0) rfl hd hu
    (fun c hc => by
      rw [Plan.mem_moving place {} hc]
      rfl)
    place {} (List.append_nil _).symm (fun _ h => nomatch h) List.nodup_nil

/-! ## The decision: a thing that is about to enter is not drawn at the joint -/

/-- A plan whose entrance starts in view: a new thing slides in from fifty to the left, whole. -/
def slide : Plan Thing :=
  ⟨Plan.moving place {}, fun _ => [(.shift ⟨-50, 0⟩ 0, {})], fun _ => [(.grow 1000 0, {})]⟩

/-- The run of the machine under that plan. -/
def slid : Reel Thing Nat := Reel.ofPictures Prod.fst slide pictures

-- The step from the second picture to the third, at its own first moment, draws the thing `3`,
-- which enters in it, fifty off its place and whole.
#guard ((slid.step 1).sample 0).map (fun x => (x.1.1, x.2.shift.x, x.2.size)) ==
  [(1, -20, 1000), (2, -20, 1000), (3, -50, 1000)]

-- The run at that joint draws the second picture at rest, and no thing `3`.
#guard slid.at 1000 == (page 1).map fun a => (a, Frame.rest)

-- One moment later the thing `3` is drawn, still fifty off its place.
#guard ((slid.at 1001).map fun x => (x.1.1, x.2.shift.x)) == [(1, -20), (2, -20), (3, -50)]

/-! ## Controls of the joint laws -/

-- A control of `Reel.joint_whole`, which asks that the plan is written from rest. A plan that
-- fades every kept thing in from nothing is not: the joint has the thing `1` whole, and the
-- step after starts it with no opacity.
#guard
  let fades : Plan Thing := ⟨fun _ _ => [(.fade 0 1000, {})], fun _ => [], fun _ => []⟩
  let r : Reel Thing Nat := Reel.ofPictures Prod.fst fades pictures
  (r.at 1000).map (fun x => (x.1.1, x.2.shown)) == [(1, 1000), (2, 1000)] &&
    ((r.step 1).frame (1, 20) 0).shown == 0

-- A control of `Reel.at_joint`, which asks that the plan settles. A new thing that grows to
-- half its size is not at rest at the joint.
#guard
  let half : Plan Thing := ⟨Plan.moving place {}, fun _ => [(.grow 0 500, {})], fun _ => []⟩
  let r : Reel Thing Nat := Reel.ofPictures Prod.fst half pictures
  (r.at 1000).map (fun x => (x.1.1, x.2.size)) == [(1, 1000), (2, 500)]

/-! ## A run that goes on, and a run with no waiting -/

-- `Reel.at_extend` on the machine: the run of the first three pictures, with the fourth added,
-- is the run of the four.
#guard
  let three : Reel Thing Nat := Reel.ofPictures Prod.fst look [page 0, page 1, page 2]
  (three.extend (page 3)).rest == run.rest && three.span == 2000 && run.span == 3000

-- `Reel.playtime`: a run in which a picture comes twice has a step in which nothing changes,
-- and that step takes no time. Three steps, two that move: two thousand, and a span of three.
#guard
  let r : Reel Thing Nat := Reel.ofPictures Prod.fst look [page 0, page 1, page 1, page 2]
  r.playtime == 2000 && r.span == 3000 && r.motions.map Motion.finish == [1000, 0, 1000]

end WhatwgTest.Svg.Reel
