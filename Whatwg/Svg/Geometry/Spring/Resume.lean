import Whatwg.Svg.Geometry.Spring.Laws
import Whatwg.Svg.Scene.Resume

/-!
# Whatwg.Svg.Geometry.Spring.Resume

Owner: a step that is interrupted and resumes with the speed its things have (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Resume.lean` resumes a step from where each thing is seen, and says that
nothing jumps. Each thing then starts its new change from standing (debt D134). This module
gives the timing of a resumed step from a spring, so that a thing on its way goes on at the
speed it has.

```
(Motion.ofJoin key (join key olds next)
  (p.springResume key place m t s pieces duration keep)).within
```

`m` is the step that is interrupted at the moment `t`, `olds` the things drawn then, `next` the
next picture, and `p` the plan of the step from `olds` to `next`, written as if every old thing
stood still. `s` is the spring that both steps take.

What is decided here, and why.

- **A piece** is `duration / pieces` per mille of the step: the duration of a resumed
  transition over the number of stops of its easing. The speed of a thing is read over one
  piece, and the numbers of the spring are for one piece, so the step before must have been
  eased by the same spring with pieces of the same length. With lean4-effect4's move, 800 per
  mille and twenty pieces, a piece is 40 per mille. The two steps are taken to be of one length.
- **What is read.** A thing is seen at its place and the shift of its frame at the cut
  (`Motion.frame m key t`), and the step before would have put it at the shift of its frame one
  piece later. Its next offset is that place less the new one, and the first piece of a fresh
  spring over the way that its place moved (`Spring.moved_next`).
- **No delay.** A resumed transition starts at the cut. A delay would stop the thing first.
- **Which coordinate.** A shift has two coordinates and one easing, so the thing goes straight
  from where it is seen to its new place. `Spring.along` takes its offset and its next offset
  along that way: the scalar products with the way, which need no square root. For a thing that
  is seen level with its new place, as every box of a rank is, that is the offset and the next
  offset themselves (`resumeEase_axis`). Otherwise the part of its speed across the way is
  dropped at the cut: the thing turns onto the straight way at once.
- **A thing that stands on its new place**, or whose run would not move it, takes the spring's
  own easing: a change of no way has nothing for an easing to share out.
- **A thing that is not calm.** `keep := true` keeps its speed (`Spring.onward`): its easing is
  proper and may leave the range from `0` to `1000`. `keep := false` keeps the speed where the
  easing stays in range, and starts the thing from rest where it would not (`Spring.calmly`):
  that easing always passes `Easing.bounded`. For a critical spring a calm thing keeps its speed
  either way (`critical_calmly_of_calm`).

What the laws say.

- A thing that stood still takes the spring's own easing, whichever way is chosen
  (`resumeEase_rest`): a step that is not interrupted is eased as the spring eases it.
- **The resumed step ends on the next picture** (`Motion.springResume_end`, by
  `Motion.resume_end`), where the plan settles and is proper and the spring's response has moved
  by its last piece.
- **At the cut nothing moves** (`Motion.springResume_nothing_moves`, by
  `Motion.nothing_moves_from`): a kept thing that the plan moves stands where it stood.
- **A resumed track follows its spring.** At the moment of each piece the transition reads the
  stop of that piece (`resumed_transition_at`). So the place that the frame of a step shows, for
  a thing on such a track, is within the bound of `mix_stop_near` of the place of the run
  (`Motion.spring_track_near`).

What `Whatwg/Svg/Scene/Resume.lean` asks that a spring cannot give as it is (findings).

- `settle` of `Plan.resume` times only what the plan does not change. A thing that the plan
  moves takes the plan's own transition, started where the thing is seen. So the speed cannot be
  given through `settle` alone: `Plan.moveBy` replaces the transition of each change of place
  of the plan, thing by thing, and `Plan.springResume` does both.
- `settle n` is one transition for every property of the thing `n` that the plan does not
  change. A thing seen at part of its size or of its opacity takes for those the easing made for
  its place. With `keep := true` that easing may leave the range, and a size or an opacity then
  does. A caller whose things can be seen so takes `keep := false`.
- `Motion.together` of `Whatwg/Svg/Scene/Together.lean` asks one transition for all kept things
  (`Plan.MovesBy`). Things that keep their speeds have one easing each, so that law does not
  reach a step resumed with speed. `Spring.critical_interrupted_gap` says what it would, of the
  exact places of a critical spring, and no law here brings it to the frames of a step.
- The speed is read from two whole-number frames, so it is known to a unit a piece.

What this module does not claim. That the step before was eased by the spring `s`: the next
offset is then the spring's own, and otherwise it is a speed that the thing happens to have. No
law says that the track of `Motion.spring_track_near` is in the resumed step: it is, where the
plan moves the thing, and the composition is left to the caller's own step.

Every law here depends on `propext`, `Quot.sound` and `Classical.choice` at most.
-/

namespace Whatwg.Svg.Scene

open Whatwg.Svg.Value

variable {α κ : Type}

namespace Spring

/-! ## The easing of a thing that goes on -/

/-- **The easing of a thing that keeps its speed.** The resumed easing, where the thing is off
its target and its run moves it. Otherwise the spring's own easing: the thing stands on its
target, or its run has not left its place by the last piece. -/
def onward (s : Spring) (pieces : Nat) (x0 x1 : Rat) : Easing :=
  if x0 ≠ 0 ∧ s.run x0 x1 pieces ≠ x0 then s.resumed x0 x1 pieces else s.easing pieces

/-- **The easing of a thing that keeps its speed where that stays in range.** Where the easing
of `onward` passes `Easing.bounded` it is that easing. Where it does not, the thing starts from
rest, with the spring's own easing. -/
def calmly (s : Spring) (pieces : Nat) (x0 x1 : Rat) : Easing :=
  if (s.onward pieces x0 x1).bounded = true then s.onward pieces x0 x1 else s.easing pieces

/-- **The two offsets of a thing along its way.** The thing is seen at `seen` and would be at
`next` one piece later. Its place is now `target`, `moved` further than it was. The first number
is its offset along the straight way to the target and the second its next offset along it,
each times the length of the way: the easing takes the share of the one in the other. -/
def along (s : Spring) (seen next target moved : IVec) : Rat × Rat :=
  let ax : Rat := (seen.x : Rat) - (target.x : Rat)
  let ay : Rat := (seen.y : Rat) - (target.y : Rat)
  let bx : Rat := (next.x : Rat) - (target.x : Rat) + (moved.x : Rat) * (1 - s.rest)
  let by' : Rat := (next.y : Rat) - (target.y : Rat) + (moved.y : Rat) * (1 - s.rest)
  (ax * ax + ay * ay, ax * bx + ay * by')

/-- **The easing of a kept thing of a resumed step.** With `keep` the thing keeps its speed
whatever comes of it. Without, it keeps it where its easing stays in range. -/
def resumeEase (s : Spring) (pieces : Nat) (keep : Bool) (seen next target moved : IVec) :
    Easing :=
  match keep with
  | true =>
    s.onward pieces (s.along seen next target moved).1 (s.along seen next target moved).2
  | false =>
    s.calmly pieces (s.along seen next target moved).1 (s.along seen next target moved).2

/-- Where the thing is off its target and its run moves it, `onward` is the resumed easing. -/
theorem onward_of_moving (s : Spring) (pieces : Nat) {x0 x1 : Rat} (h0 : x0 ≠ 0)
    (h : s.run x0 x1 pieces ≠ x0) : s.onward pieces x0 x1 = s.resumed x0 x1 pieces :=
  if_pos ⟨h0, h⟩

/-- **A thing that keeps its speed still ends on its target**: the easing of `onward` is
proper, where the response of the spring has moved by its last piece. -/
theorem onward_proper (s : Spring) (pieces : Nat) (x0 x1 : Rat) (h : s.response pieces ≠ 1) :
    (s.onward pieces x0 x1).Proper := by
  by_cases hc : x0 ≠ 0 ∧ s.run x0 x1 pieces ≠ x0
  · rw [onward, if_pos hc]
    exact s.resumed_proper x0 x1 pieces hc.2
  · rw [onward, if_neg hc]
    exact s.easing_proper pieces h

/-- The easing of `calmly` is proper, on the same term. -/
theorem calmly_proper (s : Spring) (pieces : Nat) (x0 x1 : Rat) (h : s.response pieces ≠ 1) :
    (s.calmly pieces x0 x1).Proper := by
  by_cases hc : (s.onward pieces x0 x1).bounded = true
  · rw [calmly, if_pos hc]
    exact s.onward_proper pieces x0 x1 h
  · rw [calmly, if_neg hc]
    exact s.easing_proper pieces h

/-- **The easing of `calmly` stays in range**, where the spring's own easing does. -/
theorem calmly_bounded (s : Spring) (pieces : Nat) (x0 x1 : Rat)
    (h : (s.easing pieces).bounded = true) : (s.calmly pieces x0 x1).bounded = true := by
  by_cases hc : (s.onward pieces x0 x1).bounded = true
  · rw [calmly, if_pos hc]
    exact hc
  · rw [calmly, if_neg hc]
    exact h

/-- `onward` is the same for offsets that are `l` times as far, where `l` is not `0`. -/
theorem onward_scale (s : Spring) (pieces : Nat) (l x0 x1 : Rat) (hl : l ≠ 0) :
    s.onward pieces (l * x0) (l * x1) = s.onward pieces x0 x1 := by
  have e : (l * x0 ≠ 0 ∧ s.run (l * x0) (l * x1) pieces ≠ l * x0) ↔
      (x0 ≠ 0 ∧ s.run x0 x1 pieces ≠ x0) := by
    rw [run_scale]
    generalize s.run x0 x1 pieces = y
    constructor
    · rintro ⟨a, b⟩
      exact ⟨fun h => a (by rw [h]; grind), fun h => b (by rw [h])⟩
    · rintro ⟨a, b⟩
      exact ⟨fun h => a (Decimal.rat_mul_right_cancel hl (by grind)),
        fun h => b (Decimal.rat_mul_right_cancel hl (by grind))⟩
  by_cases hc : x0 ≠ 0 ∧ s.run x0 x1 pieces ≠ x0
  · rw [onward, if_pos (e.mpr hc), onward, if_pos hc]
    exact s.resumed_scale l x0 x1 pieces hl
  · rw [onward, if_neg (fun h => hc (e.mp h)), onward, if_neg hc]

/-- `calmly` is the same for offsets that are `l` times as far, where `l` is not `0`. -/
theorem calmly_scale (s : Spring) (pieces : Nat) (l x0 x1 : Rat) (hl : l ≠ 0) :
    s.calmly pieces (l * x0) (l * x1) = s.calmly pieces x0 x1 := by
  rw [calmly, calmly, onward_scale s pieces l x0 x1 hl]

/-- **A thing at rest takes the spring's own easing.** Its next offset is its offset times the
rest of the spring, and `onward` is then the easing of the spring let go at rest. -/
theorem onward_rest (s : Spring) (pieces : Nat) (d : Rat) :
    s.onward pieces d (d * s.rest) = s.easing pieces := by
  by_cases hc : d ≠ 0 ∧ s.run d (d * s.rest) pieces ≠ d
  · have e := s.resumed_scale d 1 s.rest pieces hc.1
    rw [Rat.mul_one] at e
    rw [onward, if_pos hc]
    exact e
  · rw [onward, if_neg hc]

/-- A thing at rest takes the spring's own easing under `calmly` too. -/
theorem calmly_rest (s : Spring) (pieces : Nat) (d : Rat) :
    s.calmly pieces d (d * s.rest) = s.easing pieces := by
  by_cases hc : (s.onward pieces d (d * s.rest)).bounded = true
  · rw [calmly, if_pos hc]
    exact s.onward_rest pieces d
  · rw [calmly, if_neg hc]

/-- A calm thing on a critical spring that is moving at all has left its place by every later
piece, on either side of its target. -/
theorem critical_moved_calm (r c : Rat) (hr : 0 ≤ r) {x0 x1 : Rat} (h : Calm r x0 x1)
    (hne : x1 ≠ x0) {n : Nat} (hn : 0 < n) : (critical r c).run x0 x1 n ≠ x0 := by
  rcases h with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · exact critical_moved r c hr x0 x1 a b d hne hn
  · have m := critical_moved r c hr (-x0) (-x1) (by grind) (by grind) (by grind) (by grind) hn
    rw [run_neg] at m
    exact fun e => m (by rw [e])

/-- **A calm thing on a critical spring keeps its speed either way.** Where the thing is calm
and is moving at all, `calmly` is the resumed easing: nothing is given up to stay in range. -/
theorem critical_calmly_of_calm (r c : Rat) (hr : 0 ≤ r) {x0 x1 : Rat} (h : Calm r x0 x1)
    (hne : x1 ≠ x0) {n : Nat} (hn : 0 < n) :
    (critical r c).calmly n x0 x1 = (critical r c).resumed x0 x1 n := by
  have h0 : x0 ≠ 0 := by
    intro e
    rcases h with ⟨_, b, d⟩ | ⟨_, b, d⟩
    · exact hne (by rw [e] at b d ⊢; grind)
    · exact hne (by rw [e] at b d ⊢; grind)
  have e := onward_of_moving (critical r c) n h0 (critical_moved_calm r c hr h hne hn)
  rw [calmly, e, if_pos (critical_resumed_bounded r c hr h n)]

/-! ## Along the way -/

/-- A thing that stood still has, along its way, a next offset that is its offset times the
rest of the spring. -/
theorem along_rest (s : Spring) (seen moved : IVec) :
    (s.along seen seen (seen + moved) moved).2 =
      (s.along seen seen (seen + moved) moved).1 * s.rest := by
  simp only [along, IVec.add_x, IVec.add_y, Rat.intCast_add]
  grind

/-- **A thing that stood still takes the spring's own easing**, whichever way is chosen. So
where nothing was moving at the cut, the resumed step is eased as the spring eases a step. -/
theorem resumeEase_rest (s : Spring) (pieces : Nat) (keep : Bool) (seen moved : IVec) :
    s.resumeEase pieces keep seen seen (seen + moved) moved = s.easing pieces := by
  cases keep
  · show s.calmly pieces _ _ = _
    rw [along_rest]
    exact s.calmly_rest pieces _
  · show s.onward pieces _ _ = _
    rw [along_rest]
    exact s.onward_rest pieces _

/-- For a thing that is seen level with its new place, the two offsets along the way are its
offset and its next offset along the first axis, each times the offset. -/
theorem along_axis (s : Spring) (seen next target moved : IVec) (hy : seen.y = target.y) :
    s.along seen next target moved =
      (((seen.x : Rat) - (target.x : Rat)) * ((seen.x : Rat) - (target.x : Rat)),
        ((seen.x : Rat) - (target.x : Rat)) *
          ((next.x : Rat) - (target.x : Rat) + (moved.x : Rat) * (1 - s.rest))) := by
  have e : (seen.y : Rat) - (target.y : Rat) = 0 := by
    rw [hy]
    grind
  show ((_ : Rat) * _ + ((seen.y : Rat) - (target.y : Rat)) * _,
    (_ : Rat) * _ + ((seen.y : Rat) - (target.y : Rat)) * _) = _
  rw [e, Rat.zero_mul, Rat.add_zero, Rat.zero_mul, Rat.add_zero]

/-- **A thing of a rank takes its offsets as they are.** Where the thing is seen level with
its new place and off it, the easing of a resumed step is that of its offset and its next
offset along the first axis: nothing of its speed is dropped. -/
theorem resumeEase_axis (s : Spring) (pieces : Nat) (keep : Bool) (seen next target moved : IVec)
    (hy : seen.y = target.y) (hx : seen.x ≠ target.x) :
    s.resumeEase pieces keep seen next target moved =
      match keep with
      | true => s.onward pieces ((seen.x : Rat) - (target.x : Rat))
          ((next.x : Rat) - (target.x : Rat) + (moved.x : Rat) * (1 - s.rest))
      | false => s.calmly pieces ((seen.x : Rat) - (target.x : Rat))
          ((next.x : Rat) - (target.x : Rat) + (moved.x : Rat) * (1 - s.rest)) := by
  have hl : (seen.x : Rat) - (target.x : Rat) ≠ 0 := by
    intro e
    have e' : (seen.x : Rat) = (target.x : Rat) := by grind
    have a : seen.x ≤ target.x := Rat.intCast_le_intCast.mp (by rw [e']; exact Rat.le_refl)
    have b : target.x ≤ seen.x := Rat.intCast_le_intCast.mp (by rw [e']; exact Rat.le_refl)
    exact hx (by omega)
  cases keep
  · show s.calmly pieces _ _ = s.calmly pieces _ _
    rw [along_axis s seen next target moved hy]
    exact s.calmly_scale pieces _ _ _ hl
  · show s.onward pieces _ _ = s.onward pieces _ _
    rw [along_axis s seen next target moved hy]
    exact s.onward_scale pieces _ _ _ hl

/-- The easing of a kept thing of a resumed step is proper, where the response of the spring
has moved by its last piece. -/
theorem resumeEase_proper (s : Spring) (pieces : Nat) (keep : Bool) (seen next target moved : IVec)
    (h : s.response pieces ≠ 1) : (s.resumeEase pieces keep seen next target moved).Proper := by
  cases keep
  · exact s.calmly_proper pieces _ _ h
  · exact s.onward_proper pieces _ _ h

/-- **Without `keep` the easing of a kept thing stays in range**, where the spring's own
easing does. -/
theorem resumeEase_bounded (s : Spring) (pieces : Nat) (seen next target moved : IVec)
    (h : (s.easing pieces).bounded = true) :
    (s.resumeEase pieces false seen next target moved).bounded = true :=
  s.calmly_bounded pieces _ _ h

/-! ## A resumed transition at the moments of its pieces -/

/-- At the share of a piece a resumed easing reads the stop of that piece. -/
theorem resumed_of_stop (s : Spring) (x0 x1 : Rat) (n i num den : Nat) (hd : 0 < den)
    (hi : i ≤ n) (hp : num * n = den * i) : (s.resumed x0 x1 n).of num den = s.stop x0 x1 n i := by
  have hl : ((List.range (n + 1)).map (s.stop x0 x1 n)).length = n + 1 := by
    rw [List.length_map, List.length_range]
  rw [resumed_stops]
  show Easing.stopsOf ((List.range (n + 1)).map (s.stop x0 x1 n)) num den = s.stop x0 x1 n i
  rw [Easing.stopsOf_stop _ i num den hd (by rw [hl]; omega)
      (by rw [hl, Nat.add_sub_cancel]; exact hp),
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- **A resumed transition reads the stop of each piece at the moment of that piece.** The
transition has no delay, and the moment `u` is the piece `i` of `n` of its duration. -/
theorem resumed_transition_at (s : Spring) (x0 x1 : Rat) (n i u duration : Nat)
    (hd : 0 < duration) (hi : i ≤ n) (hu : u * n = duration * i)
    (hmoved : s.run x0 x1 n ≠ x0) :
    ({ delay := 0, duration := duration, ease := s.resumed x0 x1 n } : Transition).at u =
      s.stop x0 x1 n i := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun e => hmoved (by rw [e]; rfl)
  have hle : u ≤ duration :=
    Nat.le_of_mul_le_mul_right (hu ▸ Nat.mul_le_mul_left duration hi) hn
  have key : ({ delay := 0, duration := duration, ease := s.resumed x0 x1 n } : Transition).at u =
      (s.resumed x0 x1 n).of u duration := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0, Transition.at_before _ 0 (Nat.le_refl 0)
        (show 0 < 0 + duration by omega)]
      exact (Easing.of_zero _ _).symm
    · rcases Nat.lt_or_ge u duration with h1 | h1
      · exact Transition.at_between _ u h0 (show u < 0 + duration by omega)
      · have e : u = duration := Nat.le_antisymm hle h1
        rw [e, Transition.at_done _ duration (show 0 + duration ≤ duration by omega)]
        exact (Easing.of_self _ _ hd).symm
  rw [key]
  exact s.resumed_of_stop x0 x1 n i u duration hd hi hu

end Spring

/-! ## The timing of a resumed step -/

/-- **The transition of a kept thing in a step resumed with a spring.** `m` is the step that is
interrupted at the moment `t`. The thing `o` is seen at its place and the shift of its frame
then, and would have been at the shift of its frame one piece later; its new place is that of
`n`. The transition has no delay, and a piece is `duration / pieces` per mille of the step. -/
def Motion.springMove [BEq κ] (m : Motion κ) (t : Nat) (s : Spring) (pieces duration : Nat)
    (keep : Bool) (key : α → κ) (place : α → IVec) (o n : α) : Transition :=
  { delay := 0
    duration := duration
    ease := s.resumeEase pieces keep (place o + (m.frame (key o) t).shift)
      (place o + (m.frame (key o) (t + duration / pieces)).shift) (place n) (place n - place o) }

/-- **The plan with the transition of every change of place of a kept thing replaced**, thing
by thing. A plan gives its kept things one transition, and a thing that keeps its speed needs
its own. -/
def Plan.moveBy (p : Plan α) (move : α → α → Transition) : Plan α where
  kept := fun o n => (p.kept o n).map fun c =>
    if c.1.property = .place then (c.1, move o n) else c
  enter := p.enter
  leave := p.leave

/-- **A plan resumed with a spring.** Each kept thing that the plan moves takes the transition
of `Motion.springMove`, started where the thing is seen. Each kept thing that the plan does not
move and that is seen off its place goes to its place by that transition too. What else the plan
says stands, and a thing that leaves is resumed as `Plan.resume` resumes it. -/
def Plan.springResume [BEq κ] (key : α → κ) (place : α → IVec) (m : Motion κ) (t : Nat)
    (s : Spring) (pieces duration : Nat) (keep : Bool) (p : Plan α)
    (shape : α → Option (List ICubic) := fun _ => none) : Plan α :=
  (p.moveBy (m.springMove t s pieces duration keep key place)).resumeFrom key m t
    (fun n => m.springMove t s pieces duration keep key place n n) shape

namespace Motion

/-- The easing of `springMove` is proper, where the response of the spring has moved by its
last piece. -/
theorem springMove_proper [BEq κ] (m : Motion κ) (t : Nat) (s : Spring) (pieces duration : Nat)
    (keep : Bool) (key : α → κ) (place : α → IVec) (o n : α) (h : s.response pieces ≠ 1) :
    (m.springMove t s pieces duration keep key place o n).ease.Proper :=
  s.resumeEase_proper pieces keep _ _ _ _ h

/-- **The transition of `springMove` reads `0` at the cut**, where it has a duration: it is the
premise of the laws that nothing jumps. -/
theorem springMove_at_zero [BEq κ] (m : Motion κ) (t : Nat) (s : Spring) (pieces duration : Nat)
    (keep : Bool) (key : α → κ) (place : α → IVec) (o n : α) (h : s.response pieces ≠ 1)
    (hd : 0 < duration) : (m.springMove t s pieces duration keep key place o n).at 0 = 0 :=
  Transition.at_zero _ (springMove_proper m t s pieces duration keep key place o n h)
    (show 0 < 0 + duration by omega)

end Motion

namespace Plan

/-- The change of a retimed answer is the change. -/
private theorem retimed_change (mv : Transition) (c : Change × Transition) :
    (if c.1.property = .place then (c.1, mv) else c).1 = c.1 := by
  by_cases h : c.1.property = .place
  · rw [if_pos h]
  · rw [if_neg h]

/-- A plan with its moves retimed settles where the plan does. -/
theorem moveBy_settles {p : Plan α} (move : α → α → Transition) (hp : p.Settles) :
    (p.moveBy move).Settles := by
  refine ⟨fun o n c hc => ?_, hp.2⟩
  obtain ⟨c0, h0, rfl⟩ := List.mem_map.mp hc
  rw [retimed_change]
  exact hp.1 o n c0 h0

/-- A plan with its moves retimed is proper where the plan is and every new transition has a
proper easing. -/
theorem moveBy_proper {p : Plan α} {move : α → α → Transition} (hp : p.Proper)
    (hm : ∀ o n, (move o n).ease.Proper) : (p.moveBy move).Proper := by
  refine ⟨fun o n c hc => ?_, hp.2.1, hp.2.2⟩
  obtain ⟨c0, h0, rfl⟩ := List.mem_map.mp hc
  by_cases h : c0.1.property = .place
  · rw [if_pos h]
    exact hm o n
  · rw [if_neg h]
    exact hp.1 o n c0 h0

/-- A plan with its moves retimed has one change for each property where the plan has. -/
theorem moveBy_single {p : Plan α} (move : α → α → Transition) (hp : p.Single) :
    (p.moveBy move).Single := by
  refine ⟨fun o n => ?_, hp.2.1, hp.2.2⟩
  have e : ((p.moveBy move).kept o n).map (fun c => c.1.property) =
      (p.kept o n).map fun c => c.1.property := by
    show ((p.kept o n).map _).map _ = _
    rw [List.map_map]
    exact List.map_congr_left fun c _ => congrArg Change.property (retimed_change (move o n) c)
  rw [e]
  exact hp.1 o n

/-- **What retiming does to a plan that moves a thing**: the one shift of `Plan.moving` takes
the new transition, and what is not of the place stands. -/
theorem moveBy_moving (place : α → IVec) (move0 mv : Transition) (o n : α)
    {more : List (Change × Transition)} (hm : ∀ c ∈ more, c.1.property ≠ .place) :
    (Plan.moving place move0 o n ++ more).map
        (fun c => if c.1.property = .place then (c.1, mv) else c) =
      Plan.moving place mv o n ++ more := by
  have e1 : (Plan.moving place move0 o n).map
      (fun c => if c.1.property = .place then (c.1, mv) else c) = Plan.moving place mv o n := by
    rcases Decidable.em (place o = place n) with h | h
    · rw [(Plan.moving_nil place move0 o n).mpr h, (Plan.moving_nil place mv o n).mpr h]
      rfl
    · rw [Plan.moving_of_ne place move0 h, Plan.moving_of_ne place mv h]
      rfl
  have e2 : more.map (fun c => if c.1.property = .place then (c.1, mv) else c) = more :=
    (List.map_congr_left fun c hc => if_neg (hm c hc)).trans (List.map_id more)
  rw [List.map_append, e1, e2]

end Plan

namespace Motion

/-- **A step resumed with a spring ends on the next picture.** With a plan that settles and is
proper, and a spring whose response has moved by its last piece, each thing of the next list is
drawn as the still picture has it from the step's end on. -/
theorem springResume_end [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec) (m : Motion κ)
    (t : Nat) (s : Spring) (pieces duration : Nat) (keep : Bool) (olds next : List α)
    (p : Plan α) (shape : α → Option (List ICubic)) (hs : p.Settles) (hp : p.Proper)
    (h : s.response pieces ≠ 1) {n : α} (hn : n ∈ next) {u : Nat} (hu : 1000 ≤ u) :
    ((ofJoin key (join key olds next)
      (p.springResume key place m t s pieces duration keep shape)).within.frame (key n) u).AtRest :=
  resume_end key olds next (p.moveBy (m.springMove t s pieces duration keep key place))
    (fun a => m.frame (key a) t) shape (Plan.moveBy_settles _ hs)
    (Plan.moveBy_proper hp fun o n => springMove_proper m t s pieces duration keep key place o n h)
    (fun n => springMove_proper m t s pieces duration keep key place n n h) hn hu

/-- **At the cut nothing moves, in a step resumed with a spring.** A kept thing that the plan
moves by `Plan.moving` stands, at the first moment of the resumed step, where it stood in the
step before at the moment of the cut. The plan may give the thing more changes that are not of
its place, each by a transition that reads `0` at the moment `0`. -/
theorem springResume_nothing_moves [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec)
    (m : Motion κ) (t : Nat) (s : Spring) (pieces duration : Nat) (keep : Bool)
    (olds next : List α) (p : Plan α) (shape : α → Option (List ICubic))
    (hd : Distinct key next) {o n : α} (hu : (o, n) ∈ (join key olds next).update)
    (move : Transition) {more : List (Change × Transition)}
    (hkept : p.kept o n = Plan.moving place move o n ++ more)
    (hm : ∀ c ∈ more, c.1.property ≠ .place) (hdm : (more.map fun c => c.1.property).Nodup)
    (hmore : ∀ c ∈ more, c.2.at 0 = 0) (h : s.response pieces ≠ 1) (hdur : 0 < duration) :
    place n + ((ofJoin key (join key olds next)
        (p.springResume key place m t s pieces duration keep shape)).within.frame (key n) 0).shift =
      place o + (m.frame (key n) t).shift := by
  have hk : (p.moveBy (m.springMove t s pieces duration keep key place)).kept o n =
      Plan.moving place (m.springMove t s pieces duration keep key place o n) o n ++ more := by
    show (p.kept o n).map _ = _
    rw [hkept]
    exact Plan.moveBy_moving place move _ o n hm
  refine nothing_moves_from key m t olds next
    (p.moveBy (m.springMove t s pieces duration keep key place))
    (fun n => m.springMove t s pieces duration keep key place n n) shape hd hu ?_
    (springMove_at_zero m t s pieces duration keep key place n n h hdur) place
    (m.springMove t s pieces duration keep key place o n) hk hm hdm
  intro c hc
  rw [hk] at hc
  rcases List.mem_append.mp hc with h1 | h2
  · rw [Plan.mem_moving place _ h1]
    exact springMove_at_zero m t s pieces duration keep key place o n h hdur
  · exact hmore c h2

/-- **How near a resumed track is to its spring.** A motion has one track for each property of
a thing, and the thing `k` has the track of a shift along the first axis from where it is seen
to its place, by a resumed transition with no delay. The thing is seen right of its place, its
run has not passed the place at the last piece, and the share of the piece `i` is from `0` to
`1`. Then at the moment of the piece `i` the place that the frame shows is less than one unit,
the last offset and a two-thousandth of the first below the place of the run, and no more than
a two-thousandth of the first above it. -/
theorem spring_track_near [BEq κ] [LawfulBEq κ] {mo : Motion κ} (hS : mo.Single) {k : κ}
    (s : Spring) (seen target : Int) (x1 : Rat) (n i u duration : Nat)
    (htr : (⟨k, .shift ⟨seen - target, 0⟩ 0,
      { delay := 0, duration := duration,
        ease := s.resumed ((seen : Rat) - (target : Rat)) x1 n }⟩ : Track κ) ∈ mo)
    (hd : 0 < duration) (hi : i ≤ n) (hu : u * n = duration * i)
    (h : s.run ((seen : Rat) - (target : Rat)) x1 n ≠ (seen : Rat) - (target : Rat))
    (hx : 0 ≤ (seen : Rat) - (target : Rat))
    (hn : 0 ≤ s.run ((seen : Rat) - (target : Rat)) x1 n)
    (h0 : 0 ≤ s.share ((seen : Rat) - (target : Rat)) x1 n i)
    (h1 : s.share ((seen : Rat) - (target : Rat)) x1 n i ≤ 1) :
    (target : Rat) + s.run ((seen : Rat) - (target : Rat)) x1 i -
          s.run ((seen : Rat) - (target : Rat)) x1 n - ((seen : Rat) - (target : Rat)) / 2000 - 1 <
        ((target + (mo.frame k u).shift.x : Int) : Rat) ∧
      ((target + (mo.frame k u).shift.x : Int) : Rat) ≤
        (target : Rat) + s.run ((seen : Rat) - (target : Rat)) x1 i +
          ((seen : Rat) - (target : Rat)) / 2000 := by
  have e : target + (mo.frame k u).shift.x =
      mix seen target (s.stop ((seen : Rat) - (target : Rat)) x1 n i) := by
    rw [frame_shift hS htr u, s.resumed_transition_at _ x1 n i u duration hd hi hu h]
    show target + mix (seen - target) 0 _ = mix seen target _
    rw [← mix_add]
    exact congrArg (fun a => mix a target _) (by omega)
  rw [e]
  exact s.mix_stop_near seen target x1 n i h hx hn h0 h1

end Motion

end Whatwg.Svg.Scene
