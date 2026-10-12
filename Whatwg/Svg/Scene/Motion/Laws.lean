import Whatwg.Svg.Scene.Motion
import Whatwg.Svg.Scene.Join.Laws

/-!
# Whatwg.Svg.Scene.Motion.Laws

Owner: the laws of motion as data (slice S12 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-62).

A reader of tracks draws the moments between one picture and the next. These laws say where
that reading starts and where it ends, so that the last moment of a step is the next picture.

- Mixing. `mix u v e` is `u` at `0` and `v` at `1000`, and a value mixed with itself stays
  (`mix_start`, `mix_end`, `mix_self`).
- Easings. A cubic reads `0` at the start and `1000` at the end, whatever its two heights
  (`Easing.cubicAt_zero`, `Easing.cubicAt_end`), so every cubic is proper
  (`Easing.proper_cubic`). Stops read the value of a stop at that stop (`Easing.stopsAt_stop`),
  as `linear()` of CSS does: the first value at `0` (`Easing.stopsAt_zero`) and the last at
  `1000` (`Easing.stopsAt_end`). Stops that begin with `0` and end with `1000` are proper
  (`Easing.proper_stops`), and so are the four named easings.
- Transitions. Once its duration is over, a transition reads the end of its easing
  (`Transition.at_done`), which is `1000` where the easing is proper
  (`Transition.at_done_proper`). Until its delay is over it reads the start
  (`Transition.at_before`). A transition held inside a step ends by the step's end
  (`Transition.within_end`), keeps its easing (`Transition.within_ease`,
  `Transition.after_ease`), and reads the end of its easing at the step's end
  (`Transition.within_at_end`, `Transition.after_at_end`).
- Changes and tracks. A change is its start at `0` and its end at `1000` (`Change.at_start`,
  `Change.at_end`). **The end law of a track**: a track that is over stands at the end of its
  change (`Track.at_done`), and it is at rest there where it settles (`Track.atRest_of_done`).
- Motions. When every track is over, the poses are the ends of the changes
  (`Motion.poses_done`). A motion held inside a step is over at the step's end
  (`Motion.within_done`), and at rest there where its tracks settle (`Motion.within_atRest`).
- The motion of a join. Every arriving track settles (`Motion.arrive_settles`). There is one
  arriving track for each new thing (`Motion.length_arrive`), with the key of a new thing
  (`Motion.mem_arrive_key`). A departing track has the key of an old thing that no new thing
  has (`Motion.mem_depart_key`). **The end law of a step** (`Motion.arrive_end`): with proper
  easings, every arriving thing is at rest at the step's end.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-! ## Lists -/

/-- Inside a list, the value read at a place does not depend on the value given for a missing
place. -/
theorem getD_of_lt {α : Type} : ∀ (l : List α) (i : Nat) (d e : α), i < l.length →
    l.getD i d = l.getD i e
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _, _ => rfl
  | _ :: rest, i + 1, d, e, h => getD_of_lt rest i d e (Nat.lt_of_succ_lt_succ h)

/-- The value at the last place of a list is its last value. -/
theorem getD_last {α : Type} (l : List α) (d : α) :
    l.getD (l.length - 1) (l.getLast?.getD d) = l.getLast?.getD d := by
  rw [List.getLast?_eq_getElem?]
  show (l[l.length - 1]?).getD ((l[l.length - 1]?).getD d) = (l[l.length - 1]?).getD d
  cases l[l.length - 1]? with
  | none => rfl
  | some _ => rfl

/-! ## Mixing -/

/-- At the end of the way the mixed value is the second one. -/
theorem mix_end (u v : Int) : mix u v 1000 = v := by
  simp only [mix, Int.sub_self, Int.mul_zero, Int.zero_ediv, Int.add_zero]

/-- At the start of the way the mixed value is the first one. -/
theorem mix_start (u v : Int) : mix u v 0 = u := by
  show v + (u - v) * (1000 - 0) / 1000 = u
  omega

/-- A value mixed with itself is that value, at every progress. -/
theorem mix_self (u e : Int) : mix u u e = u := by
  simp only [mix, Int.sub_self, Int.zero_mul, Int.zero_ediv, Int.add_zero]

/-! ## Easing -/

namespace Easing

/-- A cubic starts at `0`, whatever its heights. -/
theorem cubicAt_zero (y1 y2 : Int) : cubicAt y1 y2 0 = 0 := by
  have h2 : (0 : Int) ^ 2 = 0 := rfl
  have h3 : (0 : Int) ^ 3 = 0 := rfl
  show (3 * y1 * 0 * (1000 - 0) ^ 2 + 3 * y2 * 0 ^ 2 * (1000 - 0) + 1000 * 0 ^ 3) / 1000000000 =
    (0 : Int)
  simp only [h2, h3, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_ediv]

/-- A cubic ends at `1000`, whatever its heights. -/
theorem cubicAt_end (y1 y2 : Int) : cubicAt y1 y2 1000 = 1000 := by
  have h2 : (0 : Int) ^ 2 = 0 := rfl
  show (3 * y1 * 1000 * (1000 - 1000) ^ 2 + 3 * y2 * 1000 ^ 2 * (1000 - 1000) +
    1000 * 1000 ^ 3) / 1000000000 = (1000 : Int)
  simp only [Int.sub_self, h2, Int.mul_zero, Int.zero_add]
  decide

/-- Every cubic is proper: it starts at `0` and ends at `1000`. -/
theorem proper_cubic (y1 y2 : Int) : (cubic y1 y2).Proper :=
  ⟨cubicAt_zero y1 y2, cubicAt_end y1 y2⟩

/-- Where the progress `p` falls on the stop `i`, the reading is the value of that stop, and
the last value where `i` is past the stops. -/
theorem stopsAt_on (values : List Int) (i p : Nat) (hp : p * (values.length - 1) = 1000 * i) :
    stopsAt values p = values.getD i (values.getLast?.getD 0) := by
  have hi : p * (values.length - 1) / 1000 = i := by
    rw [hp]
    exact Nat.mul_div_cancel_left i (by decide)
  have hz : ((p * (values.length - 1) - 1000 * i : Nat) : Int) = 0 :=
    congrArg (fun n : Nat => (n : Int)) (Nat.sub_eq_zero_of_le (Nat.le_of_eq hp))
  show values.getD (p * (values.length - 1) / 1000) (values.getLast?.getD 0) +
    (values.getD (p * (values.length - 1) / 1000 + 1) (values.getLast?.getD 0) -
      values.getD (p * (values.length - 1) / 1000) (values.getLast?.getD 0)) *
      ((p * (values.length - 1) - 1000 * (p * (values.length - 1) / 1000) : Nat) : Int) / 1000 =
    values.getD i (values.getLast?.getD 0)
  rw [hi, hz, Int.mul_zero, Int.zero_ediv, Int.add_zero]

/-- **At a stop the reading is the stop's value.** The stop `i` of `values` stands at the
progress `p` with `p * (values.length - 1) = 1000 * i`. -/
theorem stopsAt_stop (values : List Int) (i p : Nat) (hi : i < values.length)
    (hp : p * (values.length - 1) = 1000 * i) : stopsAt values p = values.getD i 0 :=
  (stopsAt_on values i p hp).trans (getD_of_lt values i _ 0 hi)

/-- At the start the reading is the first value. -/
theorem stopsAt_zero (v : Int) (rest : List Int) : stopsAt (v :: rest) 0 = v :=
  stopsAt_stop (v :: rest) 0 0 (Nat.succ_pos _) (Nat.zero_mul _)

/-- At the end the reading is the last value, and `0` where there is no value. -/
theorem stopsAt_end (values : List Int) : stopsAt values 1000 = values.getLast?.getD 0 :=
  (stopsAt_on values (values.length - 1) 1000 rfl).trans (getD_last values 0)

/-- Stops that begin with `0` and end with `1000` are proper. -/
theorem proper_stops (values : List Int) (h0 : values.head? = some 0)
    (h1 : values.getLast? = some 1000) : (stops values).Proper := by
  refine ⟨?_, (stopsAt_end values).trans (congrArg (fun o : Option Int => o.getD 0) h1)⟩
  cases values with
  | nil => cases h0
  | cons v rest => exact (stopsAt_zero v rest).trans (Option.some.inj h0)

/-- The progress itself is a proper easing. -/
theorem proper_linear : linear.Proper := proper_stops [0, 1000] rfl rfl

/-- The easing that is slow at first is proper. -/
theorem proper_cubicIn : cubicIn.Proper := proper_cubic 0 0

/-- The easing that is slow at last is proper. -/
theorem proper_cubicOut : cubicOut.Proper := proper_cubic 1000 1000

/-- The easing that goes past the end and comes back is proper. -/
theorem proper_backOut : backOut.Proper := proper_cubic 1567 1000

end Easing

/-! ## Transitions -/

namespace Transition

/-- Once its duration is over, a transition reads the end of its easing. -/
theorem at_done (tr : Transition) (t : Nat) (h : tr.delay + tr.duration ≤ t) :
    tr.at t = tr.ease.at 1000 := by
  rw [Transition.at, if_pos h]

/-- Until its delay is over, a transition that has not ended reads the start of its easing. -/
theorem at_before (tr : Transition) (t : Nat) (h1 : t ≤ tr.delay)
    (h2 : t < tr.delay + tr.duration) : tr.at t = tr.ease.at 0 := by
  rw [Transition.at, if_neg (Nat.not_le_of_lt h2), if_pos h1]

/-- Once its duration is over, a transition with a proper easing reads `1000`. -/
theorem at_done_proper (tr : Transition) (t : Nat) (hp : tr.ease.Proper)
    (h : tr.delay + tr.duration ≤ t) : tr.at t = 1000 :=
  (at_done tr t h).trans hp.2

/-- A transition held inside a step ends by the step's end. -/
theorem within_end (tr : Transition) : tr.within.delay + tr.within.duration ≤ 1000 := by
  show min tr.delay 1000 + min tr.duration (1000 - min tr.delay 1000) ≤ 1000
  omega

/-- A transition held inside a step keeps its easing. -/
theorem within_ease (tr : Transition) : tr.within.ease = tr.ease := rfl

/-- A transition started later keeps its easing. -/
theorem after_ease (tr : Transition) (d : Nat) : (tr.after d).ease = tr.ease := rfl

/-- A transition held inside a step reads the end of its easing at the step's end. -/
theorem within_at_end (tr : Transition) : tr.within.at 1000 = tr.ease.at 1000 :=
  at_done tr.within 1000 (within_end tr)

/-- A transition started later reads the end of its easing at the step's end. -/
theorem after_at_end (tr : Transition) (d : Nat) : (tr.after d).at 1000 = tr.ease.at 1000 :=
  within_at_end ({ tr with delay := tr.delay + d } : Transition)

end Transition

/-! ## Changes and tracks -/

namespace Change

/-- At the eased progress `1000` a change is its end. -/
theorem at_end (c : Change) : c.at 1000 = c.stop := by
  cases c with
  | shift a b => exact congrArg Pose.shift (IVec.ext (mix_end a.x b.x) (mix_end a.y b.y))
  | grow a b => exact congrArg Pose.grow (mix_end a b)
  | reveal a b => exact congrArg Pose.reveal (mix_end a b)
  | fade a b => exact congrArg Pose.fade (mix_end a b)

/-- At the eased progress `0` a change is its start. -/
theorem at_start (c : Change) : c.at 0 = c.start := by
  cases c with
  | shift a b => exact congrArg Pose.shift (IVec.ext (mix_start a.x b.x) (mix_start a.y b.y))
  | grow a b => exact congrArg Pose.grow (mix_start a b)
  | reveal a b => exact congrArg Pose.reveal (mix_start a b)
  | fade a b => exact congrArg Pose.fade (mix_start a b)

end Change

namespace Track

/-- **The end law of a track.** A track that is over stands at the end of its change. -/
theorem at_done {κ : Type} (tr : Track κ) (t : Nat) (h : tr.Done t) :
    tr.at t = tr.change.stop := by
  show tr.change.at (tr.timing.at t) = tr.change.stop
  rw [Transition.at_done_proper tr.timing t h.1 h.2]
  exact Change.at_end tr.change

/-- A track that is over and that settles is at rest. -/
theorem atRest_of_done {κ : Type} (tr : Track κ) (t : Nat) (h : tr.Done t) (hs : tr.Settles) :
    (tr.at t).AtRest := by
  rw [at_done tr t h]
  exact hs

end Track

/-! ## Motions -/

namespace Motion

/-- When every track is over, each key has the end of its change. -/
theorem poses_done {κ : Type} (m : Motion κ) (t : Nat) (h : ∀ tr ∈ m, tr.Done t) :
    m.poses t = m.map fun tr => (tr.key, tr.change.stop) :=
  List.map_congr_left fun tr htr => congrArg (Prod.mk tr.key) (Track.at_done tr t (h tr htr))

/-- A motion held inside a step, with proper easings, is over at the step's end. -/
theorem within_done {κ : Type} (m : Motion κ) (hp : ∀ tr ∈ m, tr.timing.ease.Proper) :
    ∀ tr ∈ m.within, tr.Done 1000 := by
  intro tr htr
  obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp htr
  exact ⟨hp tr0 h0, Transition.within_end tr0.timing⟩

/-- A motion held inside a step, with proper easings and tracks that settle, has every thing
at rest at the step's end. -/
theorem within_atRest {κ : Type} (m : Motion κ) (hp : ∀ tr ∈ m, tr.timing.ease.Proper)
    (hs : ∀ tr ∈ m, tr.Settles) : ∀ tr ∈ m.within, (tr.at 1000).AtRest := by
  intro tr htr
  have hd : tr.Done 1000 := within_done m hp tr htr
  obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp htr
  exact Track.atRest_of_done _ 1000 hd (hs tr0 h0)

/-- A track of the arriving things is the shift of a kept pair or the growth of a new thing. -/
theorem mem_arrive {κ α : Type} (key : α → κ) (place : α → IVec) (j : Join α)
    (move enter : Transition) {tr : Track κ} (h : tr ∈ arrive key place j move enter) :
    (∃ p ∈ j.update, tr = ⟨key p.2, .shift (place p.1 - place p.2) 0, move⟩) ∨
      ∃ n ∈ j.enter, tr = ⟨key n, .grow 0 1000, enter⟩ := by
  rcases List.mem_append.mp h with hu | he
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    exact Or.inl ⟨p, hp, rfl⟩
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    exact Or.inr ⟨n, hn, rfl⟩

/-- Every arriving track settles: a kept thing ends on its place, and a new thing ends at its
whole size. -/
theorem arrive_settles {κ α : Type} (key : α → κ) (place : α → IVec) (j : Join α)
    (move enter : Transition) : ∀ tr ∈ arrive key place j move enter, tr.Settles := by
  intro tr htr
  rcases mem_arrive key place j move enter htr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · exact rfl
  · exact rfl

/-- There is one arriving track for each thing of the new picture. -/
theorem length_arrive {κ α : Type} [BEq κ] (key : α → κ) (place : α → IVec) (old new : List α)
    (move enter : Transition) :
    (arrive key place (join key old new) move enter).length = new.length := by
  rw [arrive, List.length_append, List.length_map, List.length_map, Nat.add_comm]
  exact length_enter_add_update key old new

/-- An arriving track has the key of a thing of the new picture. -/
theorem mem_arrive_key {κ α : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec)
    (old new : List α) (move enter : Transition) {tr : Track κ}
    (h : tr ∈ arrive key place (join key old new) move enter) : ∃ n ∈ new, key n = tr.key := by
  rcases mem_arrive key place (join key old new) move enter h with
    ⟨⟨o, n⟩, hp, rfl⟩ | ⟨n, hn, rfl⟩
  · exact ⟨n, (mem_update key old new hp).2.1, rfl⟩
  · exact ⟨n, ((mem_enter key old new).mp hn).1, rfl⟩

/-- A departing track has the key of a thing of the old picture that no thing of the new
picture has. -/
theorem mem_depart_key {κ α : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α)
    (leave : Transition) {tr : Track κ} (h : tr ∈ depart key (join key old new) leave) :
    ∃ o ∈ old, key o = tr.key ∧ ∀ n ∈ new, key n ≠ tr.key := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp h
  exact ⟨o, ((mem_exit key old new).mp ho).1, rfl, ((mem_exit key old new).mp ho).2⟩

/-- **The end law of a step.** With proper easings, every arriving thing is at rest at the
end of the step: the kept things stand on their new places and the new things have their whole
size, so the step's last moment is the next picture. -/
theorem arrive_end {κ α : Type} (key : α → κ) (place : α → IVec) (j : Join α)
    (move enter : Transition) (hm : move.ease.Proper) (he : enter.ease.Proper) :
    ∀ tr ∈ (arrive key place j move enter).within, (tr.at 1000).AtRest := by
  refine within_atRest (arrive key place j move enter) (fun tr h => ?_)
    (arrive_settles key place j move enter)
  rcases mem_arrive key place j move enter h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · exact hm
  · exact he

end Motion

end Whatwg.Svg.Scene
