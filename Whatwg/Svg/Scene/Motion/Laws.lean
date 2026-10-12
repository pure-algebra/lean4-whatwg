import Whatwg.Svg.Scene.Motion
import Whatwg.Svg.Scene.Join.Laws

/-!
# Whatwg.Svg.Scene.Motion.Laws

Owner: the laws of motion as data (slice S12 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-62).

A reader of tracks draws the moments between one picture and the next. These laws say where
that reading starts and where it ends, so that the last moment of a step is the next picture.

- Mixing. `mix u v e` is `u` at `0` and `v` at `1000`, and a value mixed with itself stays
  (`mix_start`, `mix_end`, `mix_self`). A value on its way from `u` to `v` is `v` and a shift
  on its way to nothing (`mix_shift`, `mix_add`). A segment is mixed point by point
  (`ICubic.mix_start`, `ICubic.mix_end`), and a segment on its way from a moved copy of itself
  is itself, moved by a shift on its way to nothing (`ICubic.mix_move`).
- Easings. A cubic reads `0` at the start and `1000` at the end, whatever its two heights
  (`Easing.cubicAt_zero`, `Easing.cubicAt_end`), so every cubic is proper
  (`Easing.proper_cubic`). Stops read the value of a stop at that stop (`Easing.stopsAt_stop`),
  as `linear()` of CSS does: the first value at `0` (`Easing.stopsAt_zero`) and the last at
  `1000` (`Easing.stopsAt_end`). Stops that begin with `0` and end with `1000` are proper
  (`Easing.proper_stops`), and so are the four named easings.
- Easings at a share. The reading at a share of a thousand is the reading in per mille
  (`Easing.of_thousand`). At no share it is the easing's start, for every denominator
  (`Easing.of_zero`), and at the whole share it is the easing's end (`Easing.of_self`). Stops
  read a stop's value at the share that falls on it (`Easing.stopsOf_stop`).
- Transitions. Once its duration is over, a transition reads the end of its easing
  (`Transition.at_done`), which is `1000` where the easing is proper
  (`Transition.at_done_proper`). Until its delay is over it reads the start
  (`Transition.at_before`), and between the two it reads its easing at the share of its
  duration that has passed (`Transition.at_between`). A transition held inside a step ends by
  the step's end (`Transition.within_end`), keeps its easing (`Transition.within_ease`,
  `Transition.after_ease`), and reads the end of its easing at the step's end
  (`Transition.within_at_end`, `Transition.after_at_end`).
- Changes and tracks. A change is its start at `0` and its end at `1000` (`Change.at_start`,
  `Change.at_end`). A change of shape between two lists of one length mixes them segment by
  segment (`Change.at_morph`), and a shape that is only moved changes as a shift does
  (`Change.at_morph_move`). **The end law of a track**: a track that is over stands at the end
  of its change (`Track.at_done`), and it is at rest there where it settles
  (`Track.atRest_of_done`).
- Motions. When every track is over, the poses are the ends of the changes
  (`Motion.poses_done`). A motion held inside a step is over at the step's end
  (`Motion.within_done`), and at rest there where its tracks settle (`Motion.within_atRest`).
  Its tracks are the motion's with their transitions held (`Motion.mem_within`), and a pose of
  a key is the pose of a track with that key (`Motion.mem_posesOf`).
- The motion of a join. Every arriving track settles (`Motion.arrive_settles`). There is one
  arriving track for each new thing (`Motion.length_arrive`), with the key of a new thing
  (`Motion.mem_arrive_key`). A departing track has the key of an old thing that no new thing
  has (`Motion.mem_depart_key`). **The end law of a step** (`Motion.arrive_end`): with proper
  easings, every arriving thing is at rest at the step's end.
- The things of a join, each in its own way. `Motion.arrive` is `Motion.arriveWith` with one
  transition for every kept thing and one growth for every new one
  (`Motion.arrive_eq_arriveWith`). The four laws above hold of `arriveWith`
  (`Motion.arriveWith_settles`, `Motion.length_arriveWith`, `Motion.mem_arriveWith_key`,
  `Motion.arriveWith_end`), where each new thing enters by a change that ends at rest.
- Tracks started later. A delayed motion has the same tracks with the same keys and changes
  (`Motion.length_delayed`, `Motion.delayed_keys`, `Motion.delayed_changes`), each started later
  by what its key is given (`Motion.delayed_delays`). Held inside its step, it is at rest at
  the step's end (`Motion.delayed_within_atRest`).

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

/-- Two lists of one length, joined member by member by a function that gives its second
argument, are the second list. -/
theorem zipWith_right {α β : Type} (f : α → β → β) (hf : ∀ a b, f a b = b) :
    ∀ (l : List α) (m : List β), l.length = m.length → List.zipWith f l m = m
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h.symm (Nat.succ_ne_zero _)
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)
  | a :: l, b :: m, h => by
    rw [List.zipWith_cons_cons, hf, zipWith_right f hf l m (Nat.succ.inj h)]

/-- Two lists of one length, joined member by member by a function that gives its first
argument, are the first list. -/
theorem zipWith_left {α β : Type} (f : α → β → α) (hf : ∀ a b, f a b = a) :
    ∀ (l : List α) (m : List β), l.length = m.length → List.zipWith f l m = l
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)
  | a :: l, b :: m, h => by
    rw [List.zipWith_cons_cons, hf, zipWith_left f hf l m (Nat.succ.inj h)]

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

/-- **A value on its way from `u` to `v` is `v` and a shift on its way to nothing.** The shift
is what `Change.shift (u - v) 0` sets, so a thing drawn at its new place under that shift
stands where the mixed value says: a thing that moves and a line joined to it stay together. -/
theorem mix_shift (u v e : Int) : mix u v e = v + mix (u - v) 0 e := by
  simp only [mix, Int.sub_zero, Int.zero_add]

/-- A value that starts the shift `d` off `u` and goes to `u` is `u` and that shift on its way
to nothing. -/
theorem mix_add (u d e : Int) : mix (u + d) u e = u + mix d 0 e := by
  rw [mix_shift, Int.add_comm u d, Int.add_sub_cancel]

/-! ## Mixing segments -/

namespace ICubic

/-- At the end of the way the mixed segment is the second one. -/
theorem mix_end (a b : ICubic) : ICubic.mix a b 1000 = b := by
  have h : ∀ p q : IVec, (⟨Scene.mix p.x q.x 1000, Scene.mix p.y q.y 1000⟩ : IVec) = q :=
    fun p q => IVec.ext (Scene.mix_end p.x q.x) (Scene.mix_end p.y q.y)
  exact congr (congr (congr (congrArg ICubic.mk (h a.p0 b.p0)) (h a.p1 b.p1)) (h a.p2 b.p2))
    (h a.p3 b.p3)

/-- At the start of the way the mixed segment is the first one. -/
theorem mix_start (a b : ICubic) : ICubic.mix a b 0 = a := by
  have h : ∀ p q : IVec, (⟨Scene.mix p.x q.x 0, Scene.mix p.y q.y 0⟩ : IVec) = p :=
    fun p q => IVec.ext (Scene.mix_start p.x q.x) (Scene.mix_start p.y q.y)
  exact congr (congr (congr (congrArg ICubic.mk (h a.p0 b.p0)) (h a.p1 b.p1)) (h a.p2 b.p2))
    (h a.p3 b.p3)

/-- Two lists of segments of one length, mixed at the end of the way, are the second list. -/
theorem zipWith_mix_end (a b : List ICubic) (h : a.length = b.length) :
    List.zipWith (fun x y => ICubic.mix x y 1000) a b = b :=
  zipWith_right _ mix_end a b h

/-- Two lists of segments of one length, mixed at the start of the way, are the first list. -/
theorem zipWith_mix_start (a b : List ICubic) (h : a.length = b.length) :
    List.zipWith (fun x y => ICubic.mix x y 0) a b = a :=
  zipWith_left _ mix_start a b h

/-- **A shape that is only moved changes as a move does.** A segment on its way from its copy
moved by `d` to itself is itself, moved by the shift `d` on its way to nothing. The two sides
are the same sums: no sum is associated another way. -/
theorem mix_move (d : IVec) (c : ICubic) (e : Int) :
    ICubic.mix (Moves.move d c) c e = Moves.move ⟨Scene.mix d.x 0 e, Scene.mix d.y 0 e⟩ c := by
  have h : ∀ p : IVec, (⟨Scene.mix (p + d).x p.x e, Scene.mix (p + d).y p.y e⟩ : IVec) =
      p + ⟨Scene.mix d.x 0 e, Scene.mix d.y 0 e⟩ := fun p =>
    IVec.ext (mix_add p.x d.x e) (mix_add p.y d.y e)
  exact congr (congr (congr (congrArg ICubic.mk (h c.p0)) (h c.p1)) (h c.p2)) (h c.p3)

end ICubic

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

/-! ### At a share of the progress -/

/-- Stops at a share of a thousand read as they do in per mille. -/
theorem stopsOf_thousand (values : List Int) (p : Nat) :
    stopsOf values p 1000 = stopsAt values p := rfl

/-- A cubic at a share of a thousand reads as it does in per mille. -/
theorem cubicOf_thousand (y1 y2 : Int) (p : Nat) : cubicOf y1 y2 p 1000 = cubicAt y1 y2 p := rfl

/-- Where the share `num / den` falls on the stop `i`, the reading is the value of that stop,
and the last value where `i` is past the stops. With a denominator that is not `0` the first
premise follows from the second. -/
theorem stopsOf_on (values : List Int) (i num den : Nat)
    (hi : num * (values.length - 1) / den = i) (hp : num * (values.length - 1) = den * i) :
    stopsOf values num den = values.getD i (values.getLast?.getD 0) := by
  have hz : ((num * (values.length - 1) - den * i : Nat) : Int) = 0 :=
    congrArg (fun n : Nat => (n : Int)) (Nat.sub_eq_zero_of_le (Nat.le_of_eq hp))
  show values.getD (num * (values.length - 1) / den) (values.getLast?.getD 0) +
    (values.getD (num * (values.length - 1) / den + 1) (values.getLast?.getD 0) -
      values.getD (num * (values.length - 1) / den) (values.getLast?.getD 0)) *
      ((num * (values.length - 1) - den * (num * (values.length - 1) / den) : Nat) : Int) /
        (den : Int) =
    values.getD i (values.getLast?.getD 0)
  rw [hi, hz, Int.mul_zero, Int.zero_ediv, Int.add_zero]

/-- **At a stop the reading at a share is the stop's value.** The stop `i` of `values` stands
at the share `num / den` with `num * (values.length - 1) = den * i`. -/
theorem stopsOf_stop (values : List Int) (i num den : Nat) (hd : 0 < den)
    (hi : i < values.length) (hp : num * (values.length - 1) = den * i) :
    stopsOf values num den = values.getD i 0 := by
  refine (stopsOf_on values i num den ?_ hp).trans (getD_of_lt values i _ 0 hi)
  rw [hp]
  exact Nat.mul_div_cancel_left i hd

/-- At no share stops read their start, whatever the denominator. -/
theorem stopsOf_zero (values : List Int) (den : Nat) :
    stopsOf values 0 den = stopsAt values 0 := by
  have hi : 0 * (values.length - 1) / den = 0 := by rw [Nat.zero_mul, Nat.zero_div]
  exact (stopsOf_on values 0 0 den hi (Nat.zero_mul _)).trans
    (stopsAt_on values 0 0 (Nat.zero_mul _)).symm

/-- At the whole share stops read their end. -/
theorem stopsOf_self (values : List Int) (den : Nat) (h : 0 < den) :
    stopsOf values den den = stopsAt values 1000 :=
  (stopsOf_on values (values.length - 1) den den (Nat.mul_div_cancel_left _ h) rfl).trans
    (stopsAt_on values (values.length - 1) 1000 rfl).symm

/-- At no share a cubic reads `0`, whatever the denominator. -/
theorem cubicOf_zero (y1 y2 : Int) (den : Nat) : cubicOf y1 y2 0 den = 0 := by
  have h2 : (0 : Int) ^ 2 = 0 := rfl
  have h3 : (0 : Int) ^ 3 = 0 := rfl
  show (3 * y1 * 0 * ((den : Int) - 0) ^ 2 + 3 * y2 * 0 ^ 2 * ((den : Int) - 0) + 1000 * 0 ^ 3) /
    (den : Int) ^ 3 = (0 : Int)
  simp only [h2, h3, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_ediv]

/-- At the whole share a cubic reads `1000`. -/
theorem cubicOf_self (y1 y2 : Int) (den : Nat) (h : 0 < den) : cubicOf y1 y2 den den = 1000 := by
  have h2 : (0 : Int) ^ 2 = 0 := rfl
  have hd : (den : Int) ^ 3 ≠ 0 := Int.ne_of_gt (Int.pow_pos (Int.natCast_pos.mpr h))
  show (3 * y1 * (den : Int) * ((den : Int) - den) ^ 2 +
    3 * y2 * (den : Int) ^ 2 * ((den : Int) - den) + 1000 * (den : Int) ^ 3) / (den : Int) ^ 3 =
    (1000 : Int)
  simp only [Int.sub_self, h2, Int.mul_zero, Int.zero_add]
  exact Int.mul_ediv_cancel 1000 hd

/-- **The reading at a share of a thousand is the reading in per mille.** -/
theorem of_thousand (e : Easing) (p : Nat) : e.of p 1000 = e.at p := by
  cases e with
  | stops values => exact stopsOf_thousand values p
  | cubic y1 y2 => exact cubicOf_thousand y1 y2 p

/-- **At no share an easing reads its start**, whatever the denominator: with the denominator
`0` too, where every division gives `0`. -/
theorem of_zero (e : Easing) (den : Nat) : e.of 0 den = e.at 0 := by
  cases e with
  | stops values => exact stopsOf_zero values den
  | cubic y1 y2 => exact (cubicOf_zero y1 y2 den).trans (cubicAt_zero y1 y2).symm

/-- **At the whole share an easing reads its end.** -/
theorem of_self (e : Easing) (den : Nat) (h : 0 < den) : e.of den den = e.at 1000 := by
  cases e with
  | stops values => exact stopsOf_self values den h
  | cubic y1 y2 => exact (cubicOf_self y1 y2 den h).trans (cubicAt_end y1 y2).symm

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

/-- Between its delay and its end, a transition reads its easing at the share of its duration
that has passed. -/
theorem at_between (tr : Transition) (t : Nat) (h1 : tr.delay < t)
    (h2 : t < tr.delay + tr.duration) : tr.at t = tr.ease.of (t - tr.delay) tr.duration := by
  rw [Transition.at, if_neg (Nat.not_le_of_lt h2), if_neg (Nat.not_le_of_lt h1)]

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
  | morph a b =>
    show (if a.length = b.length then
        Pose.shape (List.zipWith (fun x y => ICubic.mix x y 1000) a b)
      else if (1000 : Int) < 500 then Pose.shape a
      else Pose.shape b) = Pose.shape b
    cases Nat.decEq a.length b.length with
    | isTrue h => rw [if_pos h, ICubic.zipWith_mix_end a b h]
    | isFalse h => rw [if_neg h, if_neg (by decide)]

/-- At the eased progress `0` a change is its start. -/
theorem at_start (c : Change) : c.at 0 = c.start := by
  cases c with
  | shift a b => exact congrArg Pose.shift (IVec.ext (mix_start a.x b.x) (mix_start a.y b.y))
  | grow a b => exact congrArg Pose.grow (mix_start a b)
  | reveal a b => exact congrArg Pose.reveal (mix_start a b)
  | fade a b => exact congrArg Pose.fade (mix_start a b)
  | morph a b =>
    show (if a.length = b.length then
        Pose.shape (List.zipWith (fun x y => ICubic.mix x y 0) a b)
      else if (0 : Int) < 500 then Pose.shape a
      else Pose.shape b) = Pose.shape a
    cases Nat.decEq a.length b.length with
    | isTrue h => rw [if_pos h, ICubic.zipWith_mix_start a b h]
    | isFalse h => rw [if_neg h, if_pos (by decide)]

/-- **A change of shape between two lists of one length mixes them segment by segment.** -/
theorem at_morph (a b : List ICubic) (e : Int) (h : a.length = b.length) :
    (Change.morph a b).at e = .shape (List.zipWith (fun x y => ICubic.mix x y e) a b) :=
  if_pos h

/-- **A shape that is only moved changes as a shift does.** On its way from its copy moved by
`d` to itself, a shape is itself moved by the step that `Change.shift d 0` sets at that
progress. So a line that changes shape and a thing that shifts, both by one easing, stay
joined at every moment. -/
theorem at_morph_move (d : IVec) (l : List ICubic) (e : Int) :
    (Change.morph (Moves.move d l) l).at e =
      .shape (Moves.move (⟨mix d.x 0 e, mix d.y 0 e⟩ : IVec) l) := by
  rw [at_morph (Moves.move d l) l e (Moves.length_move d l)]
  show Pose.shape (List.zipWith (fun x y => ICubic.mix x y e) (l.map (Moves.move d)) l) =
    Pose.shape (l.map (Moves.move (⟨mix d.x 0 e, mix d.y 0 e⟩ : IVec)))
  rw [List.zipWith_map_left, List.zipWith_self]
  exact congrArg Pose.shape (List.map_congr_left fun c _ => ICubic.mix_move d c e)

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

/-- A track of a motion held inside a step is a track of the motion with its transition
held. -/
theorem mem_within {κ : Type} (m : Motion κ) {tr : Track κ} (h : tr ∈ m.within) :
    ∃ tr0 ∈ m, tr = { tr0 with timing := tr0.timing.within } := by
  obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp h
  exact ⟨tr0, h0, rfl⟩

/-- A pose of a key at a moment is the pose of a track with that key. -/
theorem mem_posesOf {κ : Type} [BEq κ] (m : Motion κ) (key : κ) (t : Nat) {p : Pose}
    (h : p ∈ m.posesOf key t) : ∃ tr ∈ m, (tr.key == key) = true ∧ p = tr.at t := by
  obtain ⟨tr, htr, rfl⟩ := List.mem_map.mp h
  exact ⟨tr, (List.mem_filter.mp htr).1, (List.mem_filter.mp htr).2, rfl⟩

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

/-! ### Each thing in its own way -/

/-- The arriving tracks with one transition for every kept thing and one growth for every new
one are the arriving tracks, each in its own way, that give every thing the same. -/
theorem arrive_eq_arriveWith {κ α : Type} (key : α → κ) (place : α → IVec) (j : Join α)
    (move enter : Transition) :
    arrive key place j move enter =
      arriveWith key place j (fun _ => move) (fun _ => (.grow 0 1000, enter)) := rfl

/-- A track of the arriving things, each in its own way, is the shift of a kept pair or the
change of a new thing. -/
theorem mem_arriveWith {κ α : Type} (key : α → κ) (place : α → IVec) (j : Join α)
    (move : α → Transition) (enter : α → Change × Transition) {tr : Track κ}
    (h : tr ∈ arriveWith key place j move enter) :
    (∃ p ∈ j.update, tr = ⟨key p.2, .shift (place p.1 - place p.2) 0, move p.2⟩) ∨
      ∃ n ∈ j.enter, tr = ⟨key n, (enter n).1, (enter n).2⟩ := by
  rcases List.mem_append.mp h with hu | he
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    exact Or.inl ⟨p, hp, rfl⟩
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    exact Or.inr ⟨n, hn, rfl⟩

/-- There is one arriving track for each thing of the new picture, whatever way each takes. -/
theorem length_arriveWith {κ α : Type} [BEq κ] (key : α → κ) (place : α → IVec)
    (old new : List α) (move : α → Transition) (enter : α → Change × Transition) :
    (arriveWith key place (join key old new) move enter).length = new.length := by
  rw [arriveWith, List.length_append, List.length_map, List.length_map, Nat.add_comm]
  exact length_enter_add_update key old new

/-- Every arriving track settles, where each new thing enters by a change that ends at rest: a
kept thing ends on its place. -/
theorem arriveWith_settles {κ α : Type} (key : α → κ) (place : α → IVec) (j : Join α)
    (move : α → Transition) (enter : α → Change × Transition)
    (h : ∀ n, (enter n).1.stop.AtRest) :
    ∀ tr ∈ arriveWith key place j move enter, tr.Settles := by
  intro tr htr
  rcases mem_arriveWith key place j move enter htr with ⟨_, _, rfl⟩ | ⟨n, _, rfl⟩
  · exact rfl
  · exact h n

/-- Every arriving track has a proper easing, where every transition given has one. -/
theorem arriveWith_proper {κ α : Type} (key : α → κ) (place : α → IVec) (j : Join α)
    (move : α → Transition) (enter : α → Change × Transition)
    (hm : ∀ a, (move a).ease.Proper) (he : ∀ n, (enter n).2.ease.Proper) :
    ∀ tr ∈ arriveWith key place j move enter, tr.timing.ease.Proper := by
  intro tr htr
  rcases mem_arriveWith key place j move enter htr with ⟨p, _, rfl⟩ | ⟨n, _, rfl⟩
  · exact hm p.2
  · exact he n

/-- An arriving track has the key of a thing of the new picture, whatever way each takes. -/
theorem mem_arriveWith_key {κ α : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (place : α → IVec)
    (old new : List α) (move : α → Transition) (enter : α → Change × Transition) {tr : Track κ}
    (h : tr ∈ arriveWith key place (join key old new) move enter) :
    ∃ n ∈ new, key n = tr.key := by
  rcases mem_arriveWith key place (join key old new) move enter h with
    ⟨⟨o, n⟩, hp, rfl⟩ | ⟨n, hn, rfl⟩
  · exact ⟨n, (mem_update key old new hp).2.1, rfl⟩
  · exact ⟨n, ((mem_enter key old new).mp hn).1, rfl⟩

/-- **The end law of a step, each thing in its own way.** With proper easings and changes that
end at rest, every arriving thing is at rest at the end of the step. -/
theorem arriveWith_end {κ α : Type} (key : α → κ) (place : α → IVec) (j : Join α)
    (move : α → Transition) (enter : α → Change × Transition)
    (hm : ∀ a, (move a).ease.Proper) (he : ∀ n, (enter n).2.ease.Proper)
    (hs : ∀ n, (enter n).1.stop.AtRest) :
    ∀ tr ∈ (arriveWith key place j move enter).within, (tr.at 1000).AtRest :=
  within_atRest (arriveWith key place j move enter)
    (arriveWith_proper key place j move enter hm he) (arriveWith_settles key place j move enter hs)

/-! ### Tracks started later -/

/-- A delayed motion has as many tracks. -/
theorem length_delayed {κ : Type} (m : Motion κ) (later : κ → Nat) :
    (m.delayed later).length = m.length := List.length_map _

/-- A delayed motion has the same keys, track by track. -/
theorem delayed_keys {κ : Type} (m : Motion κ) (later : κ → Nat) :
    (m.delayed later).map (fun tr => tr.key) = m.map (fun tr => tr.key) := List.map_map

/-- A delayed motion has the same changes, track by track. -/
theorem delayed_changes {κ : Type} (m : Motion κ) (later : κ → Nat) :
    (m.delayed later).map (fun tr => tr.change) = m.map (fun tr => tr.change) := List.map_map

/-- A delayed motion starts each track later by what its key is given. -/
theorem delayed_delays {κ : Type} (m : Motion κ) (later : κ → Nat) :
    (m.delayed later).map (fun tr => tr.timing.delay) =
      m.map (fun tr => tr.timing.delay + later tr.key) := List.map_map

/-- A motion delayed by nothing is itself. -/
theorem delayed_zero {κ : Type} (m : Motion κ) : m.delayed (fun _ => 0) = m :=
  (List.map_congr_left fun _ _ => rfl).trans (List.map_id m)

/-- A track of a delayed motion is a track of the motion with its delay made longer. -/
theorem mem_delayed {κ : Type} (m : Motion κ) (later : κ → Nat) {tr : Track κ}
    (h : tr ∈ m.delayed later) :
    ∃ tr0 ∈ m, tr =
      { tr0 with timing := { tr0.timing with delay := tr0.timing.delay + later tr0.key } } := by
  obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp h
  exact ⟨tr0, h0, rfl⟩

/-- **A delayed motion held inside its step is at rest at the step's end**, with proper easings
and tracks that settle: however late a track starts, it ends by the step's end. -/
theorem delayed_within_atRest {κ : Type} (m : Motion κ) (later : κ → Nat)
    (hp : ∀ tr ∈ m, tr.timing.ease.Proper) (hs : ∀ tr ∈ m, tr.Settles) :
    ∀ tr ∈ (m.delayed later).within, (tr.at 1000).AtRest := by
  refine within_atRest (m.delayed later) (fun tr h => ?_) (fun tr h => ?_)
  · obtain ⟨tr0, h0, rfl⟩ := mem_delayed m later h
    exact hp tr0 h0
  · obtain ⟨tr0, h0, rfl⟩ := mem_delayed m later h
    exact hs tr0 h0

end Motion

end Whatwg.Svg.Scene
