import Whatwg.Svg.Scene.Motion.Laws

/-!
# Whatwg.Svg.Scene.Score

Owner: order in time (slice S13 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-74).

Order in time says order in the program. A thing must not appear before what it comes from: in a
build a child appears after its parent, and in a graph an edge reaches a box before the box
opens. `Motion.delayed` of `Whatwg/Svg/Scene/Motion.lean` starts tracks later, and no law of it
is about order. This module has the order as a predicate, the operations that keep it, and the
same step for a reader who asked for less motion.

- `Motion.finish m`: the moment the last track ends.
- `Motion.Respects before m`: a track of a key ends before a track of each key that `before`
  puts after it starts. Where `before` is decided, so is this, by evaluation.
- `Motion.andThen a b overlap`: the tracks of `a`, then the tracks of `b`, each started when `a`
  has ended, less `overlap`.
- `Motion.reduced m`: the same step with no travel. Each track keeps its key and its timing. A
  growth or a line that draws itself becomes a change of opacity between the same two numbers,
  so a thing that entered fades in and a thing that left fades out. A shift or a change of shape
  stands at its end from the first moment.
- `Motion.fit m budget`: every delay and duration scaled by one factor, so that the motion ends
  by `budget`.
- `Easing.settledBy e slack`: the first stop from which the easing stays within `slack` of
  `1000`.
- `Transition.forTravel`: a duration for a travel, between a least and a greatest.

What the laws say of a step:

- `Motion.finish_le`: every track ends by the finish, and the finish is the least such moment
  (`Motion.finish_le_of`). With proper easings the poses at the finish are the ends of the
  changes (`Motion.poses_finish`).
- `Motion.delayed_respects`: tracks that lie in one window of `gap`, delayed by `gap` for each
  rank, respect every order that the rank follows. So a child starts when its parent has ended.
  `Motion.delayed_respects_together` is the same for tracks that start together.
- `Motion.andThen_after`: with no overlap, every track of the second motion starts when every
  track of the first has ended. `Motion.andThen_respects`: the two in a row respect an order
  that each respects, where nothing of the second is before a thing of the first.
- `Motion.within_respects`, `Motion.fit_respects`, `Motion.reduced_respects`: holding a motion
  inside its step, fitting it to a budget and reducing it keep the order. A rounding breaks no
  order, since two floors are no more than the floor of the sum.
- `Motion.reduced_keys`, `Motion.reduced_timings`: a reduced motion has the same keys and the
  same timings, track by track. `Motion.reduced_settles`: a track that settles still settles.
  `Change.reduced_at`: at every moment a reduced change sets an opacity or stands at the end of
  the change, so nothing travels. The reader who asked for less motion sees the same things at
  the same moments, and the same last picture (`Motion.reduced_within_atRest`).
- `Motion.fit_finish`: a fitted motion ends by its budget, so with proper easings every track
  is over at the budget (`Motion.fit_done`).
- `Easing.settledBy_holds`: from the stop `e.settledBy slack` on, the easing reads within
  `slack` of `1000` at every whole stop, and that stop is the first such
  (`Easing.settledBy_first`). So the things that enter may start before a move ends, at a
  moment that is computed.
- `Transition.forTravel_le`, `Transition.le_forTravel`: a duration for a travel is between the
  least and the greatest.

What is the owner's to rule, and so a parameter: the order `before` and the `rank` that follows
it, the `gap` between two ranks, the `overlap` of two motions, the `budget`, the `slack`, and
the least and the greatest duration of a travel.

What this module does not claim: a step that is interrupted, and three parts staged in a row;
an order for `andThen` with an overlap; that a reduced track which does not settle ends as the
track does, since a growth that ends at half a size becomes an opacity that ends at half; that
`Transition.forTravel` gives no less for more travel, which rests on `Nat.sqrt` giving no less
for more, and the proof of that in Lean's core library is over the strict ceiling; that an
easing stays within the slack between two whole stops, where a transition whose duration is not
a thousand reads it (`Easing.of`).
-/

namespace Whatwg.Svg.Scene

variable {κ : Type}

/-! ## The end of a motion -/

/-- **The moment the last track ends**: `0` for no track. -/
def Motion.finish : Motion κ → Nat
  | [] => 0
  | tr :: rest => max (tr.timing.delay + tr.timing.duration) (Motion.finish rest)

/-- **Every track ends by the finish.** -/
theorem Motion.finish_le : ∀ (m : Motion κ) (tr : Track κ), tr ∈ m →
    tr.timing.delay + tr.timing.duration ≤ m.finish
  | [], _, h => nomatch h
  | x :: rest, tr, h => by
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact Nat.le_max_left _ _
    | inr hr => exact Nat.le_trans (Motion.finish_le rest tr hr) (Nat.le_max_right _ _)

/-- The finish is the least moment by which every track has ended. -/
theorem Motion.finish_le_of : ∀ (m : Motion κ) (b : Nat),
    (∀ tr ∈ m, tr.timing.delay + tr.timing.duration ≤ b) → m.finish ≤ b
  | [], b, _ => Nat.zero_le b
  | x :: rest, b, h =>
    Nat.max_le.mpr ⟨h x List.mem_cons_self,
      Motion.finish_le_of rest b fun tr hr => h tr (List.mem_cons_of_mem x hr)⟩

/-- A track with a proper easing is over at the finish. -/
theorem Motion.done_finish (m : Motion κ) (tr : Track κ) (h : tr ∈ m)
    (hp : tr.timing.ease.Proper) : tr.Done m.finish :=
  ⟨hp, Motion.finish_le m tr h⟩

/-- With proper easings, at the finish each key has the end of its change. -/
theorem Motion.poses_finish (m : Motion κ) (hp : ∀ tr ∈ m, tr.timing.ease.Proper) :
    m.poses m.finish = m.map fun tr => (tr.key, tr.change.stop) :=
  Motion.poses_done m m.finish fun tr h => Motion.done_finish m tr h (hp tr h)

/-! ## Order in time -/

/-- **The motion respects the order `before`**: a track of a key ends before a track of each
key that `before` puts after it starts. With `before` the edges of a program, no effect is
shown before its cause. -/
def Motion.Respects (before : κ → κ → Prop) (m : Motion κ) : Prop :=
  ∀ a ∈ m, ∀ b ∈ m, before a.key b.key → a.timing.delay + a.timing.duration ≤ b.timing.delay

/-- Where the order is decided, whether a motion respects it is decided: by evaluation, for the
tracks of one step. -/
instance (before : κ → κ → Prop) [∀ a b, Decidable (before a b)] (m : Motion κ) :
    Decidable (m.Respects before) :=
  inferInstanceAs (Decidable (∀ a ∈ m, ∀ b ∈ m,
    before a.key b.key → a.timing.delay + a.timing.duration ≤ b.timing.delay))

/-- **A motion delayed by its ranks respects the order of the ranks.** Let every track of `m`
lie in one window, from `d0` to `d0 + gap`, and let `before a b` give `rank a < rank b`. Then
`m`, each track started later by `gap` for each rank of its key, respects `before`. -/
theorem Motion.delayed_respects (before : κ → κ → Prop) (rank : κ → Nat) (gap d0 : Nat)
    (m : Motion κ) (hr : ∀ a b, before a b → rank a < rank b)
    (hs : ∀ tr ∈ m, d0 ≤ tr.timing.delay)
    (he : ∀ tr ∈ m, tr.timing.delay + tr.timing.duration ≤ d0 + gap) :
    (m.delayed fun k => gap * rank k).Respects before := by
  intro a ha b hb hab
  obtain ⟨a0, ha0, rfl⟩ := Motion.mem_delayed m _ ha
  obtain ⟨b0, hb0, rfl⟩ := Motion.mem_delayed m _ hb
  have h1 : gap * (rank a0.key + 1) ≤ gap * rank b0.key :=
    Nat.mul_le_mul_left gap (Nat.succ_le_of_lt (hr _ _ hab))
  rw [Nat.mul_add, Nat.mul_one] at h1
  have h2 := hs b0 hb0
  have h3 := he a0 ha0
  show a0.timing.delay + gap * rank a0.key + a0.timing.duration ≤
    b0.timing.delay + gap * rank b0.key
  omega

/-- A motion whose tracks start together, at `d0`, and last `gap` at most, delayed by `gap` for
each rank, respects every order that the rank follows. -/
theorem Motion.delayed_respects_together (before : κ → κ → Prop) (rank : κ → Nat)
    (gap d0 : Nat) (m : Motion κ) (hr : ∀ a b, before a b → rank a < rank b)
    (hd : ∀ tr ∈ m, tr.timing.delay = d0) (hg : ∀ tr ∈ m, tr.timing.duration ≤ gap) :
    (m.delayed fun k => gap * rank k).Respects before :=
  Motion.delayed_respects before rank gap d0 m hr (fun tr h => Nat.le_of_eq (hd tr h).symm)
    fun tr h => (hd tr h).symm ▸ Nat.add_le_add_left (hg tr h) d0

/-- A motion held inside its step respects the order that it respected: a time cut at the
step's end is no later. -/
theorem Motion.within_respects (before : κ → κ → Prop) (m : Motion κ)
    (h : m.Respects before) : m.within.Respects before := by
  intro a ha b hb hab
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
  have h1 := h a0 ha0 b0 hb0 hab
  show min a0.timing.delay 1000 + min a0.timing.duration (1000 - min a0.timing.delay 1000) ≤
    min b0.timing.delay 1000
  omega

/-! ## One motion after another -/

/-- **`b` after `a`**: the tracks of `a`, then the tracks of `b`, each started later by the
moment `a` ends, less `overlap`. -/
def Motion.andThen (a b : Motion κ) (overlap : Nat := 0) : Motion κ :=
  a ++ b.delayed fun _ => a.finish - overlap

/-- A track of `b` after `a` is a track of `a`, or a track of `b` started later. -/
theorem Motion.mem_andThen (a b : Motion κ) (overlap : Nat) {tr : Track κ}
    (h : tr ∈ a.andThen b overlap) :
    tr ∈ a ∨ ∃ tr0 ∈ b, tr = { tr0 with
      timing := { tr0.timing with delay := tr0.timing.delay + (a.finish - overlap) } } := by
  rcases List.mem_append.mp h with ha | hb
  · exact Or.inl ha
  · obtain ⟨tr0, h0, rfl⟩ := Motion.mem_delayed b _ hb
    exact Or.inr ⟨tr0, h0, rfl⟩

/-- A track of `b` after `a` is a track of `a`, or starts when `a` has ended, less the
overlap. -/
theorem Motion.andThen_starts (a b : Motion κ) (overlap : Nat) {tr : Track κ}
    (h : tr ∈ a.andThen b overlap) : tr ∈ a ∨ a.finish - overlap ≤ tr.timing.delay := by
  rcases Motion.mem_andThen a b overlap h with ha | ⟨tr0, _, rfl⟩
  · exact Or.inl ha
  · exact Or.inr (Nat.le_add_left _ _)

/-- **With no overlap, what comes second starts when the first has finished.** Every track of
`a` has ended when a track of `b` in `a.andThen b` starts. -/
theorem Motion.andThen_after (a b : Motion κ) {x y : Track κ} (hx : x ∈ a)
    (hy : y ∈ b.delayed fun _ => a.finish) :
    x.timing.delay + x.timing.duration ≤ y.timing.delay := by
  obtain ⟨y0, _, rfl⟩ := Motion.mem_delayed b _ hy
  exact Nat.le_trans (Motion.finish_le a x hx) (Nat.le_add_left _ _)

/-- With no overlap, `b` after `a` is the tracks of `a`, then the tracks of `b`, each started
later by the finish of `a`. -/
theorem Motion.andThen_eq (a b : Motion κ) :
    a.andThen b = a ++ b.delayed fun _ => a.finish := rfl

/-- **Two motions in a row keep an order.** With no overlap, `b` after `a` respects an order
that `a` and `b` respect, where no thing of `b` is before a thing of `a`. -/
theorem Motion.andThen_respects (before : κ → κ → Prop) (a b : Motion κ)
    (ha : a.Respects before) (hb : b.Respects before)
    (hba : ∀ x ∈ b, ∀ y ∈ a, ¬ before x.key y.key) : (a.andThen b).Respects before := by
  intro x hx y hy hxy
  rcases Motion.mem_andThen a b 0 hx with hxa | ⟨x0, hx0, rfl⟩
  · rcases Motion.mem_andThen a b 0 hy with hya | ⟨y0, _, rfl⟩
    · exact ha x hxa y hya hxy
    · exact Nat.le_trans (Motion.finish_le a x hxa) (Nat.le_add_left _ _)
  · rcases Motion.mem_andThen a b 0 hy with hya | ⟨y0, hy0, rfl⟩
    · exact absurd hxy (hba x0 hx0 y hya)
    · have h := hb x0 hx0 y0 hy0 hxy
      show x0.timing.delay + (a.finish - 0) + x0.timing.duration ≤
        y0.timing.delay + (a.finish - 0)
      omega

/-! ## Less motion -/

/-- **A change with no travel**, for a reader who asked for less motion. A growth and a line
that draws itself become a change of opacity between the same two numbers: what grew from
nothing fades in, and what shrank to nothing fades out. A change of opacity stays. A shift
becomes the shift that stands at its end from the first moment, and a change of shape the shape
at its end: the thing is at its new place at once, and nothing travels. -/
def Change.reduced : Change → Change
  | .shift _ stop => .shift stop stop
  | .grow start stop => .fade start stop
  | .reveal start stop => .fade start stop
  | .fade start stop => .fade start stop
  | .morph _ stop => .morph stop stop

/-- A reduced change ends at rest where the change does, and only there. -/
theorem Change.reduced_stop_atRest (c : Change) : c.reduced.stop.AtRest ↔ c.stop.AtRest := by
  cases c with
  | shift _ _ => exact Iff.rfl
  | grow _ _ => exact Iff.rfl
  | reveal _ _ => exact Iff.rfl
  | fade _ _ => exact Iff.rfl
  | morph _ _ => exact Iff.rfl

/-- **Nothing travels.** At every eased progress a reduced change sets an opacity, or stands at
the end of the change. -/
theorem Change.reduced_at (c : Change) (e : Int) :
    (∃ shown, c.reduced.at e = .fade shown) ∨ c.reduced.at e = c.stop := by
  cases c with
  | shift _ b =>
    exact Or.inr (congrArg Pose.shift (IVec.ext (Scene.mix_self b.x e) (Scene.mix_self b.y e)))
  | grow a b => exact Or.inl ⟨Scene.mix a b e, rfl⟩
  | reveal a b => exact Or.inl ⟨Scene.mix a b e, rfl⟩
  | fade a b => exact Or.inl ⟨Scene.mix a b e, rfl⟩
  | morph _ b =>
    refine Or.inr ?_
    have hp : ∀ p : IVec, (⟨Scene.mix p.x p.x e, Scene.mix p.y p.y e⟩ : IVec) = p :=
      fun p => IVec.ext (Scene.mix_self p.x e) (Scene.mix_self p.y e)
    have hc : ∀ c : ICubic, ICubic.mix c c e = c := fun c =>
      congr (congr (congr (congrArg ICubic.mk (hp c.p0)) (hp c.p1)) (hp c.p2)) (hp c.p3)
    show (Change.morph b b).at e = Pose.shape b
    rw [Change.at_morph b b e rfl, List.zipWith_self]
    exact congrArg Pose.shape ((List.map_congr_left fun c _ => hc c).trans (List.map_id b))

/-- A track with no travel: the same key and the same timing, with its change reduced. -/
def Track.reduced (tr : Track κ) : Track κ := { tr with change := tr.change.reduced }

/-- A reduced track settles where the track does, and only there. -/
theorem Track.reduced_settles (tr : Track κ) : tr.reduced.Settles ↔ tr.Settles :=
  Change.reduced_stop_atRest tr.change

/-- **The same step with no travel**: each thing changes by its opacity alone, at the same
times, or stands at its end. A writer of CSS puts these tracks inside
`@media (prefers-reduced-motion: reduce)`. -/
def Motion.reduced (m : Motion κ) : Motion κ := m.map Track.reduced

/-- A reduced motion has as many tracks. -/
theorem Motion.length_reduced (m : Motion κ) : m.reduced.length = m.length := List.length_map _

/-- **A reduced motion has the same keys**, track by track. -/
theorem Motion.reduced_keys (m : Motion κ) :
    m.reduced.map (fun tr => tr.key) = m.map (fun tr => tr.key) := List.map_map

/-- **A reduced motion has the same timings**, track by track: the same things at the same
moments. -/
theorem Motion.reduced_timings (m : Motion κ) :
    m.reduced.map (fun tr => tr.timing) = m.map (fun tr => tr.timing) := List.map_map

/-- A track of a reduced motion is a track of the motion, reduced. -/
theorem Motion.mem_reduced (m : Motion κ) {tr : Track κ} (h : tr ∈ m.reduced) :
    ∃ tr0 ∈ m, tr = tr0.reduced := by
  obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp h
  exact ⟨tr0, h0, rfl⟩

/-- **A track that settles still settles.** Where every track of a motion ends at rest, every
track of the reduced motion does. -/
theorem Motion.reduced_settles (m : Motion κ) (hs : ∀ tr ∈ m, tr.Settles) :
    ∀ tr ∈ m.reduced, tr.Settles := by
  intro tr h
  obtain ⟨tr0, h0, rfl⟩ := Motion.mem_reduced m h
  exact (Track.reduced_settles tr0).mpr (hs tr0 h0)

/-- A reduced motion ends when the motion does. -/
theorem Motion.finish_reduced : ∀ m : Motion κ, m.reduced.finish = m.finish
  | [] => rfl
  | tr :: rest =>
    congrArg (max (tr.timing.delay + tr.timing.duration)) (Motion.finish_reduced rest)

/-- **A reduced motion keeps the order.** -/
theorem Motion.reduced_respects (before : κ → κ → Prop) (m : Motion κ)
    (h : m.Respects before) : m.reduced.Respects before := by
  intro a ha b hb hab
  obtain ⟨a0, ha0, rfl⟩ := Motion.mem_reduced m ha
  obtain ⟨b0, hb0, rfl⟩ := Motion.mem_reduced m hb
  exact h a0 ha0 b0 hb0 hab

/-- **The reader who asked for less motion sees the same last picture.** A reduced motion held
inside its step, with proper easings and tracks that settle, has every thing at rest at the
step's end. -/
theorem Motion.reduced_within_atRest (m : Motion κ) (hp : ∀ tr ∈ m, tr.timing.ease.Proper)
    (hs : ∀ tr ∈ m, tr.Settles) : ∀ tr ∈ m.reduced.within, (tr.at 1000).AtRest := by
  refine Motion.within_atRest m.reduced (fun tr h => ?_) (Motion.reduced_settles m hs)
  obtain ⟨tr0, h0, rfl⟩ := Motion.mem_reduced m h
  exact hp tr0 h0

/-! ## A motion in a budget -/

/-- Two parts of a whole, scaled by one factor and rounded down, are no more than the whole,
scaled and rounded down: two floors are no more than the floor of the sum. -/
theorem Motion.scale_add_le (x y z b f : Nat) (h : x + y ≤ z) :
    x * b / f + y * b / f ≤ z * b / f := by
  cases Nat.eq_zero_or_pos f with
  | inl h0 =>
    have hx : x * b / f = 0 := (congrArg (x * b / ·) h0).trans (Nat.div_zero _)
    have hy : y * b / f = 0 := (congrArg (y * b / ·) h0).trans (Nat.div_zero _)
    rw [hx, hy]
    exact Nat.zero_le _
  | inr hf =>
    rw [Nat.le_div_iff_mul_le hf, Nat.add_mul]
    refine Nat.le_trans
      (Nat.add_le_add (Nat.div_mul_le_self (x * b) f) (Nat.div_mul_le_self (y * b) f)) ?_
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right b h

/-- **The motion in a budget**: every delay and every duration scaled by one factor, the budget
over the finish, and rounded down, so that the motion ends by `budget`. A shorter motion is
stretched and a longer one shrunk. With the budget of a thousand each timing is
`Transition.per` of the finish. -/
def Motion.fit (m : Motion κ) (budget : Nat := 1000) : Motion κ :=
  m.map fun tr => { tr with timing := { tr.timing with
    delay := tr.timing.delay * budget / m.finish,
    duration := tr.timing.duration * budget / m.finish } }

/-- With the budget of a thousand, a fitted motion has each timing in per mille of the
finish. -/
theorem Motion.fit_thousand (m : Motion κ) :
    m.fit = m.map fun tr => { tr with timing := tr.timing.per m.finish } := rfl

/-- A fitted motion has the same keys, track by track. -/
theorem Motion.fit_keys (m : Motion κ) (budget : Nat) :
    (m.fit budget).map (fun tr => tr.key) = m.map (fun tr => tr.key) := List.map_map

/-- A fitted motion has the same changes, track by track. -/
theorem Motion.fit_changes (m : Motion κ) (budget : Nat) :
    (m.fit budget).map (fun tr => tr.change) = m.map (fun tr => tr.change) := List.map_map

/-- **A fitted motion ends by its budget.** -/
theorem Motion.fit_finish (m : Motion κ) (budget : Nat) : (m.fit budget).finish ≤ budget := by
  refine Motion.finish_le_of _ budget fun tr h => ?_
  obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp h
  exact Nat.le_trans
    (Motion.scale_add_le tr0.timing.delay tr0.timing.duration _ budget m.finish (Nat.le_refl _))
    (Nat.div_le_of_le_mul (Nat.mul_le_mul_right budget (Motion.finish_le m tr0 h0)))

/-- **A fitted motion keeps the order**: a rounding breaks no order. -/
theorem Motion.fit_respects (before : κ → κ → Prop) (m : Motion κ) (budget : Nat)
    (h : m.Respects before) : (m.fit budget).Respects before := by
  intro a ha b hb hab
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
  exact Motion.scale_add_le _ _ _ budget m.finish (h a0 ha0 b0 hb0 hab)

/-- With proper easings, every track of a fitted motion is over at the budget: the last moment
of a fitted step is the next picture. -/
theorem Motion.fit_done (m : Motion κ) (budget : Nat) (hp : ∀ tr ∈ m, tr.timing.ease.Proper) :
    ∀ tr ∈ m.fit budget, tr.Done budget := by
  intro tr h
  refine ⟨?_, Nat.le_trans (Motion.finish_le _ tr h) (Motion.fit_finish m budget)⟩
  obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp h
  exact hp tr0 h0

/-! ## When an easing has settled -/

/-- The least stop from which the easing reads within `slack` of `1000` at every whole stop
below `n`. -/
def Easing.settledBy.go (e : Easing) (slack : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if (e.at n - 1000).natAbs ≤ slack then Easing.settledBy.go e slack n else n + 1

/-- **The first stop from which the easing stays within `slack` of `1000`**, in per mille: `0`
for an easing that is always that near, and `1001` for one that does not end that near. -/
def Easing.settledBy (e : Easing) (slack : Nat) : Nat := Easing.settledBy.go e slack 1001

/-- From the stop that the search gives up to `n`, the easing reads within the slack. -/
theorem Easing.settledBy.go_holds (e : Easing) (slack : Nat) : ∀ (n p : Nat),
    Easing.settledBy.go e slack n ≤ p → p < n → (e.at p - 1000).natAbs ≤ slack
  | 0, p, _, h => absurd h (Nat.not_lt_zero p)
  | n + 1, p, hs, hp => by
    rw [Easing.settledBy.go] at hs
    cases Nat.decLe (e.at n - 1000).natAbs slack with
    | isTrue hn =>
      rw [if_pos hn] at hs
      cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hp) with
      | inl e1 =>
        rw [e1]
        exact hn
      | inr hlt => exact Easing.settledBy.go_holds e slack n p hs hlt
    | isFalse hn =>
      rw [if_neg hn] at hs
      exact absurd hp (Nat.not_lt_of_le hs)

/-- The stop that the search gives is the first: at the stop before it, the easing reads
farther than the slack. -/
theorem Easing.settledBy.go_first (e : Easing) (slack : Nat) : ∀ n : Nat,
    0 < Easing.settledBy.go e slack n →
    ¬ (e.at (Easing.settledBy.go e slack n - 1) - 1000).natAbs ≤ slack
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, h => by
    rw [Easing.settledBy.go] at h ⊢
    cases Nat.decLe (e.at n - 1000).natAbs slack with
    | isTrue hn =>
      rw [if_pos hn] at h ⊢
      exact Easing.settledBy.go_first e slack n h
    | isFalse hn =>
      rw [if_neg hn]
      exact hn

/-- **From the stop `e.settledBy slack` on, the easing reads within `slack` of `1000`**, at
every whole stop up to the last. -/
theorem Easing.settledBy_holds (e : Easing) (slack p : Nat) (h : e.settledBy slack ≤ p)
    (hp : p ≤ 1000) : (e.at p - 1000).natAbs ≤ slack :=
  Easing.settledBy.go_holds e slack 1001 p h (Nat.lt_succ_of_le hp)

/-- That stop is the first: at the stop before it, the easing reads farther than `slack` from
`1000`. -/
theorem Easing.settledBy_first (e : Easing) (slack : Nat) (h : 0 < e.settledBy slack) :
    ¬ (e.at (e.settledBy slack - 1) - 1000).natAbs ≤ slack :=
  Easing.settledBy.go_first e slack 1001 h

/-! ## A duration for a travel -/

/-- **A duration for a travel**: `least` for none, `rate` more for each unit of the root of the
travel, and never above `greatest`. -/
def Transition.forTravel (least greatest rate travel : Nat) : Nat :=
  min greatest (least + rate * Nat.sqrt travel)

/-- A duration for a travel is never above the greatest. -/
theorem Transition.forTravel_le (least greatest rate travel : Nat) :
    Transition.forTravel least greatest rate travel ≤ greatest := Nat.min_le_left _ _

/-- A duration for a travel is the least at least, where the least is the greatest at most. -/
theorem Transition.le_forTravel (least greatest rate travel : Nat) (h : least ≤ greatest) :
    least ≤ Transition.forTravel least greatest rate travel :=
  Nat.le_min.mpr ⟨h, Nat.le_add_right _ _⟩

/-- No travel takes the least duration, or the greatest where that is less. -/
theorem Transition.forTravel_zero (least greatest rate : Nat) :
    Transition.forTravel least greatest rate 0 = min greatest least := rfl

/-! ## Finite evaluations

The first two are a control of `Motion.delayed_respects`: two tracks that last 300, delayed by
their keys, respect the order of the keys with a gap of 300, and not with a gap of 200. -/

#guard decide (Motion.Respects (fun a b : Nat => a < b)
  (Motion.delayed [⟨0, .grow 0 1000, { duration := 300 }⟩, ⟨1, .grow 0 1000, { duration := 300 }⟩]
    fun k => 300 * k))
#guard !decide (Motion.Respects (fun a b : Nat => a < b)
  (Motion.delayed [⟨0, .grow 0 1000, { duration := 300 }⟩, ⟨1, .grow 0 1000, { duration := 300 }⟩]
    fun k => 200 * k))
#guard Easing.cubicOut.settledBy 10 = 785
#guard Easing.backOut.settledBy 10 = 914
#guard (Easing.stops [0, 500]).settledBy 10 = 1001
#guard (Motion.fit ([⟨1, .grow 0 1000, { delay := 0, duration := 300 }⟩,
  ⟨2, .reveal 0 1000, { delay := 550, duration := 200 }⟩] : Motion Nat)).finish = 999

end Whatwg.Svg.Scene
