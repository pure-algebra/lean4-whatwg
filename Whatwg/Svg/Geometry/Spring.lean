import Whatwg.Svg.Scene.Motion

/-!
# Whatwg.Svg.Geometry.Spring

Owner: a spring as exact data (slice S17 of `docs/SVG-PACKAGE-PLAN.md`).

A thing on a spring is drawn toward a target and slowed as it goes. A textbook writes its offset
from the target with an exponential and a cosine. Read at evenly spaced moments, the same offsets
obey a rule with two constants, and the rule needs neither:

```
x (i + 2) = p * x (i + 1) - q * x i
```

So a spring here is three rational numbers, and every offset is exact. `p` and `q` are the two
constants. `rest` says what "let go at rest" means for the sampled spring: what is left, one
piece later, of an offset of `1` that was let go at rest. A rational number stands where the
textbook has `e^(-ωh)`, with `h` the length of a piece.

- `Spring.run s x0 x1` is the offsets from two first ones. It takes one multiplication for each
  constant and each piece.
- `Spring.response s` is the run let go at rest from the offset `1`, and `Spring.kick s` the run
  struck at the target. Every run is the two together (`run_split`): the first offset times the
  response, and the *momentum* `x1 - x0 * rest` times the kick.
- `Spring.critical r c` is the spring that comes to rest soonest with no swing: its offsets are
  `(a + b i) rⁱ`. `Spring.under r k c` swings: `k` stands where the textbook has a cosine.
- `Spring.resumed s x0 x1 pieces` is the easing of a thing seen at the offset `x0`, with the next
  offset `x1`: the stops of the run in per mille, from `0` to `1000`. `Spring.easing s pieces` is
  the one let go at rest. CSS writes each as `linear(…)`. `Spring.share` is a stop in exact
  numbers, and `Easing.mille` rounds it to the nearest per mille, as lean4-effect4's two tables
  are rounded.
- `Spring.Calm r x0 x1` is a test on two offsets: the thing is not moving away from its target,
  nor toward it faster than `r` a piece. It is what the laws of a critical spring ask for.

What the laws of this file say:

- A run is linear in its two first offsets (`run_linear`), and obeys the rule (`run_step`). A
  row of numbers that obeys the rule is the run from its first two (`run_eq_of_step`).
- **The tail of a run is a run** from where it stands at the cut (`run_tail`).
- **A target that moves.** A spring is running toward a target, and at a cut the target moves by
  `d`. The thing keeps its place and its momentum. Then its offsets from the new target are the
  old ones less `d` times the response (`run_moved`, and `run_interrupted` at any piece of a
  run). In places (`moved_places`): the interrupted motion is the motion that was running, going
  on as if nothing had happened, and a fresh spring let go at rest that carries the move of the
  target. So nothing jumps in place (`moved_place`). Nothing jumps in speed either: the first
  piece after the cut differs from the old next piece by `d * (1 - rest)`, which is the first
  piece of the fresh spring (`moved_next`).
- **Three pictures.** `Spring.interrupted s p0 p1 p2 k i` is the place of a thing that stood at
  `p0`, was let go at rest toward `p1`, and `k` pieces later was sent on toward `p2`. It is its
  three places weighed by three numbers that sum to `1` (`interrupted_mean`), and at the cut it
  is where the first step had put it (`interrupted_zero`).
- **What every piece takes away.** `Spring.energy s a b` is a square form of two offsets in a
  row, and each piece multiplies it by `q` exactly (`energy_step`, `energy_run`). It is why a
  spring that swings stays inside a bound that shrinks.

The laws of the two kinds of spring and of the easings are in
`Whatwg/Svg/Geometry/Spring/Laws.lean`.

What this module does not claim. A spring here is its offsets at the ends of the pieces, and no
law speaks of a time inside a piece: between two stops an easing is a straight line. "Speed" is
the step from one piece to the next. No law says that a rational `r` is the textbook's
`e^(-ωh)`, which is not rational: a caller chooses a rational number near it, and the laws are of
the spring it chose. `energy` is not the energy of a textbook, which a damped spring does not
lose by a fixed share: it is the square form that does. The second offset of a resumed easing is
the offset one piece of the new step later, and a piece is the duration of the new transition
over the number of pieces: a caller that measures a speed over another length of time brings it
to that piece. A thing that stands on its target has no way to go, so a change with an easing
cannot carry its speed. A resumed easing is for one coordinate. A thing that moves in two
dimensions with one easing keeps the direction of its way, so it takes the momentum along that
way only.

Every law here depends on `propext`, `Quot.sound` and `Classical.choice` at most.
-/

namespace Whatwg.Svg.Scene

/-- The nearest whole number of per mille to a share, a half going up: `1` is `1000`. The kit
rounds a decimal so (`Decimal.ofRat`). -/
def Easing.mille (x : Rat) : Int := (1000 * x + 1 / 2).floor

/-- A spring read at evenly spaced moments. Its offsets from the target obey
`x (i + 2) = p * x (i + 1) - q * x i`. -/
structure Spring where
  /-- The share of the last offset in the next one. -/
  p : Rat
  /-- The share of the offset before it, taken away. A spring that loses its swing has
  `q < 1`. -/
  q : Rat
  /-- What is left after one piece of an offset of `1` that was let go at rest. -/
  rest : Rat
  deriving DecidableEq, Repr, Inhabited

namespace Spring

/-- **The offsets of a spring**, from the first two: `x0` now and `x1` one piece later. Each
piece drops the older offset and makes the next one, so the offset at the piece `i` costs `i`
steps. -/
def run (s : Spring) (x0 x1 : Rat) : Nat → Rat
  | 0 => x0
  | i + 1 => run s x1 (s.p * x1 - s.q * x0) i

/-- The spring let go at rest from the offset `1`. -/
def response (s : Spring) : Nat → Rat := s.run 1 s.rest

/-- The spring struck at its target: it stands at the target, and one piece later at the offset
`1`. -/
def kick (s : Spring) : Nat → Rat := s.run 0 1

/-- **The square form that each piece multiplies by `q`**, of two offsets in a row. -/
def energy (s : Spring) (a b : Rat) : Rat := s.q * (a * a) - s.p * (a * b) + b * b

/-- **The spring that comes to rest soonest with no swing.** `r` is what is left of the offset
from one piece to the next once the speed has died: it stands where the textbook has `e^(-ωh)`.
`c` stands where it has `ωh`, so that the response is `(1 + c i) rⁱ`. -/
def critical (r c : Rat) : Spring := ⟨2 * r, r * r, (1 + c) * r⟩

/-- **A spring that swings.** `r` is the decay of one piece, and `k` stands where the textbook
has the cosine of the angle of one piece: it is from `-1` to `1`, and a rational point of the
circle gives one. `c` sets the rest, `(k + c) * r`. With `k = 1` it is `critical r c`. -/
def under (r k c : Rat) : Spring := ⟨2 * r * k, r * r, (k + c) * r⟩

/-- **The place of a thing whose step is interrupted.** The thing stood at `p0` and was let go
at rest toward `p1`. `k` pieces later its target became `p2`, and the thing kept its place and
its momentum. This is its place `i` pieces after the cut: `p2` and the run from the two offsets
it had at the cut. -/
def interrupted (s : Spring) (p0 p1 p2 : Rat) (k i : Nat) : Rat :=
  p2 + s.run ((p0 - p1) * s.response k - (p2 - p1))
    ((p0 - p1) * s.response (k + 1) - (p2 - p1) * s.rest) i

/-- **A calm thing** on a critical spring of the decay `r`. `x0` is its offset from the target
and `x1` its next one. It is not moving away from its target, and it is not moving toward it
faster than `r` a piece, on either side of the target. A calm thing never passes its target and
never turns back, and its resumed easing stays in range (`critical_stays_calm` and
`critical_resumed_bounded` of `Whatwg/Svg/Geometry/Spring/Laws.lean`). -/
def Calm (r x0 x1 : Rat) : Prop :=
  (0 ≤ x0 ∧ r * x0 ≤ x1 ∧ x1 ≤ x0) ∨ (x0 ≤ 0 ∧ x0 ≤ x1 ∧ x1 ≤ r * x0)

instance (r x0 x1 : Rat) : Decidable (Calm r x0 x1) := inferInstanceAs (Decidable (_ ∨ _))

/-- **The share of the way that is gone at the piece `i`**, for a thing seen at the offset `x0`
with the next offset `x1`: the way is from `x0` to where the run stands at the last piece. It is
`0` at the first piece, and `1` at the last one where the run has moved at all. -/
def share (s : Spring) (x0 x1 : Rat) (pieces i : Nat) : Rat :=
  (x0 - s.run x0 x1 i) / (x0 - s.run x0 x1 pieces)

/-- The stop of the piece `i`: the share of the way that is gone, in per mille. -/
def stop (s : Spring) (x0 x1 : Rat) (pieces i : Nat) : Int :=
  Easing.mille (s.share x0 x1 pieces i)

/-- **The easing of a thing that is seen moving.** The thing is at the offset `x0` from its
target and would be at `x1` one piece later. The stops are the shares of the way that are gone
at each piece, in per mille, so the easing ends at `1000` exactly. A change from the place where
the thing is seen to the target, with this easing, follows the run of the spring. Where the run
has not moved by its last piece every stop is `0`. The spring is run once for each stop. -/
def resumed (s : Spring) (x0 x1 : Rat) (pieces : Nat := 20) : Easing :=
  let way := x0 - s.run x0 x1 pieces
  .stops ((List.range (pieces + 1)).map fun i => Easing.mille ((x0 - s.run x0 x1 i) / way))

/-- **The easing of a spring let go at rest**: the stops of its response, scaled to end at
`1000`. -/
def easing (s : Spring) (pieces : Nat := 20) : Easing := s.resumed 1 s.rest pieces

/-! ## The rule -/

/-- A run starts at its first offset. -/
theorem run_zero (s : Spring) (x0 x1 : Rat) : s.run x0 x1 0 = x0 := rfl

/-- One piece later a run is at its second offset. -/
theorem run_one (s : Spring) (x0 x1 : Rat) : s.run x0 x1 1 = x1 := rfl

/-- A run one piece later is the run from the next two offsets. -/
theorem run_succ (s : Spring) (x0 x1 : Rat) (i : Nat) :
    s.run x0 x1 (i + 1) = s.run x1 (s.p * x1 - s.q * x0) i := rfl

/-- A response starts at the offset `1`. -/
theorem response_zero (s : Spring) : s.response 0 = 1 := rfl

/-- One piece later a response is at the rest of the spring. -/
theorem response_one (s : Spring) : s.response 1 = s.rest := rfl

/-- A kick starts at the target. -/
theorem kick_zero (s : Spring) : s.kick 0 = 0 := rfl

/-- One piece later a kick is at the offset `1`. -/
theorem kick_one (s : Spring) : s.kick 1 = 1 := rfl

/-- **A run obeys the rule of its spring**, at every piece. -/
theorem run_step (s : Spring) (x0 x1 : Rat) (i : Nat) :
    s.run x0 x1 (i + 2) = s.p * s.run x0 x1 (i + 1) - s.q * s.run x0 x1 i := by
  induction i generalizing x0 x1 with
  | zero => rfl
  | succ i ih => exact ih x1 (s.p * x1 - s.q * x0)

/-- Equal first offsets give equal runs. -/
theorem run_congr (s : Spring) {x0 x1 y0 y1 : Rat} (h0 : x0 = y0) (h1 : x1 = y1) (i : Nat) :
    s.run x0 x1 i = s.run y0 y1 i := by
  rw [h0, h1]

/-- **A row of numbers that obeys the rule is the run from its first two.** A closed form is
proved so: it is checked at two pieces and against the rule. -/
theorem run_eq_of_step (s : Spring) (f : Nat → Rat)
    (h : ∀ i, f (i + 2) = s.p * f (i + 1) - s.q * f i) (i : Nat) : s.run (f 0) (f 1) i = f i := by
  have g : ∀ i k, s.run (f k) (f (k + 1)) i = f (k + i) := by
    intro i
    induction i with
    | zero => exact fun k => rfl
    | succ i ih =>
      intro k
      show s.run (f (k + 1)) (s.p * f (k + 1) - s.q * f k) i = f (k + (i + 1))
      rw [← h k]
      exact (ih (k + 1)).trans (congrArg f (by omega))
  exact (g i 0).trans (congrArg f (Nat.zero_add i))

/-! ## A run is linear -/

/-- **A run is linear in its two first offsets.** -/
theorem run_linear (s : Spring) (a b x0 x1 y0 y1 : Rat) (i : Nat) :
    s.run (a * x0 + b * y0) (a * x1 + b * y1) i = a * s.run x0 x1 i + b * s.run y0 y1 i := by
  induction i generalizing x0 x1 y0 y1 with
  | zero => rfl
  | succ i ih =>
    have e : s.p * (a * x1 + b * y1) - s.q * (a * x0 + b * y0) =
        a * (s.p * x1 - s.q * x0) + b * (s.p * y1 - s.q * y0) := by grind
    show s.run (a * x1 + b * y1) (s.p * (a * x1 + b * y1) - s.q * (a * x0 + b * y0)) i =
      a * s.run x1 (s.p * x1 - s.q * x0) i + b * s.run y1 (s.p * y1 - s.q * y0) i
    rw [e]
    exact ih x1 (s.p * x1 - s.q * x0) y1 (s.p * y1 - s.q * y0)

/-- A run from offsets that are `a` times as far is `a` times as far at every piece. So a thing
left of its target moves as its mirror image does right of it. -/
theorem run_scale (s : Spring) (a x0 x1 : Rat) (i : Nat) :
    s.run (a * x0) (a * x1) i = a * s.run x0 x1 i :=
  (s.run_congr (by grind) (by grind) i).trans
    ((s.run_linear a 0 x0 x1 0 0 i).trans (by grind))

/-- The run of the mirror image is the mirror image of the run. -/
theorem run_neg (s : Spring) (x0 x1 : Rat) (i : Nat) : s.run (-x0) (-x1) i = -s.run x0 x1 i :=
  (s.run_congr (by grind) (by grind) i).trans ((s.run_scale (-1) x0 x1 i).trans (by grind))

/-- The run from the sums of two pairs of offsets is the sum of the two runs. -/
theorem run_add (s : Spring) (x0 x1 y0 y1 : Rat) (i : Nat) :
    s.run (x0 + y0) (x1 + y1) i = s.run x0 x1 i + s.run y0 y1 i :=
  (s.run_congr (by grind) (by grind) i).trans
    ((s.run_linear 1 1 x0 x1 y0 y1 i).trans (by grind))

/-- A thing at its target with no speed stays there. -/
theorem run_still (s : Spring) (i : Nat) : s.run 0 0 i = 0 :=
  (s.run_congr (by grind) (by grind) i).trans ((s.run_scale 0 0 0 i).trans (by grind))

/-- **Every run is a response and a kick.** The first offset times the spring let go at rest,
and the momentum `x1 - x0 * rest` times the spring struck at its target. A thing with no
momentum is at rest in the spring's own sense: it moves as the response does. -/
theorem run_split (s : Spring) (x0 x1 : Rat) (i : Nat) :
    s.run x0 x1 i = x0 * s.response i + (x1 - x0 * s.rest) * s.kick i :=
  (s.run_congr (by grind) (by grind) i).trans
    (s.run_linear x0 (x1 - x0 * s.rest) 1 s.rest 0 1 i)

/-! ## A cut -/

/-- **The tail of a run is a run**: from the piece `k` on, the offsets are those of the run that
starts where this one stands at `k`, with the next offset it has there. A step that is cut needs
two numbers of each thing and nothing of its past. -/
theorem run_tail (s : Spring) (x0 x1 : Rat) (k i : Nat) :
    s.run x0 x1 (k + i) = s.run (s.run x0 x1 k) (s.run x0 x1 (k + 1)) i := by
  induction k generalizing x0 x1 with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ k ih =>
    rw [Nat.add_right_comm]
    exact ih x1 (s.p * x1 - s.q * x0)

/-- **A target that moves.** A thing is at the offset `x0` and would be at `x1` one piece
later. Its target moves by `d`, and the thing keeps its place and its momentum: its offsets are
then `x0 - d` and `x1 - d * rest`. Its run toward the new target is the old run less `d` times
the response. -/
theorem run_moved (s : Spring) (x0 x1 d : Rat) (i : Nat) :
    s.run (x0 - d) (x1 - d * s.rest) i = s.run x0 x1 i - d * s.response i :=
  (s.run_congr (by grind) (by grind) i).trans
    ((s.run_linear 1 (-d) x0 x1 1 s.rest i).trans (by
      show 1 * s.run x0 x1 i + -d * s.run 1 s.rest i = s.run x0 x1 i - d * s.run 1 s.rest i
      grind))

/-- **A run that is interrupted.** A spring runs from `x0` and `x1`. At the piece `k` its
target moves by `d`, and the thing keeps its place and its momentum. From there on its offsets
from the new target are the offsets it would have had, less `d` times a response that starts at
the cut. -/
theorem run_interrupted (s : Spring) (x0 x1 d : Rat) (k i : Nat) :
    s.run (s.run x0 x1 k - d) (s.run x0 x1 (k + 1) - d * s.rest) i =
      s.run x0 x1 (k + i) - d * s.response i := by
  rw [run_moved, ← run_tail]

/-- **The interrupted motion, in places.** The target was at `target` and is now `d` further.
The thing's place at the piece `i` after the cut is the place the old motion would have had,
and what a fresh spring let go at rest has gone of the way `d`. The old motion goes on
undisturbed, and the fresh one carries the move of the target. -/
theorem moved_places (s : Spring) (target x0 x1 d : Rat) (i : Nat) :
    target + d + s.run (x0 - d) (x1 - d * s.rest) i =
      target + s.run x0 x1 i + d * (1 - s.response i) := by
  rw [run_moved]
  grind

/-- **Nothing jumps in place**: at the cut the thing is where it was. -/
theorem moved_place (s : Spring) (target x0 x1 d : Rat) :
    target + d + s.run (x0 - d) (x1 - d * s.rest) 0 = target + x0 := by
  show target + d + (x0 - d) = target + x0
  grind

/-- **Nothing jumps in speed**: one piece after the cut the thing is where the old motion would
have put it, and `d * (1 - rest)` further. That is the first piece of a spring let go at rest
over the way `d`, and it is small where the pieces are short. -/
theorem moved_next (s : Spring) (target x0 x1 d : Rat) :
    target + d + s.run (x0 - d) (x1 - d * s.rest) 1 = target + x1 + d * (1 - s.rest) := by
  show target + d + (x1 - d * s.rest) = target + x1 + d * (1 - s.rest)
  grind

/-! ## Three pictures -/

/-- A thing let go at rest from the offset `a` moves as `a` times the response. -/
theorem run_rest (s : Spring) (a : Rat) (i : Nat) : s.run a (a * s.rest) i = a * s.response i :=
  (s.run_congr (by grind) rfl i).trans (s.run_scale a 1 s.rest i)

/-- **An interrupted step is two responses.** The place of the thing is its last target, what
is left of its first way by a response that is `k` pieces old, and what is left of its second
way by a fresh one. -/
theorem interrupted_eq (s : Spring) (p0 p1 p2 : Rat) (k i : Nat) :
    s.interrupted p0 p1 p2 k i =
      p2 + (p0 - p1) * s.response (k + i) + (p1 - p2) * s.response i := by
  have e := s.run_interrupted (p0 - p1) ((p0 - p1) * s.rest) (p2 - p1) k i
  rw [run_rest, run_rest, run_rest] at e
  show p2 + s.run ((p0 - p1) * s.response k - (p2 - p1))
    ((p0 - p1) * s.response (k + 1) - (p2 - p1) * s.rest) i = _
  rw [e]
  grind

/-- **The place of an interrupted thing is its three pictures, weighed.** The three weights
are the old response, the fresh response less the old one, and what the fresh response has
gone. They sum to `1`. Where the response never rises and stays from `0` to `1`, as that of a
critical spring does, no weight is negative: the thing is at a mean of its three places. -/
theorem interrupted_mean (s : Spring) (p0 p1 p2 : Rat) (k i : Nat) :
    s.interrupted p0 p1 p2 k i =
      p0 * s.response (k + i) + p1 * (s.response i - s.response (k + i)) +
        p2 * (1 - s.response i) := by
  rw [interrupted_eq]
  grind

/-- **At the cut an interrupted thing is where its first step had put it.** -/
theorem interrupted_zero (s : Spring) (p0 p1 p2 : Rat) (k : Nat) :
    s.interrupted p0 p1 p2 k 0 = p1 + (p0 - p1) * s.response k := by
  show p2 + ((p0 - p1) * s.response k - (p2 - p1)) = p1 + (p0 - p1) * s.response k
  grind

/-! ## What every piece takes away -/

/-- **One piece multiplies the square form by `q`.** -/
theorem energy_step (s : Spring) (a b : Rat) :
    s.energy b (s.p * b - s.q * a) = s.q * s.energy a b := by
  simp only [energy]
  grind

/-- **After `i` pieces the square form of a run is `q ^ i` times what it was.** With `q < 1`
it falls by a fixed share each piece, whatever the spring does on the way. -/
theorem energy_run (s : Spring) (x0 x1 : Rat) (i : Nat) :
    s.energy (s.run x0 x1 i) (s.run x0 x1 (i + 1)) = s.q ^ i * s.energy x0 x1 := by
  induction i generalizing x0 x1 with
  | zero =>
    show s.energy x0 x1 = s.q ^ 0 * s.energy x0 x1
    rw [Rat.pow_zero, Rat.one_mul]
  | succ i ih =>
    have e := ih x1 (s.p * x1 - s.q * x0)
    rw [energy_step] at e
    rw [Rat.pow_succ, Rat.mul_assoc]
    exact e

/-! ## The stops of an easing -/

/-- The stops of a resumed easing, one by one. -/
theorem resumed_stops (s : Spring) (x0 x1 : Rat) (pieces : Nat) :
    s.resumed x0 x1 pieces = .stops ((List.range (pieces + 1)).map (s.stop x0 x1 pieces)) := rfl

/-- The easing of a spring is the resumed easing of a thing let go at rest. -/
theorem easing_eq (s : Spring) (pieces : Nat) : s.easing pieces = s.resumed 1 s.rest pieces := rfl

end Spring

end Whatwg.Svg.Scene
