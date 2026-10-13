import Whatwg.Svg.Geometry.Spring.Laws

/-!
# Whatwg.Svg.Geometry.Spring.Follow

Owner: a thing that follows its place through any number of interruptions (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`).

`Spring.interrupted` of `Whatwg/Svg/Geometry/Spring.lean` is a step that is interrupted once:
three pictures and one cut. A picture of a running program is interrupted as often as the
program moves. This module is the same for a list of pictures and cuts, and its laws are those
of three pictures, by induction on the list.

- A *leg* is a place and a number of pieces: the thing is sent on toward the place, with the
  place and the momentum it has, and runs that many pieces. The legs of a thing are a list, the
  newest first.
- `Spring.followed s p0 legs i` is the place of a thing that stood at `p0` and went through its
  legs, `i` pieces after the last of them. It is defined as the run it is: each leg starts from
  the two offsets that the leg before left (`Spring.trail`).

What the laws say:

- A thing with no leg stands (`followed_nil`). With one leg more, its place is the place it
  would have had without it, and what a fresh spring let go at rest has gone of the way that
  its place moved (`followed_cons`). That is the law of a target that moves, for any past.
- Two legs are `Spring.interrupted` (`followed_two`).
- **On a critical spring, a gap that every picture has is a gap at every piece**, through any
  number of cuts (`critical_followed_gap`). The two things are sent on at the same cuts, each
  with its own places and its own momentum: their legs are one list, each leg the place of the
  first, the place of the second and the pieces that both run (`firstOf`, `secondOf`). And a
  thing stays in a room that holds every one of its places (`critical_followed_mem`).

What this module does not claim. The laws are of the exact places of a spring. The legs of two
things are cut at the same pieces. No law here brings a place to the frames of a step: a track
of the kit goes straight from one pose to another by one easing, and a place of `followed` is a
sum of responses, which way points or shifts that add would draw.

Every law here depends on `propext`, `Quot.sound` and `Classical.choice` at most.
-/

namespace Whatwg.Svg.Scene

open Whatwg.Svg.Value

namespace Spring

/-- The place a thing is going to after its legs: that of its newest leg, and the place it
started at where it has none. -/
def aim (p0 : Rat) : List (Rat × Nat) → Rat
  | [] => p0
  | leg :: _ => leg.1

/-- **The two offsets that the legs of a thing leave**: its offset from the place it is going
to, and its next one. Each leg moves the target, keeps the place and the momentum, and runs its
pieces. A thing with no leg stands on its place. -/
def trail (s : Spring) (p0 : Rat) : List (Rat × Nat) → Rat × Rat
  | [] => (0, 0)
  | leg :: older =>
    (s.run ((s.trail p0 older).1 - (leg.1 - aim p0 older))
        ((s.trail p0 older).2 - (leg.1 - aim p0 older) * s.rest) leg.2,
      s.run ((s.trail p0 older).1 - (leg.1 - aim p0 older))
        ((s.trail p0 older).2 - (leg.1 - aim p0 older) * s.rest) (leg.2 + 1))

/-- **The place of a thing whose step is interrupted any number of times.** The thing stood at
`p0`. Each leg, the newest first, is a place it was sent on toward and the number of pieces it
ran before the next. This is its place `i` pieces after its last leg. -/
def followed (s : Spring) (p0 : Rat) (legs : List (Rat × Nat)) (i : Nat) : Rat :=
  aim p0 legs + s.run (s.trail p0 legs).1 (s.trail p0 legs).2 i

/-- A thing with no leg stands where it stood. -/
theorem followed_nil (s : Spring) (p0 : Rat) (i : Nat) : s.followed p0 [] i = p0 := by
  show p0 + s.run 0 0 i = p0
  rw [run_still]
  grind

/-- **One leg more.** The place of a thing after a new leg is the place it would have had
without it, and what a fresh spring let go at rest has gone of the way that its place moved.
What was running goes on undisturbed, whatever its past. -/
theorem followed_cons (s : Spring) (p0 p : Rat) (k : Nat) (older : List (Rat × Nat)) (i : Nat) :
    s.followed p0 ((p, k) :: older) i =
      s.followed p0 older (k + i) + (p - aim p0 older) * (1 - s.response (k + i)) := by
  show p + s.run (s.run ((s.trail p0 older).1 - (p - aim p0 older))
        ((s.trail p0 older).2 - (p - aim p0 older) * s.rest) k)
      (s.run ((s.trail p0 older).1 - (p - aim p0 older))
        ((s.trail p0 older).2 - (p - aim p0 older) * s.rest) (k + 1)) i =
    aim p0 older + s.run (s.trail p0 older).1 (s.trail p0 older).2 (k + i) +
      (p - aim p0 older) * (1 - s.response (k + i))
  rw [← run_tail, run_moved]
  grind

/-- **Two legs are one interruption**: a thing let go at rest toward `p1`, and sent on toward
`p2` after `k` pieces. -/
theorem followed_two (s : Spring) (p0 p1 p2 : Rat) (k i : Nat) :
    s.followed p0 [(p2, 0), (p1, k)] i = s.interrupted p0 p1 p2 k i := by
  rw [followed_cons, followed_cons, followed_nil, interrupted_eq, Nat.zero_add]
  show p0 + (p1 - p0) * (1 - s.response (k + i)) + (p2 - p1) * (1 - s.response i) = _
  grind

/-- The legs of the first of two things that are sent on together: each leg of the two is the
place of the first, the place of the second, and the pieces that both run. -/
def firstOf (legs : List (Rat × Rat × Nat)) : List (Rat × Nat) := legs.map fun x => (x.1, x.2.2)

/-- The legs of the second of two things that are sent on together. -/
def secondOf (legs : List (Rat × Rat × Nat)) : List (Rat × Nat) :=
  legs.map fun x => (x.2.1, x.2.2)

/-- The invariant of the law of a gap: the things are at least `g` apart, and by more where the
newest picture has more room and the fresh response has gone. -/
private theorem critical_followed_gap_aux (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (h : (1 + c) * r ≤ 1) (p0 q0 g : Rat) (h0 : p0 + g ≤ q0) (legs : List (Rat × Rat × Nat))
    (hl : ∀ x ∈ legs, x.1 + g ≤ x.2.1) (i : Nat) :
    (aim q0 (secondOf legs) - aim p0 (firstOf legs) - g) * (1 - (critical r c).response i) ≤
      (critical r c).followed q0 (secondOf legs) i -
        (critical r c).followed p0 (firstOf legs) i - g := by
  induction legs generalizing i with
  | nil =>
    have v := (critical_response_calm r c hr hc h i).1
    have m := Rat.mul_nonneg (show 0 ≤ q0 - p0 - g by grind) v
    show (q0 - p0 - g) * (1 - (critical r c).response i) ≤
      (critical r c).followed q0 [] i - (critical r c).followed p0 [] i - g
    rw [followed_nil, followed_nil]
    grind
  | cons x older ih =>
    obtain ⟨pa, pb, k⟩ := x
    have hg : pa + g ≤ pb := hl (pa, pb, k) List.mem_cons_self
    have e := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (k + i)
    have w1 := critical_response_le r c hr hc h (Nat.le_add_left i k)
    have m := Rat.mul_nonneg (show 0 ≤ pb - pa - g by grind)
      (show 0 ≤ (critical r c).response i - (critical r c).response (k + i) by grind)
    show (pb - pa - g) * (1 - (critical r c).response i) ≤
      (critical r c).followed q0 ((pb, k) :: secondOf older) i -
        (critical r c).followed p0 ((pa, k) :: firstOf older) i - g
    rw [followed_cons, followed_cons]
    grind

/-- **A gap that every picture has is a gap at every piece, through any number of cuts.** Two
things take one critical spring and are sent on at the same cuts, each toward its own places
and with its own momentum. Where the second is `g` or more past the first in every picture, it
is `g` or more past it at every piece. The order and the gaps of kept things outlast every
interruption. -/
theorem critical_followed_gap (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1)
    (p0 q0 g : Rat) (h0 : p0 + g ≤ q0) (legs : List (Rat × Rat × Nat))
    (hl : ∀ x ∈ legs, x.1 + g ≤ x.2.1) (i : Nat) :
    (critical r c).followed p0 (firstOf legs) i + g ≤
      (critical r c).followed q0 (secondOf legs) i := by
  have a := critical_followed_gap_aux r c hr hc h p0 q0 g h0 legs hl i
  have t : aim p0 (firstOf legs) + g ≤ aim q0 (secondOf legs) := by
    cases legs with
    | nil => exact h0
    | cons x _ => exact hl x List.mem_cons_self
  have v := critical_response_le_one r c hr hc h i
  have m := Rat.mul_nonneg (show 0 ≤ aim q0 (secondOf legs) - aim p0 (firstOf legs) - g by grind)
    (show 0 ≤ 1 - (critical r c).response i by grind)
  grind

/-- The legs of a thing that stands at one place through the same cuts. -/
def stood (x : Rat) (legs : List (Rat × Nat)) : List (Rat × Nat) := legs.map fun a => (x, a.2)

/-- A thing that is sent on toward the place it stands at, however often, stands. -/
theorem followed_stood (s : Spring) (x : Rat) (legs : List (Rat × Nat)) (i : Nat) :
    s.followed x (stood x legs) i = x := by
  induction legs generalizing i with
  | nil => exact s.followed_nil x i
  | cons a older ih =>
    have t : aim x (stood x older) = x := by
      cases older with
      | nil => rfl
      | cons _ _ => rfl
    show s.followed x ((x, a.2) :: stood x older) i = x
    rw [followed_cons, ih, t]
    grind

/-- **A thing stays in a room that holds every one of its places**, through any number of
cuts, on a critical spring. It may go on away from a new place for a while, and it never goes
past the furthest of the places it had. -/
theorem critical_followed_mem (r c : Rat) (hr : 0 ≤ r) (hc : 0 ≤ c) (h : (1 + c) * r ≤ 1)
    (lo hi p0 : Rat) (h0 : lo ≤ p0 ∧ p0 ≤ hi) (legs : List (Rat × Nat))
    (hl : ∀ a ∈ legs, lo ≤ a.1 ∧ a.1 ≤ hi) (i : Nat) :
    lo ≤ (critical r c).followed p0 legs i ∧ (critical r c).followed p0 legs i ≤ hi := by
  have same : ∀ l : List (Rat × Nat), l.map (fun a => (a.1, a.2)) = l := fun l =>
    (List.map_congr_left fun _ _ => rfl).trans (List.map_id l)
  have a := critical_followed_gap r c hr hc h lo p0 0 (by grind)
    (legs.map fun a => (lo, a.1, a.2)) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := (hl y hy).1
      show lo + 0 ≤ y.1
      grind) i
  have b := critical_followed_gap r c hr hc h p0 hi 0 (by grind)
    (legs.map fun a => (a.1, hi, a.2)) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := (hl y hy).2
      show y.1 + 0 ≤ hi
      grind) i
  have e1 : firstOf (legs.map fun a => (lo, a.1, a.2)) = stood lo legs := List.map_map
  have e2 : secondOf (legs.map fun a => (lo, a.1, a.2)) = legs := List.map_map.trans (same legs)
  have e3 : firstOf (legs.map fun a => (a.1, hi, a.2)) = legs := List.map_map.trans (same legs)
  have e4 : secondOf (legs.map fun a => (a.1, hi, a.2)) = stood hi legs := List.map_map
  rw [e1, e2, followed_stood] at a
  rw [e3, e4, followed_stood] at b
  constructor <;> grind

end Spring

end Whatwg.Svg.Scene