import Whatwg.Svg.Scene.Motion

/-!
# Whatwg.Svg.Scene.Between

Owner: what holds at every moment of a step (slice S13 of `docs/SVG-PACKAGE-PLAN.md`; ruling
SV-72).

A motion means a change. Each moment between two pictures is a picture too, and a reader reads
it. A relation that neither picture has must not appear between them: two boxes of one rank over
each other, or a thing outside the room that both pictures keep it in. This module says which
facts of two still pictures are facts of every moment between them, and on what terms.

It counts as `Whatwg/Svg/Scene/Motion.lean` does. A place is a whole number, a progress is in
per mille, and `mix` rounds down. Every law here holds with the rounding.

- Mixing. A gap of both pictures along one axis is a gap of every moment (`mix_gap`). A bound of
  both pictures is a bound of every moment (`mix_le`, `le_mix`, `mix_mem`). These ask that the
  eased progress is in range, from `0` to `1000`. A fixed step at both ends is that step at
  every moment, whatever the progress (`mix_add_right`). A thing that grows from nothing has the
  eased progress as its size (`mix_grow`).
- Kept relations. `Kept R` says that every moment between two pictures that have `R` has `R`.
  "Left of, by `g`", "above, by `g`" and "the fixed step `d` from" are kept (`Kept.leftOf`,
  `Kept.above`, `Kept.step`), and so are two kept relations together (`Kept.and`).
- Easings in range. `Easing.bounded` is a test on the data of an easing: every value of the
  stops is in range, or the two heights of the cubic are. An easing that passes it reads in
  range at every share of the progress (`Easing.bounded_of`, `Easing.bounded_at`).
  `Easing.over` is how far past its end an easing goes at most (`Easing.of_le_over`,
  `Easing.at_le_over`).
- Every moment of a step. At every moment a transition reads its easing at a share of the
  progress (`Transition.at_share`). So it reads in range where its easing passes the test
  (`Transition.bounded_at`), and no more than `over` past the end (`Transition.at_le_over`).
  **The law of the module** is `Kept.moment`: two things that take one transition, with an
  easing that passes the test, have at every moment each kept relation that they have in both
  pictures.
- Growing past the size. `grownLow` and `grownHigh` are the two ends of a span drawn at a size
  in per mille about its middle. They are in two-thousandths of a unit, where nothing is
  rounded. Two spans a gap `g` apart, each grown to `1000 + o` per mille at most, stay apart
  where `(w₁ + w₂) * o ≤ 2000 * g` (`grow_apart`). They share no whole unit where
  `(w₁ + w₂) * o ≤ 2000 * (g - 1)` (`grow_clear`).

Three rules of craft follow. The controls at the end of this file are pictures with numbers
where a rule is broken and a gap is lost.

- Stagger the things that enter, and never the things that are kept. `Kept.moment` gives the two
  things one transition. Two kept things with two delays have two eased progresses at one
  moment, and one may pass the other. A thing that enters only grows, and `grow_clear` asks each
  size for a bound and for nothing else.
- An easing that passes its end is for a size, and never for a place. `mix_gap` asks for
  `e ≤ 1000`. A place mixed past `1000` goes past its place in the next picture, into the gap. A
  size that goes past its end by `over` needs the room that `grow_clear` states.
- A kept thing travels straight. The laws are of `mix`, the straight way from one place to the
  other, coordinate by coordinate. A thing on an arc may leave the room between its two places
  along one axis, and no law here holds it.

A relation along one axis is kept. "Beside or above" is not: a pair that is side by side before
and one above the other after can meet on the way. So a step is known to be safe for a pair
where one axis holds the pair apart in both pictures.

What this module does not claim. `Easing.bounded` is a test that suffices: no law says that an
easing in range passes it. `Easing.over` is a bound and not the least one. It measures the high
side only: an easing that goes below its start fails the test, and nothing here says by how
much. The laws are of the kit's own reading, `Track.at`. What a host draws between two keyframes
is an observation of that host. The pairs that no one axis holds apart in both pictures are not
listed here.

`mix_add_right` is the law that the design note calls `mix_add`: `Motion/Laws.lean` has another
law of that name. This module imports `Motion.lean` only, and keeps its own copies of two laws of
`Motion/Laws.lean` as private lemmas (`mix_same` for `mix_self`, `Easing.of_mille` for
`Easing.of_thousand`).

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-! ## Mixing -/

/-- A value mixed with itself is that value, at every progress. `Motion/Laws.lean` has this law
as `mix_self`. This module does not import that one, and keeps its own copy. -/
private theorem mix_same (u e : Int) : mix u u e = u := by
  simp only [mix, Int.sub_self, Int.zero_mul, Int.zero_ediv, Int.add_zero]

/-- **A fixed step at both ends is that step at every moment.** A thing that stands the step `c`
from another in both pictures stands that step from it at every eased progress, in range or
not: the step is a whole number, and the rounding does not see it. -/
theorem mix_add_right (u v c e : Int) : mix (u + c) (v + c) e = mix u v e + c := by
  show v + c + (u + c - (v + c)) * (1000 - e) / 1000 = v + (u - v) * (1000 - e) / 1000 + c
  rw [Int.add_sub_add_right, Int.add_right_comm]

/-- **A gap of both pictures is a gap of every moment.** Where the second value is `g` or more
past the first in both pictures, it is `g` or more past it at every eased progress in range,
with the rounding. A negative `g` is an overlap, and it never grows.

With `w = 1000 - e` and `aᵢ = uᵢ - vᵢ`, each value is `vᵢ` and `aᵢ * w / 1000` rounded down.
Since `0 ≤ w ≤ 1000`, `a₁ * w` is no more than `a₂ * w` and `v₂ - v₁ - g` thousands, and the
rounding takes whole thousands out as they are. Both premises on `e` are needed, as the first
two controls of this file show. -/
theorem mix_gap (u₁ v₁ u₂ v₂ g e : Int) (h0 : 0 ≤ e) (h1 : e ≤ 1000) (hu : u₁ + g ≤ u₂)
    (hv : v₁ + g ≤ v₂) : mix u₁ v₁ e + g ≤ mix u₂ v₂ e := by
  have ha : (u₁ - v₁) * (1000 - e) ≤ (u₂ - v₂ + (v₂ - v₁ - g)) * (1000 - e) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hd : (v₂ - v₁ - g) * (1000 - e) ≤ (v₂ - v₁ - g) * 1000 :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  rw [Int.add_mul] at ha
  show v₁ + (u₁ - v₁) * (1000 - e) / 1000 + g ≤ v₂ + (u₂ - v₂) * (1000 - e) / 1000
  omega

/-- A value that is no more than `hi` in both pictures is no more than `hi` at every moment. -/
theorem mix_le (hi u v e : Int) (h0 : 0 ≤ e) (h1 : e ≤ 1000) (hu : u ≤ hi) (hv : v ≤ hi) :
    mix u v e ≤ hi := by
  have h := mix_gap u v hi hi 0 e h0 h1 (by omega) (by omega)
  rw [mix_same, Int.add_zero] at h
  exact h

/-- A value that is no less than `lo` in both pictures is no less than `lo` at every moment. -/
theorem le_mix (lo u v e : Int) (h0 : 0 ≤ e) (h1 : e ≤ 1000) (hu : lo ≤ u) (hv : lo ≤ v) :
    lo ≤ mix u v e := by
  have h := mix_gap lo lo u v 0 e h0 h1 (by omega) (by omega)
  rw [mix_same, Int.add_zero] at h
  exact h

/-- **A value between `lo` and `hi` in both pictures is between them at every moment.** A thing
inside a room in both pictures does not leave it on the way. -/
theorem mix_mem (lo hi u v e : Int) (h0 : 0 ≤ e) (h1 : e ≤ 1000) (hu : lo ≤ u ∧ u ≤ hi)
    (hv : lo ≤ v ∧ v ≤ hi) : lo ≤ mix u v e ∧ mix u v e ≤ hi :=
  ⟨le_mix lo u v e h0 h1 hu.1 hv.1, mix_le hi u v e h0 h1 hu.2 hv.2⟩

/-- A thing that grows from nothing to its size has the eased progress as its size: what
`Change.grow 0 1000` sets. So a size goes past `1000` exactly as far as its easing does. -/
theorem mix_grow (e : Int) : mix 0 1000 e = e := by
  show 1000 + (0 - 1000) * (1000 - e) / 1000 = e
  omega

/-! ## Relations that every moment keeps -/

/-- A relation of two places that every moment between two pictures keeps. Where `a` and `b`
have it in one picture and `a'` and `b'` in the next, the two places on the straight way have
it at every eased progress in range. The two things take one eased progress. -/
def Kept (R : IVec → IVec → Prop) : Prop :=
  ∀ {a a' b b' : IVec} {e : Int}, 0 ≤ e → e ≤ 1000 → R a b → R a' b' →
    R ⟨mix a.x a'.x e, mix a.y a'.y e⟩ ⟨mix b.x b'.x e, mix b.y b'.y e⟩

/-- "Left of, by `g`" is kept: a gap along the first axis. -/
theorem Kept.leftOf (g : Int) : Kept (fun a b => a.x + g ≤ b.x) := by
  intro a a' b b' e h0 h1 h h'
  exact mix_gap a.x a'.x b.x b'.x g e h0 h1 h h'

/-- "Above, by `g`" is kept: a gap along the second axis. -/
theorem Kept.above (g : Int) : Kept (fun a b => a.y + g ≤ b.y) := by
  intro a a' b b' e h0 h1 h h'
  exact mix_gap a.y a'.y b.y b'.y g e h0 h1 h h'

/-- "The fixed step `d` from" is kept: the end of a line on its box, a label on its mark. -/
theorem Kept.step (d : IVec) : Kept (fun a b => b = a + d) := by
  intro a a' b b' e _ _ h h'
  subst h
  subst h'
  exact IVec.ext (mix_add_right a.x a'.x d.x e) (mix_add_right a.y a'.y d.y e)

/-- Two kept relations together are kept: a thing inside a box is right of one side, left of
another, below a third and above a fourth. -/
theorem Kept.and {R S : IVec → IVec → Prop} (hR : Kept R) (hS : Kept S) :
    Kept (fun a b => R a b ∧ S a b) := by
  intro a a' b b' e h0 h1 h h'
  exact ⟨hR h0 h1 h.1 h'.1, hS h0 h1 h.2 h'.2⟩

/-! ## Easings that stay in range -/

/-- **The easing stays in range**: a test on its data. Every value of the stops is from `0` to
`1000`, or the two heights of the cubic are. An easing that passes reads from `0` to `1000` at
every share of the progress (`Easing.bounded_of`). The test suffices, and no law says that an
easing in range passes it. -/
def Easing.bounded : Easing → Bool
  | .stops values => values.all fun v => 0 ≤ v && v ≤ 1000
  | .cubic y1 y2 => 0 ≤ y1 && y1 ≤ 1000 && 0 ≤ y2 && y2 ≤ 1000

/-- How far past its end the easing goes at most, in per mille: the greatest value of the
stops, or the greater height of the cubic, less `1000`, and `0` where that is negative. It is a
bound and not the least one (`Easing.of_le_over`). -/
def Easing.over : Easing → Nat
  | .stops values => (values.foldl max 1000 - 1000).toNat
  | .cubic y1 y2 => (max 1000 (max y1 y2) - 1000).toNat

/-! ### Stops: a straight line between two values -/

/-- What holds of a default and of every member of a list holds of what is read at any place. -/
theorem getD_of_all {α : Type} (P : α → Prop) (l : List α) (i : Nat) (d : α) (hd : P d)
    (hl : ∀ v ∈ l, P v) : P (l.getD i d) := by
  show P ((l[i]?).getD d)
  cases h : l[i]? with
  | none => exact hd
  | some v => exact hl v (List.mem_of_getElem? h)

/-- What holds of a default and of every member of a list holds of its last value. -/
theorem last_of_all {α : Type} (P : α → Prop) (l : List α) (d : α) (hd : P d)
    (hl : ∀ v ∈ l, P v) : P (l.getLast?.getD d) := by
  rw [List.getLast?_eq_getElem?]
  exact getD_of_all P l (l.length - 1) d hd hl

/-- A quotient rounded down is no more than `b`, where the dividend is no more than `b` times
the divisor: with the divisor `0` too, where the quotient is `0`. -/
private theorem ediv_le_of_le (a b c : Int) (hc : 0 ≤ c) (hb : 0 ≤ b) (h : a ≤ b * c) :
    a / c ≤ b := by
  rcases Int.lt_or_eq_of_le hc with hc | hc
  · exact Int.ediv_le_of_le_mul hc h
  · rw [← hc, Int.ediv_zero]
    exact hb

/-- The share `r / d` of `c`, rounded down, is no more than what `0` and `c` are no more than.
With the divisor `0` the share is `0`. -/
private theorem share_le (c r d m : Int) (hr : 0 ≤ r) (hd : r ≤ d ∨ d = 0) (hm : 0 ≤ m)
    (hc : c ≤ m) : c * r / d ≤ m := by
  rcases hd with hd | hd
  · exact ediv_le_of_le (c * r) m d (Int.le_trans hr hd) hm
      (Int.le_trans (Int.mul_le_mul_of_nonneg_right hc hr) (Int.mul_le_mul_of_nonneg_left hd hm))
  · rw [hd, Int.ediv_zero]
    exact hm

/-- The share `r / d` of `c`, rounded down, is no less than what `0` and `c` are no less than.
With the divisor `0` the share is `0`. -/
private theorem le_share (c r d m : Int) (hr : 0 ≤ r) (hd : r ≤ d ∨ d = 0) (hm : m ≤ 0)
    (hc : m ≤ c) : m ≤ c * r / d := by
  rcases hd with hd | hd
  · rcases Int.lt_or_eq_of_le (Int.le_trans hr hd) with h | h
    · exact Int.le_ediv_of_mul_le h (Int.le_trans (Int.mul_le_mul_of_nonpos_left hm hd)
        (Int.mul_le_mul_of_nonneg_right hc hr))
    · rw [← h, Int.ediv_zero]
      exact hm
  · rw [hd, Int.ediv_zero]
    exact hm

/-- A point of the straight line from `a` to `b`, rounded down, is no more than what both are
no more than. -/
private theorem line_le (hi a b r d : Int) (hr : 0 ≤ r) (hd : r ≤ d ∨ d = 0) (ha : a ≤ hi)
    (hb : b ≤ hi) : a + (b - a) * r / d ≤ hi :=
  Int.add_le_of_le_sub_left
    (share_le (b - a) r d (hi - a) hr hd (Int.sub_nonneg_of_le ha) (Int.sub_le_sub_right hb a))

/-- A point of the straight line from `a` to `b`, rounded down, is no less than what both are
no less than. -/
private theorem le_line (lo a b r d : Int) (hr : 0 ≤ r) (hd : r ≤ d ∨ d = 0) (ha : lo ≤ a)
    (hb : lo ≤ b) : lo ≤ a + (b - a) * r / d :=
  Int.le_add_of_sub_left_le
    (le_share (b - a) r d (lo - a) hr hd (Int.sub_nonpos_of_le ha) (Int.sub_le_sub_right hb a))

/-- What is left of a number after its whole shares of `den` is no more than `den`, where `den`
is not `0`. -/
private theorem rest_le (n den : Nat) :
    ((n - den * (n / den) : Nat) : Int) ≤ (den : Int) ∨ (den : Int) = 0 := by
  cases den with
  | zero => exact Or.inr rfl
  | succ k =>
    refine Or.inl (Int.ofNat_le.mpr ?_)
    rw [← Nat.mod_def]
    exact Nat.le_of_lt (Nat.mod_lt n (Nat.succ_pos k))

namespace Easing

/-- Stops read no more than what `0` and every value are no more than, at every share. A
missing value reads as `0`, so `0` is one of the things to bound. -/
private theorem stopsOf_le (hi : Int) (values : List Int) (num den : Nat) (h0 : 0 ≤ hi)
    (h : ∀ v ∈ values, v ≤ hi) : stopsOf values num den ≤ hi := by
  have hlast : values.getLast?.getD 0 ≤ hi := last_of_all (· ≤ hi) values 0 h0 h
  have hget : ∀ i, values.getD i (values.getLast?.getD 0) ≤ hi := fun i =>
    getD_of_all (· ≤ hi) values i _ hlast h
  exact line_le hi _ _ _ _ (Int.natCast_nonneg _) (rest_le _ den) (hget _) (hget _)

/-- Stops read no less than what `0` and every value are no less than, at every share. -/
private theorem le_stopsOf (lo : Int) (values : List Int) (num den : Nat) (h0 : lo ≤ 0)
    (h : ∀ v ∈ values, lo ≤ v) : lo ≤ stopsOf values num den := by
  have hlast : lo ≤ values.getLast?.getD 0 := last_of_all (lo ≤ ·) values 0 h0 h
  have hget : ∀ i, lo ≤ values.getD i (values.getLast?.getD 0) := fun i =>
    getD_of_all (lo ≤ ·) values i _ hlast h
  exact le_line lo _ _ _ _ (Int.natCast_nonneg _) (rest_le _ den) (hget _) (hget _)

end Easing

/-! ### Cubics: four weights that make the cube of the whole -/

/-- A square is a product. -/
private theorem sq_eq (x : Int) : x ^ 2 = x * x := by
  rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

/-- A cube is a product. -/
private theorem cube_eq (x : Int) : x ^ 3 = x * (x * x) := by
  rw [Int.pow_succ, sq_eq, Int.mul_comm]

/-- The cube of a sum is the sum of four weights: one cube, each mixed product three times, and
the other cube. No product is written with a numeral, so that each is one unknown of the linear
arithmetic that sums them. -/
private theorem add_cube (a b : Int) :
    (a + b) * ((a + b) * (a + b)) =
      a * (a * a) + (a * (a * b) + a * (a * b) + a * (a * b)) +
        (a * (b * b) + a * (b * b) + a * (b * b)) + b * (b * b) := by
  simp only [Int.add_mul, Int.mul_add, Int.mul_comm b a, Int.mul_left_comm b a]
  omega

/-- The numerator of a cubic at the progress `q` of `q + s` is no more than `m` times the cube
of the whole, where the two heights and the end `1000` are no more than `m`. The numerator
shares `0`, the two heights and `1000` by the four weights of the cube, and no weight is
negative. -/
private theorem cubic_le (y1 y2 m q s : Int) (hq : 0 ≤ q) (hs : 0 ≤ s) (h1 : y1 ≤ m)
    (h2 : y2 ≤ m) (hm : 1000 ≤ m) :
    3 * y1 * q * s ^ 2 + 3 * y2 * q ^ 2 * s + 1000 * q ^ 3 ≤ m * (q + s) ^ 3 := by
  have w0 : 0 ≤ s * (s * s) := Int.mul_nonneg hs (Int.mul_nonneg hs hs)
  have w1 : 0 ≤ q * (s * s) := Int.mul_nonneg hq (Int.mul_nonneg hs hs)
  have w2 : 0 ≤ q * (q * s) := Int.mul_nonneg hq (Int.mul_nonneg hq hs)
  have w3 : 0 ≤ q * (q * q) := Int.mul_nonneg hq (Int.mul_nonneg hq hq)
  have f0 : 0 ≤ m * (s * (s * s)) := Int.mul_nonneg (Int.le_trans (by decide) hm) w0
  have f1 : y1 * (q * (s * s)) ≤ m * (q * (s * s)) := Int.mul_le_mul_of_nonneg_right h1 w1
  have f2 : y2 * (q * (q * s)) ≤ m * (q * (q * s)) := Int.mul_le_mul_of_nonneg_right h2 w2
  have f3 : 1000 * (q * (q * q)) ≤ m * (q * (q * q)) := Int.mul_le_mul_of_nonneg_right hm w3
  simp only [sq_eq, cube_eq, Int.mul_assoc]
  rw [add_cube]
  simp only [Int.mul_add]
  omega

/-- The numerator of a cubic is not negative, where its two heights are not. -/
private theorem cubic_nonneg (y1 y2 q s : Int) (hq : 0 ≤ q) (hs : 0 ≤ s) (h1 : 0 ≤ y1)
    (h2 : 0 ≤ y2) : 0 ≤ 3 * y1 * q * s ^ 2 + 3 * y2 * q ^ 2 * s + 1000 * q ^ 3 :=
  Int.add_nonneg
    (Int.add_nonneg
      (Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by decide) h1) hq) (Int.pow_nonneg hs))
      (Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by decide) h2) (Int.pow_nonneg hq)) hs))
    (Int.mul_nonneg (by decide) (Int.pow_nonneg hq))

namespace Easing

/-- A cubic reads no more than what its two heights and its end `1000` are no more than, at
every share that is no more than the whole. -/
private theorem cubicOf_le (m y1 y2 : Int) (num den : Nat) (hn : num ≤ den) (h1 : y1 ≤ m)
    (h2 : y2 ≤ m) (hm : 1000 ≤ m) : cubicOf y1 y2 num den ≤ m := by
  have hs : (0 : Int) ≤ (den : Int) - num := Int.sub_nonneg_of_le (Int.ofNat_le.mpr hn)
  have h := cubic_le y1 y2 m num ((den : Int) - num) (Int.natCast_nonneg num) hs h1 h2 hm
  have hk : (num : Int) + ((den : Int) - num) = den := by omega
  rw [hk] at h
  exact ediv_le_of_le _ m _ (Int.pow_nonneg (Int.natCast_nonneg den))
    (Int.le_trans (by decide) hm) h

/-- A cubic with no negative height reads no negative progress, at every share that is no more
than the whole. -/
private theorem cubicOf_nonneg (y1 y2 : Int) (num den : Nat) (hn : num ≤ den) (h1 : 0 ≤ y1)
    (h2 : 0 ≤ y2) : 0 ≤ cubicOf y1 y2 num den :=
  Int.ediv_nonneg
    (cubic_nonneg y1 y2 num ((den : Int) - num) (Int.natCast_nonneg num)
      (Int.sub_nonneg_of_le (Int.ofNat_le.mpr hn)) h1 h2)
    (Int.pow_nonneg (Int.natCast_nonneg den))

/-! ### The two measures of an easing -/

/-- The reading at a share of a thousand is the reading in per mille. `Motion/Laws.lean` has
this law as `Easing.of_thousand`. This module does not import that one, and keeps its own
copy. -/
private theorem of_mille (e : Easing) (p : Nat) : e.of p 1000 = e.at p := by
  cases e with
  | stops values => rfl
  | cubic y1 y2 => rfl

/-- **An easing that passes the test stays in range at every share of the progress** that is no
more than the whole. A transition reads its easing so, between its delay and its end. Stops
read a point of a straight line between two values in range. A cubic shares `0`, its two
heights and `1000` by four weights that are not negative. -/
theorem bounded_of (e : Easing) (num den : Nat) (h : e.bounded = true) (hn : num ≤ den) :
    0 ≤ e.of num den ∧ e.of num den ≤ 1000 := by
  cases e with
  | stops values =>
    have hv : ∀ v ∈ values, 0 ≤ v ∧ v ≤ 1000 := fun v hm => by
      have hb := List.all_eq_true.mp h v hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact hb
    exact ⟨le_stopsOf 0 values num den (Int.le_refl 0) (fun v hm => (hv v hm).1),
      stopsOf_le 1000 values num den (by decide) (fun v hm => (hv v hm).2)⟩
  | cubic y1 y2 =>
    simp only [bounded, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨cubicOf_nonneg y1 y2 num den hn h.1.1.1 h.1.2,
      cubicOf_le 1000 y1 y2 num den hn h.1.1.2 h.2 (Int.le_refl 1000)⟩

/-- **An easing that passes the test stays in range at every progress** from `0` to `1000`: it
gives `mix_gap` and `mix_mem` their premise from data. -/
theorem bounded_at (e : Easing) (p : Nat) (h : e.bounded = true) (hp : p ≤ 1000) :
    0 ≤ e.at p ∧ e.at p ≤ 1000 := by
  rw [← of_mille]
  exact bounded_of e p 1000 h hp

end Easing

/-- A running greatest value is no less than where it starts, and no less than any member. -/
theorem le_foldl_max : ∀ (l : List Int) (m : Int),
    m ≤ l.foldl max m ∧ ∀ v ∈ l, v ≤ l.foldl max m
  | [], m => ⟨Int.le_refl m, fun _ h => nomatch h⟩
  | a :: rest, m => by
    have ih := le_foldl_max rest (max m a)
    refine ⟨Int.le_trans (Int.le_max_left m a) ih.1, fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with he | hr
    · rw [he]
      exact Int.le_trans (Int.le_max_right m a) ih.1
    · exact ih.2 v hr

namespace Easing

/-- **An easing goes past its end by `over` at most**, at every share of the progress that is
no more than the whole. -/
theorem of_le_over (e : Easing) (num den : Nat) (hn : num ≤ den) :
    e.of num den ≤ 1000 + e.over := by
  cases e with
  | stops values =>
    obtain ⟨hm, hall⟩ := le_foldl_max values 1000
    have ho : (1000 : Int) + ((values.foldl max 1000 - 1000).toNat : Int) =
        values.foldl max 1000 := by omega
    show stopsOf values num den ≤ 1000 + ((values.foldl max 1000 - 1000).toNat : Int)
    rw [ho]
    exact stopsOf_le _ values num den (Int.le_trans (by decide) hm) hall
  | cubic y1 y2 =>
    have ho : (1000 : Int) + ((max 1000 (max y1 y2) - 1000).toNat : Int) =
        max 1000 (max y1 y2) := by omega
    show cubicOf y1 y2 num den ≤ 1000 + ((max 1000 (max y1 y2) - 1000).toNat : Int)
    rw [ho]
    exact cubicOf_le _ y1 y2 num den hn (by omega) (by omega) (by omega)

/-- **An easing goes past its end by `over` at most**, at every progress from `0` to `1000`. -/
theorem at_le_over (e : Easing) (p : Nat) (hp : p ≤ 1000) : e.at p ≤ 1000 + e.over := by
  rw [← of_mille]
  exact of_le_over e p 1000 hp

end Easing

/-! ## Every moment of a transition -/

namespace Transition

/-- **At every moment a transition reads its easing at a share of the progress**, and the share
is no more than the whole: none until the delay is over, the whole once the duration is over,
and between the two the share of the duration that has passed. -/
theorem at_share (tr : Transition) (t : Nat) :
    ∃ num den : Nat, num ≤ den ∧ tr.at t = tr.ease.of num den := by
  unfold Transition.at
  split
  · exact ⟨1000, 1000, Nat.le_refl 1000, (Easing.of_mille tr.ease 1000).symm⟩
  · split
    · exact ⟨0, 1000, Nat.zero_le 1000, (Easing.of_mille tr.ease 0).symm⟩
    · exact ⟨t - tr.delay, tr.duration, by omega, rfl⟩

/-- **A transition whose easing passes the test reads in range at every moment.** -/
theorem bounded_at (tr : Transition) (t : Nat) (h : tr.ease.bounded = true) :
    0 ≤ tr.at t ∧ tr.at t ≤ 1000 := by
  obtain ⟨num, den, hn, he⟩ := at_share tr t
  rw [he]
  exact Easing.bounded_of tr.ease num den h hn

/-- **A transition goes past the end by the `over` of its easing at most, at every moment.** -/
theorem at_le_over (tr : Transition) (t : Nat) : tr.at t ≤ 1000 + tr.ease.over := by
  obtain ⟨num, den, hn, he⟩ := at_share tr t
  rw [he]
  exact Easing.of_le_over tr.ease num den hn

end Transition

/-- **A kept relation of two pictures holds at every moment of a step.** Two things take one
transition, and its easing passes the test. Where their places have a kept relation in both
pictures, their places at the moment `t` have it, whatever `t` is. The places are what
`Change.shift` sets under `Track.at`. -/
theorem Kept.moment {R : IVec → IVec → Prop} (hR : Kept R) (tr : Transition) (t : Nat)
    (h : tr.ease.bounded = true) {a a' b b' : IVec} (hab : R a b) (hab' : R a' b') :
    R ⟨mix a.x a'.x (tr.at t), mix a.y a'.y (tr.at t)⟩
      ⟨mix b.x b'.x (tr.at t), mix b.y b'.y (tr.at t)⟩ :=
  hR (tr.bounded_at t h).1 (tr.bounded_at t h).2 hab hab'

/-! ## Growing past the size -/

/-- The low end of a span drawn at `k` per mille of its size about its middle, in
two-thousandths of a unit. The span starts at `x` and is `w` wide: its middle is `x + w / 2`
and half its drawn width is `w * k / 2000`. Times `2000`, nothing is rounded. -/
def grownLow (x w k : Int) : Int := 2000 * x + 1000 * w - w * k

/-- The high end of a span drawn at `k` per mille of its size about its middle, in
two-thousandths of a unit. -/
def grownHigh (x w k : Int) : Int := 2000 * x + 1000 * w + w * k

/-- At its whole size a span starts where it starts. -/
theorem grownLow_rest (x w : Int) : grownLow x w 1000 = 2000 * x := by
  show 2000 * x + 1000 * w - w * 1000 = 2000 * x
  omega

/-- At its whole size a span ends where it ends. -/
theorem grownHigh_rest (x w : Int) : grownHigh x w 1000 = 2000 * (x + w) := by
  show 2000 * x + 1000 * w + w * 1000 = 2000 * (x + w)
  omega

/-- **Two spans that grow past their size stay apart, where their gap has the room.** The
spans are `w₁` and `w₂` wide and `g` or more apart, and each is drawn at `1000 + o` per mille
at most. Each grows by half of `o` per mille of its width toward the other, so the gap has the
room where `(w₁ + w₂) * o ≤ 2000 * g`. The two sizes need not be equal: each thing may take a
timing of its own. -/
theorem grow_apart (x₁ w₁ x₂ w₂ g o k₁ k₂ : Int) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hk₁ : k₁ ≤ 1000 + o) (hk₂ : k₂ ≤ 1000 + o) (hg : x₁ + w₁ + g ≤ x₂)
    (ho : (w₁ + w₂) * o ≤ 2000 * g) : grownHigh x₁ w₁ k₁ ≤ grownLow x₂ w₂ k₂ := by
  have h1 : w₁ * k₁ ≤ w₁ * (1000 + o) := Int.mul_le_mul_of_nonneg_left hk₁ hw₁
  have h2 : w₂ * k₂ ≤ w₂ * (1000 + o) := Int.mul_le_mul_of_nonneg_left hk₂ hw₂
  rw [Int.mul_add] at h1 h2
  rw [Int.add_mul] at ho
  show 2000 * x₁ + 1000 * w₁ + w₁ * k₁ ≤ 2000 * x₂ + 1000 * w₂ - w₂ * k₂
  omega

/-- **Two spans that grow past their size share no whole unit, where their gap less one has the
room.** The high end of the first, rounded up to a whole unit, is no more than the low end of
the second, rounded down. So a reader that rounds each end outward to a whole unit draws no
unit twice. -/
theorem grow_clear (x₁ w₁ x₂ w₂ g o k₁ k₂ : Int) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hk₁ : k₁ ≤ 1000 + o) (hk₂ : k₂ ≤ 1000 + o) (hg : x₁ + w₁ + g ≤ x₂)
    (ho : (w₁ + w₂) * o ≤ 2000 * (g - 1)) :
    (grownHigh x₁ w₁ k₁ + 1999) / 2000 ≤ grownLow x₂ w₂ k₂ / 2000 := by
  have h := grow_apart x₁ w₁ (x₂ - 1) w₂ (g - 1) o k₁ k₂ hw₁ hw₂ hk₁ hk₂ (by omega) ho
  have hl : grownLow (x₂ - 1) w₂ k₂ = grownLow x₂ w₂ k₂ - 2000 := by
    show 2000 * (x₂ - 1) + 1000 * w₂ - w₂ * k₂ = 2000 * x₂ + 1000 * w₂ - w₂ * k₂ - 2000
    omega
  rw [hl] at h
  omega

/-! ## Controls

Each is a pair of pictures with numbers where a premise fails and the conclusion with it. The
kernel computes each one. -/

/-- `mix_gap` needs `0 ≤ e`. Two things stand at `0`, and the second goes to `10`: they do not
overlap before or after. At the eased progress `-100` the second stands at `-1`, behind the
first. -/
example : ¬(mix 0 0 (-100) + 0 ≤ mix 0 10 (-100)) := by decide

/-- `mix_gap` needs `e ≤ 1000`: an easing that passes its end is not for a place. A thing goes
from `0` to `100` and another stays at `116`, so both pictures have a gap of `16`.
`Easing.backOut` fails the test and reads `1080` at the progress `700`. There the first thing
stands at `108`, and the gap is `8`. -/
example :
    Easing.backOut.bounded = false ∧ Easing.backOut.at 700 = 1080 ∧
      (0 : Int) + 16 ≤ 116 ∧ (100 : Int) + 16 ≤ 116 ∧
      mix 0 100 (Easing.backOut.at 700) = 108 ∧
      ¬(mix 0 100 (Easing.backOut.at 700) + 16 ≤ mix 116 116 (Easing.backOut.at 700)) := by
  decide

/-- `Kept.moment` needs one transition for the two things: a kept thing is not staggered. Two
things go `100` to the right and are `16` apart in both pictures, by one easing that passes the
test. The first starts at once and the second waits. At the moment `500` the first has arrived
at `100` and the second still stands at `16`. -/
example :
    Easing.linear.bounded = true ∧ (0 : Int) + 16 ≤ 16 ∧ (100 : Int) + 16 ≤ 116 ∧
      ({ delay := 0, duration := 500 } : Transition).at 500 = 1000 ∧
      ({ delay := 500, duration := 500 } : Transition).at 500 = 0 ∧
      ¬(mix 0 100 (({ delay := 0, duration := 500 } : Transition).at 500) + 16 ≤
        mix 16 116 (({ delay := 500, duration := 500 } : Transition).at 500)) := by
  decide

/-- "Beside or above" is not kept, though each half is. A thing stays at the origin. Another is
`10` to its right before and `10` below it after. Half way it is `5` to the right and `5`
below, and neither axis holds the two apart. -/
example : ¬Kept (fun a b => a.x + 10 ≤ b.x ∨ a.y + 10 ≤ b.y) := fun h =>
  absurd (@h ⟨0, 0⟩ ⟨0, 0⟩ ⟨10, 0⟩ ⟨0, 10⟩ 500 (by decide) (by decide) (Or.inl (by decide))
    (Or.inr (by decide))) (by decide)

/-- `grow_clear` needs the room. Two spans are `240` wide and `16` apart, and each is drawn at
`1100` per mille: `480 * 100` is more than `2000 * 15`. The first ends in the unit `252` and the
second starts in the unit `244`. -/
example : ¬((grownHigh 0 240 1100 + 1999) / 2000 ≤ grownLow 256 240 1100 / 2000) := by decide

end Whatwg.Svg.Scene
