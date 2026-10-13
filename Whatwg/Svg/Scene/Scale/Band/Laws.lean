import Whatwg.Svg.Scene.Scale.Band
import Whatwg.Svg.Scene.Row
import Whatwg.Svg.Scene.Layout

/-!
# Whatwg.Svg.Scene.Scale.Band.Laws

Owner: the laws of equal bands at equal steps (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

What a caller gets of any `Band`:

- `at_succ`, `span_width`: neighbours are a step apart, and all bands have one width.
- `Apart.succ`, `Apart.unique`: where the bands are apart, a band ends at or before the edge of
  the next, and no place is in two bands.
- **The band under a place** (`invert_eq_some`): where the bands are apart, `invert x` is
  `some i` exactly when `i` is a band and `x` is in it. So a place in a band answers its band
  (`invert_of_mem`, `invert_at`), and whatever `invert` answers holds the place, apart or not
  (`invert_some`). d3's band scale has no inverse.
- **A band scale is a row of equal lengths** (`row_spans`): the left edges of the bands are the
  edges of `Row.spans` for `count` lengths of one step. With no gap the bands are that row, and
  they tile (`tiles_of_no_gap`).
- `inside_of_ends`: the bands lie in a range where the first and the last do.

What a caller gets of `Band.fit`, the bands shared out over a range:

- **Every band lies inside the range** (`fit_inside`), at every padding and every alignment,
  for a range that rises or descends. d3 does not keep this where the alignment is not the
  middle (the header of `Band.lean` has the case).
- **The bands are apart** (`fit_apart`): a band is no wider than a step.
- **The alignment is exact** (`fit_flush_left`, `fit_flush_right`, `fit_centred`): `0` puts the
  first band at the low end, `1000` ends the last band at the high end, and `500` leaves the
  same room on both sides, or one unit more before the first band.
- **A range that descends has the same bands in the other order** (`fit_swap`).
- `point_width`: a point scale has bands of no width.

And of `Band.fit` with no padding, which is a run of beats across a room:

- **Beats tile their range** (`fit_plain_tiles`): each band starts where the one before it
  ends. With `fit_inside`, `span_width` and `at_succ`, that is the whole of it: inside the
  range, one width, a step apart, no gap.
- **What is left over** (`fit_plain_width`, `fit_plain_ends`, `fit_plain_exact`): a beat is as
  wide as the range over the count, rounded down. The rest of that division is left over, less
  than one unit for each beat: half before the first beat and half after the last, the odd
  unit before the first. Where the range is a multiple of the count nothing is left over.

And of `Band.ofGap`, the bands with a whole gap:

- `ofGap_apart`, `ofGap_end`: they are apart, and with one gap more they are as long as
  `count` bands and gaps.
- **A row of `Layout` whose parts are all as wide is such a band scale** (`row_ofGap`): the
  things of `Layout.row gap` of `n` equal leaves stand at the left edges of
  `Band.ofGap 0 w gap n`.
- `le_fitting`: `n` bands fit in a length exactly when `n` is no more than `Band.fitting`.

What this module does not claim: that `fit` gives the widest bands that fit, which it does not
where the step is rounded down; that `invert` of bands that lie over each other answers the
first of them.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Band

/-! ## Edges and spans -/

/-- The first band starts at the start. -/
theorem at_zero (b : Band) : Band.at b 0 = b.start := by
  show b.start + b.step * ((0 : Nat) : Int) = b.start
  rw [Int.natCast_zero, Int.mul_zero, Int.add_zero]

/-- **Neighbours are a step apart.** -/
theorem at_succ (b : Band) (i : Nat) : Band.at b (i + 1) = Band.at b i + b.step := by
  show b.start + b.step * ((i + 1 : Nat) : Int) = b.start + b.step * (i : Int) + b.step
  rw [Int.natCast_add, Int.mul_add, Int.natCast_one, Int.mul_one, Int.add_assoc]

/-- **All bands have one width.** -/
theorem span_width (b : Band) (i : Nat) : (span b i).2 = (b.width : Int) := rfl

/-- The middle of a band is in the band or at its end, and is the middle to one unit. -/
theorem mid_mem (b : Band) (i : Nat) :
    Band.at b i ≤ mid b i ∧ mid b i ≤ Band.at b i + (b.width : Int) ∧
      Band.at b i + (b.width : Int) - mid b i ≤ mid b i - Band.at b i ∧
      mid b i - Band.at b i ≤ Band.at b i + (b.width : Int) - mid b i + 1 := by
  unfold mid
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega

theorem length_spansFrom (b : Band) : ∀ i n : Nat, (spansFrom b i n).length = n
  | _, 0 => rfl
  | i, n + 1 => congrArg (· + 1) (length_spansFrom b (i + 1) n)

/-- There is a span for each band. -/
theorem length_spans (b : Band) : b.spans.length = b.count := length_spansFrom b 0 b.count

theorem spansFrom_get (b : Band) : ∀ (i n k : Nat), k < n →
    (spansFrom b i n)[k]? = some (span b (i + k))
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | _, _ + 1, 0, _ => rfl
  | i, n + 1, k + 1, h => by
    have e : i + 1 + k = i + (k + 1) := by omega
    show (span b i :: spansFrom b (i + 1) n)[k + 1]? = some (span b (i + (k + 1)))
    rw [List.getElem?_cons_succ, spansFrom_get b (i + 1) n k (Nat.lt_of_succ_lt_succ h), e]

/-- The `k`-th of the spans is the `k`-th band. -/
theorem spans_get (b : Band) {k : Nat} (h : k < b.count) : b.spans[k]? = some (span b k) := by
  have e := spansFrom_get b 0 b.count k h
  rw [Nat.zero_add] at e
  exact e

/-! ## A band scale is a row -/

theorem row_spansFrom (b : Band) : ∀ i n : Nat,
    Row.spans (Band.at b i) (List.replicate n b.step) =
      (spansFrom b i n).map fun p => (p.1, b.step)
  | _, 0 => rfl
  | i, n + 1 => by
    show (Band.at b i, b.step) :: Row.spans (Band.at b i + b.step) (List.replicate n b.step) =
      (Band.at b i, b.step) :: (spansFrom b (i + 1) n).map fun p => (p.1, b.step)
    rw [← at_succ, row_spansFrom b (i + 1) n]

/-- **A band scale is a row of equal lengths.** The row of `count` lengths of one step, from
the start, has the left edges of the bands as its edges. A band and the gap after it are one
length of that row. -/
theorem row_spans (b : Band) :
    Row.spans b.start (List.replicate b.count b.step) = b.spans.map fun p => (p.1, b.step) := by
  have h := row_spansFrom b 0 b.count
  rw [at_zero] at h
  exact h

theorem spansFrom_of_no_gap {b : Band} (h : (b.width : Int) = b.step) : ∀ i n : Nat,
    spansFrom b i n = Row.spans (Band.at b i) (List.replicate n b.step)
  | _, 0 => rfl
  | i, n + 1 => by
    show (Band.at b i, (b.width : Int)) :: spansFrom b (i + 1) n =
      (Band.at b i, b.step) :: Row.spans (Band.at b i + b.step) (List.replicate n b.step)
    rw [h, ← at_succ, spansFrom_of_no_gap h (i + 1) n]

/-- **Bands with no gap tile**: each starts where the one before it ends. -/
theorem tiles_of_no_gap {b : Band} (h : (b.width : Int) = b.step) : Row.Tiles b.spans := by
  show Row.Tiles (spansFrom b 0 b.count)
  rw [spansFrom_of_no_gap h]
  exact Row.tiles_spans _ _

/-! ## Bands that are apart -/

/-- **Neighbours share no unit**: a band ends at or before the edge of the next, or the next
ends at or before the edge of the band where the bands run from right to left. -/
theorem Apart.succ {b : Band} (ha : b.Apart) (i : Nat) :
    Band.at b i + (b.width : Int) ≤ Band.at b (i + 1) ∨
      Band.at b (i + 1) + (b.width : Int) ≤ Band.at b i := by
  rw [at_succ]
  rcases ha with ha | ha
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Where a place of a band stands, counted in steps from the start: the quotient is the band
and the rest is how far into the band the place is. -/
theorem locate {b : Band} (ha : b.Apart) {i : Nat} {x : Int} (h1 : Band.at b i ≤ x)
    (h2 : x < Band.at b i + (b.width : Int)) :
    (x - b.start) / b.step = (i : Int) ∧ (x - b.start) % b.step = x - Band.at b i := by
  have h1' : b.start + b.step * (i : Int) ≤ x := h1
  have h2' : x < b.start + b.step * (i : Int) + (b.width : Int) := h2
  show (x - b.start) / b.step = (i : Int) ∧
    (x - b.start) % b.step = x - (b.start + b.step * (i : Int))
  rcases ha with ha | ha
  · exact (Int.ediv_emod_unique (by omega)).mpr ⟨by omega, by omega, by omega⟩
  · have h := (Int.ediv_emod_unique (a := x - b.start) (b := -b.step)
        (r := x - (b.start + b.step * (i : Int))) (q := -(i : Int)) (by omega)).mpr
        ⟨by rw [Int.neg_mul_neg]; omega, by omega, by omega⟩
    constructor
    · have e : (x - b.start) / b.step = -((x - b.start) / -b.step) := by
        rw [Int.ediv_neg, Int.neg_neg]
      rw [e, h.1, Int.neg_neg]
    · rw [← h.2, Int.emod_neg]

/-- **No place is in two bands**, where the bands are apart. -/
theorem Apart.unique {b : Band} (ha : b.Apart) {i j : Nat} {x : Int} (hi1 : Band.at b i ≤ x)
    (hi2 : x < Band.at b i + (b.width : Int)) (hj1 : Band.at b j ≤ x)
    (hj2 : x < Band.at b j + (b.width : Int)) : i = j := by
  have e := (locate ha hi1 hi2).1.symm.trans (locate ha hj1 hj2).1
  omega

/-! ## The band under a place -/

/-- **Whatever `invert` answers holds the place**: it is a band, and the place is in it. -/
theorem invert_some {b : Band} {x : Int} {i : Nat} (h : b.invert x = some i) :
    i < b.count ∧ Band.at b i ≤ x ∧ x < Band.at b i + (b.width : Int) := by
  unfold invert at h
  rcases Decidable.em (0 ≤ (x - b.start) / b.step ∧ (x - b.start) / b.step < (b.count : Int) ∧
      0 ≤ (x - b.start) % b.step ∧ (x - b.start) % b.step < (b.width : Int)) with hc | hc
  · rw [if_pos hc] at h
    have e : ((x - b.start) / b.step).toNat = i := Option.some.inj h
    have hk := Int.emod_add_mul_ediv (x - b.start) b.step
    obtain ⟨c1, c2, c3, c4⟩ := hc
    have ei : (i : Int) = (x - b.start) / b.step := by omega
    show i < b.count ∧ b.start + b.step * (i : Int) ≤ x ∧
      x < b.start + b.step * (i : Int) + (b.width : Int)
    rw [ei]
    generalize (x - b.start) / b.step = q at *
    generalize (x - b.start) % b.step = r at *
    generalize b.step * q = m at *
    refine ⟨?_, ?_, ?_⟩
    · omega
    · omega
    · omega
  · rw [if_neg hc] at h
    exact nomatch h

/-- **A place in a band answers its band**, where the bands are apart. -/
theorem invert_of_mem {b : Band} (ha : b.Apart) {i : Nat} (hi : i < b.count) {x : Int}
    (h1 : Band.at b i ≤ x) (h2 : x < Band.at b i + (b.width : Int)) : b.invert x = some i := by
  obtain ⟨hq, hr⟩ := locate ha h1 h2
  have hc : 0 ≤ (i : Int) ∧ (i : Int) < (b.count : Int) ∧ 0 ≤ x - Band.at b i ∧
      x - Band.at b i < (b.width : Int) := ⟨by omega, by omega, by omega, by omega⟩
  unfold invert
  rw [hq, hr, if_pos hc, Int.toNat_natCast]

/-- **The band under a place.** Where the bands are apart, `invert x` is `some i` exactly when
`i` is a band and `x` is in it. -/
theorem invert_eq_some {b : Band} (ha : b.Apart) {x : Int} {i : Nat} :
    b.invert x = some i ↔ i < b.count ∧ Band.at b i ≤ x ∧ x < Band.at b i + (b.width : Int) :=
  ⟨invert_some, fun h => invert_of_mem ha h.1 h.2.1 h.2.2⟩

/-- The left edge of a band with some width answers the band. -/
theorem invert_at {b : Band} (ha : b.Apart) {i : Nat} (hi : i < b.count) (hw : 0 < b.width) :
    b.invert (Band.at b i) = some i :=
  invert_of_mem ha hi (Int.le_refl _) (by omega)

/-! ## Inside a range -/

/-- **The bands lie in a range where the first and the last do.** -/
theorem inside_of_ends {b : Band} {lo hi : Int} (h0 : lo ≤ Band.at b 0)
    (h0' : Band.at b 0 + (b.width : Int) ≤ hi) (hn : lo ≤ Band.at b (b.count - 1))
    (hn' : Band.at b (b.count - 1) + (b.width : Int) ≤ hi) : b.Inside lo hi := by
  intro i hi'
  rw [at_zero] at h0 h0'
  have hn1 : lo ≤ b.start + b.step * ((b.count - 1 : Nat) : Int) := hn
  have hn2 : b.start + b.step * ((b.count - 1 : Nat) : Int) + (b.width : Int) ≤ hi := hn'
  have hle : (i : Int) ≤ ((b.count - 1 : Nat) : Int) := by omega
  show lo ≤ b.start + b.step * (i : Int) ∧ b.start + b.step * (i : Int) + (b.width : Int) ≤ hi
  rcases Int.le_total 0 b.step with hs | hs
  · have a1 := Int.mul_nonneg hs (Int.natCast_nonneg i)
    have a2 := Int.mul_le_mul_of_nonneg_left hle hs
    exact ⟨by omega, by omega⟩
  · have a1 := Int.mul_le_mul_of_nonpos_left hs (Int.natCast_nonneg i)
    have a2 := Int.mul_le_mul_of_nonpos_left hs hle
    rw [Int.mul_zero] at a1
    exact ⟨by omega, by omega⟩

/-! ## Bands shared out over a range: the arithmetic -/

/-- A band is no wider than its step. -/
theorem widthOf_le (p : Padding) (step : Nat) : widthOf p step ≤ step := by
  have h : step * (1000 - min 1000 p.inner) ≤ step * 1000 := Nat.mul_le_mul_left step (by omega)
  unfold widthOf
  omega

/-- With an inner padding of the whole step a band has no width. -/
theorem widthOf_of_inner {p : Padding} (h : 1000 ≤ p.inner) (step : Nat) : widthOf p step = 0 := by
  unfold widthOf
  rewrite [Nat.min_eq_left h, Nat.sub_self, Nat.mul_zero]
  omega

/-- **The bands and the steps between them are no longer than the range.** -/
theorem used_le (p : Padding) (count length : Nat) :
    stepOf p count length * (count - 1) + widthOf p (stepOf p count length) ≤ length := by
  have hd : stepOf p count length *
      max 1000 (1000 * count + 2 * p.outer - min 1000 p.inner) ≤ 1000 * length :=
    Nat.div_mul_le_self _ _
  have hk : 1000 * (count - 1) + (1000 - min 1000 p.inner) ≤
      max 1000 (1000 * count + 2 * p.outer - min 1000 p.inner) := by omega
  have h1 := Nat.mul_le_mul_left (stepOf p count length) hk
  rw [Nat.mul_add, Nat.mul_left_comm] at h1
  unfold widthOf
  generalize stepOf p count length = s at hd h1 ⊢
  generalize s * max 1000 (1000 * count + 2 * p.outer - min 1000 p.inner) = r at hd h1
  generalize s * (count - 1) = m at h1 ⊢
  generalize s * (1000 - min 1000 p.inner) = q at h1 ⊢
  omega

/-- The room before the first band is no more than the room left over. -/
theorem beforeOf_le (p : Padding) (count length : Nat) :
    beforeOf p count length ≤ slackOf p count length := by
  have h := Nat.mul_le_mul_left (slackOf p count length) (Nat.min_le_left 1000 p.align)
  unfold beforeOf
  omega

/-! ## Bands shared out over a range: the readings -/

theorem fit_count (count : Nat) (lo hi : Int) (p : Padding) :
    (fit count lo hi p).count = count := by
  unfold fit
  rcases Decidable.em (lo ≤ hi) with h | h
  · rw [if_pos h]
  · rw [if_neg h]

theorem fit_width (count : Nat) (lo hi : Int) (p : Padding) :
    (fit count lo hi p).width = widthOf p (stepOf p count (hi - lo).natAbs) := by
  unfold fit
  rcases Decidable.em (lo ≤ hi) with h | h
  · rw [if_pos h]
  · rw [if_neg h]

theorem fit_step_of_le {lo hi : Int} (h : lo ≤ hi) (count : Nat) (p : Padding) :
    (fit count lo hi p).step = (stepOf p count (hi - lo).natAbs : Nat) := by
  unfold fit
  rw [if_pos h]

theorem fit_step_of_lt {lo hi : Int} (h : hi < lo) (count : Nat) (p : Padding) :
    (fit count lo hi p).step = -(stepOf p count (hi - lo).natAbs : Nat) := by
  unfold fit
  rw [if_neg (Int.not_le.mpr h)]

theorem fit_start_of_le {lo hi : Int} (h : lo ≤ hi) (count : Nat) (p : Padding) :
    (fit count lo hi p).start = lo + (beforeOf p count (hi - lo).natAbs : Nat) := by
  unfold fit
  rw [if_pos h]

/-- The edges of bands on a range that rises. -/
theorem fit_at_of_le {lo hi : Int} (h : lo ≤ hi) (count : Nat) (p : Padding) (i : Nat) :
    Band.at (fit count lo hi p) i =
      lo + (beforeOf p count (hi - lo).natAbs : Nat) +
        ((stepOf p count (hi - lo).natAbs * i : Nat) : Int) := by
  rw [Int.natCast_mul (stepOf p count (hi - lo).natAbs) i]
  unfold fit
  rw [if_pos h]
  rfl

/-- The edges of bands on a range that descends. -/
theorem fit_at_of_lt {lo hi : Int} (h : hi < lo) (count : Nat) (p : Padding) (i : Nat) :
    Band.at (fit count lo hi p) i =
      hi + (beforeOf p count (hi - lo).natAbs : Nat) +
        ((stepOf p count (hi - lo).natAbs * (count - 1) : Nat) : Int) -
        ((stepOf p count (hi - lo).natAbs * i : Nat) : Int) := by
  rw [Int.natCast_mul (stepOf p count (hi - lo).natAbs) i, Int.sub_eq_add_neg, ← Int.neg_mul]
  unfold fit
  rw [if_neg (Int.not_le.mpr h)]
  rfl

/-! ## Bands shared out over a range: the laws -/

/-- **Every band lies inside the range**, at every padding and every alignment, on a range that
rises or descends. -/
theorem fit_inside (count : Nat) (lo hi : Int) (p : Padding) :
    (fit count lo hi p).Inside (min lo hi) (max lo hi) := by
  intro i hi'
  rw [fit_count] at hi'
  have hu := used_le p count (hi - lo).natAbs
  have hb := beforeOf_le p count (hi - lo).natAbs
  unfold slackOf at hb
  have hm : stepOf p count (hi - lo).natAbs * i ≤ stepOf p count (hi - lo).natAbs * (count - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [fit_width]
  rcases Int.lt_or_le hi lo with h | h
  · rw [fit_at_of_lt h]
    generalize stepOf p count (hi - lo).natAbs = s at hu hb hm ⊢
    generalize widthOf p s = w at hu hb ⊢
    generalize beforeOf p count (hi - lo).natAbs = before at hb ⊢
    generalize s * (count - 1) = m at hu hb hm ⊢
    generalize s * i = q at hm ⊢
    exact ⟨by omega, by omega⟩
  · rw [fit_at_of_le h]
    generalize stepOf p count (hi - lo).natAbs = s at hu hb hm ⊢
    generalize widthOf p s = w at hu hb ⊢
    generalize beforeOf p count (hi - lo).natAbs = before at hb ⊢
    generalize s * (count - 1) = m at hu hb hm ⊢
    generalize s * i = q at hm ⊢
    exact ⟨by omega, by omega⟩

/-- **The bands of a range are apart**: a band is no wider than a step is long. -/
theorem fit_apart (count : Nat) (lo hi : Int) (p : Padding) : (fit count lo hi p).Apart := by
  have h := widthOf_le p (stepOf p count (hi - lo).natAbs)
  unfold Apart
  rw [fit_width]
  rcases Int.lt_or_le hi lo with hl | hl
  · rw [fit_step_of_lt hl]
    exact Or.inr (by omega)
  · rw [fit_step_of_le hl]
    exact Or.inl (by omega)

/-- **The alignment `0` puts the first band at the low end of the range.** -/
theorem fit_flush_left {lo hi : Int} (h : lo ≤ hi) (count : Nat) {p : Padding} (ha : p.align = 0) :
    (fit count lo hi p).start = lo := by
  have e : beforeOf p count (hi - lo).natAbs = 0 := by
    unfold beforeOf
    rewrite [ha, Nat.min_zero]
    omega
  rewrite [fit_start_of_le h, e]
  omega

/-- **The alignment `1000` ends the last band at the high end of the range.** -/
theorem fit_flush_right {lo hi : Int} (h : lo ≤ hi) (count : Nat) {p : Padding}
    (ha : 1000 ≤ p.align) :
    Band.at (fit count lo hi p) (count - 1) + ((fit count lo hi p).width : Int) = hi := by
  have hu := used_le p count (hi - lo).natAbs
  have e : beforeOf p count (hi - lo).natAbs = slackOf p count (hi - lo).natAbs := by
    unfold beforeOf
    rewrite [Nat.min_eq_left ha]
    omega
  rewrite [fit_at_of_le h, fit_width, e]
  unfold slackOf
  generalize stepOf p count (hi - lo).natAbs = s at hu ⊢
  generalize widthOf p s = w at hu ⊢
  generalize s * (count - 1) = m at hu ⊢
  omega

/-- **The alignment `500` is the middle**: the room after the last band is the room before the
first, or one unit less. -/
theorem fit_centred {lo hi : Int} (h : lo ≤ hi) (count : Nat) {p : Padding}
    (ha : p.align = 500) :
    hi - (Band.at (fit count lo hi p) (count - 1) + ((fit count lo hi p).width : Int)) ≤
        (fit count lo hi p).start - lo ∧
      (fit count lo hi p).start - lo ≤
        hi - (Band.at (fit count lo hi p) (count - 1) + ((fit count lo hi p).width : Int)) + 1 := by
  have hu := used_le p count (hi - lo).natAbs
  have e : beforeOf p count (hi - lo).natAbs = (slackOf p count (hi - lo).natAbs + 1) / 2 := by
    unfold beforeOf
    rewrite [ha, Nat.min_eq_right (by omega : 500 ≤ 1000)]
    omega
  rewrite [fit_at_of_le h, fit_width, fit_start_of_le h, e]
  unfold slackOf
  generalize stepOf p count (hi - lo).natAbs = s at hu ⊢
  generalize widthOf p s = w at hu ⊢
  generalize s * (count - 1) = m at hu ⊢
  exact ⟨by omega, by omega⟩

/-- **A range that descends has the same bands in the other order.** -/
theorem fit_swap {lo hi : Int} (h : lo < hi) {count i : Nat} (hi' : i < count) (p : Padding) :
    Band.at (fit count hi lo p) i = Band.at (fit count lo hi p) (count - 1 - i) := by
  have e : (lo - hi).natAbs = (hi - lo).natAbs := by omega
  have hm : stepOf p count (hi - lo).natAbs * i ≤ stepOf p count (hi - lo).natAbs * (count - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  rewrite [fit_at_of_lt h, fit_at_of_le (Int.le_of_lt h), e,
    Nat.mul_sub (stepOf p count (hi - lo).natAbs) (count - 1) i]
  generalize stepOf p count (hi - lo).natAbs * (count - 1) = m at hm ⊢
  generalize stepOf p count (hi - lo).natAbs * i = q at hm ⊢
  omega

/-- **A point scale has bands of no width.** -/
theorem point_width (count : Nat) (lo hi : Int) (outer align : Nat) :
    (point count lo hi outer align).width = 0 := by
  unfold point
  rw [fit_width]
  exact widthOf_of_inner (Nat.le_refl 1000) _

/-! ## Bands with no padding: the beats of a run

A run of `count` beats across a room is `fit count lo hi` with no padding: a band for each beat
and no gap. What follows says exactly how such bands tile their range. -/

/-- With no padding the step is the length over the count, rounded down. -/
theorem stepOf_plain {p : Padding} (hi : p.inner = 0) (ho : p.outer = 0) {count : Nat}
    (hc : 0 < count) (length : Nat) : stepOf p count length = length / count := by
  have e : max 1000 (1000 * count + 2 * 0 - min 1000 0) = 1000 * count := by omega
  unfold stepOf
  rw [hi, ho, e, Nat.mul_div_mul_left _ _ (by omega : 0 < 1000)]

/-- With no inner padding a band is as wide as a step. -/
theorem widthOf_plain {p : Padding} (hi : p.inner = 0) (step : Nat) : widthOf p step = step := by
  unfold widthOf
  rewrite [hi, Nat.min_zero, Nat.sub_zero]
  omega

/-- With no padding, what the bands leave over is the rest of the division. -/
theorem slackOf_plain {p : Padding} (hi : p.inner = 0) (ho : p.outer = 0) {count : Nat}
    (hc : 0 < count) (length : Nat) : slackOf p count length = length % count := by
  have e : length / count * (count - 1) + length / count = count * (length / count) := by
    have h := Nat.mul_succ (length / count) (count - 1)
    have hs : Nat.succ (count - 1) = count := by omega
    rw [hs] at h
    rw [← h, Nat.mul_comm]
  unfold slackOf
  rw [stepOf_plain hi ho hc, widthOf_plain hi, e, Nat.mod_def]

/-- **Beats are as wide as the range over their count, rounded down.** -/
theorem fit_plain_width {p : Padding} (hi0 : p.inner = 0) (ho : p.outer = 0) {count : Nat}
    (hc : 0 < count) (lo hi : Int) : (fit count lo hi p).width = (hi - lo).natAbs / count := by
  rw [fit_width, widthOf_plain hi0, stepOf_plain hi0 ho hc]

/-- **Beats tile**: with no inner padding each band starts where the one before it ends, on a
range that rises. With `fit_inside`, `span_width` and `at_succ`: the bands lie inside the range,
have one width, are a step apart, and leave no gap between them. -/
theorem fit_plain_tiles {lo hi : Int} (h : lo ≤ hi) {p : Padding} (hi0 : p.inner = 0)
    (count : Nat) : Row.Tiles (fit count lo hi p).spans :=
  tiles_of_no_gap (by rw [fit_width, widthOf_plain hi0, fit_step_of_le h])

/-- **What beats leave over at the two ends.** Where the range is not a multiple of the count,
the rest of the division is left over, which is less than one unit for each beat. Half of it
stands before the first beat and half after the last, and an odd unit stands before the
first. -/
theorem fit_plain_ends {lo hi : Int} (h : lo ≤ hi) {p : Padding} (hi0 : p.inner = 0)
    (ho : p.outer = 0) (ha : p.align = 500) {count : Nat} (hc : 0 < count) :
    (fit count lo hi p).start - lo = (((hi - lo).natAbs % count + 1) / 2 : Nat) ∧
      hi - (Band.at (fit count lo hi p) (count - 1) + ((fit count lo hi p).width : Int)) =
        (((hi - lo).natAbs % count) / 2 : Nat) := by
  have hu := used_le p count (hi - lo).natAbs
  have es := slackOf_plain hi0 ho hc (hi - lo).natAbs
  have e : beforeOf p count (hi - lo).natAbs = (slackOf p count (hi - lo).natAbs + 1) / 2 := by
    unfold beforeOf
    rewrite [ha, Nat.min_eq_right (by omega : 500 ≤ 1000)]
    omega
  rewrite [fit_at_of_le h, fit_width, fit_start_of_le h, e, ← es]
  unfold slackOf
  generalize stepOf p count (hi - lo).natAbs = s at hu ⊢
  generalize widthOf p s = w at hu ⊢
  generalize s * (count - 1) = m at hu ⊢
  exact ⟨by omega, by omega⟩

/-- **Where the range is a multiple of the count, beats fill it**: the first starts at the low
end and the last ends at the high end. -/
theorem fit_plain_exact {lo hi : Int} (h : lo ≤ hi) {p : Padding} (hi0 : p.inner = 0)
    (ho : p.outer = 0) (ha : p.align = 500) {count : Nat} (hc : 0 < count)
    (hd : (hi - lo).natAbs % count = 0) :
    (fit count lo hi p).start = lo ∧
      Band.at (fit count lo hi p) (count - 1) + ((fit count lo hi p).width : Int) = hi := by
  obtain ⟨e1, e2⟩ := fit_plain_ends h hi0 ho ha hc
  rw [hd] at e1 e2
  exact ⟨by omega, by omega⟩

/-! ## Bands with a whole gap -/

/-- Bands with a whole gap are apart. -/
theorem ofGap_apart (start : Int) (width gap count : Nat) : (ofGap start width gap count).Apart :=
  Or.inl (by
    show (width : Int) ≤ ((width + gap : Nat) : Int)
    omega)

/-- **Bands with a whole gap, and one gap more, are as long as `count` bands and gaps.** It is
`Layout.row_w` for parts that are all as wide. -/
theorem ofGap_end (start : Int) (width gap : Nat) {count : Nat} (hc : 0 < count) :
    Band.at (ofGap start width gap count) (count - 1) + (width : Int) + (gap : Int) =
      start + ((width + gap : Nat) : Int) * (count : Int) := by
  have e : (count : Int) = ((count - 1 : Nat) : Int) + 1 := by omega
  show start + ((width + gap : Nat) : Int) * ((count - 1 : Nat) : Int) + (width : Int) +
      (gap : Int) = start + ((width + gap : Nat) : Int) * (count : Int)
  rewrite [e, Int.mul_add, Int.mul_one]
  omega

/-- **How many bands fit.** `n` bands with a gap between each two, and one gap more, are no
longer than a length and a gap exactly when `n` is no more than `fitting`. -/
theorem le_fitting {width gap : Nat} (h : 0 < width + gap) (length n : Nat) :
    n ≤ fitting width gap length ↔ n * (width + gap) ≤ length + gap :=
  Nat.le_div_iff_mul_le h

/-! ## A row of equal parts -/

section

variable {α : Type} [Moves IVec α]

/-- A thing at the left edge of each band from the `i`-th on, moved by a step, is a thing at
the left edge of each band from the next on. -/
theorem move_spansFrom (b : Band) (a : α) : ∀ i n : Nat,
    Moves.move (⟨b.step, 0⟩ : IVec)
        ((spansFrom b i n).map fun p => Moves.move (⟨p.1, 0⟩ : IVec) a) =
      (spansFrom b (i + 1) n).map fun p => Moves.move (⟨p.1, 0⟩ : IVec) a
  | _, 0 => rfl
  | i, n + 1 => by
    have e : (⟨Band.at b i, 0⟩ : IVec) + ⟨b.step, 0⟩ = ⟨Band.at b (i + 1), 0⟩ :=
      IVec.ext (at_succ b i).symm (Int.add_zero 0)
    show Moves.move (⟨b.step, 0⟩ : IVec) (Moves.move (⟨Band.at b i, 0⟩ : IVec) a) ::
        Moves.move (⟨b.step, 0⟩ : IVec)
          ((spansFrom b (i + 1) n).map fun p => Moves.move (⟨p.1, 0⟩ : IVec) a) =
      Moves.move (⟨Band.at b (i + 1), 0⟩ : IVec) a ::
        (spansFrom b (i + 1 + 1) n).map fun p => Moves.move (⟨p.1, 0⟩ : IVec) a
    rw [Moves.move_move, e, move_spansFrom b a (i + 1) n]

/-- **A row of equal parts is a band scale with a whole gap.** The things of `Layout.row gap` of
`n` leaves, each `w` wide, stand at the left edges of the bands of `Band.ofGap 0 w gap`, in
order. -/
theorem row_ofGap (gap w h count : Nat) (a : α) : ∀ n : Nat,
    (Layout.row gap (List.replicate n (Layout.leaf w h a))).items =
      (spansFrom (ofGap 0 w gap count) 0 n).map fun p => Moves.move (⟨p.1, 0⟩ : IVec) a
  | 0 => rfl
  | 1 => by
    have e : (⟨Band.at (ofGap 0 w gap count) 0, 0⟩ : IVec) = 0 :=
      IVec.ext (at_zero _) rfl
    show [a] = [Moves.move (⟨Band.at (ofGap 0 w gap count) 0, 0⟩ : IVec) a]
    rw [e, Moves.move_zero]
  | n + 2 => by
    have e : (⟨Band.at (ofGap 0 w gap count) 0, 0⟩ : IVec) = 0 :=
      IVec.ext (at_zero _) rfl
    have ih := row_ofGap gap w h count a (n + 1)
    show a :: Moves.move (Layout.across (w + gap))
        (Layout.row gap (List.replicate (n + 1) (Layout.leaf w h a))).items =
      Moves.move (⟨Band.at (ofGap 0 w gap count) 0, 0⟩ : IVec) a ::
        (spansFrom (ofGap 0 w gap count) 1 (n + 1)).map fun p => Moves.move (⟨p.1, 0⟩ : IVec) a
    rw [ih, e, Moves.move_zero]
    exact congrArg (a :: ·) (move_spansFrom (ofGap 0 w gap count) a 0 (n + 1))

end

end Band

end Whatwg.Svg.Scene
