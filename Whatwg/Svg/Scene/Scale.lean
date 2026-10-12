import Whatwg.Svg.Scene.Branch
import Whatwg.Svg.Scene.Join.Laws

/-!
# Whatwg.Svg.Scene.Scale

Owner: a quantity as a length, and what the picture says (slice S14 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-78).

A length in a picture says a quantity. The reader compares two lengths and believes what they
say of the two quantities. So a scale has one rule: *more is never drawn as less, and where two
different values are drawn alike the picture says so*. This module has a scale as data, the
function that draws with it, the list of the values that it draws alike, and a table of what
each channel of a picture means. A legend is drawn from the table by the function that draws
the picture, so the two cannot differ.

It is module M8 of `docs/research/2026-10-12-pictures-craft-modules.md`. Everything counts in
whole numbers, in the caller's own units: a share in millionths, a depth, a count, a width in
pixels. A division rounds down. So the layer needs no fraction and stays under the strict
ceiling.

- `Scale`: `linear`, a straight line; `root k`, where the `k`-th powers of the lengths are in
  proportion, by the root of `Whatwg/Svg/Scene/Branch.lean`; `log2`, one step for each doubling;
  `steps`, a base level and a level for each threshold.
- `Scale.at s v`: the length of the value `v`. A value outside the range of the data is drawn at
  the nearer end.
- `Scale.Rising`, `Scale.Falling`: the scale goes up, or down. Each is decided by evaluation.
- `Scale.ties s values`: the pairs of `values` that the scale draws alike.
  `Scale.groups s values`: the values by their length, which is the form that a legend prints.
- `Scale.fromZero s`: no quantity is no length.
- `Channel`, `Encoding`: one row of what a picture says. `Encoding.samples`: the marks of a
  legend. `Encoding.Single`: no channel has two rows.

What the laws say of a picture drawn with a scale:

- `Scale.at_mono`: with a rising scale, more is never drawn as less. So a longer mark never
  means less (`Scale.lt_of_at_lt`), and a band drawn from the mark of `a` to the mark of `b`
  holds the mark of every value between them (`Scale.at_between`). `Scale.at_anti` is the same
  for a falling scale: with weight by depth, a deeper thing is never heavier.
- **The rule of the module** (`Scale.at_lt_or_tie`): of two values of a list, the greater is
  drawn longer, or the pair is in `ties`. Where `ties` is empty, more is always drawn as more
  (`Scale.at_lt_of_no_ties`). `Scale.mem_ties` says what the pairs are. Every value is in the
  group of its length (`Scale.mem_groups_of_mem`), a group holds the values of its length and
  no other (`Scale.mem_groups`), and two values of one group are a tie (`Scale.tie_of_group`).
- `Scale.linear_strict`: a `linear` scale with one unit of length or more for each unit of the
  quantity draws no two values of its range alike. With a whole number of units for each, it
  has no rounding (`Scale.linear_exact`).
- `Scale.linear_ratio`: on a `linear` scale from nothing, `n` times the quantity has `n` times
  the length, and less than `n` units more. Twice the quantity is twice the length, or one unit
  more.
- `Scale.fromZero_at`: a scale from nothing draws nothing with no length. `Scale.linear_lo`,
  `Scale.linear_hi`, `Scale.linear_clamp`: the two ends of the data are drawn at the two ends of
  the scale, and a value outside at the nearer end.
- `Scale.log2_double`, `Scale.log2_step`: a doubling is one step, of the same length each time.
- `Scale.root_rising`: a rising `root` scale draws a value `Share.width` past `lo`, so the laws
  of `Branch.lean` are laws of it.
- `Encoding.mem_samples`: a mark of a legend is a value with the length that `Scale.at` gives
  it. `Encoding.eq_of_single`: in a table with one row for each channel, a channel has one
  meaning and one scale.

How this differs from the design note, whose signatures no Lean had checked:

- `at_mono` asks for `s.Rising`. For `steps` that is "the levels never fall, the base level
  first": a `steps` scale has no `lo` and no `hi`.
- The note reads `at_mono` as "a deeper item is never heavier". That is a scale that falls, so
  `Falling` and `at_anti` are here for it.
- `linear_ratio` is stated on one side: the length of `n * a` is never less than `n` lengths of
  `a`, since both round down.
- `fromZero` reads the scale's data, and not `at 0 = 0` alone. A scale whose data starts at `5`
  draws `0` at its low end, and that is the bar that does not start at nothing.
- `steps` is a base level and a list of pairs, each a threshold and its level. The note has
  two lists, whose lengths could differ. A value that reaches no threshold is drawn at the base
  level. The thresholds are read in order, and the reading stops at the first that the value
  does not reach.
- `ties` lists a pair with its lesser value first, and so lists no pair in both orders.
  `groups` is added: a legend names a group, and no pair.
- `fromZero` of a `steps` scale is "the level of `0` is `0`": such a scale has no range.
- `Encoding.Single` is `Distinct` of `Whatwg/Svg/Scene/Join.lean`, with the channel as the key.
- `root` goes from `lo` toward `hi` by the root, up or down.
- `log2` rounds its logarithm down, so two values between one power of two and the next are
  drawn alike, and `ties` lists them.

What this module does not claim: that a length, a time and a count are not mixed, since each is
an `Int` here; a logarithm to a base other than two, or a scale with a break; the text of a
legend; that a `root` scale's powers are in proportion exactly, since a root is rounded
(`Share.width_conserves` has the bounds); `linear_strict` and `linear_ratio` for a `root` or a
`log2` scale; that each length stands once among the `groups`, which holds and which no law
here states; a lookup of a channel in a table.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- How a quantity becomes a length. A value outside the range of the data is drawn at the
nearer end. -/
inductive Scale where
  /-- Equal steps of the quantity are equal steps of the length: `lo` at `dataLo` and `hi` at
  `dataHi`. -/
  | linear (dataLo dataHi lo hi : Int)
  /-- The `k`-th root: the `k`-th powers of the lengths past `lo` are in proportion to the
  quantities past `dataLo`. -/
  | root (k : Nat) (dataLo dataHi lo hi : Int)
  /-- One step of length for each doubling: `lo` at `dataLo` and `hi` at `dataHi`. -/
  | log2 (dataLo dataHi : Nat) (lo hi : Int)
  /-- Levels: a value is drawn at the level of the last threshold that it reaches, and at the
  base level where it reaches none. Each member of `levels` is a threshold and its level. -/
  | steps (base : Int) (levels : List (Int × Int))
  deriving DecidableEq, Repr

namespace Scale

/-! ## A value in a range -/

/-- A value held in the range of the data: the nearer end where it is outside. A range with no
value holds every value at its low end. -/
def clamp (dataLo dataHi v : Int) : Int := max dataLo (min v dataHi)

/-- A value in the range is held as it is. -/
theorem clamp_of_mem {dataLo dataHi v : Int} (h1 : dataLo ≤ v) (h2 : v ≤ dataHi) :
    clamp dataLo dataHi v = v := by
  unfold clamp
  omega

/-- A greater value is held no lower. -/
theorem clamp_mono (dataLo dataHi : Int) {a b : Int} (h : a ≤ b) :
    clamp dataLo dataHi a ≤ clamp dataLo dataHi b := by
  unfold clamp
  omega

/-- A held value is held as it is. -/
theorem clamp_clamp (dataLo dataHi v : Int) :
    clamp dataLo dataHi (clamp dataLo dataHi v) = clamp dataLo dataHi v := by
  unfold clamp
  omega

/-- A range with one value or none holds every value at its low end. -/
theorem clamp_of_empty {dataLo dataHi : Int} (h : dataHi ≤ dataLo) (v : Int) :
    clamp dataLo dataHi v = dataLo := by
  unfold clamp
  omega

/-! ## A straight line -/

/-- The length of `v` on the straight line from `lo` at `dataLo` to `hi` at `dataHi`, rounded
down. A range with one value or none is drawn at `lo`. -/
def lineAt (dataLo dataHi lo hi v : Int) : Int :=
  lo + (hi - lo) * (clamp dataLo dataHi v - dataLo) / (dataHi - dataLo)

/-- On a line that rises, a greater value is drawn no shorter. -/
theorem lineAt_mono (dataLo dataHi : Int) {lo hi : Int} (h : lo ≤ hi) {a b : Int} (hab : a ≤ b) :
    lineAt dataLo dataHi lo hi a ≤ lineAt dataLo dataHi lo hi b := by
  rcases Int.lt_or_le 0 (dataHi - dataLo) with hd | hd
  · exact Int.add_le_add_left (Int.ediv_le_ediv hd (Int.mul_le_mul_of_nonneg_left
      (Int.sub_le_sub_right (clamp_mono dataLo dataHi hab) dataLo) (Int.sub_nonneg_of_le h))) lo
  · have e : ∀ v, clamp dataLo dataHi v = dataLo := clamp_of_empty (by omega)
    unfold lineAt
    rw [e a, e b]
    exact Int.le_refl _

/-- On a line that falls, a greater value is drawn no longer. -/
theorem lineAt_anti (dataLo dataHi : Int) {lo hi : Int} (h : hi ≤ lo) {a b : Int} (hab : a ≤ b) :
    lineAt dataLo dataHi lo hi b ≤ lineAt dataLo dataHi lo hi a := by
  rcases Int.lt_or_le 0 (dataHi - dataLo) with hd | hd
  · exact Int.add_le_add_left (Int.ediv_le_ediv hd (Int.mul_le_mul_of_nonpos_left
      (Int.sub_nonpos_of_le h) (Int.sub_le_sub_right (clamp_mono dataLo dataHi hab) dataLo))) lo
  · have e : ∀ v, clamp dataLo dataHi v = dataLo := clamp_of_empty (by omega)
    unfold lineAt
    rw [e a, e b]
    exact Int.le_refl _

/-- A line from nothing draws a value of its range at `hi * v / dataHi`, rounded down. -/
theorem lineAt_zero (dataHi hi : Int) {v : Int} (h0 : 0 ≤ v) (h1 : v ≤ dataHi) :
    lineAt 0 dataHi 0 hi v = hi * v / dataHi := by
  unfold lineAt
  rw [clamp_of_mem h0 h1]
  simp only [Int.sub_zero, Int.zero_add]

/-- A line with `u` units of length for each unit of the quantity has no rounding: a value of
its range is drawn `u` units past `lo` for each unit that it is past `dataLo`. -/
theorem lineAt_exact (dataLo dataHi lo hi u : Int) (hd : dataLo < dataHi)
    (hu : hi - lo = u * (dataHi - dataLo)) {v : Int} (h1 : dataLo ≤ v) (h2 : v ≤ dataHi) :
    lineAt dataLo dataHi lo hi v = lo + u * (v - dataLo) := by
  unfold lineAt
  rw [clamp_of_mem h1 h2, hu, Int.mul_right_comm, Int.mul_ediv_cancel _ (by omega)]

/-! ## A root -/

/-- The share of the range of the data that `v` is past its low end. -/
def share (dataLo dataHi v : Int) : Share :=
  ⟨(clamp dataLo dataHi v - dataLo).toNat, (dataHi - dataLo).toNat⟩

/-- The length of `v` on the scale of the `k`-th root: from `lo` toward `hi`, by the width that
`Share.width` gives the share of `v`, where the whole range is as wide as from `lo` to `hi`. -/
def rootAt (k : Nat) (dataLo dataHi lo hi v : Int) : Int :=
  if lo ≤ hi then lo + ((share dataLo dataHi v).width k (hi - lo).natAbs : Nat)
  else lo - ((share dataLo dataHi v).width k (hi - lo).natAbs : Nat)

/-- A greater value has no narrower share of the root. -/
theorem share_width_mono (k trunk : Nat) (dataLo dataHi : Int) {a b : Int} (hab : a ≤ b) :
    (share dataLo dataHi a).width k trunk ≤ (share dataLo dataHi b).width k trunk := by
  have h := clamp_mono dataLo dataHi hab
  refine Share.width_mono k trunk rfl ?_
  show (clamp dataLo dataHi a - dataLo).toNat ≤ (clamp dataLo dataHi b - dataLo).toNat
  omega

/-- With a trunk of no width every share is drawn with no width. -/
theorem width_trunk_zero (k : Nat) (s : Share) : s.width k 0 = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    show rootDown (k + 1) (0 ^ (k + 1) * s.num / s.den) = 0
    rw [Nat.zero_pow (Nat.succ_pos k), Nat.zero_mul, Nat.zero_div]
    rfl

/-- On a root that rises, a greater value is drawn no shorter. -/
theorem rootAt_mono (k : Nat) (dataLo dataHi : Int) {lo hi : Int} (h : lo ≤ hi) {a b : Int}
    (hab : a ≤ b) : rootAt k dataLo dataHi lo hi a ≤ rootAt k dataLo dataHi lo hi b := by
  have hw := share_width_mono k (hi - lo).natAbs dataLo dataHi hab
  unfold rootAt
  rw [if_pos h, if_pos h]
  omega

/-- On a root that falls, a greater value is drawn no longer. -/
theorem rootAt_anti (k : Nat) (dataLo dataHi : Int) {lo hi : Int} (h : hi ≤ lo) {a b : Int}
    (hab : a ≤ b) : rootAt k dataLo dataHi lo hi b ≤ rootAt k dataLo dataHi lo hi a := by
  have hw := share_width_mono k (hi - lo).natAbs dataLo dataHi hab
  unfold rootAt
  rcases Int.lt_or_le hi lo with hlt | hle
  · rw [if_neg (Int.not_le.mpr hlt), if_neg (Int.not_le.mpr hlt)]
    omega
  · have e : (hi - lo).natAbs = 0 := by omega
    rw [if_pos hle, if_pos hle, e, width_trunk_zero, width_trunk_zero]
    exact Int.le_refl _

/-! ## A logarithm -/

/-- A greater number has no smaller logarithm, rounded down. -/
theorem log2_mono {n m : Nat} (h : n ≤ m) : Nat.log2 n ≤ Nat.log2 m := by
  cases Nat.eq_zero_or_pos n with
  | inl h0 =>
    rw [h0, Nat.log2_zero]
    exact Nat.zero_le _
  | inr hp =>
    exact (Nat.le_log2 (Nat.ne_of_gt (Nat.lt_of_lt_of_le hp h))).mpr
      (Nat.le_trans (Nat.log2_self_le (Nat.ne_of_gt hp)) h)

/-- **A doubling is one more.** Twice a number that is not `0` has the logarithm of the number
and one, rounded down. -/
theorem log2_double {n : Nat} (h : n ≠ 0) : Nat.log2 (2 * n) = Nat.log2 n + 1 := by
  have h2 : 2 * n ≠ 0 := by omega
  have hlo := Nat.log2_self_le h
  have hhi := Nat.lt_log2_self (n := n)
  refine Nat.le_antisymm (Nat.le_of_lt_succ ((Nat.log2_lt h2).mpr ?_)) ((Nat.le_log2 h2).mpr ?_)
  · rw [Nat.pow_succ]
    omega
  · rw [Nat.pow_succ]
    omega

/-! ## Levels -/

/-- The level of the last threshold that `v` reaches, and `cur` where it reaches none. Each
level stands with its threshold. The thresholds are read in order, and the reading stops at the
first that `v` does not reach. -/
def stepsAt : List (Int × Int) → Int → Int → Int
  | [], cur, _ => cur
  | (t, l) :: rest, cur, v => if t ≤ v then stepsAt rest l v else cur

/-- The level that the steps give is the one they start from, or one of the levels. -/
theorem stepsAt_mem : ∀ (ls : List (Int × Int)) (cur v : Int),
    stepsAt ls cur v = cur ∨ stepsAt ls cur v ∈ ls.map Prod.snd
  | [], _, _ => Or.inl rfl
  | (t, l) :: rest, cur, v => by
    show (if t ≤ v then stepsAt rest l v else cur) = cur ∨
      (if t ≤ v then stepsAt rest l v else cur) ∈ l :: rest.map Prod.snd
    rcases Decidable.em (t ≤ v) with h | h
    · rw [if_pos h]
      rcases stepsAt_mem rest l v with e | m
      · rw [e]
        exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem l m)
    · rw [if_neg h]
      exact Or.inl rfl

/-- **The levels of two values stand as the levels do.** Let `R` hold of each number with
itself, and of each level with every later one, the base level first. Then `R` holds of the
level of a value with the level of a greater value. With `R` "no more than", levels that never
fall give a scale that never falls. -/
theorem stepsAt_rel (R : Int → Int → Prop) (hr : ∀ x, R x x) :
    ∀ (ls : List (Int × Int)) (cur : Int), (cur :: ls.map Prod.snd).Pairwise R →
      ∀ (a b : Int), a ≤ b → R (stepsAt ls cur a) (stepsAt ls cur b)
  | [], cur, _, _, _, _ => hr cur
  | (t, l) :: rest, cur, hp, a, b, hab => by
    have hp' : (∀ x ∈ l :: rest.map Prod.snd, R cur x) ∧ (l :: rest.map Prod.snd).Pairwise R :=
      List.pairwise_cons.mp hp
    show R (if t ≤ a then stepsAt rest l a else cur) (if t ≤ b then stepsAt rest l b else cur)
    rcases Decidable.em (t ≤ a) with h | h
    · rw [if_pos h, if_pos (Int.le_trans h hab)]
      exact stepsAt_rel R hr rest l hp'.2 a b hab
    · rw [if_neg h]
      rcases Decidable.em (t ≤ b) with h2 | h2
      · rw [if_pos h2]
        rcases stepsAt_mem rest l b with e | m
        · rw [e]
          exact hp'.1 l List.mem_cons_self
        · exact hp'.1 _ (List.mem_cons_of_mem l m)
      · rw [if_neg h2]
        exact hr cur

end Scale

/-! ## The length of a value -/

/-- **The length of a value.** A value outside the range of the data is drawn at the nearer
end. -/
def Scale.at : Scale → Int → Int
  | .linear dataLo dataHi lo hi, v => Scale.lineAt dataLo dataHi lo hi v
  | .root k dataLo dataHi lo hi, v => Scale.rootAt k dataLo dataHi lo hi v
  | .log2 dataLo dataHi lo hi, v =>
    Scale.lineAt (Nat.log2 dataLo : Nat) (Nat.log2 dataHi : Nat) lo hi (Nat.log2 v.toNat : Nat)
  | .steps base levels, v => Scale.stepsAt levels base v

/-- **The scale rises**: its `lo` is no more than its `hi`, and the levels of `steps` never
fall, the base level first. -/
def Scale.Rising : Scale → Prop
  | .linear _ _ lo hi => lo ≤ hi
  | .root _ _ _ lo hi => lo ≤ hi
  | .log2 _ _ lo hi => lo ≤ hi
  | .steps base levels => (base :: levels.map Prod.snd).Pairwise (· ≤ ·)

/-- Whether a scale rises is decided from its data. -/
instance (s : Scale) : Decidable s.Rising := by
  cases s <;> unfold Scale.Rising <;> exact inferInstance

/-- **The scale falls**: its `hi` is no more than its `lo`, and the levels of `steps` never
rise, the base level first. Weight by depth is such a scale. -/
def Scale.Falling : Scale → Prop
  | .linear _ _ lo hi => hi ≤ lo
  | .root _ _ _ lo hi => hi ≤ lo
  | .log2 _ _ lo hi => hi ≤ lo
  | .steps base levels => (base :: levels.map Prod.snd).Pairwise (· ≥ ·)

/-- Whether a scale falls is decided from its data. -/
instance (s : Scale) : Decidable s.Falling := by
  cases s <;> unfold Scale.Falling <;> exact inferInstance

namespace Scale

/-- **More is never drawn as less.** On a scale that rises, a greater value is drawn no
shorter. -/
theorem at_mono (s : Scale) (h : s.Rising) {a b : Int} (hab : a ≤ b) : s.at a ≤ s.at b := by
  cases s with
  | linear dataLo dataHi lo hi => exact lineAt_mono dataLo dataHi h hab
  | root k dataLo dataHi lo hi => exact rootAt_mono k dataLo dataHi h hab
  | log2 dataLo dataHi lo hi =>
    exact lineAt_mono _ _ h (Int.ofNat_le.mpr (log2_mono (Int.toNat_le_toNat hab)))
  | steps base levels => exact stepsAt_rel (· ≤ ·) Int.le_refl levels base h a b hab

/-- **On a scale that falls, more is never drawn as more**: a greater value is drawn no longer.
With weight by depth, a deeper thing is never heavier. -/
theorem at_anti (s : Scale) (h : s.Falling) {a b : Int} (hab : a ≤ b) : s.at b ≤ s.at a := by
  cases s with
  | linear dataLo dataHi lo hi => exact lineAt_anti dataLo dataHi h hab
  | root k dataLo dataHi lo hi => exact rootAt_anti k dataLo dataHi h hab
  | log2 dataLo dataHi lo hi =>
    exact lineAt_anti _ _ h (Int.ofNat_le.mpr (log2_mono (Int.toNat_le_toNat hab)))
  | steps base levels => exact stepsAt_rel (· ≥ ·) Int.le_refl levels base h a b hab

/-- **A band holds the mark of every value of its interval.** On a scale that rises, the mark of
a value between `a` and `b` is between the marks of `a` and of `b`. -/
theorem at_between (s : Scale) (h : s.Rising) {a v b : Int} (hav : a ≤ v) (hvb : v ≤ b) :
    s.at a ≤ s.at v ∧ s.at v ≤ s.at b :=
  ⟨at_mono s h hav, at_mono s h hvb⟩

/-- **A longer mark never means less.** On a scale that rises, the value with the longer mark
is the greater. -/
theorem lt_of_at_lt (s : Scale) (h : s.Rising) {a b : Int} (hlt : s.at a < s.at b) : a < b :=
  Int.lt_of_not_ge fun hle => Int.not_lt.mpr (at_mono s h hle) hlt

/-! ## A straight line, in its range -/

/-- **A value outside the range of the data is drawn at the nearer end.** -/
theorem linear_clamp (dataLo dataHi lo hi v : Int) :
    (Scale.linear dataLo dataHi lo hi).at v =
      (Scale.linear dataLo dataHi lo hi).at (clamp dataLo dataHi v) := by
  show lineAt dataLo dataHi lo hi v = lineAt dataLo dataHi lo hi (clamp dataLo dataHi v)
  unfold lineAt
  rw [clamp_clamp]

/-- The low end of the data is drawn at `lo`. -/
theorem linear_lo (dataLo dataHi lo hi : Int) (h : dataLo ≤ dataHi) :
    (Scale.linear dataLo dataHi lo hi).at dataLo = lo := by
  show lineAt dataLo dataHi lo hi dataLo = lo
  unfold lineAt
  rw [clamp_of_mem (Int.le_refl dataLo) h, Int.sub_self, Int.mul_zero, Int.zero_ediv,
    Int.add_zero]

/-- The high end of the data is drawn at `hi`, where the range has two values or more. -/
theorem linear_hi (dataLo dataHi lo hi : Int) (h : dataLo < dataHi) :
    (Scale.linear dataLo dataHi lo hi).at dataHi = hi := by
  show lineAt dataLo dataHi lo hi dataHi = hi
  unfold lineAt
  rw [clamp_of_mem (Int.le_of_lt h) (Int.le_refl dataHi), Int.mul_ediv_cancel _ (by omega)]
  omega

/-- **Equal steps of the quantity are equal steps of the length**, with no rounding, where the
scale has a whole number `u` of units of length for each unit of the quantity. -/
theorem linear_exact (dataLo dataHi lo hi u : Int) (hd : dataLo < dataHi)
    (hu : hi - lo = u * (dataHi - dataLo)) {v : Int} (h1 : dataLo ≤ v) (h2 : v ≤ dataHi) :
    (Scale.linear dataLo dataHi lo hi).at v = lo + u * (v - dataLo) :=
  lineAt_exact dataLo dataHi lo hi u hd hu h1 h2

/-- **A scale that is long enough draws no two values alike.** A `linear` scale with one unit of
length or more for each unit of the quantity draws a greater value of its range longer. Where a
scale is shorter than that, `ties` lists the pairs. -/
theorem linear_strict (dataLo dataHi lo hi : Int) (hu : dataHi - dataLo ≤ hi - lo) {a b : Int}
    (ha : dataLo ≤ a) (hab : a < b) (hb : b ≤ dataHi) :
    (Scale.linear dataLo dataHi lo hi).at a < (Scale.linear dataLo dataHi lo hi).at b := by
  have hd : 0 < dataHi - dataLo := by omega
  have e : (hi - lo) * (b - dataLo) = (hi - lo) * (a - dataLo) + (hi - lo) * (b - a) := by
    rw [← Int.mul_add]
    exact congrArg ((hi - lo) * ·) (by omega)
  have h1 : (hi - lo) * 1 ≤ (hi - lo) * (b - a) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  rw [Int.mul_one] at h1
  have h2 : ((hi - lo) * (a - dataLo) + 1 * (dataHi - dataLo)) / (dataHi - dataLo) ≤
      (hi - lo) * (b - dataLo) / (dataHi - dataLo) := by
    refine Int.ediv_le_ediv hd ?_
    rw [e, Int.one_mul]
    omega
  rw [Int.add_mul_ediv_right _ _ (Int.ne_of_gt hd)] at h2
  show lineAt dataLo dataHi lo hi a < lineAt dataLo dataHi lo hi b
  unfold lineAt
  rw [clamp_of_mem ha (by omega), clamp_of_mem (by omega) hb]
  omega

end Scale

/-! ## From nothing -/

/-- **No quantity is no length**: the range of the data starts at nothing, and nothing is drawn
with no length. A logarithm has no nothing, so a `log2` scale is never from nothing. A `steps`
scale has no range of its own, and is from nothing where the level of `0` is `0`. A picture
whose lengths are compared says so where this is `false`: a bar that does not start at nothing
is longer or shorter than its quantity. -/
def Scale.fromZero : Scale → Bool
  | .linear dataLo _ lo _ => dataLo == 0 && lo == 0
  | .root _ dataLo _ lo _ => dataLo == 0 && lo == 0
  | .log2 _ _ _ _ => false
  | .steps base levels => Scale.stepsAt levels base 0 == 0

namespace Scale

/-- A `linear` scale from nothing has its data from `0` and its lengths from `0`. -/
theorem fromZero_linear {dataLo dataHi lo hi : Int}
    (h : (Scale.linear dataLo dataHi lo hi).fromZero = true) : dataLo = 0 ∧ lo = 0 := by
  have h' : (dataLo == 0 && lo == 0) = true := h
  rw [Bool.and_eq_true] at h'
  exact ⟨beq_iff_eq.mp h'.1, beq_iff_eq.mp h'.2⟩

/-- **A scale from nothing draws nothing with no length.** -/
theorem fromZero_at (s : Scale) (h : s.fromZero = true) : s.at 0 = 0 := by
  cases s with
  | linear dataLo dataHi lo hi =>
    obtain ⟨e1, e2⟩ := fromZero_linear h
    subst e1
    subst e2
    have e : clamp 0 dataHi 0 = 0 := by
      unfold clamp
      omega
    show 0 + (hi - 0) * (clamp 0 dataHi 0 - 0) / (dataHi - 0) = 0
    rw [e, Int.sub_self, Int.mul_zero, Int.zero_ediv, Int.add_zero]
  | root k dataLo dataHi lo hi =>
    have h' : (dataLo == 0 && lo == 0) = true := h
    rw [Bool.and_eq_true] at h'
    have e1 : dataLo = 0 := beq_iff_eq.mp h'.1
    have e2 : lo = 0 := beq_iff_eq.mp h'.2
    subst e1
    subst e2
    have e : clamp 0 dataHi 0 = 0 := by
      unfold clamp
      omega
    have hw : (share 0 dataHi 0).width k (hi - 0).natAbs = 0 := by
      show rootDown k ((hi - 0).natAbs ^ k * (clamp 0 dataHi 0 - 0).toNat / (dataHi - 0).toNat) = 0
      rw [e]
      show rootDown k ((hi - 0).natAbs ^ k * 0 / (dataHi - 0).toNat) = 0
      rw [Nat.mul_zero, Nat.zero_div]
      cases k with
      | zero => rfl
      | succ k => rfl
    show rootAt k 0 dataHi 0 hi 0 = 0
    unfold rootAt
    rw [hw]
    rcases Decidable.em ((0 : Int) ≤ hi) with hh | hh
    · rw [if_pos hh]
      rfl
    · rw [if_neg hh]
      rfl
  | log2 dataLo dataHi lo hi => exact nomatch h
  | steps base levels => exact beq_iff_eq.mp h

/-- **Twice the quantity is twice the length, to a rounding.** On a `linear` scale from
nothing, `n` times a quantity of the range has `n` times the length or more, and less than `n`
units more. Both lengths are rounded down, so the greater one is never short. -/
theorem linear_ratio (dataLo dataHi lo hi : Int)
    (h0 : (Scale.linear dataLo dataHi lo hi).fromZero = true) (hd : 0 < dataHi) {n a : Int}
    (hn : 0 < n) (ha : 0 ≤ a) (hna : n * a ≤ dataHi) :
    n * (Scale.linear dataLo dataHi lo hi).at a ≤ (Scale.linear dataLo dataHi lo hi).at (n * a) ∧
      (Scale.linear dataLo dataHi lo hi).at (n * a) <
        n * (Scale.linear dataLo dataHi lo hi).at a + n := by
  obtain ⟨e1, e2⟩ := fromZero_linear h0
  subst e1
  subst e2
  have hle : a ≤ n * a := by
    have h := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ n by omega) ha
    rw [Int.one_mul] at h
    exact h
  show n * lineAt 0 dataHi 0 hi a ≤ lineAt 0 dataHi 0 hi (n * a) ∧
    lineAt 0 dataHi 0 hi (n * a) < n * lineAt 0 dataHi 0 hi a + n
  rw [lineAt_zero dataHi hi ha (Int.le_trans hle hna),
    lineAt_zero dataHi hi (Int.mul_nonneg (Int.le_of_lt hn) ha) hna, Int.mul_left_comm hi n a]
  constructor
  · refine Int.le_ediv_of_mul_le hd ?_
    rw [Int.mul_assoc n (hi * a / dataHi) dataHi]
    exact Int.mul_le_mul_of_nonneg_left (Int.ediv_mul_le _ (Int.ne_of_gt hd)) (Int.le_of_lt hn)
  · refine Int.ediv_lt_of_lt_mul hd ?_
    have h2 := Int.mul_lt_mul_of_pos_left (Int.lt_ediv_add_one_mul_self (hi * a) hd) hn
    rw [← Int.mul_assoc n (hi * a / dataHi + 1) dataHi, Int.mul_add, Int.mul_one] at h2
    exact h2

/-! ## A root and a logarithm, in their ranges -/

/-- A `root` scale that rises draws a value the width of its share past `lo`. So the laws of
`Share.width` are laws of the scale: the `k`-th power of that width is the share of the `k`-th
power of the whole length, to one unit of length (`rootDown_pow_le`, `lt_rootDown_succ_pow`). -/
theorem root_rising (k : Nat) (dataLo dataHi lo hi v : Int) (h : lo ≤ hi) :
    (Scale.root k dataLo dataHi lo hi).at v =
      lo + ((share dataLo dataHi v).width k (hi - lo).natAbs : Nat) :=
  if_pos h

/-- **A doubling is one step, of the same length each time.** Let a `log2` scale have a whole
number `u` of units of length for each doubling of its range. Then twice a value of the range
is drawn `u` units past the value, where the range holds both. -/
theorem log2_step (dataLo dataHi : Nat) (lo hi u : Int)
    (hu : hi - lo = u * ((Nat.log2 dataHi : Nat) - (Nat.log2 dataLo : Nat) : Int)) {v : Nat}
    (hv : v ≠ 0) (h1 : dataLo ≤ v) (h2 : 2 * v ≤ dataHi) :
    (Scale.log2 dataLo dataHi lo hi).at ((2 * v : Nat) : Int) =
      (Scale.log2 dataLo dataHi lo hi).at (v : Int) + u := by
  have hL := log2_mono h1
  have hU := log2_mono h2
  rw [log2_double hv] at hU
  have hvv : v ≤ 2 * v := by omega
  have hM := log2_mono hvv
  rw [log2_double hv] at hM
  show lineAt (Nat.log2 dataLo : Nat) (Nat.log2 dataHi : Nat) lo hi
      (Nat.log2 (((2 * v : Nat) : Int).toNat) : Nat) =
    lineAt (Nat.log2 dataLo : Nat) (Nat.log2 dataHi : Nat) lo hi
      (Nat.log2 ((v : Int).toNat) : Nat) + u
  rw [Int.toNat_natCast, Int.toNat_natCast, log2_double hv,
    lineAt_exact _ _ lo hi u (by omega) hu (by omega) (by omega),
    lineAt_exact _ _ lo hi u (by omega) hu (by omega) (by omega)]
  have e : ((Nat.log2 v + 1 : Nat) : Int) - (Nat.log2 dataLo : Nat) =
      ((Nat.log2 v : Nat) : Int) - (Nat.log2 dataLo : Nat) + 1 := by omega
  rw [e, Int.mul_add, Int.mul_one, Int.add_assoc]

end Scale

/-! ## Values that are drawn alike -/

/-- **The pairs of the values that the scale draws alike**: two different values of the list
with one length, the lesser first. They are alike by an end of the range, by a level, or by a
rounding. A value that the list has twice gives its pairs twice. -/
def Scale.ties (s : Scale) (values : List Int) : List (Int × Int) :=
  values.flatMap fun a =>
    (values.filter fun b => decide (a < b ∧ s.at a = s.at b)).map fun b => (a, b)

namespace Scale

/-- A pair is a tie exactly when its two values are of the list, the first is the lesser, and
the scale draws them alike. -/
theorem mem_ties (s : Scale) (values : List Int) (a b : Int) :
    (a, b) ∈ s.ties values ↔ a ∈ values ∧ b ∈ values ∧ a < b ∧ s.at a = s.at b := by
  constructor
  · intro h
    obtain ⟨a', ha', hm⟩ := List.mem_flatMap.mp h
    obtain ⟨b', hb', he⟩ := List.mem_map.mp hm
    have ea : a' = a := congrArg Prod.fst he
    have eb : b' = b := congrArg Prod.snd he
    subst ea
    subst eb
    exact ⟨ha', (List.mem_filter.mp hb').1, of_decide_eq_true (List.mem_filter.mp hb').2⟩
  · intro ⟨ha, hb, hlt, he⟩
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr
      ⟨b, List.mem_filter.mpr ⟨hb, decide_eq_true ⟨hlt, he⟩⟩, rfl⟩⟩

/-- **More is never drawn as less, and where two different values are drawn alike the picture
says so.** Of two values of a list, on a scale that rises, the greater is drawn longer, or the
pair is a tie. -/
theorem at_lt_or_tie (s : Scale) (h : s.Rising) (values : List Int) {a b : Int} (ha : a ∈ values)
    (hb : b ∈ values) (hab : a < b) : s.at a < s.at b ∨ (a, b) ∈ s.ties values := by
  rcases Int.lt_or_eq_of_le (at_mono s h (Int.le_of_lt hab)) with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ((mem_ties s values a b).mpr ⟨ha, hb, hab, heq⟩)

/-- **With no tie, more is always drawn as more.** Where a scale that rises draws no two values
of a list alike, it draws the greater of two of them longer. -/
theorem at_lt_of_no_ties (s : Scale) (h : s.Rising) (values : List Int)
    (ht : s.ties values = []) {a b : Int} (ha : a ∈ values) (hb : b ∈ values) (hab : a < b) :
    s.at a < s.at b := by
  rcases at_lt_or_tie s h values ha hb hab with hlt | hm
  · exact hlt
  · rw [ht] at hm
    exact nomatch hm

end Scale

/-- **The values of a list by the length that the scale draws them at.** Each length stands
once, in the order of its first value, with the values of the list that have it, in their
order. A group of two values or more is what a legend names together: with weight by depth on
three levels, "3 and deeper". -/
def Scale.groups (s : Scale) (values : List Int) : List (Int × List Int) :=
  (values.map s.at).eraseDups.map fun l => (l, values.filter fun v => s.at v == l)

namespace Scale

/-- The values of a group are the values of the list that the scale draws at the group's
length. -/
theorem mem_groups (s : Scale) (values : List Int) {l : Int} {vs : List Int}
    (h : (l, vs) ∈ s.groups values) (v : Int) : v ∈ vs ↔ v ∈ values ∧ s.at v = l := by
  obtain ⟨l', _, he⟩ := List.mem_map.mp h
  have e1 : l' = l := congrArg Prod.fst he
  have e2 : (values.filter fun w => s.at w == l') = vs := congrArg Prod.snd he
  subst e1
  subst e2
  exact ⟨fun hv => ⟨(List.mem_filter.mp hv).1, beq_iff_eq.mp (List.mem_filter.mp hv).2⟩,
    fun hv => List.mem_filter.mpr ⟨hv.1, beq_iff_eq.mpr hv.2⟩⟩

/-- **Every value of the list is in the group of its length.** -/
theorem mem_groups_of_mem (s : Scale) (values : List Int) {v : Int} (hv : v ∈ values) :
    ∃ vs, (s.at v, vs) ∈ s.groups values ∧ v ∈ vs :=
  ⟨values.filter fun w => s.at w == s.at v,
    List.mem_map.mpr
      ⟨s.at v, List.mem_eraseDups.mpr (List.mem_map.mpr ⟨v, hv, rfl⟩), rfl⟩,
    List.mem_filter.mpr ⟨hv, beq_iff_eq.mpr rfl⟩⟩

/-- **Two different values of one group are a tie**, the lesser first. So the pairs of `ties`
are what the groups of two values or more hold. -/
theorem tie_of_group (s : Scale) (values : List Int) {l : Int} {vs : List Int}
    (h : (l, vs) ∈ s.groups values) {a b : Int} (ha : a ∈ vs) (hb : b ∈ vs) (hab : a < b) :
    (a, b) ∈ s.ties values :=
  (mem_ties s values a b).mpr
    ⟨((mem_groups s values h a).mp ha).1, ((mem_groups s values h b).mp hb).1, hab,
      ((mem_groups s values h a).mp ha).2.trans ((mem_groups s values h b).mp hb).2.symm⟩

end Scale

/-! ## What a picture says -/

/-- A channel of a picture: one way in which a mark differs from another. -/
inductive Channel where
  /-- The place of a mark from left to right. -/
  | across
  /-- The place of a mark from top to bottom. -/
  | down
  /-- How wide a mark is. -/
  | width
  /-- How high a mark is. -/
  | height
  /-- How light or dark a mark is. -/
  | tone
  /-- The hue of a mark. -/
  | hue
  /-- The dashes of a line. -/
  | dash
  /-- The texture that fills a mark. -/
  | texture
  /-- When a mark appears in a step. -/
  | orderInTime
  deriving DecidableEq, Repr

/-- One line of what a picture says: a channel, what it means, and how it is drawn. -/
structure Encoding where
  /-- The channel that carries the meaning. -/
  channel : Channel
  /-- What the channel means, in the words of the legend. -/
  meaning : String
  /-- How a quantity is drawn in the channel, and `none` for a channel that tells kinds
  apart. -/
  scale : Option Scale
  deriving DecidableEq, Repr

namespace Encoding

/-- **The marks of a legend**: sample values with the lengths that the picture draws them at.
A channel with no scale has none. -/
def samples (e : Encoding) (values : List Int) : List (Int × Int) :=
  match e.scale with
  | none => []
  | some s => values.map fun v => (v, s.at v)

/-- The marks of a legend of a channel with a scale are the values with their lengths. -/
theorem samples_some (e : Encoding) (values : List Int) {s : Scale} (h : e.scale = some s) :
    e.samples values = values.map fun v => (v, s.at v) := by
  unfold samples
  rw [h]

/-- **A legend and its picture cannot differ**: a mark of a legend is a sample value with the
length that `Scale.at` gives it, by the scale of the row. -/
theorem mem_samples (e : Encoding) (values : List Int) {v l : Int}
    (h : (v, l) ∈ e.samples values) : ∃ s, e.scale = some s ∧ v ∈ values ∧ l = s.at v := by
  cases hs : e.scale with
  | none =>
    unfold samples at h
    rw [hs] at h
    exact nomatch h
  | some s =>
    rw [samples_some e values hs] at h
    obtain ⟨w, hw, he⟩ := List.mem_map.mp h
    have e1 : w = v := congrArg Prod.fst he
    have e2 : s.at w = l := congrArg Prod.snd he
    subst e1
    exact ⟨s, rfl, hw, e2.symm⟩

/-- **No channel holds a meaning twice**: a table of what a picture says has one row at most
for each channel. It is `Distinct` of `Whatwg/Svg/Scene/Join.lean`, with the channel of a row
as its key. -/
def Single (table : List Encoding) : Prop := Distinct Encoding.channel table

/-- Whether a table has one row at most for each channel is decided by evaluation. -/
instance (table : List Encoding) : Decidable (Single table) :=
  inferInstanceAs (Decidable (List.Nodup _))

/-- **A channel has one meaning.** In a table with one row at most for each channel, two rows
with one channel are one row: one meaning and one scale. -/
theorem eq_of_single {table : List Encoding} (h : Single table) {a b : Encoding}
    (ha : a ∈ table) (hb : b ∈ table) (hc : a.channel = b.channel) : a = b :=
  eq_of_distinct Encoding.channel table h a b ha hb hc

end Encoding

/-! ## Finite evaluations

The first four are the probe of the design note. Regions are nested four deep, and the weight
of a region is its depth on a scale of three levels. The fourth depth is drawn as the third, and
`ties` says so: the group of the third level has two depths, which a legend names "3 and
deeper". With four levels no two depths are drawn alike. The legend has the marks that the
picture has. -/

#guard (Scale.steps 1 [(2, 2), (3, 3)]).ties [1, 2, 3, 4] == [(3, 4)]
#guard (Scale.steps 1 [(2, 2), (3, 3)]).groups [1, 2, 3, 4] == [(1, [1]), (2, [2]), (3, [3, 4])]
#guard (Scale.steps 1 [(2, 2), (3, 3), (4, 4)]).ties [1, 2, 3, 4] == []
#guard ({ channel := .width, meaning := "depth", scale := some (.steps 1 [(2, 2), (3, 3)]) } :
  Encoding).samples [1, 2, 3, 4] == [(1, 1), (2, 2), (3, 3), (4, 3)]

-- The width of an edge: a share in millionths of a trunk `8` wide, and never finer than `1`.
-- Half the work is half the width. Every share below an eighth is drawn at `1`, and `ties`
-- lists the pairs that this end hides.
#guard (Scale.linear 125000 1000000 1 8).at 500000 == 4
#guard (Scale.linear 125000 1000000 1 8).ties [50000, 100000, 125000, 250000] ==
  [(50000, 100000), (50000, 125000), (100000, 125000)]

-- A root: a quarter of the quantity is half the length. A logarithm: a doubling is a tenth of
-- the length, from `1` to `1024`.
#guard (Scale.root 2 0 100 0 10).at 25 == 5
#guard [32, 64].map (Scale.log2 1 1024 0 100).at == [50, 60]

-- Weight by depth, heavier at the top: the scale falls, and it does not rise.
#guard decide (Scale.steps 3 [(2, 2), (3, 1)]).Falling
#guard !decide (Scale.steps 3 [(2, 2), (3, 1)]).Rising

-- A control of `Scale.at_mono`, which needs a scale that rises. With levels that fall, the
-- greater value is drawn shorter.
#guard (Scale.steps 5 [(2, 3)]).at 1 == 5 && (Scale.steps 5 [(2, 3)]).at 2 == 3

-- A control of `Scale.linear_strict`, which needs a unit of length for each unit of the
-- quantity. Ten values on five units of length are drawn two by two.
#guard (Scale.linear 0 10 0 5).ties [0, 1, 2, 3] == [(0, 1), (2, 3)]

-- A control of `Scale.linear_ratio`, which needs a scale from nothing. On a scale whose data
-- starts at `5`, twice the quantity `5` is not twice its length, and the scale says that it is
-- not from nothing. It draws `0` at its low end, with no length, all the same.
#guard (Scale.linear 5 10 0 100).at 5 == 0 && (Scale.linear 5 10 0 100).at 10 == 100
#guard !(Scale.linear 5 10 0 100).fromZero && (Scale.linear 5 10 0 100).at 0 == 0
#guard (Scale.linear 0 10 0 100).fromZero

-- A table with one row for each channel, and a table that gives the width two meanings.
#guard decide (Encoding.Single [⟨.width, "work", none⟩, ⟨.tone, "depth", none⟩])
#guard !decide (Encoding.Single [⟨.width, "work", none⟩, ⟨.width, "depth", none⟩])

end Whatwg.Svg.Scene
