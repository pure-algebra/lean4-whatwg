/-!
# Whatwg.Svg.Scene.Metrics

Owner: what a host says of a face, and the width of a text as two bounds (slice S14 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-75).

A layout must know how wide a text is before it draws a box round it. Lean has no font. A host
has one, and it says what it knows once, as numbers: for each range of code points, the least
and the greatest advance of a character of the range. The width of a text is then two numbers:
the sum of the least advances and the sum of the greatest. A layout that gives a text its
greatest width as its room is right for every host that the numbers describe. Every length is a
whole number of thousandths of the picture's unit, so the layer needs no fraction and stays
under the strict ceiling. This module measures nothing itself.

- `Metrics`: a face at one size. Four heights, the ranges with their advances, and the advances
  of a character in no range.
- `Metrics.mono cell ascent descent`: a face in which every character is `cell` wide. It needs
  no host.
- `Metrics.advance m c`, `Metrics.width m codes`: the two bounds of a character and of a run.
- `Metrics.Fits m codes room`: the run is within the room at its greatest width.
- `Metrics.FitsRow m base rowHeight`: a row holds the face on a baseline.
- `Metrics.any ms`: several faces as one, for a list of fallback families.
- `Metrics.tabular m`: every digit has one advance, and the face knows it exactly.
- `Metrics.Draws m codes advances`: what a host may draw of a run.
- `Metrics.codes text`: the code points of a string.

What the laws say of a picture laid out with these widths:

- `width_draws`, `fits_draws`: whatever a host draws within the metrics, the drawn width is
  between the two bounds. So a text that fits its room in Lean fits it on the screen.
- `width_append`, `fits_append`: the bounds of two runs in a row are the sums of their bounds.
  A room is computed part by part.
- `mono_width`: in a face of one advance, both bounds are `cell` times the count of
  characters. A grid of cells is this face.
- `advance_join`, `advance_any`, `advance_any_attained`: the bounds of several faces as one
  hold the bounds of each, and each of the two is the bound of one of the faces. So the
  bounds are no wider than the faces make them.
- `fits_any`, `fitsRow_any`, `draws_any`: a room and a row computed for a list of fallback
  families hold for the family that the host picks.
- `tabular_aligns`: where `tabular` holds, two runs of digits of one count have one width, the
  least equal to the greatest. Counts and addresses align on the right.
- `width_le`: where every pair of bounds is in order (`Ordered`), the least width is the
  greatest at most.

What a caller must supply: the numbers. A tool of the host measures each face once and writes
the ranges. A range's two advances count whatever kerning and joining the host does, so a
character's advance in any text lies between them. Where a face's advances are not known, its
greatest advance must still be a true bound, or `Fits` says nothing of the screen.

What this module does not claim: that a host draws within the numbers it was given; that the
least and the greatest width are near each other; a width for a text whose direction or shaping
moves characters (`Draws` has one advance for each code point); that a string's code points are
its characters as a reader counts them. `codes` reads the bytes of a string as UTF-8 and has no
law.
-/

namespace Whatwg.Svg.Scene

/-- A range of code points with its advances: the first code point, the last, and the least and
the greatest advance of a character of the range. -/
abbrev Metrics.Range : Type := Nat × Nat × Nat × Nat

/-- What a host says of a face at one size. Every length is in thousandths of the picture's
unit. A height is the greatest that the face has: no ink is higher than `ascent` above the
baseline or lower than `descent` below it. -/
structure Metrics where
  /-- how far the face rises above the baseline, at most -/
  ascent : Nat
  /-- how far the face falls below the baseline, at most -/
  descent : Nat
  /-- the height of a capital letter, at most -/
  capHeight : Nat
  /-- the height of a small letter such as `x`, at most -/
  xHeight : Nat
  /-- ranges of code points: first, last, and the least and the greatest advance of a character
  of the range, with whatever kerning and joining the host does. The first range that holds a
  code point speaks for it. -/
  ranges : List Metrics.Range
  /-- the least and the greatest advance of a character in no range -/
  other : Nat × Nat
  deriving DecidableEq, Repr, Inhabited

namespace Metrics

/-! ## Advances and widths -/

/-- The range holds the code point. -/
def covers (r : Range) (c : Nat) : Bool := decide (r.1 ≤ c) && decide (c ≤ r.2.1)

/-- The two advances of a code point among ranges: those of the first range that holds it, and
`other` where none does. -/
def find : List Range → Nat × Nat → Nat → Nat × Nat
  | [], other, _ => other
  | r :: rs, other, c => bif covers r c then r.2.2 else find rs other c

/-- **The least and the greatest advance of a character.** -/
def advance (m : Metrics) (c : Nat) : Nat × Nat := find m.ranges m.other c

/-- **The least and the greatest width of a run of characters**: the sums of their advances. -/
def width (m : Metrics) : List Nat → Nat × Nat
  | [] => (0, 0)
  | c :: cs => ((m.advance c).1 + (width m cs).1, (m.advance c).2 + (width m cs).2)

/-- A range holds a code point where the code point is between its first and its last. -/
theorem covers_iff (r : Range) (c : Nat) : covers r c = true ↔ r.1 ≤ c ∧ c ≤ r.2.1 := by
  unfold covers
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- **The bounds of two runs in a row are the sums of their bounds.** -/
theorem width_append (m : Metrics) : ∀ a b : List Nat,
    m.width (a ++ b) = ((m.width a).1 + (m.width b).1, (m.width a).2 + (m.width b).2)
  | [], b => by
    show m.width b = (0 + (m.width b).1, 0 + (m.width b).2)
    rw [Nat.zero_add, Nat.zero_add]
  | c :: a, b => by
    have ih := width_append m a b
    show ((m.advance c).1 + (m.width (a ++ b)).1, (m.advance c).2 + (m.width (a ++ b)).2) = _
    rw [ih]
    exact congr (congrArg Prod.mk (Nat.add_assoc _ _ _).symm) (Nat.add_assoc _ _ _).symm

/-! ## What a host draws -/

/-- **What a host may draw of a run**: one advance for each character, each between the two
bounds of its character. The advance of a character may differ from place to place, as kerning
makes it. -/
def Draws (m : Metrics) : List Nat → List Nat → Prop
  | [], [] => True
  | c :: cs, a :: ws => ((m.advance c).1 ≤ a ∧ a ≤ (m.advance c).2) ∧ Draws m cs ws
  | [], _ :: _ => False
  | _ :: _, [] => False

/-- **The drawn width is between the two bounds**, whatever the host draws within the
metrics. -/
theorem width_draws (m : Metrics) : ∀ codes ws : List Nat, m.Draws codes ws →
    (m.width codes).1 ≤ ws.sum ∧ ws.sum ≤ (m.width codes).2
  | [], [], _ => ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | c :: cs, a :: ws, h => by
    have h' : ((m.advance c).1 ≤ a ∧ a ≤ (m.advance c).2) ∧ m.Draws cs ws := h
    have ih := width_draws m cs ws h'.2
    rw [List.sum_cons]
    exact ⟨Nat.add_le_add h'.1.1 ih.1, Nat.add_le_add h'.1.2 ih.2⟩
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

/-- The run fits the room, whatever the host draws within the metrics. -/
def Fits (m : Metrics) (codes : List Nat) (room : Nat) : Prop := (m.width codes).2 ≤ room

/-- Whether a run fits a room can be computed. -/
instance (m : Metrics) (codes : List Nat) (room : Nat) : Decidable (m.Fits codes room) :=
  Nat.decLe _ _

/-- **A text that fits in Lean fits on the screen**: the drawn width of a run that fits its room
is within the room, for every host that draws within the metrics. -/
theorem fits_draws (m : Metrics) (codes ws : List Nat) (room : Nat) (h : m.Fits codes room)
    (hd : m.Draws codes ws) : ws.sum ≤ room :=
  Nat.le_trans (width_draws m codes ws hd).2 h

/-- Two runs that fit their rooms fit, in a row, the two rooms together. -/
theorem fits_append (m : Metrics) (a b : List Nat) (roomA roomB : Nat) (ha : m.Fits a roomA)
    (hb : m.Fits b roomB) : m.Fits (a ++ b) (roomA + roomB) := by
  unfold Fits
  rw [width_append]
  exact Nat.add_le_add ha hb

/-- A row holds the face: its ascent above the baseline, its descent below. The baseline is
`base` below the top of the row, and the row is `rowHeight` high. -/
def FitsRow (m : Metrics) (base rowHeight : Nat) : Prop :=
  m.ascent ≤ base ∧ base + m.descent ≤ rowHeight

/-- Whether a row holds a face can be computed. -/
instance (m : Metrics) (base rowHeight : Nat) : Decidable (m.FitsRow base rowHeight) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Where the baseline is inside the row, a row holds a face where the room below the baseline
holds its descent. -/
theorem fitsRow_iff (m : Metrics) (base rowHeight : Nat) (h : base ≤ rowHeight) :
    m.FitsRow base rowHeight ↔ m.ascent ≤ base ∧ m.descent ≤ rowHeight - base := by
  unfold FitsRow
  refine ⟨fun ⟨a, b⟩ => ⟨a, ?_⟩, fun ⟨a, b⟩ => ⟨a, ?_⟩⟩
  · omega
  · omega

/-! ## A face of one advance -/

/-- **A face in which every character has the advance `cell`**: the data face. The two heights
of letters are the ascent, where the caller gives none. -/
def mono (cell ascent descent : Nat) (capHeight : Nat := ascent) (xHeight : Nat := capHeight) :
    Metrics :=
  { ascent, descent, capHeight, xHeight, ranges := [], other := (cell, cell) }

/-- **In a face of one advance, both bounds are `cell` times the count of characters.** -/
theorem mono_width (cell ascent descent capHeight xHeight : Nat) : ∀ codes : List Nat,
    (mono cell ascent descent capHeight xHeight).width codes =
      (cell * codes.length, cell * codes.length)
  | [] => rfl
  | _ :: cs => by
    have ih := mono_width cell ascent descent capHeight xHeight cs
    show (cell + ((mono cell ascent descent capHeight xHeight).width cs).1,
      cell + ((mono cell ascent descent capHeight xHeight).width cs).2) =
        (cell * (cs.length + 1), cell * (cs.length + 1))
    rw [ih, Nat.mul_add_one]
    exact congr (congrArg Prod.mk (Nat.add_comm _ _)) (Nat.add_comm _ _)

/-- A run in a face of one advance fits a room of as many cells as it has characters. -/
theorem mono_fits (cell ascent descent capHeight xHeight : Nat) (codes : List Nat) :
    (mono cell ascent descent capHeight xHeight).Fits codes (cell * codes.length) := by
  unfold Fits
  rw [mono_width]
  exact Nat.le_refl _

/-! ## Bounds in order -/

/-- Every pair of bounds of the face is in order: the least is the greatest at most. A face
that is not so describes no host. -/
def Ordered (m : Metrics) : Prop := (∀ r ∈ m.ranges, r.2.2.1 ≤ r.2.2.2) ∧ m.other.1 ≤ m.other.2

/-- Whether the bounds of a face are in order can be computed. -/
instance (m : Metrics) : Decidable m.Ordered := inferInstanceAs (Decidable (_ ∧ _))

/-- The two advances found among ranges in order are in order. -/
theorem find_le (other : Nat × Nat) (c : Nat) (ho : other.1 ≤ other.2) : ∀ rs : List Range,
    (∀ r ∈ rs, r.2.2.1 ≤ r.2.2.2) → (find rs other c).1 ≤ (find rs other c).2
  | [], _ => ho
  | r :: rs, h => by
    show (bif covers r c then r.2.2 else find rs other c).1 ≤
      (bif covers r c then r.2.2 else find rs other c).2
    cases covers r c
    · exact find_le other c ho rs fun x hx => h x (List.mem_cons_of_mem r hx)
    · exact h r List.mem_cons_self

/-- In a face whose bounds are in order, a character's least advance is its greatest at
most. -/
theorem advance_le (m : Metrics) (h : m.Ordered) (c : Nat) : (m.advance c).1 ≤ (m.advance c).2 :=
  find_le m.other c h.2 m.ranges h.1

/-- **In a face whose bounds are in order, the least width of a run is its greatest at
most.** -/
theorem width_le (m : Metrics) (h : m.Ordered) : ∀ codes : List Nat,
    (m.width codes).1 ≤ (m.width codes).2
  | [] => Nat.le_refl 0
  | c :: cs => Nat.add_le_add (advance_le m h c) (width_le m h cs)

/-- A face of one advance has its bounds in order. -/
theorem mono_ordered (cell ascent descent capHeight xHeight : Nat) :
    (mono cell ascent descent capHeight xHeight).Ordered :=
  And.intro (fun _ h => nomatch h) (Nat.le_refl cell)

/-! ## Several faces as one -/

/-- The bounds that hold two pairs of bounds: the lesser least and the greater greatest. -/
def hull (a b : Nat × Nat) : Nat × Nat := (min a.1 b.1, max a.2 b.2)

/-- The ranges `bs`, each with its bounds widened to hold `o`. -/
def widen (o : Nat × Nat) : List Range → List Range
  | [] => []
  | b :: bs => (b.1, b.2.1, hull o b.2.2) :: widen o bs

/-- The parts of the range `r` that the ranges `bs` also hold, each with the bounds that hold
both, and then `tail`. A range of `bs` that shares no code point with `r` gives no part. -/
def clip (r : Range) (tail : List Range) : List Range → List Range
  | [] => tail
  | b :: bs =>
    if max r.1 b.1 ≤ min r.2.1 b.2.1 then
      (max r.1 b.1, min r.2.1 b.2.1, hull r.2.2 b.2.2) :: clip r tail bs
    else clip r tail bs

/-- The ranges of two faces as one. For each range of the first face: its parts in the ranges of
the second, and then the range itself for the code points that the second face has in no range.
Last, the ranges of the second face for the code points that the first has in no range. -/
def joinRanges (bs : List Range) (bo ao : Nat × Nat) : List Range → List Range
  | [] => widen ao bs
  | r :: rs => clip r ((r.1, r.2.1, hull r.2.2 bo) :: joinRanges bs bo ao rs) bs

/-- **Two faces as one**: a character's bounds hold its bounds in each, and each height is the
greater of the two. -/
def join (a b : Metrics) : Metrics where
  ascent := max a.ascent b.ascent
  descent := max a.descent b.descent
  capHeight := max a.capHeight b.capHeight
  xHeight := max a.xHeight b.xHeight
  ranges := joinRanges b.ranges b.other a.other a.ranges
  other := hull a.other b.other

/-- **The metrics of several faces as one**: the bounds of each are within its bounds. With no
face it is the face of no width and no height. -/
def any : List Metrics → Metrics
  | [] => ⟨0, 0, 0, 0, [], (0, 0)⟩
  | [m] => m
  | m :: n :: ms => join m (any (n :: ms))

/-- A part of a range in another holds a code point where both ranges hold it. -/
theorem covers_clip (r b : Range) (x : Nat × Nat) (c : Nat) :
    covers (max r.1 b.1, min r.2.1 b.2.1, x) c = (covers r c && covers b c) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, covers_iff, covers_iff, covers_iff]
  show (max r.1 b.1 ≤ c ∧ c ≤ min r.2.1 b.2.1) ↔ _
  rw [Nat.max_le, Nat.le_min]
  exact ⟨fun ⟨⟨a, d⟩, e, f⟩ => ⟨⟨a, e⟩, d, f⟩, fun ⟨⟨a, e⟩, d, f⟩ => ⟨⟨a, d⟩, e, f⟩⟩

/-- Among widened ranges, a code point has its bounds among the ranges, widened. -/
theorem find_widen (o bo : Nat × Nat) (c : Nat) : ∀ bs : List Range,
    find (widen o bs) (hull o bo) c = hull o (find bs bo c)
  | [] => rfl
  | b :: bs => by
    show (bif covers b c then hull o b.2.2 else find (widen o bs) (hull o bo) c) =
      hull o (bif covers b c then b.2.2 else find bs bo c)
    cases covers b c
    · exact find_widen o bo c bs
    · rfl

/-- Among the parts of a range `r` and what follows them: a code point of `r` has the bounds
that hold those of `r` and its bounds among `bs`; any other code point has its bounds in what
follows. -/
theorem find_clip (r : Range) (bo o : Nat × Nat) (rest : List Range) (c : Nat) :
    ∀ bs : List Range, find (clip r ((r.1, r.2.1, hull r.2.2 bo) :: rest) bs) o c =
      bif covers r c then hull r.2.2 (find bs bo c) else find rest o c
  | [] => rfl
  | b :: bs => by
    have ih := find_clip r bo o rest c bs
    show find (clip r ((r.1, r.2.1, hull r.2.2 bo) :: rest) (b :: bs)) o c =
      bif covers r c then hull r.2.2 (bif covers b c then b.2.2 else find bs bo c)
      else find rest o c
    rw [clip]
    cases Nat.decLe (max r.1 b.1) (min r.2.1 b.2.1) with
    | isTrue h =>
      rw [if_pos h]
      show (bif covers (max r.1 b.1, min r.2.1 b.2.1, hull r.2.2 b.2.2) c then hull r.2.2 b.2.2
        else find (clip r ((r.1, r.2.1, hull r.2.2 bo) :: rest) bs) o c) = _
      rw [covers_clip, ih]
      cases covers r c <;> cases covers b c <;> rfl
    | isFalse h =>
      rw [if_neg h, ih]
      cases hr : covers r c with
      | false => rfl
      | true =>
        cases hb : covers b c with
        | false => rfl
        | true =>
          have hr' := (covers_iff r c).mp hr
          have hb' := (covers_iff b c).mp hb
          exact absurd (Nat.le_trans (Nat.max_le.mpr ⟨hr'.1, hb'.1⟩)
            (Nat.le_min.mpr ⟨hr'.2, hb'.2⟩)) h

/-- Among the ranges of two faces as one, a code point has the bounds that hold its bounds in
each. -/
theorem find_joinRanges (bs : List Range) (bo ao : Nat × Nat) (c : Nat) : ∀ rs : List Range,
    find (joinRanges bs bo ao rs) (hull ao bo) c = hull (find rs ao c) (find bs bo c)
  | [] => find_widen ao bo c bs
  | r :: rs => by
    show find (clip r ((r.1, r.2.1, hull r.2.2 bo) :: joinRanges bs bo ao rs) bs) (hull ao bo) c =
      hull (bif covers r c then r.2.2 else find rs ao c) (find bs bo c)
    rw [find_clip]
    cases covers r c
    · exact find_joinRanges bs bo ao c rs
    · rfl

/-- **In two faces as one, a character's bounds are exactly those that hold its bounds in
each**: the lesser least and the greater greatest. -/
theorem advance_join (a b : Metrics) (c : Nat) :
    (join a b).advance c = hull (a.advance c) (b.advance c) :=
  find_joinRanges b.ranges b.other a.other c a.ranges

/-- **In several faces as one, a character's bounds hold its bounds in each face.** -/
theorem advance_any (c : Nat) : ∀ (ms : List Metrics) (m : Metrics), m ∈ ms →
    ((any ms).advance c).1 ≤ (m.advance c).1 ∧ (m.advance c).2 ≤ ((any ms).advance c).2
  | [], _, h => nomatch h
  | [n], m, h => by
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    | inr h' => nomatch h'
  | n :: n' :: ms, m, h => by
    show ((join n (any (n' :: ms))).advance c).1 ≤ (m.advance c).1 ∧
      (m.advance c).2 ≤ ((join n (any (n' :: ms))).advance c).2
    rw [advance_join]
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact ⟨Nat.min_le_left _ _, Nat.le_max_left _ _⟩
    | inr h' =>
      have ih := advance_any c (n' :: ms) m h'
      exact ⟨Nat.le_trans (Nat.min_le_right _ _) ih.1, Nat.le_trans ih.2 (Nat.le_max_right _ _)⟩

/-- **Each bound of several faces as one is the bound of one of them**: the bounds are no wider
than the faces make them. -/
theorem advance_any_attained (c : Nat) : ∀ ms : List Metrics, ms ≠ [] →
    (∃ m ∈ ms, ((any ms).advance c).1 = (m.advance c).1) ∧
      (∃ m ∈ ms, ((any ms).advance c).2 = (m.advance c).2)
  | [], h => absurd rfl h
  | [n], _ => ⟨⟨n, List.mem_cons_self, rfl⟩, ⟨n, List.mem_cons_self, rfl⟩⟩
  | n :: n' :: ms, _ => by
    obtain ⟨⟨m1, hm1, e1⟩, ⟨m2, hm2, e2⟩⟩ :=
      advance_any_attained c (n' :: ms) (List.cons_ne_nil _ _)
    show (∃ m ∈ n :: n' :: ms, ((join n (any (n' :: ms))).advance c).1 = (m.advance c).1) ∧
      (∃ m ∈ n :: n' :: ms, ((join n (any (n' :: ms))).advance c).2 = (m.advance c).2)
    rw [advance_join]
    refine ⟨?_, ?_⟩
    · cases Nat.le_total (n.advance c).1 ((any (n' :: ms)).advance c).1 with
      | inl h => exact ⟨n, List.mem_cons_self, Nat.min_eq_left h⟩
      | inr h => exact ⟨m1, List.mem_cons_of_mem n hm1, (Nat.min_eq_right h).trans e1⟩
    · cases Nat.le_total (n.advance c).2 ((any (n' :: ms)).advance c).2 with
      | inl h => exact ⟨m2, List.mem_cons_of_mem n hm2, (Nat.max_eq_right h).trans e2⟩
      | inr h => exact ⟨n, List.mem_cons_self, Nat.max_eq_left h⟩

/-- In several faces as one, the bounds of a run hold its bounds in each face. -/
theorem width_any (ms : List Metrics) (m : Metrics) (h : m ∈ ms) : ∀ codes : List Nat,
    ((any ms).width codes).1 ≤ (m.width codes).1 ∧ (m.width codes).2 ≤ ((any ms).width codes).2
  | [] => ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | c :: cs =>
    ⟨Nat.add_le_add (advance_any c ms m h).1 (width_any ms m h cs).1,
      Nat.add_le_add (advance_any c ms m h).2 (width_any ms m h cs).2⟩

/-- **A room computed for a list of fallback families holds for the one the host picks**: a
run that fits a room in several faces as one fits it in each face. -/
theorem fits_any (ms : List Metrics) (codes : List Nat) (room : Nat)
    (h : (any ms).Fits codes room) (m : Metrics) (hm : m ∈ ms) : m.Fits codes room :=
  Nat.le_trans (width_any ms m hm codes).2 h

/-- What a host may draw in one of several faces, it may draw in the faces as one. -/
theorem draws_any (ms : List Metrics) (m : Metrics) (hm : m ∈ ms) : ∀ codes ws : List Nat,
    m.Draws codes ws → (any ms).Draws codes ws
  | [], [], _ => True.intro
  | c :: cs, a :: ws, h => by
    have h' : ((m.advance c).1 ≤ a ∧ a ≤ (m.advance c).2) ∧ m.Draws cs ws := h
    have hc := advance_any c ms m hm
    exact ⟨⟨Nat.le_trans hc.1 h'.1.1, Nat.le_trans h'.1.2 hc.2⟩, draws_any ms m hm cs ws h'.2⟩
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

/-- In several faces as one, each height is the height of each face at least. -/
theorem heights_any : ∀ (ms : List Metrics) (m : Metrics), m ∈ ms →
    m.ascent ≤ (any ms).ascent ∧ m.descent ≤ (any ms).descent ∧
      m.capHeight ≤ (any ms).capHeight ∧ m.xHeight ≤ (any ms).xHeight
  | [], _, h => nomatch h
  | [n], m, h => by
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
    | inr h' => nomatch h'
  | n :: n' :: ms, m, h => by
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩
    | inr h' =>
      obtain ⟨a, b, d, e⟩ := heights_any (n' :: ms) m h'
      exact ⟨Nat.le_trans a (Nat.le_max_right _ _), Nat.le_trans b (Nat.le_max_right _ _),
        Nat.le_trans d (Nat.le_max_right _ _), Nat.le_trans e (Nat.le_max_right _ _)⟩

/-- **A row that holds several faces as one holds each face.** -/
theorem fitsRow_any (ms : List Metrics) (base rowHeight : Nat)
    (h : (any ms).FitsRow base rowHeight) (m : Metrics) (hm : m ∈ ms) :
    m.FitsRow base rowHeight :=
  have hs := heights_any ms m hm
  ⟨Nat.le_trans hs.1 h.1, Nat.le_trans (Nat.add_le_add_left hs.2.1 base) h.2⟩

/-! ## Digits of one advance -/

/-- A code point of a digit, from `0` to `9`. -/
def Digit (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 57

/-- The first `n` digits all have `g` as both their bounds. -/
def digitsHave (m : Metrics) (g : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => decide (m.advance (48 + n) = (g, g)) && digitsHave m g n

/-- The first `n` digits all have `g` as both their bounds, where the check says so and only
there. -/
theorem digitsHave_iff (m : Metrics) (g : Nat) : ∀ n : Nat,
    digitsHave m g n = true ↔ ∀ k, k < n → m.advance (48 + k) = (g, g)
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | n + 1 => by
    rw [digitsHave, Bool.and_eq_true, decide_eq_true_eq, digitsHave_iff m g n]
    refine ⟨fun ⟨h0, hn⟩ k hk => ?_, fun h => ⟨h n (Nat.lt_succ_self n), fun k hk =>
      h k (Nat.lt_succ_of_lt hk)⟩⟩
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with
    | inl e =>
      rw [e]
      exact h0
    | inr lt => exact hn k lt

/-- **Every digit has one advance, and the face knows it exactly**: the two bounds of every
digit are the least advance of the digit `0`. A face whose digits have one advance that it
knows only between two bounds is not `tabular` here. -/
def tabular (m : Metrics) : Bool := digitsHave m (m.advance 48).1 10

/-- In a tabular face, the two bounds of a digit are the least advance of the digit `0`. -/
theorem tabular_advance (m : Metrics) (h : m.tabular = true) (c : Nat) (hc : Digit c) :
    m.advance c = ((m.advance 48).1, (m.advance 48).1) := by
  have h1 : 48 ≤ c := hc.1
  have h2 : c ≤ 57 := hc.2
  have h' := (digitsHave_iff m (m.advance 48).1 10).mp h (c - 48) (by omega)
  have e : 48 + (c - 48) = c := by omega
  rw [e] at h'
  exact h'

/-- In a tabular face, both bounds of a run of digits are the advance of a digit times their
count. -/
theorem tabular_width (m : Metrics) (h : m.tabular = true) : ∀ codes : List Nat,
    (∀ c ∈ codes, Digit c) →
    m.width codes = ((m.advance 48).1 * codes.length, (m.advance 48).1 * codes.length)
  | [], _ => rfl
  | c :: cs, hd => by
    have ih := tabular_width m h cs fun x hx => hd x (List.mem_cons_of_mem c hx)
    show ((m.advance c).1 + (m.width cs).1, (m.advance c).2 + (m.width cs).2) =
      ((m.advance 48).1 * (cs.length + 1), (m.advance 48).1 * (cs.length + 1))
    rw [ih, tabular_advance m h c (hd c List.mem_cons_self), Nat.mul_add_one]
    exact congr (congrArg Prod.mk (Nat.add_comm _ _)) (Nat.add_comm _ _)

/-- **In a tabular face, two runs of digits of one count have one width, the least equal to the
greatest.** Counts and addresses align on the right. -/
theorem tabular_aligns (m : Metrics) (h : m.tabular = true) (a b : List Nat)
    (ha : ∀ c ∈ a, Digit c) (hb : ∀ c ∈ b, Digit c) (hlen : a.length = b.length) :
    m.width a = m.width b ∧ (m.width a).1 = (m.width a).2 := by
  rw [tabular_width m h a ha, tabular_width m h b hb, hlen]
  exact ⟨rfl, rfl⟩

/-- A face of one advance is tabular. -/
theorem mono_tabular (cell ascent descent capHeight xHeight : Nat) :
    (mono cell ascent descent capHeight xHeight).tabular = true :=
  (digitsHave_iff _ cell 10).mpr fun _ _ => rfl

/-! ## The code points of a string -/

/-- The code points of a run of UTF-8 bytes, read from the left. `cur` is the code point that
is being read. A byte that continues a character adds six bits to it; any other byte ends it
and begins the next. -/
def codesOfBytes : Option Nat → List UInt8 → List Nat
  | cur, [] => cur.toList
  | cur, b :: bs =>
    if 128 ≤ b.toNat ∧ b.toNat < 192 then
      codesOfBytes (some (cur.getD 0 * 64 + (b.toNat - 128))) bs
    else
      cur.toList ++ codesOfBytes (some (
        if b.toNat < 128 then b.toNat
        else if b.toNat < 224 then b.toNat - 192
        else if b.toNat < 240 then b.toNat - 224
        else b.toNat - 240)) bs

/-- **The code points of a string**, for `width` and `Fits`. It reads the bytes of the string,
because the functions of core that read its characters are over this layer's ceiling. -/
def codes (text : String) : List Nat := codesOfBytes none text.toUTF8.data.toList

end Metrics

/-! ## Finite evaluations -/

-- The code points of a string whose characters take one, two, three and four bytes.
#guard Metrics.codes (String.ofList [Char.ofNat 97, Char.ofNat 233, Char.ofNat 8364,
  Char.ofNat 128512]) = [97, 233, 8364, 128512]

-- A line of a program in the data face, a cell of eight units: twenty-nine cells.
#guard (Metrics.mono 8000 16000 8000).width (Metrics.codes "awaitFiber (var 0) awaitValue") =
  (232000, 232000)

-- A proportional face with tabular digits: letters between two bounds, a space in no range.
#guard (⟨10000, 3000, 7000, 5000, [(48, 57, 5500, 5500), (97, 122, 2500, 9000)], (2000, 12000)⟩ :
  Metrics).width (Metrics.codes "fiber 12") = (25500, 68000)

-- A control: eight characters fit eight cells of 5000 in a face of one advance, and a
-- proportional face may draw the same text wider. A count of cells is no width of it.
#guard (Metrics.mono 5000 10000 3000).Fits (Metrics.codes "fiber 12") 40000
#guard ¬ (⟨10000, 3000, 7000, 5000, [(48, 57, 5500, 5500), (97, 122, 2500, 9000)],
  (2000, 12000)⟩ : Metrics).Fits (Metrics.codes "fiber 12") 40000

-- Two fallback families as one: a letter has the lesser least and the greater greatest, and a
-- code point in a range of one face only has the other face's `other` in its bounds.
#guard (Metrics.any [⟨10000, 3000, 7000, 5000, [(97, 122, 2500, 9000)], (2000, 12000)⟩,
  ⟨11000, 2500, 7200, 5100, [(97, 109, 3000, 9500), (48, 57, 6000, 6000)], (1000, 10000)⟩]).width
    [97, 122, 48, 32] = (2500 + 1000 + 2000 + 1000, 9500 + 10000 + 12000 + 12000)

-- A control for `tabular_aligns`: where the digit `1` is narrower than the digit `0`, the face
-- is not tabular, and two runs of two digits have two widths.
#guard (⟨10000, 3000, 7000, 5000, [(49, 49, 3000, 3000), (48, 57, 5500, 5500)], (2000, 12000)⟩ :
  Metrics).tabular = false
#guard (⟨10000, 3000, 7000, 5000, [(49, 49, 3000, 3000), (48, 57, 5500, 5500)], (2000, 12000)⟩ :
  Metrics).width [49, 49] ≠ (⟨10000, 3000, 7000, 5000, [(49, 49, 3000, 3000),
    (48, 57, 5500, 5500)], (2000, 12000)⟩ : Metrics).width [48, 48]

-- A control for `FitsRow`: a baseline below the row holds no face, though the face has no
-- descent and the row's height less the baseline is `0` in whole numbers.
#guard ¬ (Metrics.mono 8000 16000 0).FitsRow 30000 24000
#guard (Metrics.mono 8000 16000 8000).FitsRow 16000 24000

end Whatwg.Svg.Scene
