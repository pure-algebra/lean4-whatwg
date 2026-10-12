import Whatwg.Svg.Scene.Metrics

/-!
# Whatwg.Svg.Scene.Label

Owner: a label fitted to a room (slice S14 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-76).

A node of a picture has a label, and its box is often too small for it. A label that is cut at
its end loses the piece that names the thing, and two long names with one prefix become one
text. Here a label is a list of pieces that are never broken: a name, a number, a mark of
punctuation. A piece carries its width, how much it matters, and whether a line may end after
it. The fitting reads no character and holds no text. It takes widths from the caller and gives
back the identities of pieces, so it needs no font and no fraction and stays under the strict
ceiling.

A label is shown in the first of four forms that its room holds:

- whole: every piece, on the fewest lines that hold them, three at most, and among the ways to
  break it into that many lines the one whose widest line is the narrowest;
- cut: the pieces that matter most, with one mark for each run of pieces that are left out. The
  piece of least `keep` is left out first, and the later one on a tie;
- a sign, where a mark fits: the thing is there, and its name is not shown;
- nothing.

- `Piece π`, `Shown π`: a piece and a form. `Shown.text`, `Shown.pieces`, `Shown.rank`,
  `Shown.rows`: what a form says.
- `Label.fit room rows mark label`: one label in a room of `room` by `rows` lines.
- `Label.fitAll room rows mark labels`: the labels of one picture. Each is `Label.fitAmong`:
  a cut is shown only where its text reads as that label and as no other label of the picture.
- `Label.Reads text label`: a cut text reads as a label. Each piece of the text is that piece
  of the label, in order, and each mark stands for one piece or more that is left out.
  `Label.reads` computes it.
- `Label.broken`, `Label.ranked`, `Label.elide`: the lines, the ranks of the pieces, and the
  cut text of a level.
- `Label.fitWith ok`: the fit with a test of the caller on a cut text. `fit` and `fitAmong` are
  `fitWith`, so each law of `fitWith` is a law of both.

What the laws say of a picture whose labels are fitted here:

- `fit_fits` (`fitWith_whole`, `fitWith_cut`, `fitWith_sign`, `fitWith_rows`): each line of the
  result is within the room at its greatest width, there are `rows` lines at most, and a line
  ends only after a piece that permits it. A piece is never broken: a line is a list of pieces.
- `fit_whole`, `fit_one_line`: a whole result holds every piece of the label, in order, and a
  label that fits on one line is shown whole on one line.
- `fitWith_whole_of`, `cutOf_lowest`: the form is the first that the room holds. A label that
  can be put on lines within the room is shown whole, and a cut is of the lowest level that
  may be shown within the room.
- `fit_subsequence` (`fitWith_reads`): a cut text reads as its label. Its pieces are pieces of
  the label in order (`Reads.sublist`), and a mark stands at each place where pieces were left
  out and nowhere else. A run that is left out has one mark (`fitWith_cut_apart`).
- `fitWith_cut_marked`, `fitWith_unmarked`: a cut text has a mark, and a text with no mark is
  the whole label. So a cut text never reads as a whole one.
- `mem_elide`: a piece of a cut text is a piece of the label with that piece's widths, or a
  mark as wide as the caller's mark. The fitting makes no width.
- `fit_mono`, `fitAll_mono`: with more room, in width or in rows, the result shows every piece
  that it showed with less, and its form says no less. A picture drawn larger never says less.
- `fitAmong_alone`: a text that is shown reads as its own label and as no other label of the
  picture. `fitAll_distinct`: two labels that differ, both shown as text, are shown as two
  texts. Where the only cut that fits reads as two labels, neither is shown as text: each is a
  sign, and the picture says that it does not tell them apart.
- `ranked_order`: of two pieces of a label, the one of lesser rank has less `keep`, or as much
  and a later place. A cut shows the pieces of its level's rank or more, so what it leaves out
  matters no more than what it shows.
- `broken_balanced`, `broken_fewest`: no way to put the pieces on as many lines has a narrower
  widest line, and no way to put them on fewer lines is within the room.
- `wide_text`: where each piece is as wide as its text in a face, a line is as wide as its
  text in `Metrics.width`. So a line that is within the room here is a text that `Metrics.Fits`
  puts within it.

What a caller must supply: the pieces, made from its own structure and not from a lexer; for
each piece its two widths, from `Metrics.width` or from a count of cells; its `keep`, where the
piece that names the thing has the most; whether a line may end after it; and the width of the
mark of a cut. The caller writes the text of each piece, of the mark and of the sign itself.

What this module does not claim: that some cut is shown wherever one would fit, since only the
cuts of the levels are tried, in the order of `keep`; that each level leaves out one piece more
than the level before, which the evaluations below show for one label; that a mark is never
alone on a line; a width for a piece that the caller did not measure; more than three lines; a
fast answer for a long label with many marks, since `reads` takes each way a mark may stand for
a run in turn. The least width of a piece is carried and not used.
-/

namespace Whatwg.Svg.Scene

/-- A piece of a label that is never broken: a name, a number, a mark of punctuation. -/
structure Piece (π : Type) where
  /-- what the piece is: the caller writes its text -/
  id : π
  /-- its least width -/
  least : Nat
  /-- its greatest width: the fitting gives the piece this much room -/
  greatest : Nat
  /-- how much the piece matters: the piece that names the thing has the most -/
  keep : Nat
  /-- a line may end after this piece -/
  breakAfter : Bool
  deriving DecidableEq, Repr

/-- How a label is shown. Each form says less than the one before it. -/
inductive Shown (π : Type) where
  /-- every piece, on these lines -/
  | whole (lines : List (List π))
  /-- some pieces, with a mark where others were left out: `none` is a mark -/
  | cut (lines : List (List (Option π)))
  /-- a sign of one or two characters: the thing is there, and its name is not shown -/
  | sign
  /-- nothing -/
  | none
  deriving DecidableEq, Repr

/-- A piece of a text in a face: its two widths are those of its run of characters. -/
def Piece.of {π : Type} (m : Metrics) (id : π) (codes : List Nat) (keep : Nat)
    (breakAfter : Bool) : Piece π :=
  ⟨id, (m.width codes).1, (m.width codes).2, keep, breakAfter⟩

/-- A piece that is its own text, measured in a face. -/
def Piece.text (m : Metrics) (text : String) (keep : Nat) (breakAfter : Bool) : Piece String :=
  Piece.of m text (Metrics.codes text) keep breakAfter

/-- A label whose pieces are their own texts, measured in a face: for each piece its text, its
`keep`, and whether a line may end after it. -/
def Label.ofTexts (m : Metrics) (parts : List (String × Nat × Bool)) : List (Piece String) :=
  parts.map fun part => Piece.text m part.1 part.2.1 part.2.2

namespace Shown

variable {π : Type}

/-- The text of a form, piece by piece, with `none` at each mark. A sign and nothing have no
text. -/
def text : Shown π → Option (List (Option π))
  | .whole lines => some (lines.flatten.map some)
  | .cut lines => some lines.flatten
  | .sign => Option.none
  | .none => Option.none

/-- The pieces that a form shows, in order. -/
def pieces : Shown π → List π
  | .whole lines => lines.flatten
  | .cut lines => lines.flatten.filterMap id
  | .sign => []
  | .none => []

/-- How much a form says: `3` for the whole label, `2` for a cut, `1` for a sign, `0` for
nothing. -/
def rank : Shown π → Nat
  | .whole _ => 3
  | .cut _ => 2
  | .sign => 1
  | .none => 0

/-- How many lines a form takes. A sign takes one. -/
def rows : Shown π → Nat
  | .whole lines => lines.length
  | .cut lines => lines.length
  | .sign => 1
  | .none => 0

end Shown

namespace Label

variable {π σ : Type}

/-! ## A text that reads as a label -/

/-- **A cut text reads as a label**: each piece of the text is that piece of the label, in
order, and each mark stands for one piece or more that the text leaves out. Nothing else is left
out. A text with no mark reads as itself only. -/
inductive Reads : List (Option π) → List π → Prop where
  /-- the text of no piece reads as the label of no piece -/
  | nil : Reads [] []
  /-- a piece of the text is the next piece of the label -/
  | piece (a : π) {text : List (Option π)} {label : List π} (h : Reads text label) :
    Reads (some a :: text) (a :: label)
  /-- a mark stands for one piece of the label -/
  | mark (a : π) {text : List (Option π)} {label : List π} (h : Reads text label) :
    Reads (Option.none :: text) (a :: label)
  /-- a mark stands for one piece more -/
  | more (a : π) {text : List (Option π)} {label : List π}
    (h : Reads (Option.none :: text) label) : Reads (Option.none :: text) (a :: label)

/-- A label reads as itself. -/
theorem Reads.refl : ∀ a : List π, Reads (a.map some) a
  | [] => Reads.nil
  | x :: a => Reads.piece x (Reads.refl a)

/-- **A text with no mark reads as one label only**: itself. -/
theorem Reads.whole : ∀ (a b : List π), Reads (a.map some) b → a = b
  | [], b, h => by
    have h' : Reads ([] : List (Option π)) b := h
    cases h'
    rfl
  | x :: a, b, h => by
    have h' : Reads (some x :: a.map some) b := h
    cases h' with
    | piece _ h'' => exact congrArg (x :: ·) (Reads.whole a _ h'')

/-- **The pieces of a text are pieces of the label that it reads as, in the label's order.** -/
theorem Reads.sublist {text : List (Option π)} {label : List π} (h : Reads text label) :
    (text.filterMap id).Sublist label := by
  induction h with
  | nil => exact List.Sublist.slnil
  | piece a _ ih => exact List.Sublist.cons_cons a ih
  | mark a _ ih => exact List.Sublist.cons a ih
  | more a _ ih => exact List.Sublist.cons a ih

/-- Whether a text reads as a label, computed. -/
def reads [DecidableEq π] : List (Option π) → List π → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | some a :: text, b :: label => decide (a = b) && reads text label
  | Option.none :: text, _ :: label => reads text label || reads (Option.none :: text) label

/-- Where a text reads as a label, the computation says so. -/
theorem reads_of_reads [DecidableEq π] {text : List (Option π)} {label : List π}
    (h : Reads text label) : reads text label = true := by
  induction h with
  | nil => rfl
  | @piece a text label _ ih =>
    show (decide (a = a) && reads text label) = true
    rw [ih, decide_eq_true rfl]
    rfl
  | @mark a text label _ ih =>
    show (reads text label || reads (Option.none :: text) label) = true
    rw [ih]
    rfl
  | @more a text label _ ih =>
    show (reads text label || reads (Option.none :: text) label) = true
    rw [ih]
    exact Bool.or_true _

/-- Where the computation says that a text reads as a label, it does. -/
theorem reads_sound [DecidableEq π] : ∀ (label : List π) (text : List (Option π)),
    reads text label = true → Reads text label
  | [], [], _ => Reads.nil
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | b :: label, some a :: text, h => by
    have h' : (decide (a = b) && reads text label) = true := h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h'
    rw [h'.1]
    exact Reads.piece b (reads_sound label text h'.2)
  | b :: label, Option.none :: text, h => by
    have h' : (reads text label || reads (Option.none :: text) label) = true := h
    rw [Bool.or_eq_true] at h'
    cases h' with
    | inl h1 => exact Reads.mark b (reads_sound label text h1)
    | inr h2 => exact Reads.more b (reads_sound label (Option.none :: text) h2)

/-! ## Lines and their widths -/

/-- What the pieces are, in order. -/
def ids (pieces : List (Piece σ)) : List σ := pieces.map fun p => p.id

/-- The greatest width of a line: the sum of the greatest widths of its pieces. -/
def wide : List (Piece σ) → Nat
  | [] => 0
  | p :: line => p.greatest + wide line

/-- The cost of a breaking: the greatest width of its widest line. -/
def cost : List (List (Piece σ)) → Nat
  | [] => 0
  | line :: lines => max (wide line) (cost lines)

/-- The line ends after a piece that permits a break. -/
def endsOpen : List (Piece σ) → Bool
  | [] => false
  | [p] => p.breakAfter
  | _ :: q :: line => endsOpen (q :: line)

/-- Every line but the last ends after a piece that permits a break. -/
def Permitted : List (List (Piece σ)) → Prop
  | [] => True
  | [_] => True
  | a :: b :: lines => endsOpen a = true ∧ Permitted (b :: lines)

/-- A line is as wide as the cost of its breaking at most. -/
theorem wide_le_cost : ∀ (lines : List (List (Piece σ))) (line : List (Piece σ)),
    line ∈ lines → wide line ≤ cost lines
  | [], _, h => nomatch h
  | a :: lines, line, h => by
    show wide line ≤ max (wide a) (cost lines)
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact Nat.le_max_left _ _
    | inr h' => exact Nat.le_trans (wide_le_cost lines line h') (Nat.le_max_right _ _)

/-- The pieces of the lines, line after line, are the pieces of the whole. -/
theorem ids_flatten : ∀ lines : List (List (Piece σ)),
    (lines.map ids).flatten = ids lines.flatten
  | [] => rfl
  | a :: lines => by
    show ids a ++ (lines.map ids).flatten = ids (a ++ lines.flatten)
    rw [ids_flatten lines]
    exact List.map_append.symm

/-- **Where each piece is as wide as its text in a face, a line is as wide as its text.** So a
line that the fitting puts within a room is a text that `Metrics.Fits` puts within it. -/
theorem wide_text (m : Metrics) (text : σ → List Nat) : ∀ line : List (Piece σ),
    (∀ p ∈ line, p.greatest = (m.width (text p.id)).2) →
    wide line = (m.width (line.flatMap fun p => text p.id)).2
  | [], _ => rfl
  | p :: line, h => by
    show p.greatest + wide line = _
    rw [List.flatMap_cons, Metrics.width_append, h p List.mem_cons_self,
      wide_text m text line fun q hq => h q (List.mem_cons_of_mem p hq)]

/-! ## Breaking into lines -/

/-- Every way to end a first line after a piece that permits it, with pieces left for a second:
the first line and the rest. -/
def splits : List (Piece σ) → List (List (Piece σ) × List (Piece σ))
  | [] => []
  | [_] => []
  | p :: q :: l =>
    (bif p.breakAfter then [([p], q :: l)] else []) ++
      (splits (q :: l)).map fun ab => (p :: ab.1, ab.2)

/-- Every breaking of pieces into `k` lines at permitted places, no line empty where `k` is two
or more. -/
def breakings : Nat → List (Piece σ) → List (List (List (Piece σ)))
  | 0, _ => []
  | 1, l => [[l]]
  | k + 2, l => (splits l).flatMap fun ab => (breakings (k + 1) ab.2).map fun lines => ab.1 :: lines

/-- A split has all the pieces in order, its first line ends where a break is permitted, and
pieces are left. -/
theorem mem_splits : ∀ (l a b : List (Piece σ)), (a, b) ∈ splits l →
    a ++ b = l ∧ endsOpen a = true ∧ b ≠ []
  | [], _, _, h => nomatch h
  | [_], _, _, h => nomatch h
  | p :: q :: l, a, b, h => by
    have h' : (a, b) ∈ (bif p.breakAfter then [([p], q :: l)] else []) ++
      (splits (q :: l)).map fun ab => (p :: ab.1, ab.2) := h
    cases List.mem_append.mp h' with
    | inl h1 =>
      cases hb : p.breakAfter with
      | false =>
        rw [hb] at h1
        have h2 : (a, b) ∈ ([] : List (List (Piece σ) × List (Piece σ))) := h1
        nomatch h2
      | true =>
        rw [hb] at h1
        have h2 : (a, b) ∈ [([p], q :: l)] := h1
        cases List.mem_singleton.mp h2
        exact ⟨rfl, hb, List.cons_ne_nil _ _⟩
    | inr h1 =>
      obtain ⟨ab, hm, e⟩ := List.mem_map.mp h1
      have e' : (p :: ab.1, ab.2) = (a, b) := e
      cases e'
      obtain ⟨e1, e2, e3⟩ := mem_splits (q :: l) ab.1 ab.2 hm
      refine ⟨by rw [List.cons_append, e1], ?_, e3⟩
      cases hab : ab.1 with
      | nil =>
        rw [hab] at e2
        exact absurd e2 Bool.false_ne_true
      | cons x rest =>
        rw [hab] at e2
        exact e2

/-- **A breaking has every piece, in order**, as many lines as were asked for, and ends each
line but the last where a break is permitted. -/
theorem mem_breakings : ∀ (k : Nat) (l : List (Piece σ)) (lines : List (List (Piece σ))),
    lines ∈ breakings k l → lines.flatten = l ∧ lines.length = k ∧ Permitted lines
  | 0, _, _, h => nomatch h
  | 1, l, lines, h => by
    have h' : lines ∈ [[l]] := h
    cases List.mem_singleton.mp h'
    exact ⟨List.append_nil l, rfl, True.intro⟩
  | k + 2, l, lines, h => by
    have h' : lines ∈ (splits l).flatMap fun ab =>
      (breakings (k + 1) ab.2).map fun ls => ab.1 :: ls := h
    obtain ⟨ab, hab, hl⟩ := List.mem_flatMap.mp h'
    obtain ⟨rest, hr, e⟩ := List.mem_map.mp hl
    have e' : ab.1 :: rest = lines := e
    cases e'
    obtain ⟨e1, e2, _⟩ := mem_splits l ab.1 ab.2 hab
    obtain ⟨f1, f2, f3⟩ := mem_breakings (k + 1) ab.2 rest hr
    refine ⟨?_, ?_, ?_⟩
    · show ab.1 ++ rest.flatten = l
      rw [f1, e1]
    · show rest.length + 1 = k + 2
      rw [f2]
    · cases rest with
      | nil => exact absurd f2 (Nat.succ_ne_zero k).symm
      | cons b0 rest' => exact ⟨e2, f3⟩

/-- A first line that ends where a break is permitted, with pieces left after it, is a split. -/
theorem splits_complete : ∀ (a b : List (Piece σ)), endsOpen a = true → b ≠ [] →
    (a, b) ∈ splits (a ++ b)
  | [], _, h, _ => absurd h Bool.false_ne_true
  | [p], b, h, hb => by
    cases b with
    | nil => exact absurd rfl hb
    | cons q l =>
      have hp : p.breakAfter = true := h
      show ([p], q :: l) ∈ (bif p.breakAfter then [([p], q :: l)] else []) ++
        (splits (q :: l)).map fun ab => (p :: ab.1, ab.2)
      rw [hp]
      exact List.mem_append.mpr (Or.inl List.mem_cons_self)
  | p :: x :: a, b, h, hb => by
    have ih := splits_complete (x :: a) b h hb
    show (p :: x :: a, b) ∈ (bif p.breakAfter then [([p], x :: (a ++ b))] else []) ++
      (splits (x :: (a ++ b))).map fun ab => (p :: ab.1, ab.2)
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨(x :: a, b), ih, rfl⟩))

/-- **Every breaking at permitted places is among the breakings**: lines of which none is
empty, each but the last ending where a break is permitted, are a breaking of their pieces into
their count of lines. -/
theorem breakings_complete : ∀ lines : List (List (Piece σ)), lines ≠ [] →
    (∀ line ∈ lines, line ≠ []) → Permitted lines →
    lines ∈ breakings lines.length lines.flatten
  | [], h, _, _ => absurd rfl h
  | [l], _, _, _ => by
    show [l] ∈ breakings 1 (l ++ [])
    rw [List.append_nil]
    exact List.mem_cons_self
  | a :: b :: rest, _, hne, hp => by
    have ih := breakings_complete (b :: rest) (List.cons_ne_nil _ _)
      (fun x hx => hne x (List.mem_cons_of_mem a hx)) hp.2
    have hb : (b :: rest).flatten ≠ [] := by
      have hb0 := hne b (List.mem_cons_of_mem a List.mem_cons_self)
      cases b with
      | nil => exact absurd rfl hb0
      | cons y b' => exact List.cons_ne_nil _ _
    have hs := splits_complete a (b :: rest).flatten hp.1 hb
    show a :: b :: rest ∈ (splits (a ++ (b :: rest).flatten)).flatMap fun ab =>
      (breakings (rest.length + 1) ab.2).map fun ls => ab.1 :: ls
    exact List.mem_flatMap.mpr ⟨(a, (b :: rest).flatten), hs,
      List.mem_map.mpr ⟨b :: rest, ih, rfl⟩⟩

/-- The breaking of least cost among `c` and those of a list, the first of them on a tie. -/
def bestFrom (c : List (List (Piece σ))) : List (List (List (Piece σ))) → List (List (Piece σ))
  | [] => c
  | d :: ds => if cost d < cost c then bestFrom d ds else bestFrom c ds

/-- The breaking of least cost of a list, the first of them on a tie. -/
def best : List (List (List (Piece σ))) → Option (List (List (Piece σ)))
  | [] => Option.none
  | c :: cs => some (bestFrom c cs)

/-- The best is one of the breakings, and none of them costs less. -/
theorem bestFrom_spec : ∀ (ds : List (List (List (Piece σ)))) (c : List (List (Piece σ))),
    (bestFrom c ds = c ∨ bestFrom c ds ∈ ds) ∧ cost (bestFrom c ds) ≤ cost c ∧
      ∀ d ∈ ds, cost (bestFrom c ds) ≤ cost d
  | [], c => ⟨Or.inl rfl, Nat.le_refl _, fun _ h => nomatch h⟩
  | d :: ds, c => by
    rw [bestFrom]
    cases Nat.decLt (cost d) (cost c) with
    | isTrue h =>
      rw [if_pos h]
      obtain ⟨m, le, all⟩ := bestFrom_spec ds d
      refine ⟨Or.inr ?_, Nat.le_trans le (Nat.le_of_lt h), fun x hx => ?_⟩
      · cases m with
        | inl e =>
          rw [e]
          exact List.mem_cons_self
        | inr hm => exact List.mem_cons_of_mem d hm
      · cases List.mem_cons.mp hx with
        | inl e =>
          rw [e]
          exact le
        | inr hx' => exact all x hx'
    | isFalse h =>
      rw [if_neg h]
      obtain ⟨m, le, all⟩ := bestFrom_spec ds c
      refine ⟨?_, le, fun x hx => ?_⟩
      · cases m with
        | inl e => exact Or.inl e
        | inr hm => exact Or.inr (List.mem_cons_of_mem d hm)
      · cases List.mem_cons.mp hx with
        | inl e =>
          rw [e]
          exact Nat.le_trans le (Nat.le_of_not_lt h)
        | inr hx' => exact all x hx'

/-- The best of a list is one of the list, and none of the list costs less. -/
theorem best_spec : ∀ (cs : List (List (List (Piece σ)))) (c : List (List (Piece σ))),
    best cs = some c → c ∈ cs ∧ ∀ d ∈ cs, cost c ≤ cost d
  | [], _, h => nomatch h
  | x :: cs, c, h => by
    have h' : some (bestFrom x cs) = some c := h
    cases h'
    obtain ⟨m, le, all⟩ := bestFrom_spec cs x
    refine ⟨?_, fun d hd => ?_⟩
    · cases m with
      | inl e =>
        rw [e]
        exact List.mem_cons_self
      | inr hm => exact List.mem_cons_of_mem x hm
    · cases List.mem_cons.mp hd with
      | inl e =>
        rw [e]
        exact le
      | inr hd' => exact all d hd'

/-- A list with no best is empty. -/
theorem best_none : ∀ cs : List (List (List (Piece σ))), best cs = Option.none → cs = []
  | [], _ => rfl
  | _ :: _, h => nomatch h

/-! ## The first that fits -/

/-- The first of `j`, `j + 1`, and so on, `fuel` numbers in all, at which `f` has a value: the
number and the value. -/
def firstSome {α : Type} (f : Nat → Option α) : Nat → Nat → Option (Nat × α)
  | 0, _ => Option.none
  | fuel + 1, j =>
    match f j with
    | some a => some (j, a)
    | Option.none => firstSome f fuel (j + 1)

/-- What the first is: `f` has that value there, it is among the numbers searched, and `f` has
no value before it. -/
theorem firstSome_spec {α : Type} (f : Nat → Option α) : ∀ (fuel j x : Nat) (a : α),
    firstSome f fuel j = some (x, a) →
    f x = some a ∧ j ≤ x ∧ x < j + fuel ∧ ∀ y, j ≤ y → y < x → f y = Option.none
  | 0, _, _, _, h => nomatch h
  | fuel + 1, j, x, a, h => by
    have h' : (match f j with
      | some a => some (j, a)
      | Option.none => firstSome f fuel (j + 1)) = some (x, a) := h
    cases hf : f j with
    | some b =>
      rw [hf] at h'
      have e : some (j, b) = some (x, a) := h'
      cases e
      exact ⟨hf, Nat.le_refl _, Nat.lt_add_of_pos_right (Nat.succ_pos fuel),
        fun y h1 h2 => absurd h1 (Nat.not_le_of_lt h2)⟩
    | none =>
      rw [hf] at h'
      have h'' : firstSome f fuel (j + 1) = some (x, a) := h'
      obtain ⟨p1, p2, p3, p4⟩ := firstSome_spec f fuel (j + 1) x a h''
      have q2 : j ≤ x := Nat.le_of_succ_le p2
      have q3 : x < j + (fuel + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 fuel] at p3
        exact p3
      refine ⟨p1, q2, q3, fun y h1 h2 => ?_⟩
      cases Nat.eq_or_lt_of_le h1 with
      | inl e =>
        rw [← e]
        exact hf
      | inr lt => exact p4 y lt h2

/-- Where there is no first, `f` has no value at any of the numbers searched. -/
theorem firstSome_none {α : Type} (f : Nat → Option α) : ∀ (fuel j : Nat),
    firstSome f fuel j = Option.none → ∀ y, j ≤ y → y < j + fuel → f y = Option.none
  | 0, _, _, _, h1, h2 => absurd h2 (Nat.not_lt_of_le h1)
  | fuel + 1, j, h, y, h1, h2 => by
    have h' : (match f j with
      | some a => some (j, a)
      | Option.none => firstSome f fuel (j + 1)) = Option.none := h
    cases hf : f j with
    | some a =>
      rw [hf] at h'
      nomatch h'
    | none =>
      rw [hf] at h'
      have h'' : firstSome f fuel (j + 1) = Option.none := h'
      cases Nat.eq_or_lt_of_le h1 with
      | inl e =>
        rw [← e]
        exact hf
      | inr lt =>
        refine firstSome_none f fuel (j + 1) h'' y lt ?_
        rw [Nat.add_assoc, Nat.add_comm 1 fuel]
        exact h2

/-- Where `f` has a value at the first number searched, that is the first. -/
theorem firstSome_first {α : Type} (f : Nat → Option α) (fuel j : Nat) (a : α)
    (h : f j = some a) : firstSome f (fuel + 1) j = some (j, a) := by
  show (match f j with
    | some a => some (j, a)
    | Option.none => firstSome f fuel (j + 1)) = some (j, a)
  rw [h]

/-- **With more that has a value, the first comes no later.** Where `g` has a value wherever `f`
has one, and searches as many numbers at least, the first of `g` is the first of `f` or
before it. -/
theorem firstSome_mono {α β : Type} (f : Nat → Option α) (g : Nat → Option β)
    (hfg : ∀ x a, f x = some a → ∃ b, g x = some b) : ∀ (fuel fuel' j x : Nat) (a : α),
    fuel ≤ fuel' → firstSome f fuel j = some (x, a) →
    ∃ x' b, firstSome g fuel' j = some (x', b) ∧ x' ≤ x
  | 0, _, _, _, _, _, h => nomatch h
  | fuel + 1, 0, _, _, _, hle, _ => absurd hle (Nat.not_succ_le_zero fuel)
  | fuel + 1, fuel' + 1, j, x, a, hle, h => by
    have h' : (match f j with
      | some a => some (j, a)
      | Option.none => firstSome f fuel (j + 1)) = some (x, a) := h
    show ∃ x' b, (match g j with
      | some b => some (j, b)
      | Option.none => firstSome g fuel' (j + 1)) = some (x', b) ∧ x' ≤ x
    cases hg : g j with
    | some b => exact ⟨j, b, rfl, (firstSome_spec f (fuel + 1) j x a h).2.1⟩
    | none =>
      cases hf : f j with
      | some a' =>
        obtain ⟨b, hb⟩ := hfg j a' hf
        rw [hg] at hb
        nomatch hb
      | none =>
        rw [hf] at h'
        have h'' : firstSome f fuel (j + 1) = some (x, a) := h'
        exact firstSome_mono f g hfg fuel fuel' (j + 1) x a (Nat.le_of_succ_le_succ hle) h''

/-! ## The balanced breaking that fits -/

/-- A label is shown on three lines at most: it is no paragraph. -/
def maxLines : Nat := 3

/-- The breaking of the pieces into `k` lines whose widest line is the narrowest, where that
line is within the room. -/
def tryLines (room : Nat) (items : List (Piece σ)) (k : Nat) : Option (List (List (Piece σ))) :=
  match best (breakings k items) with
  | some c => if cost c ≤ room then some c else Option.none
  | Option.none => Option.none

/-- **The pieces on lines within the room**: on the fewest lines that hold them, `rows` and
three at most, and among the breakings into that many lines the one whose widest line is the
narrowest. Nothing where no such breaking is within the room. -/
def broken (room rows : Nat) (items : List (Piece σ)) : Option (List (List (Piece σ))) :=
  match firstSome (tryLines room items) (min rows maxLines) 1 with
  | some found => some found.2
  | Option.none => Option.none

/-- What `tryLines` gives is the best breaking into that many lines, and it is within the
room. -/
theorem tryLines_some {room k : Nat} {items : List (Piece σ)} {c : List (List (Piece σ))}
    (h : tryLines room items k = some c) : best (breakings k items) = some c ∧ cost c ≤ room := by
  unfold tryLines at h
  cases hb : best (breakings k items) with
  | none =>
    rw [hb] at h
    have h' : (Option.none : Option (List (List (Piece σ)))) = some c := h
    nomatch h'
  | some d =>
    rw [hb] at h
    have h' : (if cost d ≤ room then some d else Option.none) = some c := h
    cases Nat.decLe (cost d) room with
    | isTrue hle =>
      rw [if_pos hle] at h'
      cases h'
      exact ⟨rfl, hle⟩
    | isFalse hgt =>
      rw [if_neg hgt] at h'
      nomatch h'

/-- Where `tryLines` gives nothing, every breaking into that many lines has a line wider than
the room. -/
theorem tryLines_none {room k : Nat} {items : List (Piece σ)}
    (h : tryLines room items k = Option.none) : ∀ d ∈ breakings k items, room < cost d := by
  intro d hd
  unfold tryLines at h
  cases hb : best (breakings k items) with
  | none =>
    rw [best_none _ hb] at hd
    nomatch hd
  | some c =>
    rw [hb] at h
    have h' : (if cost c ≤ room then some c else Option.none) = Option.none := h
    cases Nat.decLe (cost c) room with
    | isTrue hle =>
      rw [if_pos hle] at h'
      nomatch h'
    | isFalse hgt => exact Nat.lt_of_lt_of_le (Nat.lt_of_not_le hgt) ((best_spec _ _ hb).2 d hd)

/-- What `tryLines` gives in a room, it gives in a wider room. -/
theorem tryLines_mono {room room' k : Nat} (h1 : room ≤ room') {items : List (Piece σ)}
    {c : List (List (Piece σ))} (h : tryLines room items k = some c) :
    tryLines room' items k = some c := by
  obtain ⟨hb, hc⟩ := tryLines_some h
  unfold tryLines
  rw [hb]
  show (if cost c ≤ room' then some c else Option.none) = some c
  rw [if_pos (Nat.le_trans hc h1)]

/-- What `broken` gives is the first breaking that `tryLines` gives. -/
theorem broken_some {room rows : Nat} {items : List (Piece σ)} {lines : List (List (Piece σ))}
    (h : broken room rows items = some lines) :
    ∃ k, firstSome (tryLines room items) (min rows maxLines) 1 = some (k, lines) := by
  unfold broken at h
  cases hf : firstSome (tryLines room items) (min rows maxLines) 1 with
  | none =>
    rw [hf] at h
    have h' : (Option.none : Option (List (List (Piece σ)))) = some lines := h
    nomatch h'
  | some found =>
    rw [hf] at h
    have h' : some found.2 = some lines := h
    cases h'
    exact ⟨found.1, rfl⟩

/-- **The lines hold every piece in order, each within the room**, on `rows` lines and three at
most, and each line but the last ends where a break is permitted. -/
theorem broken_spec {room rows : Nat} {items : List (Piece σ)} {lines : List (List (Piece σ))}
    (h : broken room rows items = some lines) :
    lines.flatten = items ∧ (∀ line ∈ lines, wide line ≤ room) ∧ 0 < lines.length ∧
      lines.length ≤ rows ∧ lines.length ≤ maxLines ∧ Permitted lines := by
  obtain ⟨k, hf⟩ := broken_some h
  obtain ⟨ht, h1, h2, _⟩ := firstSome_spec (tryLines room items) _ 1 k lines hf
  obtain ⟨hb, hc⟩ := tryLines_some ht
  obtain ⟨f1, f2, f3⟩ := mem_breakings k items lines (best_spec _ _ hb).1
  have hk : k ≤ min rows maxLines := by
    rw [Nat.add_comm] at h2
    exact Nat.le_of_lt_succ h2
  refine ⟨f1, fun line hl => Nat.le_trans (wide_le_cost lines line hl) hc, ?_, ?_, ?_, f3⟩
  · rw [f2]
    exact h1
  · rw [f2]
    exact Nat.le_trans hk (Nat.min_le_left _ _)
  · rw [f2]
    exact Nat.le_trans hk (Nat.min_le_right _ _)

/-- The lines cost no more than any of the breakings into as many lines. -/
theorem broken_least {room rows : Nat} {items : List (Piece σ)}
    {lines : List (List (Piece σ))} (h : broken room rows items = some lines) :
    ∀ d ∈ breakings lines.length items, cost lines ≤ cost d := by
  obtain ⟨k, hf⟩ := broken_some h
  obtain ⟨ht, _, _, _⟩ := firstSome_spec (tryLines room items) _ 1 k lines hf
  obtain ⟨hb, _⟩ := tryLines_some ht
  rw [(mem_breakings k items lines (best_spec _ _ hb).1).2.1]
  exact (best_spec _ _ hb).2

/-- Each of the breakings into fewer lines has a line wider than the room. -/
theorem broken_first {room rows : Nat} {items : List (Piece σ)}
    {lines : List (List (Piece σ))} (h : broken room rows items = some lines) (k : Nat)
    (h0 : 0 < k) (hk : k < lines.length) : ∀ d ∈ breakings k items, room < cost d := by
  obtain ⟨n, hf⟩ := broken_some h
  obtain ⟨ht, _, _, h4⟩ := firstSome_spec (tryLines room items) _ 1 n lines hf
  obtain ⟨hb, _⟩ := tryLines_some ht
  rw [(mem_breakings n items lines (best_spec _ _ hb).1).2.1] at hk
  exact tryLines_none (h4 k h0 hk)

/-- **The breaking is balanced**: no way to put the pieces on as many lines, none empty and
each but the last ending where a break is permitted, has a narrower widest line. -/
theorem broken_balanced {room rows : Nat} {items : List (Piece σ)}
    {lines : List (List (Piece σ))} (h : broken room rows items = some lines)
    (d : List (List (Piece σ))) (hd : d.flatten = items) (hlen : d.length = lines.length)
    (hne : ∀ line ∈ d, line ≠ []) (hp : Permitted d) : cost lines ≤ cost d := by
  have hpos := (broken_spec h).2.2.1
  have hd0 : d ≠ [] := fun e => by
    rw [e] at hlen
    rw [← hlen] at hpos
    exact absurd hpos (Nat.lt_irrefl 0)
  have hm := breakings_complete d hd0 hne hp
  rw [hd, hlen] at hm
  exact broken_least h d hm

/-- **The breaking has the fewest lines**: every way to put the pieces on fewer lines, none
empty and each but the last ending where a break is permitted, has a line wider than the
room. -/
theorem broken_fewest {room rows : Nat} {items : List (Piece σ)}
    {lines : List (List (Piece σ))} (h : broken room rows items = some lines)
    (d : List (List (Piece σ))) (hd : d.flatten = items) (hd0 : d ≠ [])
    (hlen : d.length < lines.length) (hne : ∀ line ∈ d, line ≠ []) (hp : Permitted d) :
    room < cost d := by
  have hm := breakings_complete d hd0 hne hp
  rw [hd] at hm
  have hpos : 0 < d.length := by
    cases d with
    | nil => exact absurd rfl hd0
    | cons _ _ => exact Nat.succ_pos _
  exact broken_first h d.length hpos hlen d hm

/-- **Pieces that can be put on lines within the room are on lines**: where some way to put
them on `rows` lines and three at most, none empty and each but the last ending where a break
is permitted, has every line within the room. -/
theorem broken_complete {room rows : Nat} {items : List (Piece σ)} (d : List (List (Piece σ)))
    (hd : d.flatten = items) (hd0 : d ≠ []) (hrows : d.length ≤ rows)
    (hmax : d.length ≤ maxLines) (hne : ∀ line ∈ d, line ≠ []) (hp : Permitted d)
    (hc : cost d ≤ room) : ∃ lines, broken room rows items = some lines := by
  cases hf : firstSome (tryLines room items) (min rows maxLines) 1 with
  | some found =>
    refine ⟨found.2, ?_⟩
    unfold broken
    rw [hf]
  | none =>
    have hpos : 1 ≤ d.length := by
      cases d with
      | nil => exact absurd rfl hd0
      | cons _ _ => exact Nat.succ_pos _
    have hlt : d.length < 1 + min rows maxLines := by
      rw [Nat.add_comm]
      exact Nat.lt_succ_of_le (Nat.le_min.mpr ⟨hrows, hmax⟩)
    have hm := breakings_complete d hd0 hne hp
    rw [hd] at hm
    exact absurd hc (Nat.not_le_of_lt
      (tryLines_none (firstSome_none _ _ 1 hf d.length hpos hlt) d hm))

/-- **What is on lines in a room is on lines in a wider room of as many rows or more.** -/
theorem broken_mono {room room' rows rows' : Nat} (h1 : room ≤ room') (h2 : rows ≤ rows')
    {items : List (Piece σ)} {lines : List (List (Piece σ))}
    (h : broken room rows items = some lines) :
    ∃ lines', broken room' rows' items = some lines' := by
  obtain ⟨k, hf⟩ := broken_some h
  obtain ⟨k', lines', hf', _⟩ := firstSome_mono (tryLines room items) (tryLines room' items)
    (fun _ a hx => ⟨a, tryLines_mono h1 hx⟩) _ (min rows' maxLines) 1 k lines
    (Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) h2, Nat.min_le_right _ _⟩) hf
  refine ⟨lines', ?_⟩
  unfold broken
  rw [hf']

/-- **Pieces that fit on one line are on one line.** -/
theorem broken_one {room rows : Nat} {items : List (Piece σ)} (h : wide items ≤ room)
    (h0 : 0 < rows) : broken room rows items = some [items] := by
  have hc : cost [items] ≤ room := Nat.max_le.mpr ⟨h, Nat.zero_le _⟩
  have ht : tryLines room items 1 = some [items] := by
    show (if cost [items] ≤ room then some [items] else Option.none) = some [items]
    rw [if_pos hc]
  have hm : 0 < min rows maxLines := Nat.lt_min.mpr ⟨h0, Nat.succ_pos 2⟩
  unfold broken
  cases hk : min rows maxLines with
  | zero =>
    rw [hk] at hm
    exact absurd hm (Nat.lt_irrefl 0)
  | succ m => rw [firstSome_first (tryLines room items) m 1 [items] ht]

/-! ## Which pieces go first -/

/-- A piece of keep `k` at the place `i` outlasts a piece of keep `k'` at the place `i'`: it
matters more, or as much and it comes earlier. -/
def outlasts (k i k' i' : Nat) : Bool := decide (k' < k) || (decide (k' = k) && decide (i < i'))

/-- How many pieces of a list, the first of them at the place `m`, a piece of keep `k` at the
place `i` outlasts. -/
def worse (k i : Nat) : Nat → List (Piece π) → Nat
  | _, [] => 0
  | m, p :: l => (bif outlasts k i p.keep m then 1 else 0) + worse k i (m + 1) l

/-- The pieces `l` of a label, the first of them at the place `i`, each with its rank: how many
pieces of the label it outlasts. -/
def rankedFrom (label : List (Piece π)) : Nat → List (Piece π) → List (Piece π × Nat)
  | _, [] => []
  | i, p :: l => (p, worse p.keep i 0 label) :: rankedFrom label (i + 1) l

/-- **Each piece of a label with its rank**: how many pieces of the label it outlasts. A cut
leaves out the pieces of least rank first: the piece of least `keep`, and the later one on a
tie. -/
def ranked (label : List (Piece π)) : List (Piece π × Nat) := rankedFrom label 0 label

/-- A piece outlasts another where it has more keep, or as much and an earlier place. -/
theorem outlasts_iff (k i k' i' : Nat) :
    outlasts k i k' i' = true ↔ k' < k ∨ (k' = k ∧ i < i') := by
  unfold outlasts
  rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]

/-- A piece that outlasts a second outlasts what the second outlasts. -/
theorem outlasts_trans {k1 i1 k2 i2 k3 i3 : Nat} (h1 : outlasts k1 i1 k2 i2 = true)
    (h2 : outlasts k2 i2 k3 i3 = true) : outlasts k1 i1 k3 i3 = true := by
  rw [outlasts_iff] at h1 h2 ⊢
  cases h1 with
  | inl a =>
    cases h2 with
    | inl b => exact Or.inl (Nat.lt_trans b a)
    | inr b =>
      rw [b.1]
      exact Or.inl a
  | inr a =>
    cases h2 with
    | inl b =>
      rw [← a.1]
      exact Or.inl b
    | inr b => exact Or.inr ⟨b.1.trans a.1, Nat.lt_trans a.2 b.2⟩

/-- A piece that outlasts all that a second outlasts has no lesser rank. -/
theorem worse_le (k i k2 i2 : Nat)
    (h : ∀ k' m, outlasts k2 i2 k' m = true → outlasts k i k' m = true) :
    ∀ (l : List (Piece π)) (s : Nat), worse k2 i2 s l ≤ worse k i s l
  | [], _ => Nat.le_refl 0
  | p :: l, s => by
    show (bif outlasts k2 i2 p.keep s then 1 else 0) + worse k2 i2 (s + 1) l ≤
      (bif outlasts k i p.keep s then 1 else 0) + worse k i (s + 1) l
    refine Nat.add_le_add ?_ (worse_le k i k2 i2 h l (s + 1))
    cases h2 : outlasts k2 i2 p.keep s with
    | false => exact Nat.zero_le _
    | true =>
      rw [h _ _ h2]
      exact Nat.le_refl 1

/-- The piece at a place of the ranked list is the piece of the label there, and its rank is
the count of the pieces that it outlasts. -/
theorem rankedFrom_getElem? (label : List (Piece π)) : ∀ (l : List (Piece π)) (s i : Nat)
    (p : Piece π) (r : Nat), (rankedFrom label s l)[i]? = some (p, r) →
    l[i]? = some p ∧ r = worse p.keep (s + i) 0 label
  | [], _, _, _, _, h => by
    have h' : ([] : List (Piece π × Nat))[_]? = some _ := h
    rw [List.getElem?_nil] at h'
    nomatch h'
  | q :: l, s, 0, p, r, h => by
    have h' : ((q, worse q.keep s 0 label) :: rankedFrom label (s + 1) l)[0]? = some (p, r) := h
    rw [List.getElem?_cons_zero] at h'
    cases h'
    exact ⟨List.getElem?_cons_zero, rfl⟩
  | q :: l, s, i + 1, p, r, h => by
    have h' : ((q, worse q.keep s 0 label) :: rankedFrom label (s + 1) l)[i + 1]? =
      some (p, r) := h
    rw [List.getElem?_cons_succ] at h'
    obtain ⟨a, b⟩ := rankedFrom_getElem? label l (s + 1) i p r h'
    rw [List.getElem?_cons_succ]
    refine ⟨a, ?_⟩
    rw [b, Nat.add_assoc, Nat.add_comm 1 i]

/-- The pieces of the ranked list are the pieces of the label. -/
theorem rankedFrom_ids (label : List (Piece π)) : ∀ (l : List (Piece π)) (s : Nat),
    (rankedFrom label s l).map (fun pr => pr.1.id) = ids l
  | [], _ => rfl
  | p :: l, s => congrArg (p.id :: ·) (rankedFrom_ids label l (s + 1))

/-- **A piece of lesser rank never matters more.** Of two pieces of a label, the one of lesser
rank has less `keep`, or as much and it comes later. So what a cut leaves out matters no more
than what it shows. -/
theorem ranked_order (label : List (Piece π)) (a b : Nat) (p q : Piece π) (ra rb : Nat)
    (ha : (ranked label)[a]? = some (p, ra)) (hb : (ranked label)[b]? = some (q, rb))
    (h : ra < rb) : p.keep < q.keep ∨ (p.keep = q.keep ∧ b < a) := by
  have ea := (rankedFrom_getElem? label label 0 a p ra ha).2
  have eb := (rankedFrom_getElem? label label 0 b q rb hb).2
  rw [Nat.zero_add] at ea eb
  rw [ea, eb] at h
  cases Nat.lt_or_ge p.keep q.keep with
  | inl lt => exact Or.inl lt
  | inr ge =>
    cases Nat.eq_or_lt_of_le ge with
    | inr lt =>
      exact absurd h (Nat.not_lt_of_le (worse_le p.keep a q.keep b
        (fun _ _ h' => outlasts_trans ((outlasts_iff _ _ _ _).mpr (Or.inl lt)) h') label 0))
    | inl e =>
      cases Nat.lt_or_ge b a with
      | inl lt => exact Or.inr ⟨e.symm, lt⟩
      | inr ge2 =>
        cases Nat.eq_or_lt_of_le ge2 with
        | inl e2 =>
          rw [e, e2] at h
          exact absurd h (Nat.lt_irrefl _)
        | inr lt2 =>
          exact absurd h (Nat.not_lt_of_le (worse_le p.keep a q.keep b
            (fun _ _ h' => outlasts_trans ((outlasts_iff _ _ _ _).mpr (Or.inr ⟨e, lt2⟩)) h')
            label 0))

/-! ## A cut text -/

/-- The pieces that a cut at the level `j` shows: those of rank `j` or more. -/
def shownAt (j : Nat) : List (Piece π × Nat) → List π
  | [] => []
  | pr :: l => if j ≤ pr.2 then pr.1.id :: shownAt j l else shownAt j l

/-- A piece as a piece of a cut text. -/
def shownPiece (p : Piece π) : Piece (Option π) :=
  ⟨some p.id, p.least, p.greatest, p.keep, p.breakAfter⟩

/-- The mark of a cut, `mark` wide. A line may end after it where it might after the last piece
that it stands for. -/
def markPiece (mark : Nat) (breakAfter : Bool) : Piece (Option π) :=
  ⟨Option.none, mark, mark, 0, breakAfter⟩

/-- The mark that is owed, where pieces were left out and no mark stands for them yet. -/
def flush (mark : Nat) : Option Bool → List (Piece (Option π))
  | Option.none => []
  | some b => [markPiece mark b]

/-- The cut text of ranked pieces at the level `j`. `pending` says that pieces were left out
just before, with whether a line may end after the last of them. -/
def elideFrom (mark j : Nat) : Option Bool → List (Piece π × Nat) → List (Piece (Option π))
  | pending, [] => flush mark pending
  | pending, pr :: l =>
    if j ≤ pr.2 then flush mark pending ++ shownPiece pr.1 :: elideFrom mark j Option.none l
    else elideFrom mark j (some pr.1.breakAfter) l

/-- **The cut text of a label at the level `j`**: its pieces of rank `j` or more, and one mark
for each run of the others. -/
def elide (mark j : Nat) (label : List (Piece π)) : List (Piece (Option π)) :=
  elideFrom mark j Option.none (ranked label)

/-- A cut text reads as its label. With pieces left out just before, it begins with their
mark. -/
theorem elideFrom_reads (mark j : Nat) : ∀ l : List (Piece π × Nat),
    Reads (ids (elideFrom mark j Option.none l)) (l.map fun pr => pr.1.id) ∧
      ∀ (b : Bool) (a : π), ∃ rest, ids (elideFrom mark j (some b) l) = Option.none :: rest ∧
        Reads (Option.none :: rest) (a :: l.map fun pr => pr.1.id)
  | [] => ⟨Reads.nil, fun _ a => ⟨[], rfl, Reads.mark a Reads.nil⟩⟩
  | pr :: l => by
    obtain ⟨ihA, ihB⟩ := elideFrom_reads mark j l
    cases Nat.decLe j pr.2 with
    | isTrue h =>
      refine ⟨?_, fun b a => ?_⟩
      · rw [elideFrom, if_pos h]
        exact Reads.piece pr.1.id ihA
      · rw [elideFrom, if_pos h]
        exact ⟨some pr.1.id :: ids (elideFrom mark j Option.none l), rfl,
          Reads.mark a (Reads.piece pr.1.id ihA)⟩
    | isFalse h =>
      refine ⟨?_, fun b a => ?_⟩
      · rw [elideFrom, if_neg h]
        obtain ⟨rest, e, r⟩ := ihB pr.1.breakAfter pr.1.id
        rw [e]
        exact r
      · rw [elideFrom, if_neg h]
        obtain ⟨rest, e, r⟩ := ihB pr.1.breakAfter pr.1.id
        exact ⟨rest, e, Reads.more a r⟩

/-- The pieces of a cut text are the pieces of rank `j` or more. -/
theorem elideFrom_pieces (mark j : Nat) : ∀ (l : List (Piece π × Nat)) (pending : Option Bool),
    (ids (elideFrom mark j pending l)).filterMap id = shownAt j l
  | [], Option.none => rfl
  | [], some _ => rfl
  | pr :: l, pending => by
    rw [elideFrom, shownAt]
    cases Nat.decLe j pr.2 with
    | isTrue h =>
      rw [if_pos h, if_pos h]
      cases pending with
      | none => exact congrArg (pr.1.id :: ·) (elideFrom_pieces mark j l Option.none)
      | some b => exact congrArg (pr.1.id :: ·) (elideFrom_pieces mark j l Option.none)
    | isFalse h =>
      rw [if_neg h, if_neg h]
      exact elideFrom_pieces mark j l _

/-- **A cut at a lower level shows every piece that a cut at a higher level shows.** -/
theorem shownAt_sublist (j j' : Nat) (h : j' ≤ j) : ∀ l : List (Piece π × Nat),
    (shownAt j l).Sublist (shownAt j' l)
  | [] => List.Sublist.slnil
  | pr :: l => by
    rw [shownAt, shownAt]
    cases Nat.decLe j pr.2 with
    | isTrue h1 =>
      rw [if_pos h1, if_pos (Nat.le_trans h h1)]
      exact List.Sublist.cons_cons _ (shownAt_sublist j j' h l)
    | isFalse h1 =>
      rw [if_neg h1]
      cases Nat.decLe j' pr.2 with
      | isTrue h2 =>
        rw [if_pos h2]
        exact List.Sublist.cons _ (shownAt_sublist j j' h l)
      | isFalse h2 =>
        rw [if_neg h2]
        exact shownAt_sublist j j' h l

/-- The pieces that a cut shows are pieces of the ranked list, in order. -/
theorem shownAt_sublist_all (j : Nat) : ∀ l : List (Piece π × Nat),
    (shownAt j l).Sublist (l.map fun pr => pr.1.id)
  | [] => List.Sublist.slnil
  | pr :: l => by
    rw [shownAt]
    cases Nat.decLe j pr.2 with
    | isTrue h =>
      rw [if_pos h]
      exact List.Sublist.cons_cons _ (shownAt_sublist_all j l)
    | isFalse h =>
      rw [if_neg h]
      exact List.Sublist.cons _ (shownAt_sublist_all j l)

/-- **A cut text reads as its label**: its pieces are pieces of the label in order, and a mark
stands at each place where pieces were left out. -/
theorem elide_reads (mark j : Nat) (label : List (Piece π)) :
    Reads (ids (elide mark j label)) (ids label) := by
  have h := (elideFrom_reads mark j (ranked label)).1
  have e : (ranked label).map (fun pr => pr.1.id) = ids label := rankedFrom_ids label label 0
  rw [e] at h
  exact h

/-- No two marks of a text stand side by side. -/
def MarksApart : List (Option π) → Prop
  | [] => True
  | [_] => True
  | a :: b :: text => (a = Option.none → b ≠ Option.none) ∧ MarksApart (b :: text)

/-- A piece before a text whose marks are apart leaves them apart. -/
theorem MarksApart.piece (a : π) : ∀ text : List (Option π), MarksApart text →
    MarksApart (some a :: text)
  | [], _ => True.intro
  | b :: text, h => by
    show (some a = Option.none → b ≠ Option.none) ∧ MarksApart (b :: text)
    exact ⟨fun e => (nomatch e), h⟩

/-- The marks of a cut text are apart. With pieces left out just before, it begins with their
one mark. -/
theorem elideFrom_apart (mark j : Nat) : ∀ l : List (Piece π × Nat),
    MarksApart (ids (elideFrom mark j Option.none l)) ∧
      ∀ b : Bool, ∃ rest, ids (elideFrom mark j (some b) l) = Option.none :: rest ∧
        MarksApart (Option.none :: rest)
  | [] => ⟨True.intro, fun _ => ⟨[], rfl, True.intro⟩⟩
  | pr :: l => by
    obtain ⟨ihA, ihB⟩ := elideFrom_apart mark j l
    cases Nat.decLe j pr.2 with
    | isTrue h =>
      refine ⟨?_, fun b => ?_⟩
      · rw [elideFrom, if_pos h]
        exact MarksApart.piece pr.1.id _ ihA
      · rw [elideFrom, if_pos h]
        refine ⟨some pr.1.id :: ids (elideFrom mark j Option.none l), rfl, ?_⟩
        show ((Option.none : Option π) = Option.none → some pr.1.id ≠ Option.none) ∧
          MarksApart (some pr.1.id :: ids (elideFrom mark j Option.none l))
        exact ⟨fun _ e => (nomatch e), MarksApart.piece pr.1.id _ ihA⟩
    | isFalse h =>
      refine ⟨?_, fun b => ?_⟩
      · rw [elideFrom, if_neg h]
        obtain ⟨rest, e, r⟩ := ihB pr.1.breakAfter
        rw [e]
        exact r
      · rw [elideFrom, if_neg h]
        exact ihB pr.1.breakAfter

/-- **A run of pieces that is left out has one mark**: no two marks of a cut text stand side by
side. -/
theorem elide_apart (mark j : Nat) (label : List (Piece π)) :
    MarksApart (ids (elide mark j label)) :=
  (elideFrom_apart mark j (ranked label)).1

/-- A piece of the ranked list is a piece of the label. -/
theorem mem_rankedFrom (label : List (Piece π)) : ∀ (l : List (Piece π)) (s : Nat)
    (pr : Piece π × Nat), pr ∈ rankedFrom label s l → pr.1 ∈ l
  | [], _, _, h => nomatch h
  | p :: l, s, pr, h => by
    have h' : pr ∈ (p, worse p.keep s 0 label) :: rankedFrom label (s + 1) l := h
    cases List.mem_cons.mp h' with
    | inl e =>
      rw [e]
      exact List.mem_cons_self
    | inr h2 => exact List.mem_cons_of_mem p (mem_rankedFrom label l (s + 1) pr h2)

/-- A piece of a cut text is a piece of the ranked list or a mark. -/
theorem mem_elideFrom (mark j : Nat) : ∀ (l : List (Piece π × Nat)) (pending : Option Bool)
    (x : Piece (Option π)), x ∈ elideFrom mark j pending l →
    (∃ pr ∈ l, x = shownPiece pr.1) ∨ ∃ b, x = markPiece mark b
  | [], Option.none, _, h => nomatch h
  | [], some b, _, h => Or.inr ⟨b, List.mem_singleton.mp h⟩
  | pr :: l, pending, x, h => by
    rw [elideFrom] at h
    cases Nat.decLe j pr.2 with
    | isTrue hj =>
      rw [if_pos hj] at h
      cases List.mem_append.mp h with
      | inl h1 =>
        cases pending with
        | none => nomatch h1
        | some b => exact Or.inr ⟨b, List.mem_singleton.mp h1⟩
      | inr h2 =>
        cases List.mem_cons.mp h2 with
        | inl e => exact Or.inl ⟨pr, List.mem_cons_self, e⟩
        | inr h3 =>
          cases mem_elideFrom mark j l Option.none x h3 with
          | inl hp =>
            obtain ⟨q, hq, e⟩ := hp
            exact Or.inl ⟨q, List.mem_cons_of_mem pr hq, e⟩
          | inr hm => exact Or.inr hm
    | isFalse hj =>
      rw [if_neg hj] at h
      cases mem_elideFrom mark j l _ x h with
      | inl hp =>
        obtain ⟨q, hq, e⟩ := hp
        exact Or.inl ⟨q, List.mem_cons_of_mem pr hq, e⟩
      | inr hm => exact Or.inr hm

/-- **A cut text has no width of its own making**: each of its pieces is a piece of the label
with that piece's widths, or a mark as wide as the caller's mark. -/
theorem mem_elide (mark j : Nat) (label : List (Piece π)) (x : Piece (Option π))
    (h : x ∈ elide mark j label) : (∃ p ∈ label, x = shownPiece p) ∨ ∃ b, x = markPiece mark b := by
  cases mem_elideFrom mark j (ranked label) Option.none x h with
  | inl hp =>
    obtain ⟨pr, hpr, e⟩ := hp
    exact Or.inl ⟨pr.1, mem_rankedFrom label label 0 pr hpr, e⟩
  | inr hm => exact Or.inr hm

/-! ## The fit -/

/-- A cut text that may be shown: it has a mark, so it does not read as a whole label; it has a
piece, so it is no bare sign; and the caller's test admits it. -/
def cutOk (ok : List (Option π) → Bool) (text : List (Option π)) : Bool :=
  text.any Option.isNone && text.any Option.isSome && ok text

/-- The cut of a label at the level `j` on lines within the room, where it may be shown. -/
def tryCut (ok : List (Option π) → Bool) (room rows mark : Nat) (label : List (Piece π))
    (j : Nat) : Option (List (List (Piece (Option π)))) :=
  bif cutOk ok (ids (elide mark j label)) then broken room rows (elide mark j label)
  else Option.none

/-- The lowest level at which a cut of the label may be shown within the room, and its lines. -/
def cutOf (ok : List (Option π) → Bool) (room rows mark : Nat) (label : List (Piece π)) :
    Option (Nat × List (List (Piece (Option π)))) :=
  firstSome (tryCut ok room rows mark label) (label.length - 1) 1

/-- **The label in a room, with a test of the caller on a cut text.** Whole where it fits; else
the cut of the lowest level that fits and that `ok` admits; else a sign where a mark fits; else
nothing. -/
def fitWith (ok : List (Option π) → Bool) (room rows mark : Nat) (label : List (Piece π)) :
    Shown π :=
  match broken room rows label with
  | some lines => .whole (lines.map ids)
  | Option.none =>
    match cutOf ok room rows mark label with
    | some found => .cut (found.2.map ids)
    | Option.none => bif decide (mark ≤ room) && decide (0 < rows) then .sign else .none

/-- **The label in a room of `room` by `rows` lines.** `mark` is the width of the mark of a cut,
and of the sign. -/
def fit (room rows mark : Nat) (label : List (Piece π)) : Shown π :=
  fitWith (fun _ => true) room rows mark label

/-- A cut text reads as the label alone among the labels of a picture: no label of the picture
with other pieces reads as it. -/
def alone [DecidableEq π] (labels : List (List (Piece π))) (label : List (Piece π))
    (text : List (Option π)) : Bool :=
  labels.all fun other => !reads text (ids other) || decide (ids other = ids label)

/-- **A label fitted among the labels of its picture**: a cut is shown only where its text reads
as this label alone. -/
def fitAmong [DecidableEq π] (labels : List (List (Piece π))) (room rows mark : Nat)
    (label : List (Piece π)) : Shown π :=
  fitWith (alone labels label) room rows mark label

/-- **The labels of one picture, fitted together.** -/
def fitAll [DecidableEq π] (room rows mark : Nat) (labels : List (List (Piece π))) :
    List (Shown π) :=
  labels.map (fitAmong labels room rows mark)

/-- What `tryCut` gives may be shown, and it is the cut on lines within the room. -/
theorem tryCut_some {ok : List (Option π) → Bool} {room rows mark j : Nat}
    {label : List (Piece π)} {ls : List (List (Piece (Option π)))}
    (h : tryCut ok room rows mark label j = some ls) :
    cutOk ok (ids (elide mark j label)) = true ∧
      broken room rows (elide mark j label) = some ls := by
  unfold tryCut at h
  cases hk : cutOk ok (ids (elide mark j label)) with
  | false =>
    rw [hk] at h
    have h' : (Option.none : Option (List (List (Piece (Option π))))) = some ls := h
    nomatch h'
  | true =>
    rw [hk] at h
    exact ⟨rfl, h⟩

/-- What `cutOf` gives: a level above `0`, a cut that may be shown, on lines within the room. -/
theorem cutOf_spec {ok : List (Option π) → Bool} {room rows mark j : Nat}
    {label : List (Piece π)} {ls : List (List (Piece (Option π)))}
    (h : cutOf ok room rows mark label = some (j, ls)) :
    0 < j ∧ cutOk ok (ids (elide mark j label)) = true ∧
      broken room rows (elide mark j label) = some ls := by
  obtain ⟨ht, h1, _, _⟩ := firstSome_spec _ _ 1 j ls h
  obtain ⟨a, b⟩ := tryCut_some ht
  exact ⟨h1, a, b⟩

/-- **The cut is of the lowest level that may be shown within the room**: at each level below
it, the cut text may not be shown or is not within the room. -/
theorem cutOf_lowest {ok : List (Option π) → Bool} {room rows mark j : Nat}
    {label : List (Piece π)} {ls : List (List (Piece (Option π)))}
    (h : cutOf ok room rows mark label = some (j, ls)) (y : Nat) (h0 : 0 < y) (hy : y < j) :
    tryCut ok room rows mark label y = Option.none :=
  (firstSome_spec _ _ 1 j ls h).2.2.2 y h0 hy

/-- With more room, the level of the cut is no higher. -/
theorem cutOf_mono (ok : List (Option π) → Bool) (mark : Nat) (label : List (Piece π))
    {room room' rows rows' : Nat} (h1 : room ≤ room') (h2 : rows ≤ rows') {j : Nat}
    {ls : List (List (Piece (Option π)))} (h : cutOf ok room rows mark label = some (j, ls)) :
    ∃ j' ls', cutOf ok room' rows' mark label = some (j', ls') ∧ j' ≤ j :=
  firstSome_mono (tryCut ok room rows mark label) (tryCut ok room' rows' mark label)
    (fun x a hx => by
      obtain ⟨hk, hb⟩ := tryCut_some hx
      obtain ⟨ls', hb'⟩ := broken_mono h1 h2 hb
      refine ⟨ls', ?_⟩
      unfold tryCut
      rw [hk]
      exact hb')
    (label.length - 1) (label.length - 1) 1 j ls (Nat.le_refl _) h

/-- The pieces of a cut are the pieces of its level's rank or more. -/
theorem cut_pieces {ok : List (Option π) → Bool} {room rows mark j : Nat}
    {label : List (Piece π)} {ls : List (List (Piece (Option π)))}
    (h : cutOf ok room rows mark label = some (j, ls)) :
    (Shown.cut (ls.map ids)).pieces = shownAt j (ranked label) := by
  show ((ls.map ids).flatten).filterMap id = shownAt j (ranked label)
  rw [ids_flatten, (broken_spec (cutOf_spec h).2.2).1]
  exact elideFrom_pieces mark j (ranked label) Option.none

/-- A label that is on lines within the room is shown whole on them. -/
theorem fitWith_of_broken {ok : List (Option π) → Bool} {room rows mark : Nat}
    {label : List (Piece π)} {lines : List (List (Piece π))}
    (h : broken room rows label = some lines) :
    fitWith ok room rows mark label = .whole (lines.map ids) := by
  unfold fitWith
  rw [h]

/-- A label that is not on lines within the room, and has a cut, is shown cut. -/
theorem fitWith_of_cut {ok : List (Option π) → Bool} {room rows mark : Nat}
    {label : List (Piece π)} {found : Nat × List (List (Piece (Option π)))}
    (hb : broken room rows label = Option.none)
    (hc : cutOf ok room rows mark label = some found) :
    fitWith ok room rows mark label = .cut (found.2.map ids) := by
  unfold fitWith
  rw [hb, hc]

/-- A label with no lines and no cut within the room is a sign where a mark fits, and nothing
elsewhere. -/
theorem fitWith_of_neither {ok : List (Option π) → Bool} {room rows mark : Nat}
    {label : List (Piece π)} (hb : broken room rows label = Option.none)
    (hc : cutOf ok room rows mark label = Option.none) :
    fitWith ok room rows mark label =
      bif decide (mark ≤ room) && decide (0 < rows) then .sign else .none := by
  unfold fitWith
  rw [hb, hc]

/-- **The four forms, and when each is shown.** -/
theorem fitWith_cases (ok : List (Option π) → Bool) (room rows mark : Nat)
    (label : List (Piece π)) :
    (∃ ls, broken room rows label = some ls ∧
      fitWith ok room rows mark label = .whole (ls.map ids)) ∨
    (∃ j ls, broken room rows label = Option.none ∧
      cutOf ok room rows mark label = some (j, ls) ∧
      fitWith ok room rows mark label = .cut (ls.map ids)) ∨
    (broken room rows label = Option.none ∧ cutOf ok room rows mark label = Option.none ∧
      mark ≤ room ∧ 0 < rows ∧ fitWith ok room rows mark label = .sign) ∨
    (broken room rows label = Option.none ∧ cutOf ok room rows mark label = Option.none ∧
      ¬ (mark ≤ room ∧ 0 < rows) ∧ fitWith ok room rows mark label = .none) := by
  cases hb : broken room rows label with
  | some ls => exact Or.inl ⟨ls, rfl, fitWith_of_broken hb⟩
  | none =>
    cases hc : cutOf ok room rows mark label with
    | some found => exact Or.inr (Or.inl ⟨found.1, found.2, rfl, rfl, fitWith_of_cut hb hc⟩)
    | none =>
      have e := fitWith_of_neither hb hc
      cases hs : (decide (mark ≤ room) && decide (0 < rows)) with
      | false =>
        rw [hs] at e
        refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, fun hn => ?_, e⟩))
        rw [decide_eq_true hn.1, decide_eq_true hn.2] at hs
        exact absurd hs (by decide)
      | true =>
        rw [hs] at e
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hs
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hs.1, hs.2, e⟩))

/-! ## Laws of the fit -/

/-- **A whole result holds every piece of the label, in order**, on lines that are each within
the room, `rows` at most, each but the last ending where a break is permitted. -/
theorem fitWith_whole {ok : List (Option π) → Bool} {room rows mark : Nat}
    {label : List (Piece π)} {lines : List (List π)}
    (h : fitWith ok room rows mark label = .whole lines) :
    ∃ ls : List (List (Piece π)), lines = ls.map ids ∧ ls.flatten = label ∧
      (∀ line ∈ ls, wide line ≤ room) ∧ ls.length ≤ rows ∧ Permitted ls := by
  obtain ⟨ls, hb, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, e⟩ :=
    fitWith_cases ok room rows mark label
  · rw [e] at h
    obtain ⟨f1, f2, _, f4, _, f6⟩ := broken_spec hb
    exact ⟨ls, (Shown.whole.inj h).symm, f1, f2, f4, f6⟩
  · rw [e] at h
    nomatch h
  · rw [e] at h
    nomatch h
  · rw [e] at h
    nomatch h

/-- **A cut result is the cut text of some level above `0`**, on lines that are each within the
room, `rows` at most, each but the last ending where a break is permitted; and the caller's
test admits its text. -/
theorem fitWith_cut {ok : List (Option π) → Bool} {room rows mark : Nat}
    {label : List (Piece π)} {lines : List (List (Option π))}
    (h : fitWith ok room rows mark label = .cut lines) :
    ∃ (j : Nat) (ls : List (List (Piece (Option π)))), 0 < j ∧ lines = ls.map ids ∧
      ls.flatten = elide mark j label ∧ (∀ line ∈ ls, wide line ≤ room) ∧ ls.length ≤ rows ∧
      Permitted ls ∧ cutOk ok lines.flatten = true := by
  obtain ⟨_, _, e⟩ | ⟨j, ls, _, hc, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, e⟩ :=
    fitWith_cases ok room rows mark label
  · rw [e] at h
    nomatch h
  · rw [e] at h
    obtain ⟨hj, hk, hb⟩ := cutOf_spec hc
    obtain ⟨f1, f2, _, f4, _, f6⟩ := broken_spec hb
    cases Shown.cut.inj h
    refine ⟨j, ls, hj, rfl, f1, f2, f4, f6, ?_⟩
    rw [ids_flatten, f1]
    exact hk
  · rw [e] at h
    nomatch h
  · rw [e] at h
    nomatch h

/-- A sign is shown only where a mark fits the room and there is a row. -/
theorem fitWith_sign {ok : List (Option π) → Bool} {room rows mark : Nat}
    {label : List (Piece π)} (h : fitWith ok room rows mark label = .sign) :
    mark ≤ room ∧ 0 < rows := by
  obtain ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, h1, h2, _⟩ | ⟨_, _, _, e⟩ :=
    fitWith_cases ok room rows mark label
  · rw [e] at h
    nomatch h
  · rw [e] at h
    nomatch h
  · exact ⟨h1, h2⟩
  · rw [e] at h
    nomatch h

/-- **The result takes `rows` lines at most.** -/
theorem fitWith_rows (ok : List (Option π) → Bool) (room rows mark : Nat)
    (label : List (Piece π)) : (fitWith ok room rows mark label).rows ≤ rows := by
  obtain ⟨ls, hb, e⟩ | ⟨j, ls, _, hc, e⟩ | ⟨_, _, _, h2, e⟩ | ⟨_, _, _, e⟩ :=
    fitWith_cases ok room rows mark label
  · rw [e]
    show (ls.map ids).length ≤ rows
    rw [List.length_map]
    exact (broken_spec hb).2.2.2.1
  · rw [e]
    show (ls.map ids).length ≤ rows
    rw [List.length_map]
    exact (broken_spec (cutOf_spec hc).2.2).2.2.2.1
  · rw [e]
    exact h2
  · rw [e]
    exact Nat.zero_le rows

/-- **A cut text never reads as a whole one, and it is no bare sign**: it has a mark and a
piece. -/
theorem fitWith_cut_marked {ok : List (Option π) → Bool} {room rows mark : Nat}
    {label : List (Piece π)} {lines : List (List (Option π))}
    (h : fitWith ok room rows mark label = .cut lines) :
    Option.none ∈ lines.flatten ∧ ∃ a, some a ∈ lines.flatten := by
  obtain ⟨_, _, _, _, _, _, _, _, hk⟩ := fitWith_cut h
  unfold cutOk at hk
  rw [Bool.and_eq_true, Bool.and_eq_true] at hk
  obtain ⟨x, hx, ex⟩ := List.any_eq_true.mp hk.1.1
  obtain ⟨y, hy, ey⟩ := List.any_eq_true.mp hk.1.2
  refine ⟨?_, ?_⟩
  · cases x with
    | none => exact hx
    | some _ => exact absurd ex Bool.false_ne_true
  · cases y with
    | none => exact absurd ey Bool.false_ne_true
    | some a => exact ⟨a, hy⟩

/-- **A run of pieces that a cut result leaves out has one mark**: no two marks of it stand side
by side. -/
theorem fitWith_cut_apart {ok : List (Option π) → Bool} {room rows mark : Nat}
    {label : List (Piece π)} {lines : List (List (Option π))}
    (h : fitWith ok room rows mark label = .cut lines) : MarksApart lines.flatten := by
  obtain ⟨j, ls, _, a, b, _, _, _, _⟩ := fitWith_cut h
  rw [a, ids_flatten, b]
  exact elide_apart mark j label

/-- **The text of a result reads as its label.** A whole text is every piece of the label in
order. The pieces of a cut text are pieces of the label in its order, and a mark stands at each
place where pieces were left out. -/
theorem fitWith_reads {ok : List (Option π) → Bool} {room rows mark : Nat}
    {label : List (Piece π)} {t : List (Option π)}
    (h : (fitWith ok room rows mark label).text = some t) : Reads t (ids label) := by
  obtain ⟨ls, hb, e⟩ | ⟨j, ls, _, hc, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, e⟩ :=
    fitWith_cases ok room rows mark label
  · rw [e] at h
    have h' : some (((ls.map ids).flatten).map some) = some t := h
    cases h'
    rw [ids_flatten, (broken_spec hb).1]
    exact Reads.refl (ids label)
  · rw [e] at h
    have h' : some ((ls.map ids).flatten) = some t := h
    cases h'
    rw [ids_flatten, (broken_spec (cutOf_spec hc).2.2).1]
    exact elide_reads mark j label
  · rw [e] at h
    have h' : (Option.none : Option (List (Option π))) = some t := h
    nomatch h'
  · rw [e] at h
    have h' : (Option.none : Option (List (Option π))) = some t := h
    nomatch h'

/-- **A text with no mark of a cut is the whole label**: every piece of it, in order. -/
theorem fitWith_unmarked {ok : List (Option π) → Bool} {room rows mark : Nat}
    {label : List (Piece π)} {t : List (Option π)}
    (h : (fitWith ok room rows mark label).text = some t) (hn : Option.none ∉ t) :
    t = (ids label).map some := by
  obtain ⟨ls, hb, e⟩ | ⟨j, ls, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, e⟩ :=
    fitWith_cases ok room rows mark label
  · rw [e] at h
    have h' : some (((ls.map ids).flatten).map some) = some t := h
    cases h'
    rw [ids_flatten, (broken_spec hb).1]
  · rw [e] at h
    have h' : some ((ls.map ids).flatten) = some t := h
    cases h'
    exact absurd (fitWith_cut_marked e).1 hn
  · rw [e] at h
    have h' : (Option.none : Option (List (Option π))) = some t := h
    nomatch h'
  · rw [e] at h
    have h' : (Option.none : Option (List (Option π))) = some t := h
    nomatch h'

/-- **A label that fits on one line is shown whole on one line.** -/
theorem fitWith_one_line (ok : List (Option π) → Bool) {room rows : Nat} (mark : Nat)
    {label : List (Piece π)} (h : wide label ≤ room) (h0 : 0 < rows) :
    fitWith ok room rows mark label = .whole [ids label] :=
  fitWith_of_broken (broken_one h h0)

/-- **A label that can be put on lines within the room is shown whole**: where some way to put
its pieces on `rows` lines and three at most, none empty and each but the last ending where a
break is permitted, has every line within the room. -/
theorem fitWith_whole_of (ok : List (Option π) → Bool) {room rows : Nat} (mark : Nat)
    {label : List (Piece π)} (d : List (List (Piece π))) (hd : d.flatten = label) (hd0 : d ≠ [])
    (hrows : d.length ≤ rows) (hmax : d.length ≤ maxLines) (hne : ∀ line ∈ d, line ≠ [])
    (hp : Permitted d) (hc : cost d ≤ room) :
    ∃ lines, fitWith ok room rows mark label = .whole lines := by
  obtain ⟨ls, hb⟩ := broken_complete d hd hd0 hrows hmax hne hp hc
  exact ⟨ls.map ids, fitWith_of_broken hb⟩

/-- Where a mark fits the room and there is a row, something is shown. -/
theorem fitWith_rank_pos (ok : List (Option π) → Bool) {room rows mark : Nat}
    (label : List (Piece π)) (h1 : mark ≤ room) (h2 : 0 < rows) :
    1 ≤ (fitWith ok room rows mark label).rank := by
  obtain ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, hn, _⟩ :=
    fitWith_cases ok room rows mark label
  · rw [e]
    exact Nat.succ_pos 2
  · rw [e]
    exact Nat.succ_pos 1
  · rw [e]
    exact Nat.le_refl 1
  · exact absurd ⟨h1, h2⟩ hn

/-- **With more room, the result shows every piece that it showed with less, and its form says
no less.** So a picture drawn larger never says less. -/
theorem fitWith_mono (ok : List (Option π) → Bool) (mark : Nat) (label : List (Piece π))
    {room room' rows rows' : Nat} (h1 : room ≤ room') (h2 : rows ≤ rows') :
    (fitWith ok room rows mark label).pieces.Sublist (fitWith ok room' rows' mark label).pieces ∧
      (fitWith ok room rows mark label).rank ≤ (fitWith ok room' rows' mark label).rank := by
  obtain ⟨ls, hb, e⟩ | ⟨j, ls, _, hc, e⟩ | ⟨_, _, hm, hr, e⟩ | ⟨_, _, _, e⟩ :=
    fitWith_cases ok room rows mark label
  · obtain ⟨ls', hb'⟩ := broken_mono h1 h2 hb
    rw [e, fitWith_of_broken hb']
    show ((ls.map ids).flatten).Sublist ((ls'.map ids).flatten) ∧ 3 ≤ 3
    rw [ids_flatten, ids_flatten, (broken_spec hb).1, (broken_spec hb').1]
    exact ⟨List.Sublist.refl _, Nat.le_refl 3⟩
  · rw [e, cut_pieces hc]
    obtain ⟨j'', ls'', hc'', le⟩ := cutOf_mono ok mark label h1 h2 hc
    obtain ⟨ls', hb', e'⟩ | ⟨j', ls', _, hc', e'⟩ | ⟨_, hc', _, _, _⟩ | ⟨_, hc', _, _⟩ :=
      fitWith_cases ok room' rows' mark label
    · rw [e']
      show (shownAt j (ranked label)).Sublist ((ls'.map ids).flatten) ∧ 2 ≤ 3
      rw [ids_flatten, (broken_spec hb').1, ← rankedFrom_ids label label 0]
      exact ⟨shownAt_sublist_all j (ranked label), Nat.le_succ 2⟩
    · rw [e', cut_pieces hc']
      have ej : j' = j'' := congrArg Prod.fst (Option.some.inj (hc'.symm.trans hc''))
      rw [ej]
      exact ⟨shownAt_sublist j j'' le (ranked label), Nat.le_refl 2⟩
    · rw [hc'] at hc''
      nomatch hc''
    · rw [hc'] at hc''
      nomatch hc''
  · rw [e]
    exact ⟨List.nil_sublist _,
      fitWith_rank_pos ok label (Nat.le_trans hm h1) (Nat.lt_of_lt_of_le hr h2)⟩
  · rw [e]
    exact ⟨List.nil_sublist _, Nat.zero_le _⟩

/-! ## The label alone -/

/-- **Each line of the result is within the room at its greatest width, and there are `rows`
lines at most.** A whole result and a cut result are lines of pieces with their widths, and a
sign is one mark. -/
theorem fit_fits (room rows mark : Nat) (label : List (Piece π)) :
    (fit room rows mark label).rows ≤ rows ∧
    (∀ lines, fit room rows mark label = .whole lines →
      ∃ ls : List (List (Piece π)), lines = ls.map ids ∧ ls.flatten = label ∧
        ∀ line ∈ ls, wide line ≤ room) ∧
    (∀ lines, fit room rows mark label = .cut lines →
      ∃ (j : Nat) (ls : List (List (Piece (Option π)))), lines = ls.map ids ∧
        ls.flatten = elide mark j label ∧ ∀ line ∈ ls, wide line ≤ room) ∧
    (fit room rows mark label = .sign → mark ≤ room) := by
  refine ⟨fitWith_rows _ room rows mark label, fun lines h => ?_, fun lines h => ?_,
    fun h => (fitWith_sign h).1⟩
  · obtain ⟨ls, a, b, c, _, _⟩ := fitWith_whole h
    exact ⟨ls, a, b, c⟩
  · obtain ⟨j, ls, _, a, b, c, _, _, _⟩ := fitWith_cut h
    exact ⟨j, ls, a, b, c⟩

/-- **A whole result holds every piece of the label, in order.** -/
theorem fit_whole {room rows mark : Nat} {label : List (Piece π)} {lines : List (List π)}
    (h : fit room rows mark label = .whole lines) : lines.flatten = ids label := by
  obtain ⟨ls, a, b, _, _, _⟩ := fitWith_whole h
  rw [a, ids_flatten, b]

/-- **A label that fits on one line is shown whole on one line.** -/
theorem fit_one_line {room rows : Nat} (mark : Nat) {label : List (Piece π)}
    (h : wide label ≤ room) (h0 : 0 < rows) : fit room rows mark label = .whole [ids label] :=
  fitWith_one_line _ mark h h0

/-- **The pieces of a cut result are pieces of the label, in its order, and a mark stands at
each place where pieces were left out**: the cut text reads as the label. -/
theorem fit_subsequence {room rows mark : Nat} {label : List (Piece π)}
    {lines : List (List (Option π))} (h : fit room rows mark label = .cut lines) :
    Reads lines.flatten (ids label) ∧ (lines.flatten.filterMap id).Sublist (ids label) := by
  have hr : Reads lines.flatten (ids label) :=
    fitWith_reads (ok := fun _ => true) (room := room) (rows := rows) (mark := mark) (by
      show (fit room rows mark label).text = some lines.flatten
      rw [h]
      rfl)
  exact ⟨hr, hr.sublist⟩

/-- **With more room, the result shows every piece that it showed with less.** So a picture
drawn larger never says less. -/
theorem fit_mono (mark : Nat) (label : List (Piece π)) {room room' rows rows' : Nat}
    (h1 : room ≤ room') (h2 : rows ≤ rows') :
    (fit room rows mark label).pieces.Sublist (fit room' rows' mark label).pieces ∧
      (fit room rows mark label).rank ≤ (fit room' rows' mark label).rank :=
  fitWith_mono _ mark label h1 h2

/-! ## The labels of one picture -/

/-- **A text that is shown reads as its own label and as no other label of the picture.** So a
reader who has the labels of the picture knows which one a cut text is. -/
theorem fitAmong_alone [DecidableEq π] (labels : List (List (Piece π))) (room rows mark : Nat)
    (label : List (Piece π)) (t : List (Option π))
    (ht : (fitAmong labels room rows mark label).text = some t) (other : List (Piece π))
    (ho : other ∈ labels) (hr : Reads t (ids other)) : ids other = ids label := by
  unfold fitAmong at ht
  obtain ⟨ls, hb, e⟩ | ⟨j, ls, _, hc, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, e⟩ :=
    fitWith_cases (alone labels label) room rows mark label
  · rw [e] at ht
    have h' : some (((ls.map ids).flatten).map some) = some t := ht
    cases h'
    rw [ids_flatten, (broken_spec hb).1] at hr
    exact (Reads.whole _ _ hr).symm
  · rw [e] at ht
    have h' : some ((ls.map ids).flatten) = some t := ht
    cases h'
    have hk := (cutOf_spec hc).2.1
    rw [ids_flatten, (broken_spec (cutOf_spec hc).2.2).1] at hr
    unfold cutOk at hk
    rw [Bool.and_eq_true] at hk
    have ha := List.all_eq_true.mp hk.2 other ho
    rw [reads_of_reads hr] at ha
    exact of_decide_eq_true ha
  · rw [e] at ht
    have h' : (Option.none : Option (List (Option π))) = some t := ht
    nomatch h'
  · rw [e] at ht
    have h' : (Option.none : Option (List (Option π))) = some t := ht
    nomatch h'

/-- **Two labels of a picture that differ are not shown as one text.** -/
theorem fitAmong_distinct [DecidableEq π] (labels : List (List (Piece π))) (room rows mark : Nat)
    (a b : List (Piece π)) (ha : a ∈ labels) (hne : ids a ≠ ids b) (t : List (Option π))
    (hta : (fitAmong labels room rows mark a).text = some t) :
    (fitAmong labels room rows mark b).text ≠ some t :=
  fun htb => hne (fitAmong_alone labels room rows mark b t htb a ha (fitWith_reads hta))

/-- **Two labels that differ, both shown as text, are shown as two texts.** -/
theorem fitAll_distinct [DecidableEq π] (room rows mark : Nat) (labels : List (List (Piece π)))
    (i j : Nat) (a b : List (Piece π)) (ha : labels[i]? = some a) (hb : labels[j]? = some b)
    (hne : ids a ≠ ids b) (sa sb : Shown π)
    (hsa : (fitAll room rows mark labels)[i]? = some sa)
    (hsb : (fitAll room rows mark labels)[j]? = some sb) (t : List (Option π))
    (hta : sa.text = some t) : sb.text ≠ some t := by
  unfold fitAll at hsa hsb
  rw [List.getElem?_map, ha] at hsa
  rw [List.getElem?_map, hb] at hsb
  have ea : some (fitAmong labels room rows mark a) = some sa := hsa
  have eb : some (fitAmong labels room rows mark b) = some sb := hsb
  cases ea
  cases eb
  exact fitAmong_distinct labels room rows mark a b (List.mem_of_getElem? ha) hne t hta

/-- **Fitted together, with more room each label shows every piece that it showed with less.** -/
theorem fitAll_mono [DecidableEq π] (mark : Nat) (labels : List (List (Piece π)))
    {room room' rows rows' : Nat} (h1 : room ≤ room') (h2 : rows ≤ rows') (i : Nat)
    (s s' : Shown π) (hs : (fitAll room rows mark labels)[i]? = some s)
    (hs' : (fitAll room' rows' mark labels)[i]? = some s') :
    s.pieces.Sublist s'.pieces ∧ s.rank ≤ s'.rank := by
  unfold fitAll at hs hs'
  rw [List.getElem?_map] at hs hs'
  cases hl : labels[i]? with
  | none =>
    rw [hl] at hs
    have h' : (Option.none : Option (Shown π)) = some s := hs
    nomatch h'
  | some a =>
    rw [hl] at hs hs'
    have e : some (fitAmong labels room rows mark a) = some s := hs
    have e' : some (fitAmong labels room' rows' mark a) = some s' := hs'
    cases e
    cases e'
    exact fitWith_mono (alone labels a) mark a h1 h2

end Label

/-! ## Finite evaluations -/

-- A name of sixteen cells in the data face, in rooms of sixteen, twelve, six and no cells on
-- one row: whole; cut, with the last name kept when the prefix goes; a sign; nothing.
#guard [16, 12, 6, 0].map (fun cells => Label.fit (8000 * cells) 1 8000
    (Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("Stream", 1, false), (".", 0, true), ("mapEffect", 2, true)])) =
  [.whole [["Stream", ".", "mapEffect"]], .cut [[none, some "mapEffect"]], .sign, .none]

-- The same name in twelve cells by two rows: whole, broken after the dot and not in a name.
#guard Label.fit 96000 2 8000 (Label.ofTexts (Metrics.mono 8000 16000 8000)
    [("Stream", 1, false), (".", 0, true), ("mapEffect", 2, true)]) =
  .whole [["Stream", "."], ["mapEffect"]]

-- A line of a program, twenty-nine cells wide, in rooms of thirty, twenty-eight and twenty
-- cells: the argument goes first, then the second name.
#guard [30, 28, 20].map (fun cells => Label.fit (8000 * cells) 1 8000
    (Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("awaitFiber ", 3, true), ("(var 0) ", 1, true), ("awaitValue", 2, true)])) =
  [.whole [["awaitFiber ", "(var 0) ", "awaitValue"]],
    .cut [[some "awaitFiber ", none, some "awaitValue"]], .cut [[some "awaitFiber ", none]]]

-- Four words in nine cells by two rows are two and two. Filling the first line would leave
-- one word alone on the second.
#guard Label.fit 72000 2 8000 (Label.ofTexts (Metrics.mono 8000 16000 8000)
    [("aa ", 1, true), ("bb ", 1, true), ("cc ", 1, true), ("dd", 1, true)]) =
  .whole [["aa ", "bb "], ["cc ", "dd"]]

-- The levels of a cut of four pieces of one `keep`: each leaves out one piece more, the later
-- piece first, and a run that is left out has one mark.
#guard (List.range 5).map (fun level => Label.ids (Label.elide 8000 level
    (Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("aa ", 1, true), ("bb ", 1, true), ("cc ", 1, true), ("dd", 1, true)]))) =
  [[some "aa ", some "bb ", some "cc ", some "dd"], [some "aa ", some "bb ", some "cc ", none],
    [some "aa ", some "bb ", none], [some "aa ", none], [none]]

-- Three operations of one module in ten cells: the prefix goes, and no two have one text.
#guard Label.fitAll 80000 1 8000 [
    Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("Stream", 1, false), (".", 0, true), ("mapEffect", 2, true)],
    Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("Stream", 1, false), (".", 0, true), ("run", 2, true)],
    Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("Stream", 1, false), (".", 0, true), ("fold", 2, true)]] =
  [.cut [[none, some "mapEffect"]], .whole [["Stream", ".", "run"]], .cut [[none, some "fold"]]]

-- A control for `fitAll`: two names that differ in the prefix only, in ten cells. Fitted alone,
-- each is cut to one text. Fitted together, neither is shown as text.
#guard [Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("Stream", 1, false), (".", 0, true), ("mapEffect", 2, true)],
    Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("Sink", 1, false), (".", 0, true), ("mapEffect", 2, true)]].map (Label.fit 80000 1 8000) =
  [.cut [[none, some "mapEffect"]], .cut [[none, some "mapEffect"]]]
#guard Label.fitAll 80000 1 8000 [
    Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("Stream", 1, false), (".", 0, true), ("mapEffect", 2, true)],
    Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("Sink", 1, false), (".", 0, true), ("mapEffect", 2, true)]] = [.sign, .sign]

-- A control for the premise of `fitAll_distinct`: two labels of the same pieces are one text.
#guard Label.fitAll 80000 1 8000 [
    Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("Stream", 1, false), (".", 0, true), ("mapEffect", 2, true)],
    Label.ofTexts (Metrics.mono 8000 16000 8000)
      [("Stream", 1, false), (".", 0, true), ("mapEffect", 2, true)]] =
  [.cut [[none, some "mapEffect"]], .cut [[none, some "mapEffect"]]]

-- A control for the premise of `fit_one_line`: with no row, a label that fits is not shown.
#guard Label.fit 1000000 0 8000 (Label.ofTexts (Metrics.mono 8000 16000 8000)
    [("Stream", 1, false), (".", 0, true), ("mapEffect", 2, true)]) = .none

-- A mark stands for one piece at least: a text that begins with a mark reads as no label that
-- begins with the text's first piece.
#guard Label.reads [none, some 1, none] [0, 1, 2, 3]
#guard !Label.reads [none, some 1, none] [1, 2, 3]

end Whatwg.Svg.Scene
