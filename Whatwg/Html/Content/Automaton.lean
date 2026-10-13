import Whatwg.Html.Content.Sequence

/-!
# Whatwg.Html.Content.Automaton

Owner: the ordered content model as an automaton (slice S22 of `docs/SVG-PACKAGE-PLAN.md`;
entry W9 of `docs/research/2026-10-12-whatwg-requests.md`; debt D139).

`Whatwg/Html/Content/Sequence.lean` decides an ordered model by Brzozowski's derivative:
`Seq.accepts base s tags` is `nullable` of the derivative of `s` by each tag in turn. That is a
fold, and a fold of a list that is two lists in a row is two folds in a row. This module says
so, which is what lets the children of `dl`, `details`, `head` or `table` be written in parts.

What it gives:

- `Seq.after base s tags`, the state of the model `s` after the tags: a sequence again.
  `Seq.after_append` is the law of two runs in a row, and `Seq.accepts_append` the same for the
  decision. `Seq.matches_after_iff` says what a state means: it matches exactly the
  continuations that the model accepts after the tags read so far.
- A loop. `Seq.after_of_fixed` and `Seq.after_flatten_of_fixed`: a tag, or a word of tags, that
  leaves a state where it was may be repeated any number of times.
- The model of one element. `keep t tags` is what the model of `t` reads of the tags of a
  child list, and `modelTags t children` the same from the children; both go through an append.
  `Seq.start t` is the model's first state and `Seq.next t s tag` its state after one more
  child. `Seq.absorbs t s among` is the closed test that every tag of a set leaves `s` fixed,
  for children whose tags are not known, and `Seq.after_keep_of_absorbs` its law.
- `seqOk_eq_of_seq`, `seqOk_of_after` and `after_of_seqOk`: `seqOk` is `nullable` of the state
  after the children.
- `Seq.Matches.mono` and `seqOk_mono`: a model accepts no less over a wider base.

`Whatwg/Html/Node/Run.lean` is the typed tree's use of these laws.

What this module does not claim: that two states with one language are one state. A state is a
term, and `Seq.after` gives the term that the simplifying constructors `sq` and `al` leave. A
test `after base s w = s` may fail for a word after which the model accepts the same
continuations. `Seq.next` and `Seq.absorbs` read the element's own base, which is the base of
its children unless the element is transparent (`audio` and `video`, among those that have an
ordered model).
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema
open Whatwg.Html (RawNode)

namespace Seq

variable {base : Tag → Bool}

/-! ## The state after a run -/

/-- The state of a sequence after a list of tags: its derivative by each tag in turn. -/
def after (base : Tag → Bool) (s : Seq) (tags : List Tag) : Seq := tags.foldl (deriv base) s

theorem after_nil (s : Seq) : after base s [] = s := rfl

theorem after_cons (s : Seq) (t : Tag) (tags : List Tag) :
    after base s (t :: tags) = after base (deriv base s t) tags := rfl

/-- Two runs in a row: the state after both is the state after the second, from the state after
the first. -/
theorem after_append (s : Seq) (tags more : List Tag) :
    after base s (tags ++ more) = after base (after base s tags) more :=
  List.foldl_append

/-- The decision is `nullable` of the state after the tags. -/
theorem accepts_eq (s : Seq) (tags : List Tag) : accepts base s tags = nullable (after base s tags) :=
  rfl

/-- The model accepts two runs in a row exactly when its state after the first accepts the
second. -/
theorem accepts_append (s : Seq) (tags more : List Tag) :
    accepts base s (tags ++ more) = accepts base (after base s tags) more := by
  rw [accepts_eq, after_append, accepts_eq]

/-- What a state means: it matches the continuations that the model accepts after the tags
read so far. -/
theorem matches_after_iff (s : Seq) (tags more : List Tag) :
    Matches base (after base s tags) more ↔ Matches base s (tags ++ more) := by
  induction tags generalizing s with
  | nil => exact Iff.rfl
  | cons t rest ih =>
    rw [after_cons, ih, List.cons_append]
    exact deriv_iff s t (rest ++ more)

/-! ## A loop -/

/-- Tags that each leave the state where it was leave it there together. -/
theorem after_of_fixed {s : Seq} : ∀ {tags : List Tag},
    (∀ t ∈ tags, deriv base s t = s) → after base s tags = s
  | [], _ => rfl
  | t :: rest, h => by
    rw [after_cons, h t List.mem_cons_self]
    exact after_of_fixed fun later hlater => h later (List.mem_cons_of_mem t hlater)

/-- Words that each lead from a state back to it may stand in a row, any number of them. -/
theorem after_flatten_of_fixed {s : Seq} : ∀ {words : List (List Tag)},
    (∀ w ∈ words, after base s w = s) → after base s words.flatten = s
  | [], _ => rfl
  | w :: rest, h => by
    rw [List.flatten_cons, after_append, h w List.mem_cons_self]
    exact after_flatten_of_fixed fun v hv => h v (List.mem_cons_of_mem w hv)

/-! ## A wider base -/

/-- A match over a base is a match over every base that holds it: only `base except` reads the
base, and it asks that a tag be in it. -/
theorem Matches.mono {wide : Tag → Bool} (h : ∀ t, base t = true → wide t = true) {s : Seq}
    {tags : List Tag} (m : Matches base s tags) : Matches wide s tags := by
  induction m with
  | eps => exact .eps
  | tag t => exact .tag t
  | base t hb hex => exact .base t (h t hb) hex
  | seq _ _ iha ihb => exact .seq iha ihb
  | altL _ ih => exact .altL ih
  | altR _ ih => exact .altR ih
  | starNil => exact .starNil
  | starCons _ _ iha ihs => exact .starCons iha ihs
  | optNil => exact .optNil
  | optSome _ ih => exact .optSome ih
  | plus _ _ iha ihs => exact .plus iha ihs

theorem accepts_mono {wide : Tag → Bool} (h : ∀ t, base t = true → wide t = true) {s : Seq}
    {tags : List Tag} (ha : accepts base s tags = true) : accepts wide s tags = true :=
  (accepts_iff s tags).mpr (((accepts_iff s tags).mp ha).mono h)

/-- The first state of the ordered model of an element. An element with no ordered model takes
any children in any order, and its state is one that every tag of its base leaves fixed. -/
def start (t : Tag) : Seq :=
  match t.seq? with
  | some (s, _) => s
  | none => .star (.base [])

end Seq

/-! ## What the model of an element reads -/

/-- What the ordered model of `t` reads of the tags of a child list: where the model intermixes
script-supporting elements, they are left out. -/
def keep (t : Tag) (tags : List Tag) : List Tag :=
  match t.seq? with
  | some (_, true) => tags.filter fun tag => !Cats.scriptSupporting tag
  | _ => tags

theorem keep_nil (t : Tag) : keep t [] = [] := by
  unfold keep
  split <;> rfl

/-- The model reads two lists of tags in a row as what it reads of each. -/
theorem keep_append (t : Tag) (tags more : List Tag) :
    keep t (tags ++ more) = keep t tags ++ keep t more := by
  unfold keep
  split
  · exact List.filter_append tags more
  · rfl

theorem keep_cons (t : Tag) (tag : Tag) (rest : List Tag) :
    keep t (tag :: rest) = keep t [tag] ++ keep t rest :=
  keep_append t [tag] rest

/-- The tags that the ordered model of `t` reads from a child list: comments are no children of
the model, and where the model intermixes script-supporting elements they are left out. -/
def modelTags (t : Tag) (children : List RawNode) : List Tag := keep t (childTags children)

theorem childTags_append (nodes more : List RawNode) :
    childTags (nodes ++ more) = childTags nodes ++ childTags more :=
  List.filterMap_append

theorem modelTags_nil (t : Tag) : modelTags t [] = [] := keep_nil t

/-- The model reads two lists of children in a row as the tags of the first and then of the
second. -/
theorem modelTags_append (t : Tag) (nodes more : List RawNode) :
    modelTags t (nodes ++ more) = modelTags t nodes ++ modelTags t more := by
  unfold modelTags
  rw [childTags_append, keep_append]

/-- The model reads a list of lists of children as the tags of each, in a row. -/
theorem modelTags_flatten (t : Tag) : ∀ lists : List (List RawNode),
    modelTags t lists.flatten = (lists.map (modelTags t)).flatten
  | [] => modelTags_nil t
  | nodes :: rest => by
    rw [List.flatten_cons, modelTags_append, modelTags_flatten t rest, List.map_cons,
      List.flatten_cons]

/-- What the model reads of one child whose tag is known. -/
theorem modelTags_singleton {t : Tag} {node : RawNode} {tag : Tag}
    (h : RawNode.tag? node = some tag) : modelTags t [node] = keep t [tag] := by
  unfold modelTags childTags
  rw [List.filterMap_cons, h, List.filterMap_nil]

namespace Seq

/-- The state of the model of `t` after one more child of the tag, over the element's own base.
A closed term when `t`, the state and the tag are. -/
def next (t : Tag) (s : Seq) (tag : Tag) : Seq := after t.ownBase.contains s (keep t [tag])

/-- The state after the tags of a child list, one child at a time. -/
theorem after_keep_cons (t : Tag) (s : Seq) (tag : Tag) (rest : List Tag) :
    after t.ownBase.contains s (keep t (tag :: rest)) =
      after t.ownBase.contains (next t s tag) (keep t rest) := by
  rw [keep_cons, after_append]
  rfl

/-- Children whose tags each leave the state where it was leave it there together. -/
theorem after_keep_of_fixed {t : Tag} {s : Seq} : ∀ {tags : List Tag},
    (∀ tag ∈ tags, next t s tag = s) → after t.ownBase.contains s (keep t tags) = s
  | [], _ => by rw [keep_nil]; rfl
  | tag :: rest, h => by
    rw [after_keep_cons, h tag List.mem_cons_self]
    exact after_keep_of_fixed fun later hlater => h later (List.mem_cons_of_mem tag hlater)

/-- Every tag of the set `among` leaves the state of the model of `t` where it was. The test is
closed when the state is: one evaluation answers for every child whose tag is in the set. -/
def absorbs (t : Tag) (s : Seq) (among : Tag → Bool) : Bool :=
  Tag.all.all fun tag => !among tag || next t s tag == s

theorem next_of_absorbs {t : Tag} {s : Seq} {among : Tag → Bool} (h : absorbs t s among = true)
    {tag : Tag} (htag : among tag = true) : next t s tag = s := by
  have hall := forall_tag_of_all _ h tag
  rw [htag, Bool.not_true, Bool.false_or] at hall
  exact eq_of_beq hall

/-- Children whose tags are of a set that the state absorbs leave the state where it was. -/
theorem after_keep_of_absorbs {t : Tag} {s : Seq} {among : Tag → Bool}
    (h : absorbs t s among = true) {tags : List Tag} (htags : ∀ tag ∈ tags, among tag = true) :
    after t.ownBase.contains s (keep t tags) = s :=
  after_keep_of_fixed fun tag htag => next_of_absorbs h (htags tag htag)

end Seq

/-! ## The decision as a fold -/

/-- `seqOk` is a fold: `nullable` of the model's state after the children. -/
theorem seqOk_eq_of_seq {t : Tag} {s : Seq} {interleave : Bool} (h : t.seq? = some (s, interleave))
    (c : Ctx) (children : List RawNode) :
    seqOk c t children = Seq.nullable (Seq.after c.base.contains s (modelTags t children)) := by
  unfold seqOk modelTags keep
  rw [h]
  cases interleave <;> rfl

theorem Seq.start_of_seq {t : Tag} {s : Seq} {interleave : Bool} (h : t.seq? = some (s, interleave)) :
    Seq.start t = s := by
  unfold Seq.start
  rw [h]

/-- Children after which the model's state is nullable follow the model. For an element with
no ordered model there is nothing to follow. -/
theorem seqOk_of_after (c : Ctx) (t : Tag) (children : List RawNode)
    (h : Seq.nullable (Seq.after c.base.contains (Seq.start t) (modelTags t children)) = true) :
    seqOk c t children = true := by
  cases hseq : t.seq? with
  | none => exact seqOk_of_none c t hseq children
  | some model =>
    obtain ⟨s, interleave⟩ := model
    rw [seqOk_eq_of_seq hseq, ← Seq.start_of_seq hseq]
    exact h

/-- The converse, for an element that has an ordered model. -/
theorem after_of_seqOk {c : Ctx} {t : Tag} {children : List RawNode} (hsome : t.seq?.isSome = true)
    (h : seqOk c t children = true) :
    Seq.nullable (Seq.after c.base.contains (Seq.start t) (modelTags t children)) = true := by
  cases hseq : t.seq? with
  | none =>
    rw [hseq] at hsome
    exact Bool.noConfusion hsome
  | some model =>
    obtain ⟨s, interleave⟩ := model
    rw [Seq.start_of_seq hseq, ← seqOk_eq_of_seq hseq]
    exact h

/-- An ordered model accepts no less at a position with a wider base. -/
theorem seqOk_mono {c wide : Ctx} (h : ∀ t, c.base.contains t = true → wide.base.contains t = true)
    (t : Tag) (children : List RawNode) (hc : seqOk c t children = true) :
    seqOk wide t children = true := by
  unfold seqOk at hc ⊢
  cases hseq : t.seq? with
  | none => rfl
  | some model =>
    rw [hseq] at hc
    exact Seq.accepts_mono h hc

/-- The children of an element that is not transparent are read over its own base. -/
theorem Ctx.child_base_of_not_transparent (c : Ctx) {t : Tag} (h : t.isTransparent = false) :
    (c.child t).base = t.ownBase := by
  simp only [Ctx.child, h, Bool.false_eq_true, ↓reduceIte]

end Whatwg.Html.Content
