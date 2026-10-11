import Whatwg.Html.Content.Context
import Whatwg.Html.Node.Raw

/-!
# Whatwg.Html.Content.Sequence

The ordered content models, checked (ruling HP-13, slices H7.1 and H7.4).
An element whose reading is a sequence (`Tag.seq?`) requires the tags of its
children, in order, to match a regular expression over tags.

The meaning of a sequence is the inductive relation `Seq.Matches`; the
decision procedure `Seq.accepts` is Brzozowski's derivative with the
simplifying constructors `sq` and `al`, and `accepts_iff` proves it decides
`Matches`. Without the simplifications the derivative terms grew without
bound and a `<dl>` of a hundred groups cost nine seconds of kernel time
(performance review §5); with them the derivative of every sequence at the
pin stays a handful of nodes at any length. Text counts as the tag `pcdata`;
a comment is not a child of the sequence; where the sentence intermixes
script-supporting elements, they are removed before matching. `base except`
matches one tag the children's base admits other than the named ones.
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema
open Whatwg.Html (RawNode)

namespace Seq

/-! ## The denotation -/

/-- The sequence matches the list of tags, over the base `base`. -/
inductive Matches (base : Tag → Bool) : Seq → List Tag → Prop
  | eps : Matches base .eps []
  | tag (t : Tag) : Matches base (.tag t) [t]
  | base {ex : List Tag} (t : Tag) (hb : base t = true) (hex : ex.contains t = false) :
      Matches base (.base ex) [t]
  | seq {a b : Seq} {l₁ l₂ : List Tag} : Matches base a l₁ → Matches base b l₂ →
      Matches base (.seq a b) (l₁ ++ l₂)
  | altL {a b : Seq} {l : List Tag} : Matches base a l → Matches base (.alt a b) l
  | altR {a b : Seq} {l : List Tag} : Matches base b l → Matches base (.alt a b) l
  | starNil {a : Seq} : Matches base (.star a) []
  | starCons {a : Seq} {l₁ l₂ : List Tag} : Matches base a l₁ → Matches base (.star a) l₂ →
      Matches base (.star a) (l₁ ++ l₂)
  | optNil {a : Seq} : Matches base (.opt a) []
  | optSome {a : Seq} {l : List Tag} : Matches base a l → Matches base (.opt a) l
  | plus {a : Seq} {l₁ l₂ : List Tag} : Matches base a l₁ → Matches base (.star a) l₂ →
      Matches base (.plus a) (l₁ ++ l₂)

/-! ## The decision procedure -/

def nullable : Seq → Bool
  | .eps => true
  | .empty => false
  | .tag _ => false
  | .base _ => false
  | .seq a b => nullable a && nullable b
  | .alt a b => nullable a || nullable b
  | .star _ => true
  | .opt _ => true
  | .plus a => nullable a

/-- `seq`, simplified: `empty` absorbs, `eps` is the unit. -/
def sq : Seq → Seq → Seq
  | .empty, _ => .empty
  | _, .empty => .empty
  | .eps, b => b
  | a, .eps => a
  | a, b => .seq a b

/-- `alt`, simplified: `empty` is the unit, and `a | a` is `a`. -/
def al : Seq → Seq → Seq
  | .empty, b => b
  | a, .empty => a
  | a, b => if a = b then a else .alt a b

/-- The derivative by one tag, with `base` the children's base. -/
def deriv (base : Tag → Bool) : Seq → Tag → Seq
  | .eps, _ => .empty
  | .empty, _ => .empty
  | .tag other, t => if t == other then .eps else .empty
  | .base ex, t => if base t && !ex.contains t then .eps else .empty
  | .seq a b, t => al (sq (deriv base a t) b) (if nullable a then deriv base b t else .empty)
  | .alt a b, t => al (deriv base a t) (deriv base b t)
  | .star a, t => sq (deriv base a t) (.star a)
  | .opt a, t => deriv base a t
  | .plus a, t => sq (deriv base a t) (.star a)

/-- The sequence accepts the list of tags. -/
def accepts (base : Tag → Bool) (s : Seq) (ts : List Tag) : Bool :=
  nullable (ts.foldl (deriv base) s)

/-! ## Correctness -/

section
variable {base : Tag → Bool}

/-! Inversion lemmas, each stated with a variable list index so that `cases`
applies; the concrete indices `[]` and `t :: ts` are handled by the
equation they return. -/

theorem not_matches_empty {l : List Tag} : ¬ Matches base .empty l := by
  intro h; cases h

theorem eps_inv {l : List Tag} (h : Matches base .eps l) : l = [] := by cases h; rfl

theorem tag_inv {t : Tag} {l : List Tag} (h : Matches base (.tag t) l) : l = [t] := by cases h; rfl

theorem base_inv {ex : List Tag} {l : List Tag} (h : Matches base (.base ex) l) :
    ∃ t, l = [t] ∧ base t = true ∧ ex.contains t = false := by
  cases h with | base t hb hex => exact ⟨t, rfl, hb, hex⟩

theorem seq_inv {a b : Seq} {l : List Tag} (h : Matches base (.seq a b) l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ Matches base a l₁ ∧ Matches base b l₂ := by
  cases h with | seq ha hb => exact ⟨_, _, rfl, ha, hb⟩

theorem alt_inv {a b : Seq} {l : List Tag} (h : Matches base (.alt a b) l) :
    Matches base a l ∨ Matches base b l := by
  cases h with
  | altL h => exact Or.inl h
  | altR h => exact Or.inr h

theorem opt_inv {a : Seq} {l : List Tag} (h : Matches base (.opt a) l) : l = [] ∨ Matches base a l := by
  cases h with
  | optNil => exact Or.inl rfl
  | optSome h => exact Or.inr h

theorem plus_inv {a : Seq} {l : List Tag} (h : Matches base (.plus a) l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ Matches base a l₁ ∧ Matches base (.star a) l₂ := by
  cases h with | plus ha hs => exact ⟨_, _, rfl, ha, hs⟩

theorem matches_eps_iff {l : List Tag} : Matches base .eps l ↔ l = [] :=
  ⟨eps_inv, by rintro rfl; exact .eps⟩

theorem nullable_iff : ∀ s : Seq, nullable s = true ↔ Matches base s [] := by
  intro s
  induction s with
  | eps => simp [nullable, Matches.eps]
  | empty => simp [nullable, not_matches_empty]
  | tag t => simp only [nullable, Bool.false_eq_true, false_iff]; intro h; have := tag_inv h; simp at this
  | base ex =>
    simp only [nullable, Bool.false_eq_true, false_iff]
    intro h; obtain ⟨t, ht, _, _⟩ := base_inv h; simp at ht
  | seq a b iha ihb =>
    simp only [nullable, Bool.and_eq_true, iha, ihb]
    constructor
    · rintro ⟨ha, hb⟩; exact Matches.seq (l₁ := []) (l₂ := []) ha hb
    · intro h
      obtain ⟨l₁, l₂, heq, ha, hb⟩ := seq_inv h
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp heq.symm
      exact ⟨ha, hb⟩
  | alt a b iha ihb =>
    simp only [nullable, Bool.or_eq_true, iha, ihb]
    constructor
    · rintro (h | h); exact .altL h; exact .altR h
    · exact alt_inv
  | star a _ => simp [nullable, Matches.starNil]
  | opt a _ => simp [nullable, Matches.optNil]
  | plus a iha =>
    simp only [nullable, iha]
    constructor
    · intro h; exact Matches.plus (l₁ := []) (l₂ := []) h .starNil
    · intro h
      obtain ⟨l₁, l₂, heq, ha, _⟩ := plus_inv h
      obtain ⟨rfl, _⟩ := List.append_eq_nil_iff.mp heq.symm
      exact ha

/-- The simplifying constructors have the meaning of the plain ones. -/
theorem matches_sq_iff (a b : Seq) (l : List Tag) :
    Matches base (sq a b) l ↔ Matches base (.seq a b) l := by
  unfold sq
  split
  · constructor
    · intro h; exact absurd h not_matches_empty
    · intro h; obtain ⟨_, _, _, ha, _⟩ := seq_inv h; exact absurd ha not_matches_empty
  · constructor
    · intro h; exact absurd h not_matches_empty
    · intro h; obtain ⟨_, _, _, _, hb⟩ := seq_inv h; exact absurd hb not_matches_empty
  · constructor
    · intro h; exact Matches.seq (l₁ := []) .eps h
    · intro h
      obtain ⟨l₁, l₂, heq, ha, hb⟩ := seq_inv h
      subst heq; rw [eps_inv ha]; simpa using hb
  · constructor
    · intro h; simpa using Matches.seq (l₂ := []) h .eps
    · intro h
      obtain ⟨l₁, l₂, heq, ha, hb⟩ := seq_inv h
      subst heq; rw [eps_inv hb]; simpa using ha
  · exact Iff.rfl

theorem matches_al_iff (a b : Seq) (l : List Tag) :
    Matches base (al a b) l ↔ Matches base (.alt a b) l := by
  unfold al
  split
  · constructor
    · intro h; exact .altR h
    · intro h; rcases alt_inv h with h | h
      · exact absurd h not_matches_empty
      · exact h
  · constructor
    · intro h; exact .altL h
    · intro h; rcases alt_inv h with h | h
      · exact h
      · exact absurd h not_matches_empty
  · split
    · rename_i heq; subst heq
      constructor
      · intro h; exact .altL h
      · intro h; rcases alt_inv h with h | h <;> exact h
    · exact Iff.rfl

/-- A `star` match of a nonempty list begins with a nonempty match of the body. -/
theorem star_cons_aux {s : Seq} {l : List Tag} (h : Matches base s l) :
    ∀ a, s = .star a → ∀ t ts, l = t :: ts →
      ∃ l₁ l₂, Matches base a (t :: l₁) ∧ Matches base (.star a) l₂ ∧ ts = l₁ ++ l₂ := by
  induction h with
  | @starCons a l₁ l₂ ha hs _ ih =>
    intro a' hsa t ts hl
    injection hsa with hsa
    subst hsa
    cases l₁ with
    | nil => exact ih _ rfl t ts (by simpa using hl)
    | cons v l₁' =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨l₁', l₂, ha, hs, rfl⟩
  | starNil => intro _ _ t ts hl; simp at hl
  | eps => intro _ hsa; cases hsa
  | tag => intro _ hsa; cases hsa
  | base => intro _ hsa; cases hsa
  | seq => intro _ hsa; cases hsa
  | altL => intro _ hsa; cases hsa
  | altR => intro _ hsa; cases hsa
  | optNil => intro _ hsa; cases hsa
  | optSome => intro _ hsa; cases hsa
  | plus => intro _ hsa; cases hsa

theorem star_cons {a : Seq} {t : Tag} {ts : List Tag} (h : Matches base (.star a) (t :: ts)) :
    ∃ l₁ l₂, Matches base a (t :: l₁) ∧ Matches base (.star a) l₂ ∧ ts = l₁ ++ l₂ :=
  star_cons_aux h a rfl t ts rfl

/-- The derivative is correct. -/
theorem deriv_iff : ∀ (s : Seq) (t : Tag) (ts : List Tag),
    Matches base (deriv base s t) ts ↔ Matches base s (t :: ts) := by
  intro s
  induction s with
  | eps =>
    intro t ts; rw [deriv]
    constructor
    · intro h; exact absurd h not_matches_empty
    · intro h; exact absurd (eps_inv h) (by simp)
  | empty =>
    intro t ts; rw [deriv]
    constructor
    · intro h; exact absurd h not_matches_empty
    · intro h; exact absurd h not_matches_empty
  | tag other =>
    intro t ts; rw [deriv]
    by_cases h : t = other
    · subst h
      simp only [beq_self_eq_true, ↓reduceIte, matches_eps_iff]
      constructor
      · rintro rfl; exact .tag t
      · intro h; simpa using tag_inv h
    · have : (t == other) = false := by simpa using h
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h; exact absurd h not_matches_empty
      · intro h'; have := tag_inv h'; simp only [List.cons.injEq] at this; exact absurd this.1 h
  | base ex =>
    intro t ts; rw [deriv]
    by_cases hb : (base t && !ex.contains t) = true
    · simp only [hb, ↓reduceIte, matches_eps_iff]
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
      constructor
      · rintro rfl; exact .base t hb.1 hb.2
      · intro h; obtain ⟨v, hv, _, _⟩ := base_inv h; simp only [List.cons.injEq] at hv; exact hv.2
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h; exact absurd h not_matches_empty
      · intro h
        obtain ⟨v, hv, h1, h2⟩ := base_inv h
        simp only [List.cons.injEq] at hv
        obtain ⟨rfl, _⟩ := hv
        exact (hb (by rw [h1, h2]; rfl)).elim
  | seq a b iha ihb =>
    intro t ts
    rw [deriv, matches_al_iff]
    constructor
    · intro h
      rcases alt_inv h with h | h
      · rw [matches_sq_iff] at h
        obtain ⟨l₁, l₂, heq, ha, hb⟩ := seq_inv h
        subst heq
        rw [iha] at ha
        simpa using Matches.seq ha hb
      · by_cases hn : nullable a = true
        · simp only [hn, ↓reduceIte] at h
          rw [ihb] at h
          have ha : Matches base a [] := (nullable_iff a).mp hn
          simpa using Matches.seq ha h
        · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
          exact absurd h not_matches_empty
    · intro h
      obtain ⟨l₁, l₂, heq, ha, hb⟩ := seq_inv h
      cases l₁ with
      | nil =>
        simp only [List.nil_append] at heq
        subst heq
        apply Matches.altR
        have hn : nullable a = true := (nullable_iff a).mpr ha
        simp only [hn, ↓reduceIte]
        exact (ihb t ts).mpr hb
      | cons v l₁' =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact Matches.altL ((matches_sq_iff _ _ _).mpr (Matches.seq ((iha t l₁').mpr ha) hb))
  | alt a b iha ihb =>
    intro t ts
    rw [deriv, matches_al_iff]
    constructor
    · intro h; rcases alt_inv h with h | h
      · exact .altL ((iha t ts).mp h)
      · exact .altR ((ihb t ts).mp h)
    · intro h; rcases alt_inv h with h | h
      · exact .altL ((iha t ts).mpr h)
      · exact .altR ((ihb t ts).mpr h)
  | star a iha =>
    intro t ts
    rw [deriv, matches_sq_iff]
    constructor
    · intro h
      obtain ⟨l₁, l₂, heq, ha, hs⟩ := seq_inv h
      subst heq
      rw [iha] at ha
      simpa using Matches.starCons ha hs
    · intro h
      obtain ⟨l₁, l₂, ha, hs, rfl⟩ := star_cons h
      exact Matches.seq ((iha t l₁).mpr ha) hs
  | opt a iha =>
    intro t ts
    rw [deriv]
    constructor
    · intro h; exact .optSome ((iha t ts).mp h)
    · intro h; rcases opt_inv h with h | h
      · simp at h
      · exact (iha t ts).mpr h
  | plus a iha =>
    intro t ts
    rw [deriv, matches_sq_iff]
    constructor
    · intro h
      obtain ⟨l₁, l₂, heq, ha, hs⟩ := seq_inv h
      subst heq
      rw [iha] at ha
      simpa using Matches.plus ha hs
    · intro h
      obtain ⟨l₁, l₂, heq, ha, hs⟩ := plus_inv h
      cases l₁ with
      | nil =>
        simp only [List.nil_append] at heq
        subst heq
        obtain ⟨m₁, m₂, ha', hs', rfl⟩ := star_cons hs
        exact Matches.seq ((iha t m₁).mpr ha') hs'
      | cons v l₁' =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact Matches.seq ((iha t l₁').mpr ha) hs

/-- `accepts` decides `Matches`. -/
theorem accepts_iff (s : Seq) (ts : List Tag) :
    accepts base s ts = true ↔ Matches base s ts := by
  induction ts generalizing s with
  | nil => exact nullable_iff s
  | cons t ts ih =>
    simp only [accepts, List.foldl_cons]
    rw [← deriv_iff]
    exact ih (deriv base s t)

end

end Seq

/-- The tag a raw node counts as in a sequence: its element tag, or its
foreign tag when its name is a foreign element's (`svg`); `pcdata` for text
and entities; none for a comment or an unknown name. A foreign child takes
a place in a sequence as any flow or phrasing child does. -/
def RawNode.tag? : RawNode → Option Tag
  | .element name _ _ => (Tag.ofName? name).orElse fun _ => Tag.ofForeignName? name
  | .text _ => some .pcdata
  | .entity _ => some .pcdata
  | .comment _ => none

/-- The tags of a child list, comments dropped. -/
def childTags (children : List RawNode) : List Tag := children.filterMap RawNode.tag?

/-- The children of an element of tag `t`, checked at the children's context
`c`, follow the element's ordered model; trivially so when it has none. -/
def seqOk (c : Ctx) (t : Tag) (children : List RawNode) : Bool :=
  match t.seq? with
  | none => true
  | some (s, interleave) =>
    let ts := childTags children
    let ts := if interleave then ts.filter (fun tg => !Cats.scriptSupporting tg) else ts
    Seq.accepts c.base.contains s ts

/-- Why the children do not follow the model, for messages. -/
def seqProblem? (c : Ctx) (t : Tag) (children : List RawNode) : Option String :=
  match t.seq? with
  | none => none
  | some (s, _) =>
    if seqOk c t children then none
    else some ("the children of <" ++ t.markupText ++ "> do not follow its content model: " ++ s.render)

theorem seqOk_of_none (c : Ctx) (t : Tag) (h : t.seq? = none) (children : List RawNode) :
    seqOk c t children = true := by
  simp [seqOk, h]

/-- The tags with a sequence at the pin. -/
theorem sequenced_tags : Tag.all.filter (fun t => (Tag.seq? t).isSome) =
    [.html, .head, .hgroup, .dl, .figure, .picture, .video, .audio, .table, .select, .optgroup, .fieldset, .details] := by
  decide +kernel

end Whatwg.Html.Content
