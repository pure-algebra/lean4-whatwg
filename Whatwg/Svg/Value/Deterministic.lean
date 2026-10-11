import Whatwg.Svg.Value.Greedy

/-!
# Whatwg.Svg.Value.Deterministic

Owner: the bridge from the reader's rule to the language of the expression, for a
deterministic description (node V3c of `docs/SVG-PACKAGE-PLAN.md`, section 6; ruling SV-33;
slice S4d; note G2 of `docs/research/2026-10-11-svg-seat-guidance-2.md`, as section 4 of
`docs/research/2026-10-11-svg-seat-guidance-3.md` restates it).

The reader's rule is `Greedy` of `Whatwg/Svg/Value/Greedy.lean` (node V3b), and its language
is in general smaller than that of the expression `Syn.erase`. A description is deterministic
when one character decides each choice of its reader on every text of the language of its
expression. The reader of such a description accepts exactly that language, so `Syn.check`
decides `Regex.Matches`, and the two languages are one (`Syn.greedy_iff_matches`).

`Syn.ok` does not give this. It is computed from what the description prints, so it says that
a printed value reads back, and it says nothing of the other texts of the language. For
`number comma_wsp? number`, the text `12` is two numbers to the expression and one to the
reader, which commits to the longest match. The test of this module is the same test, computed
from what the description reads:

- `Syn.readContinues g` holds the characters that may continue the reader past a text of the
  language. It is `Syn.continues` with `readsEmpty` in place of `printsEmpty`.
- `Syn.deterministic g` is `Syn.ok` with `readsEmpty`, `readFirst` and `readContinues` in place
  of `printsEmpty`, `printFirst` and `continues`, and with no test of a canonical spelling,
  which the reader never sees. After a part, the first character of what follows cannot
  continue that part; the first alternative of a choice reads no empty text and opens as no
  text of the second; a repeated part reads no empty text and ends before its next copy.

Three facts are proved, each once over the description:

- `Syn.matches_head`: a text of the language is empty only if `readsEmpty` holds, and opens
  with a character of `readFirst`. It needs no premise.
- `Syn.read_complete` (node V3c): if `g.deterministic` holds, then `g.read` on a text of the
  language, followed by a text that cannot continue it, answers a value and that text.
- `Syn.check_iff_matches`: if `g.deterministic` holds, then `g.check s` holds exactly when `s`
  is a text of the language. The direction from the check is `Syn.matches_of_check`, which
  needs no premise.

A grammar discharges `g.deterministic` by one evaluation, as it discharges `g.ok`.

The source is Brüggemann-Klein and Wood, "One-unambiguous regular languages" (1998), on the
expressions that a reader matches with one character of lookahead and no backtracking. The
test is the condition of LL(1) parsing on its FIRST and FOLLOW sets: `readFirst` is the FIRST
set of a part, and `readContinues` holds the characters with which the reader of a part may
go on after a text of the part.

What this module does not claim: that a grammar which commits to the longest match, such as
path data, is deterministic. The sealed path grammar asks for the greedy rule at
`vendor/w3c-svgwg-47e645ef/master/paths.html` under the heading `PathDataBNF`, and there the
rule's language is the chapter's and the expression's is larger. The test is sufficient and not necessary: a description that fails it may
still read every text of its language, and `WhatwgTest/Svg/Deterministic.lean` holds one.
`Syn.read_complete` says that the reader answers a value and says nothing of which one:
`Regex.Matches` forgets the types.
-/

namespace Whatwg.Svg.Value

/-! ## The pieces of a repeated text -/

/-- Induction over the pieces of a text of a star: the empty text, and a text of the part
followed by a text of the star. -/
theorem Regex.Matches.star_induction {a : Regex} {motive : List Char → Prop}
    (nil : motive [])
    (cons : ∀ l₁ l₂ : List Char, a.Matches l₁ → (Regex.star a).Matches l₂ → motive l₂ →
      motive (l₁ ++ l₂)) :
    ∀ {l : List Char}, (Regex.star a).Matches l → motive l := by
  intro l h
  generalize hr : Regex.star a = r at h
  induction h with
  | eps => cases hr
  | set => cases hr
  | seq => cases hr
  | altL => cases hr
  | altR => cases hr
  | starNil => exact nil
  | starCons h₁ h₂ _ ih₂ =>
    cases hr
    exact cons _ _ h₁ h₂ (ih₂ rfl)

namespace Syn

/-! ## The test -/

/-- The characters that may continue the reader past a text of the description's language: a
text that opens with none of them leaves the reader where the text of the language ends. -/
def readContinues : {α : Type} → Syn α → CharSet
  | _, .eps => .empty
  | _, .one _ => .empty
  | _, .seq a b => if b.readsEmpty then b.readContinues.union a.readContinues else b.readContinues
  | _, .alt a b =>
    if b.readsEmpty then (a.readContinues.union b.readContinues).union a.readFirst
    else a.readContinues.union b.readContinues
  | _, .many a => a.readContinues.union a.readFirst
  | _, .map _ _ _ a => a.readContinues
  | _, .skip a _ => a.readContinues

/-- One character decides each choice of the reader on every text of the language. After a
part, the first character of what follows cannot continue that part; the first alternative of
a choice reads no empty text and opens as no text of the second; a repeated part reads no
empty text and ends before its next copy. -/
def deterministic : {α : Type} → Syn α → Bool
  | _, .eps => true
  | _, .one _ => true
  | _, .seq a b => a.deterministic && b.deterministic && a.readContinues.disjoint b.readFirst
  | _, .alt a b =>
    a.deterministic && b.deterministic && !a.readsEmpty && a.readFirst.disjoint b.readFirst
  | _, .many a => a.deterministic && !a.readsEmpty && a.readContinues.disjoint a.readFirst
  | _, .map _ _ _ a => a.deterministic
  | _, .skip a _ => a.deterministic

/-! ## What a text of the language opens with -/

/-- A text of the language is empty only if the reader may read nothing, and opens with a
character of `readFirst`. -/
theorem matches_head {α : Type} (g : Syn α) : ∀ l : List Char, g.erase.Matches l →
    (l = [] → g.readsEmpty = true) ∧ (∀ c t, l = c :: t → g.readFirst.mem c = true) := by
  induction g with
  | eps =>
    intro l h
    cases h
    exact ⟨fun _ => rfl, fun _ _ hl => nomatch hl⟩
  | one set =>
    intro l h
    cases h with
    | set hm =>
      refine ⟨(fun hl => nomatch hl), fun c t hl => ?_⟩
      rw [List.cons.injEq] at hl
      rw [← hl.1]
      exact hm
  | seq a b iha ihb =>
    intro l h
    cases h with
    | @seq _ _ l₁ l₂ h₁ h₂ =>
      obtain ⟨hae, haf⟩ := iha l₁ h₁
      obtain ⟨hbe, hbf⟩ := ihb l₂ h₂
      simp only [readsEmpty, readFirst]
      cases l₁ with
      | nil =>
        have hea := hae rfl
        refine ⟨fun hl => ?_, fun c t hl => ?_⟩
        · rw [List.nil_append] at hl
          rw [hea, hbe hl]
          rfl
        · rw [List.nil_append] at hl
          rw [hea, if_pos rfl, CharSet.mem_union, hbf c t hl, Bool.or_true]
      | cons c' t' =>
        refine ⟨(fun hl => nomatch hl), fun c t hl => ?_⟩
        rw [List.cons_append, List.cons.injEq] at hl
        have hmem := haf c' t' rfl
        rw [hl.1] at hmem
        cases a.readsEmpty with
        | false => exact hmem
        | true => rw [if_pos rfl, CharSet.mem_union, hmem, Bool.true_or]
  | alt a b iha ihb =>
    intro l h
    cases h with
    | altL h₁ =>
      obtain ⟨hae, haf⟩ := iha l h₁
      refine ⟨fun hl => ?_, fun c t hl => ?_⟩
      · simp only [readsEmpty, hae hl, Bool.true_or]
      · simp only [readFirst, CharSet.mem_union, haf c t hl, Bool.true_or]
    | altR h₂ =>
      obtain ⟨hbe, hbf⟩ := ihb l h₂
      refine ⟨fun hl => ?_, fun c t hl => ?_⟩
      · simp only [readsEmpty, hbe hl, Bool.or_true]
      · simp only [readFirst, CharSet.mem_union, hbf c t hl, Bool.or_true]
  | many a iha =>
    intro l h
    refine ⟨fun _ => rfl, ?_⟩
    refine Regex.Matches.star_induction
      (motive := fun l => ∀ c t, l = c :: t → a.readFirst.mem c = true) ?_ ?_ h
    · intro c t hl
      exact nomatch hl
    · intro l₁ l₂ h₁ _ ih c t hl
      cases l₁ with
      | nil =>
        rw [List.nil_append] at hl
        exact ih c t hl
      | cons c' t' =>
        rw [List.cons_append, List.cons.injEq] at hl
        have hmem := (iha (c' :: t') h₁).2 c' t' rfl
        rw [hl.1] at hmem
        exact hmem
  | map to back hlaw a iha => intro l h; exact iha l h
  | skip a canonical iha => intro l h; exact iha l h

/-! ## The completeness of the reader -/

/-- The repetition reads every text of the star whole, when its part reads every text of its
own language whole, reads no empty text, and ends before its next copy. -/
theorem readMany_complete {α : Type} (a : Syn α)
    (hread : ∀ (pre rest : List Char), a.erase.Matches pre → Stops a.readContinues rest →
      ∃ v, a.read (pre ++ rest) = some (v, rest))
    (hre : a.readsEmpty = false) (hdis : a.readContinues.disjoint a.readFirst = true)
    {rest : List Char} (hstops : Stops (a.readContinues.union a.readFirst) rest) :
    ∀ {pre : List Char}, (Regex.star a.erase).Matches pre → ∀ fuel : Nat, pre.length ≤ fuel →
      ∃ vs, readMany a.read fuel (pre ++ rest) = (vs, rest) := by
  intro pre h
  refine Regex.Matches.star_induction
    (motive := fun pre => ∀ fuel : Nat, pre.length ≤ fuel →
      ∃ vs, readMany a.read fuel (pre ++ rest) = (vs, rest)) ?_ ?_ h
  · intro fuel _
    rw [List.nil_append]
    cases fuel with
    | zero => exact ⟨[], rfl⟩
    | succ f => exact ⟨[], by simp only [readMany, read_eq_none a hre hstops.of_union_right]⟩
  · intro l₁ l₂ h₁ h₂ ih fuel hfuel
    cases l₁ with
    | nil =>
      have he := (matches_head a [] h₁).1 rfl
      rw [hre] at he
      exact Bool.noConfusion he
    | cons c₁ t₁ =>
      rw [List.cons_append, List.length_cons] at hfuel
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_succ_le_zero _)
      | succ f =>
        have htail : Stops a.readContinues (l₂ ++ rest) := by
          intro c t hc
          cases l₂ with
          | nil =>
            rw [List.nil_append] at hc
            exact hstops.of_union_left c t hc
          | cons c' t' =>
            rw [List.cons_append, List.cons.injEq] at hc
            have hmem := (matches_head (.many a) (c' :: t') h₂).2 c' t' rfl
            rw [hc.1] at hmem
            exact CharSet.not_mem_left_of_disjoint hdis hmem
        obtain ⟨x, hx⟩ := hread (c₁ :: t₁) (l₂ ++ rest) h₁ htail
        have hlt : (l₂ ++ rest).length < (c₁ :: t₁ ++ (l₂ ++ rest)).length := by
          rw [List.length_append (as := c₁ :: t₁), List.length_cons]
          exact Nat.lt_add_of_pos_left (Nat.succ_pos _)
        have hlen : l₂.length ≤ f := by
          have hle := Nat.le_of_succ_le_succ hfuel
          rw [List.length_append] at hle
          exact Nat.le_trans (Nat.le_add_left _ _) hle
        obtain ⟨vs, hvs⟩ := ih f hlen
        refine ⟨x :: vs, ?_⟩
        rw [List.append_assoc]
        simp only [readMany, hx, if_pos hlt, hvs]

/-- Node V3c for a deterministic description: the reader reads every text of the language
whole, when the text after it cannot continue it. -/
theorem read_complete {α : Type} (g : Syn α) : g.deterministic = true →
    ∀ (pre rest : List Char), g.erase.Matches pre → Stops g.readContinues rest →
      ∃ v, g.read (pre ++ rest) = some (v, rest) := by
  induction g with
  | eps =>
    intro _ pre rest hm _
    cases hm
    exact ⟨(), rfl⟩
  | one set =>
    intro _ pre rest hm _
    cases hm with
    | @set _ c hmem =>
      refine ⟨c, ?_⟩
      simp only [List.cons_append, List.nil_append, read]
      rw [if_pos hmem]
  | seq a b iha ihb =>
    intro hdet pre rest hm hstops
    simp only [deterministic, Bool.and_eq_true] at hdet
    obtain ⟨⟨hda, hdb⟩, hdis⟩ := hdet
    cases hm with
    | @seq _ _ p₁ p₂ h₁ h₂ =>
      obtain ⟨hbe, hbf⟩ := matches_head b p₂ h₂
      have hb : Stops b.readContinues rest := by
        simp only [readContinues] at hstops
        cases hbn : b.readsEmpty with
        | false => rw [hbn] at hstops; exact hstops
        | true => rw [hbn, if_pos rfl] at hstops; exact hstops.of_union_left
      have ha : Stops a.readContinues (p₂ ++ rest) := by
        intro c t hc
        cases p₂ with
        | nil =>
          rw [List.nil_append] at hc
          simp only [readContinues, hbe rfl, if_pos] at hstops
          exact hstops.of_union_right c t hc
        | cons c' t' =>
          rw [List.cons_append, List.cons.injEq] at hc
          have hmem := hbf c' t' rfl
          rw [hc.1] at hmem
          exact CharSet.not_mem_left_of_disjoint hdis hmem
      obtain ⟨x, hx⟩ := iha hda p₁ (p₂ ++ rest) h₁ ha
      obtain ⟨y, hy⟩ := ihb hdb p₂ rest h₂ hb
      exact ⟨(x, y), by simp only [read, List.append_assoc, hx, hy]⟩
  | alt a b iha ihb =>
    intro hdet pre rest hm hstops
    simp only [deterministic, Bool.and_eq_true, Bool.not_eq_true'] at hdet
    obtain ⟨⟨⟨hda, hdb⟩, hre⟩, hdis⟩ := hdet
    have hunion : Stops (a.readContinues.union b.readContinues) rest := by
      simp only [readContinues] at hstops
      cases hbn : b.readsEmpty with
      | false => rw [hbn] at hstops; exact hstops
      | true => rw [hbn, if_pos rfl] at hstops; exact hstops.of_union_left
    cases hm with
    | altL h₁ =>
      obtain ⟨x, hx⟩ := iha hda pre rest h₁ hunion.of_union_left
      exact ⟨.inl x, by simp only [read, hx]⟩
    | altR h₂ =>
      obtain ⟨hbe, hbf⟩ := matches_head b pre h₂
      have hnone : a.read (pre ++ rest) = none := by
        refine read_eq_none a hre ?_
        intro c t hc
        cases pre with
        | nil =>
          rw [List.nil_append] at hc
          simp only [readContinues, hbe rfl, if_pos] at hstops
          exact hstops.of_union_right c t hc
        | cons c' t' =>
          rw [List.cons_append, List.cons.injEq] at hc
          have hmem := hbf c' t' rfl
          rw [hc.1] at hmem
          exact CharSet.not_mem_left_of_disjoint hdis hmem
      obtain ⟨y, hy⟩ := ihb hdb pre rest h₂ hunion.of_union_right
      exact ⟨.inr y, by simp only [read, hnone, hy]⟩
  | many a iha =>
    intro hdet pre rest hm hstops
    simp only [deterministic, Bool.and_eq_true, Bool.not_eq_true'] at hdet
    obtain ⟨⟨hda, hre⟩, hdis⟩ := hdet
    have hfuel : pre.length ≤ (pre ++ rest).length := by
      rw [List.length_append]
      exact Nat.le_add_right _ _
    obtain ⟨vs, hvs⟩ := readMany_complete a (iha hda) hre hdis hstops hm _ hfuel
    exact ⟨vs, by simp only [read, hvs]⟩
  | map to back hlaw a iha =>
    intro hdet pre rest hm hstops
    obtain ⟨x, hx⟩ := iha hdet pre rest hm hstops
    exact ⟨to x, by simp only [read, hx]⟩
  | skip a canonical iha =>
    intro hdet pre rest hm hstops
    obtain ⟨x, hx⟩ := iha hdet pre rest hm hstops
    exact ⟨(), by simp only [read, hx]⟩

/-- For a deterministic description the check decides the language of its expression. -/
theorem check_iff_matches {α : Type} (g : Syn α) (h : g.deterministic = true) (s : List Char) :
    g.check s = true ↔ g.erase.Matches s := by
  refine ⟨fun hc => matches_of_check g hc, fun hm => ?_⟩
  obtain ⟨v, hv⟩ := read_complete g h s [] hm (Stops.nil _)
  rw [List.append_nil] at hv
  simp only [check, readAll, hv, Option.isSome_some]

/-- For a deterministic description the rule's language is the expression's: the rule reads a
text whole exactly when the text is of the language of `Syn.erase`. -/
theorem greedy_iff_matches {α : Type} (g : Syn α) (h : g.deterministic = true) (s : List Char) :
    (∃ v, Greedy g s (some (v, []))) ↔ g.erase.Matches s :=
  (check_iff_greedy g s).symm.trans (check_iff_matches g h s)

end Syn

/-! ## A deterministic grammar -/

namespace Grammar

/-- Node V3c at a grammar: for a deterministic grammar the check decides the language of its
description's expression. -/
theorem check_iff_matches {α : Type} (g : Grammar α) (h : g.syn.deterministic = true)
    (s : List Char) : g.check s = true ↔ g.syn.erase.Matches s :=
  Syn.check_iff_matches g.syn h s

end Grammar

end Whatwg.Svg.Value
