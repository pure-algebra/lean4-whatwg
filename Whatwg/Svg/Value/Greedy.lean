import Whatwg.Svg.Value.Grammar

/-!
# Whatwg.Svg.Value.Greedy

Owner: the rule of the reader, stated as a relation (node V3b of `docs/SVG-PACKAGE-PLAN.md`,
section 6; section 4 of `docs/research/2026-10-11-svg-seat-guidance-3.md`; debt D91 of
`COORDINATION.md`).

The sealed path grammar states how its productions are read. Under the heading `PathDataBNF`
of `vendor/w3c-svgwg-47e645ef/master/paths.html`, the processing must "consume as much of a
given EBNF production as possible", and it stops at the first character that no longer
satisfies the production. That is the reading of a parsing expression: a choice is ordered, a
repetition is greedy, and a part is not read again in another way when what follows it fails.
`Greedy g s o` states that reading for a description `g`: `o` is the outcome of reading the
text `s`.

An outcome is `none`, a refusal, or `some (v, r)`, the value and the text that is left. The
relation needs the refusal. An ordered choice takes its second alternative only when the first
fails, and a repetition stops only when its part fails or leaves a text that is not shorter. A
relation over successes alone would state both rules with a negative premise, and an inductive
relation has none. With the outcome, a failure is a derivation like any other.

What is proved:

- `readMany_fuel`: the answer of `readMany` does not depend on its fuel, once the fuel covers
  the length of the text.
- `Syn.greedy_read`: the reader's answer on a text is an outcome of the rule on it. So every
  reading has an outcome.
- `Syn.read_of_greedy`: an outcome of the rule on a text is the reader's answer on it.
- `Syn.greedy_iff_read` (node V3b): `Greedy g s o ↔ g.read s = o`. The reader is the decision
  procedure of the rule.
- `Greedy.unique`: the rule gives a reading at most one outcome.
- `Syn.check_iff_greedy` and `Grammar.check_iff_greedy`: the check holds exactly on the texts
  that the rule reads whole.
- `Greedy.sound`: what the rule reads is a text of the language of the description's
  expression. This is `Syn.read_sound` (node V3a), restated at the rule.

The source is Ford, "Parsing expression grammars: a recognition-based syntactic foundation"
(POPL 2004). The paper gives a parsing expression its meaning as a relation from an expression
and a text to an outcome, which is a failure or the text consumed. `Greedy` is that relation
over the forms of `Syn`, and its outcome holds the value read and the text left. One rule
differs. In the paper a repetition whose part succeeds and consumes nothing has no outcome,
and a well-formed grammar has no such repetition. Here the repetition stops, as `readMany`
does: the rule is `Greedy.manyStall`. The paper is not among the texts sealed in this
repository. It names the idea, and no law of this module rests on it.

What this module does not claim: that the language of the rule is the language of the
expression `Syn.erase`. It is smaller: the expression has texts that the rule does not read
whole, and `WhatwgTest/Svg/Greedy.lean` holds one. `Greedy.sound` is the one link between the
two, and `Whatwg/Svg/Value/Deterministic.lean` states when they agree. Nor does it claim that
a transcribed description is the chapter's grammar: no gate compares the two.

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from
Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C
Document License, https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Svg.Value

/-! ## The rule -/

/-- The meaning of a description as a parsing expression: the outcome of reading a text. The
outcome `none` is a refusal, and `some (v, r)` is the value read and the text that is left.

- `eps` reads nothing and succeeds.
- `one set` reads one character of the set, and fails on every other text.
- `seq a b` reads `a`, then `b` on what `a` leaves. It fails when either fails.
- `alt a b` reads `a`, and reads `b` only when `a` fails.
- `many a` never fails. It reads `a` for as long as `a` succeeds and leaves a shorter text.
- `map` and `skip` read their part, and map or forget its value. -/
inductive Greedy : {α : Type} → Syn α → List Char → Option (α × List Char) → Prop where
  /-- The empty description reads nothing, and succeeds on every text. -/
  | eps {s : List Char} : Greedy .eps s (some ((), s))
  /-- One character fails on the empty text. -/
  | oneNil {set : CharSet} : Greedy (.one set) [] none
  /-- One character reads a member of its set. -/
  | oneMem {set : CharSet} {c : Char} {t : List Char} : set.mem c = true →
      Greedy (.one set) (c :: t) (some (c, t))
  /-- One character fails on a character that is no member of its set. -/
  | oneNot {set : CharSet} {c : Char} {t : List Char} : set.mem c = false →
      Greedy (.one set) (c :: t) none
  /-- A sequence fails when its first part fails. -/
  | seqFail {α β : Type} {a : Syn α} {b : Syn β} {s : List Char} : Greedy a s none →
      Greedy (.seq a b) s none
  /-- A sequence fails when its first part succeeds and its second part fails on what the
  first leaves. The first part is not read again in another way. -/
  | seqRight {α β : Type} {a : Syn α} {b : Syn β} {s s₁ : List Char} {x : α} :
      Greedy a s (some (x, s₁)) → Greedy b s₁ none → Greedy (.seq a b) s none
  /-- A sequence reads its first part, then its second part on what the first leaves. -/
  | seq {α β : Type} {a : Syn α} {b : Syn β} {s s₁ s₂ : List Char} {x : α} {y : β} :
      Greedy a s (some (x, s₁)) → Greedy b s₁ (some (y, s₂)) →
      Greedy (.seq a b) s (some ((x, y), s₂))
  /-- A choice takes its first alternative when that one succeeds. -/
  | altLeft {α β : Type} {a : Syn α} {b : Syn β} {s s₁ : List Char} {x : α} :
      Greedy a s (some (x, s₁)) → Greedy (.alt a b) s (some (.inl x, s₁))
  /-- A choice takes its second alternative when the first fails. The second reads the same
  text, whatever the first consumed before it failed. -/
  | altRight {α β : Type} {a : Syn α} {b : Syn β} {s s₁ : List Char} {y : β} :
      Greedy a s none → Greedy b s (some (y, s₁)) → Greedy (.alt a b) s (some (.inr y, s₁))
  /-- A choice fails when both alternatives fail. -/
  | altFail {α β : Type} {a : Syn α} {b : Syn β} {s : List Char} :
      Greedy a s none → Greedy b s none → Greedy (.alt a b) s none
  /-- A repetition stops when its part fails: it reads no value and leaves the text. -/
  | manyStop {α : Type} {a : Syn α} {s : List Char} : Greedy a s none →
      Greedy (.many a) s (some ([], s))
  /-- A repetition stops when its part succeeds and leaves a text that is not shorter: it reads
  no value and leaves the text. The value of that part is not kept. -/
  | manyStall {α : Type} {a : Syn α} {s s₁ : List Char} {x : α} :
      Greedy a s (some (x, s₁)) → s.length ≤ s₁.length → Greedy (.many a) s (some ([], s))
  /-- A repetition goes on when its part succeeds and leaves a shorter text: it keeps the
  part's value and reads the rest from what the part leaves. -/
  | manyStep {α : Type} {a : Syn α} {s s₁ s₂ : List Char} {x : α} {xs : List α} :
      Greedy a s (some (x, s₁)) → s₁.length < s.length → Greedy (.many a) s₁ (some (xs, s₂)) →
      Greedy (.many a) s (some (x :: xs, s₂))
  /-- A mapped part fails when the part fails. -/
  | mapFail {α β : Type} {to : α → β} {back : β → α} {h : ∀ b, to (back b) = b} {a : Syn α}
      {s : List Char} : Greedy a s none → Greedy (.map to back h a) s none
  /-- A mapped part reads the part, and maps its value. -/
  | map {α β : Type} {to : α → β} {back : β → α} {h : ∀ b, to (back b) = b} {a : Syn α}
      {s s₁ : List Char} {x : α} :
      Greedy a s (some (x, s₁)) → Greedy (.map to back h a) s (some (to x, s₁))
  /-- A forgotten part fails when the part fails. -/
  | skipFail {α : Type} {a : Syn α} {canonical : α} {s : List Char} : Greedy a s none →
      Greedy (.skip a canonical) s none
  /-- A forgotten part reads the part, and forgets its value. -/
  | skip {α : Type} {a : Syn α} {canonical : α} {s s₁ : List Char} {x : α} :
      Greedy a s (some (x, s₁)) → Greedy (.skip a canonical) s (some ((), s₁))

/-! ## The fuel of a repetition

`Syn.read` runs `readMany` with the length of the text as its fuel. The rule has no fuel. So
the proofs below need the three cases of one step of `readMany` at that fuel, and the step
case needs `readMany_fuel`: the rest of the text is read with less fuel than its own length
would give it, and the answer is the same. -/

/-- On the empty text, `readMany` reads no part, whatever its fuel. -/
theorem readMany_nil {α : Type} (step : List Char → Option (α × List Char)) :
    ∀ fuel : Nat, readMany step fuel [] = ([], [])
  | 0 => rfl
  | fuel + 1 => by
    cases hstep : step [] with
    | none => simp only [readMany, hstep]
    | some found =>
      have hnot : ¬ found.2.length < ([] : List Char).length := Nat.not_lt_zero _
      simp only [readMany, hstep, if_neg hnot]

/-- The outcome of `readMany` does not depend on its fuel, once the fuel covers the text. -/
theorem readMany_fuel {α : Type} (step : List Char → Option (α × List Char)) :
    ∀ (fuel₁ fuel₂ : Nat) (s : List Char), s.length ≤ fuel₁ → s.length ≤ fuel₂ →
      readMany step fuel₁ s = readMany step fuel₂ s
  | 0, fuel₂, s, h₁, _ => by
    rw [List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h₁), readMany_nil, readMany_nil]
  | fuel₁ + 1, 0, s, _, h₂ => by
    rw [List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h₂), readMany_nil, readMany_nil]
  | fuel₁ + 1, fuel₂ + 1, s, h₁, h₂ => by
    cases hstep : step s with
    | none => simp only [readMany, hstep]
    | some found =>
      cases hlt : decide (found.2.length < s.length) with
      | false => simp only [readMany, hstep, if_neg (of_decide_eq_false hlt)]
      | true =>
        have hlt' : found.2.length < s.length := of_decide_eq_true hlt
        have ih := readMany_fuel step fuel₁ fuel₂ found.2
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt' h₁))
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt' h₂))
        simp only [readMany, hstep, if_pos hlt', ih]

/-- A run of `readMany` whose step fails reads no part. -/
theorem readMany_of_none {α : Type} {step : List Char → Option (α × List Char)}
    {s : List Char} (h : step s = none) : ∀ fuel : Nat, readMany step fuel s = ([], s)
  | 0 => rfl
  | fuel + 1 => by simp only [readMany, h]

/-- A run of `readMany` whose step leaves a text that is not shorter reads no part. -/
theorem readMany_of_stall {α : Type} {step : List Char → Option (α × List Char)}
    {s s₁ : List Char} {x : α} (h : step s = some (x, s₁)) (hle : s.length ≤ s₁.length) :
    ∀ fuel : Nat, readMany step fuel s = ([], s)
  | 0 => rfl
  | fuel + 1 => by simp only [readMany, h, if_neg (Nat.not_lt.mpr hle)]

/-- A run of `readMany` whose step leaves a shorter text keeps the step's value and goes on
from what the step leaves. Each run has the length of its text as its fuel. -/
theorem readMany_of_step {α : Type} {step : List Char → Option (α × List Char)}
    {s s₁ r : List Char} {x : α} {xs : List α} (h : step s = some (x, s₁))
    (hlt : s₁.length < s.length) (hrest : readMany step s₁.length s₁ = (xs, r)) :
    readMany step s.length s = (x :: xs, r) := by
  cases hn : s.length with
  | zero =>
    rw [hn] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | succ n =>
    have hle : s₁.length ≤ n := Nat.le_of_lt_succ (Nat.lt_of_lt_of_eq hlt hn)
    rw [readMany_fuel step s₁.length n s₁ (Nat.le_refl _) hle] at hrest
    simp only [readMany, h, if_pos hlt, hrest]

namespace Syn

/-! ## The reader decides the rule -/

/-- The answer of a repetition's reader is an outcome of the rule, when the answer of its
part's reader is one. -/
theorem greedy_readMany {α : Type} (a : Syn α)
    (hread : ∀ s : List Char, Greedy a s (a.read s)) :
    ∀ s : List Char, Greedy (.many a) s (some (readMany a.read s.length s)) := by
  have step : ∀ s : List Char,
      (∀ s₁ : List Char, s₁.length < s.length →
        Greedy (.many a) s₁ (some (readMany a.read s₁.length s₁))) →
      Greedy (.many a) s (some (readMany a.read s.length s)) := by
    intro s ih
    have ha := hread s
    cases hr : a.read s with
    | none =>
      rw [hr] at ha
      rw [readMany_of_none hr]
      exact .manyStop ha
    | some found =>
      obtain ⟨x, s₁⟩ := found
      rw [hr] at ha
      cases hlt : decide (s₁.length < s.length) with
      | false =>
        have hle : s.length ≤ s₁.length := Nat.not_lt.mp (of_decide_eq_false hlt)
        rw [readMany_of_stall hr hle]
        exact .manyStall ha hle
      | true =>
        have hlt' : s₁.length < s.length := of_decide_eq_true hlt
        have hmore := ih s₁ hlt'
        cases hrest : readMany a.read s₁.length s₁ with
        | mk xs r =>
          rw [hrest] at hmore
          rw [readMany_of_step hr hlt' hrest]
          exact .manyStep ha hlt' hmore
  have bounded : ∀ (n : Nat) (s : List Char), s.length ≤ n →
      Greedy (.many a) s (some (readMany a.read s.length s)) := by
    intro n
    induction n with
    | zero =>
      intro s hn
      exact step s fun s₁ h => absurd (Nat.lt_of_lt_of_le h hn) (Nat.not_lt_zero _)
    | succ k ih =>
      intro s hn
      exact step s fun s₁ h => ih s₁ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h hn))
  exact fun s => bounded s.length s (Nat.le_refl _)

/-- The reader's answer is an outcome of the rule: every reading has one. -/
theorem greedy_read {α : Type} (g : Syn α) : ∀ s : List Char, Greedy g s (g.read s) := by
  induction g with
  | eps => intro s; exact .eps
  | one set =>
    intro s
    cases s with
    | nil => exact .oneNil
    | cons c t =>
      show Greedy (.one set) (c :: t) (if set.mem c = true then some (c, t) else none)
      cases hm : set.mem c with
      | true =>
        rw [if_pos rfl]
        exact .oneMem hm
      | false =>
        rw [if_neg Bool.false_ne_true]
        exact .oneNot hm
  | seq a b iha ihb =>
    intro s
    have ha := iha s
    cases hra : a.read s with
    | none =>
      rw [hra] at ha
      simp only [read, hra]
      exact .seqFail ha
    | some found =>
      obtain ⟨x, s₁⟩ := found
      rw [hra] at ha
      have hb := ihb s₁
      cases hrb : b.read s₁ with
      | none =>
        rw [hrb] at hb
        simp only [read, hra, hrb]
        exact .seqRight ha hb
      | some found₂ =>
        obtain ⟨y, s₂⟩ := found₂
        rw [hrb] at hb
        simp only [read, hra, hrb]
        exact .seq ha hb
  | alt a b iha ihb =>
    intro s
    have ha := iha s
    cases hra : a.read s with
    | some found =>
      obtain ⟨x, s₁⟩ := found
      rw [hra] at ha
      simp only [read, hra]
      exact .altLeft ha
    | none =>
      rw [hra] at ha
      have hb := ihb s
      cases hrb : b.read s with
      | some found =>
        obtain ⟨y, s₁⟩ := found
        rw [hrb] at hb
        simp only [read, hra, hrb]
        exact .altRight ha hb
      | none =>
        rw [hrb] at hb
        simp only [read, hra, hrb]
        exact .altFail ha hb
  | many a iha => intro s; exact greedy_readMany a iha s
  | map to back hlaw a iha =>
    intro s
    have ha := iha s
    cases hra : a.read s with
    | none =>
      rw [hra] at ha
      simp only [read, hra]
      exact .mapFail ha
    | some found =>
      obtain ⟨x, s₁⟩ := found
      rw [hra] at ha
      simp only [read, hra]
      exact .map ha
  | skip a canonical iha =>
    intro s
    have ha := iha s
    cases hra : a.read s with
    | none =>
      rw [hra] at ha
      simp only [read, hra]
      exact .skipFail ha
    | some found =>
      obtain ⟨x, s₁⟩ := found
      rw [hra] at ha
      simp only [read, hra]
      exact .skip ha

/-- An outcome of the rule is the reader's answer: the rule gives each reading one outcome. -/
theorem read_of_greedy {α : Type} {g : Syn α} {s : List Char} {o : Option (α × List Char)}
    (h : Greedy g s o) : g.read s = o := by
  induction h with
  | eps => rfl
  | oneNil => rfl
  | oneMem hm =>
    simp only [read]
    rw [if_pos hm]
  | oneNot hm =>
    simp only [read]
    rw [if_neg (ne_true_of_eq_false hm)]
  | seqFail _ iha => simp only [read, iha]
  | seqRight _ _ iha ihb => simp only [read, iha, ihb]
  | seq _ _ iha ihb => simp only [read, iha, ihb]
  | altLeft _ iha => simp only [read, iha]
  | altRight _ _ iha ihb => simp only [read, iha, ihb]
  | altFail _ _ iha ihb => simp only [read, iha, ihb]
  | manyStop _ iha =>
    simp only [read, Option.some.injEq]
    exact readMany_of_none iha _
  | manyStall _ hle iha =>
    simp only [read, Option.some.injEq]
    exact readMany_of_stall iha hle _
  | manyStep _ hlt _ iha ihm =>
    simp only [read, Option.some.injEq] at ihm
    simp only [read, Option.some.injEq]
    exact readMany_of_step iha hlt ihm
  | mapFail _ iha => simp only [read, iha]
  | map _ iha => simp only [read, iha]
  | skipFail _ iha => simp only [read, iha]
  | skip _ iha => simp only [read, iha]

/-- Node V3b: the reader is the decision procedure of the rule. -/
theorem greedy_iff_read {α : Type} (g : Syn α) (s : List Char) (o : Option (α × List Char)) :
    Greedy g s o ↔ g.read s = o :=
  ⟨read_of_greedy, fun h => h ▸ greedy_read g s⟩

/-- The check decides the language of the rule: the texts that the rule reads whole. -/
theorem check_iff_greedy {α : Type} (g : Syn α) (s : List Char) :
    g.check s = true ↔ ∃ v, Greedy g s (some (v, [])) := by
  constructor
  · intro h
    simp only [check, readAll] at h
    cases hr : g.read s with
    | none =>
      rw [hr] at h
      exact Bool.noConfusion h
    | some found =>
      obtain ⟨v, r⟩ := found
      cases r with
      | nil => exact ⟨v, hr ▸ greedy_read g s⟩
      | cons c t =>
        rw [hr] at h
        exact Bool.noConfusion h
  · intro ⟨v, h⟩
    simp only [check, readAll, read_of_greedy h, Option.isSome_some]

end Syn

/-- The rule gives a reading at most one outcome. -/
theorem Greedy.unique {α : Type} {g : Syn α} {s : List Char} {o₁ o₂ : Option (α × List Char)}
    (h₁ : Greedy g s o₁) (h₂ : Greedy g s o₂) : o₁ = o₂ :=
  (Syn.read_of_greedy h₁).symm.trans (Syn.read_of_greedy h₂)

/-- What the rule reads is a text of the expression's language (node V3a, restated at the
rule): the text is what was read, then what is left. -/
theorem Greedy.sound {α : Type} {g : Syn α} {s r : List Char} {v : α}
    (h : Greedy g s (some (v, r))) : ∃ pre, s = pre ++ r ∧ g.erase.Matches pre :=
  Syn.read_sound g s v r (Syn.read_of_greedy h)

/-- The check of a grammar decides the language of the rule: the texts that the rule reads
whole. -/
theorem Grammar.check_iff_greedy {α : Type} (g : Grammar α) (s : List Char) :
    g.check s = true ↔ ∃ v, Greedy g.syn s (some (v, [])) :=
  Syn.check_iff_greedy g.syn s

end Whatwg.Svg.Value
