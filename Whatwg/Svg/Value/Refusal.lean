import Whatwg.Svg.Value.Grammar.Laws

/-!
# Whatwg.Svg.Value.Refusal

Owner: the located refusal of a value (note G3 of
`docs/research/2026-10-11-svg-seat-guidance-2.md`; node V6 of `docs/SVG-PACKAGE-PLAN.md`,
section 6) and the locality of its offset (node V6b). When a whole text is not a spelling of a
description, `Syn.explain` names the offset of the first character that no reading continues.

`Syn.run` is the reader with its reach. The reach of a reading is the length of the shortest
text the reading stood on. Every position that a part reached by success counts, and so does
every position at which a part refused. A reading that tries a part and gives it up keeps the
part's reach: the reader hands back the text where the part began, and the reach stays where
the part stopped. So `s.length - reach` is the furthest offset the reading got to, and that is
the first character that no reading continues.

`Syn.explain` is that offset, and it is absent when the text is read in full. The offset is
the reader's own position, found in the one reading. No second pass looks for it.

What is proved:

- `Syn.run_answer`: the answer of a run is the reader's, so `run` is `read` with one more
  component.
- `Syn.run_reach_le` and `Syn.run_reach_le_rest`: a reading stands on no text longer than its
  own, and a reading that succeeds stood on the text it leaves.
- `Syn.explain_eq_none_iff`: the refusal is absent exactly when `Syn.check` holds.
- `Syn.explain_le`: the offset is a position of the text, its end included.
- `Syn.le_explain_of_read`: when the reader leaves text, the offset is no earlier than the
  place where the reader stopped.
- `Syn.run_local`: a run depends only on the text it stood on. A run whose reach is longer than
  the end `r` of its text is the same run when another text takes the place of `r`.
- `Syn.explain_local` (node V6b): the offset is a fact of the text up to it. A text that is
  refused at offset `n`, and has a character there, shares the refusal with every text that
  agrees with it on the first `n + 1` characters. `Syn.explain_append_of_lt` is the same law
  for a text in two parts.
- `Grammar.explain_print`: a printed value is not refused.

The cost is one reading. Each part also takes the length of its text, as `readMany` does.

What this module does not claim: that the offset is where an author's mistake is. It is only
where the reader could not go on. Nor does a refusal at the end of a text say anything of a
longer text. The locality law asks for a character at the offset, and
`WhatwgTest/Svg/Refusal.lean` holds a text that is refused at its end and a spelling that
extends it.
-/

namespace Whatwg.Svg.Value

/-! ## The reader with its reach -/

/-- `readMany` with its reach: the least reach of the steps it took, the step that stopped it
included. -/
def runMany {α : Type} (step : List Char → Nat × Option (α × List Char)) :
    Nat → List Char → Nat × (List α × List Char)
  | 0, s => (s.length, ([], s))
  | fuel + 1, s =>
    match step s with
    | (reach, none) => (reach, ([], s))
    | (reach, some (x, s₁)) =>
      if s₁.length < s.length then
        let more := runMany step fuel s₁
        (min reach more.1, (x :: more.2.1, more.2.2))
      else (reach, ([], s))

/-- The answer of `runMany` is that of `readMany`, when each step answers as the reader's. -/
theorem runMany_answer {α : Type} (step : List Char → Nat × Option (α × List Char))
    (read : List Char → Option (α × List Char)) (h : ∀ s, (step s).2 = read s)
    (fuel : Nat) (s : List Char) : (runMany step fuel s).2 = readMany read fuel s := by
  fun_induction runMany step fuel s with
  | case1 s => rfl
  | case2 fuel s reach hstep =>
    have hread : read s = none := (h s).symm.trans (congrArg Prod.snd hstep)
    simp only [readMany, hread]
  | case3 fuel s reach x s₁ hstep hlt more ih =>
    have hread : read s = some (x, s₁) := (h s).symm.trans (congrArg Prod.snd hstep)
    simp only [readMany, hread, if_pos hlt, ← ih]
    rfl
  | case4 fuel s reach x s₁ hstep hlt =>
    have hread : read s = some (x, s₁) := (h s).symm.trans (congrArg Prod.snd hstep)
    simp only [readMany, hread, if_neg hlt]

/-- A run of `runMany` stands on no text longer than its own, when no step does. -/
theorem runMany_reach_le {α : Type} (step : List Char → Nat × Option (α × List Char))
    (h : ∀ s, (step s).1 ≤ s.length) (fuel : Nat) (s : List Char) :
    (runMany step fuel s).1 ≤ s.length := by
  have hle := h s
  fun_induction runMany step fuel s with
  | case1 s => exact Nat.le_refl _
  | case2 fuel s reach hstep => rw [hstep] at hle; exact hle
  | case3 fuel s reach x s₁ hstep hlt more ih =>
    rw [hstep] at hle
    exact Nat.le_trans (Nat.min_le_left _ _) hle
  | case4 fuel s reach x s₁ hstep hlt => rw [hstep] at hle; exact hle

/-- A run of `runMany` stood on the text it leaves, when no step stands on a text longer than
its own. -/
theorem runMany_reach_le_rest {α : Type} (step : List Char → Nat × Option (α × List Char))
    (h : ∀ s, (step s).1 ≤ s.length) (fuel : Nat) (s : List Char) :
    (runMany step fuel s).1 ≤ (runMany step fuel s).2.2.length := by
  have hle := h s
  fun_induction runMany step fuel s with
  | case1 s => exact Nat.le_refl _
  | case2 fuel s reach hstep => rw [hstep] at hle; exact hle
  | case3 fuel s reach x s₁ hstep hlt more ih =>
    exact Nat.le_trans (Nat.min_le_right _ _) (ih (h s₁))
  | case4 fuel s reach x s₁ hstep hlt => rw [hstep] at hle; exact hle

namespace Syn

/-- The reader with its reach: the answer of `read`, and the length of the shortest text the
reading stood on. A part that refuses is counted where it refused, and a part that is given up
keeps its reach. -/
def run : {α : Type} → Syn α → List Char → Nat × Option (α × List Char)
  | _, .eps, s => (s.length, some ((), s))
  | _, .one _, [] => (0, none)
  | _, .one set, c :: t =>
    if set.mem c then (t.length, some (c, t)) else ((c :: t).length, none)
  | _, .seq a b, s =>
    match a.run s with
    | (reach, none) => (reach, none)
    | (reach, some (x, s₁)) =>
      match b.run s₁ with
      | (reach₂, none) => (min reach reach₂, none)
      | (reach₂, some (y, s₂)) => (min reach reach₂, some ((x, y), s₂))
  | _, .alt a b, s =>
    match a.run s with
    | (reach, some (x, s₁)) => (reach, some (.inl x, s₁))
    | (reach, none) =>
      match b.run s with
      | (reach₂, some (y, s₁)) => (min reach reach₂, some (.inr y, s₁))
      | (reach₂, none) => (min reach reach₂, none)
  | _, .many a, s =>
    match runMany a.run s.length s with
    | (reach, found) => (reach, some found)
  | _, .map to _ _ a, s =>
    match a.run s with
    | (reach, none) => (reach, none)
    | (reach, some (x, s₁)) => (reach, some (to x, s₁))
  | _, .skip a _, s =>
    match a.run s with
    | (reach, none) => (reach, none)
    | (reach, some (_, s₁)) => (reach, some ((), s₁))

/-- The answer of a run is the reader's. -/
theorem run_answer {α : Type} (g : Syn α) : ∀ s : List Char, (g.run s).2 = g.read s := by
  induction g with
  | eps => intro s; rfl
  | one set =>
    intro s
    cases s with
    | nil => rfl
    | cons c t =>
      cases hm : set.mem c with
      | false => simp only [run, read, hm, Bool.false_eq_true, if_false]
      | true => simp only [run, read, hm, if_true]
  | seq a b iha ihb =>
    intro s
    cases hra : a.run s with
    | mk reach out =>
      have ha : a.read s = out := (iha s).symm.trans (congrArg Prod.snd hra)
      cases out with
      | none => simp only [run, read, hra, ha]
      | some fa =>
        cases fa with
        | mk x s₁ =>
          cases hrb : b.run s₁ with
          | mk reach₂ out₂ =>
            have hb : b.read s₁ = out₂ := (ihb s₁).symm.trans (congrArg Prod.snd hrb)
            cases out₂ with
            | none => simp only [run, read, hra, ha, hrb, hb]
            | some fb =>
              cases fb with
              | mk y s₂ => simp only [run, read, hra, ha, hrb, hb]
  | alt a b iha ihb =>
    intro s
    cases hra : a.run s with
    | mk reach out =>
      have ha : a.read s = out := (iha s).symm.trans (congrArg Prod.snd hra)
      cases out with
      | some fa =>
        cases fa with
        | mk x s₁ => simp only [run, read, hra, ha]
      | none =>
        cases hrb : b.run s with
        | mk reach₂ out₂ =>
          have hb : b.read s = out₂ := (ihb s).symm.trans (congrArg Prod.snd hrb)
          cases out₂ with
          | none => simp only [run, read, hra, ha, hrb, hb]
          | some fb =>
            cases fb with
            | mk y s₂ => simp only [run, read, hra, ha, hrb, hb]
  | many a iha =>
    intro s
    simp only [run, read, runMany_answer a.run a.read iha s.length s]
  | map to back hlaw a iha =>
    intro s
    cases hra : a.run s with
    | mk reach out =>
      have ha : a.read s = out := (iha s).symm.trans (congrArg Prod.snd hra)
      cases out with
      | none => simp only [run, read, hra, ha]
      | some fa =>
        cases fa with
        | mk x s₁ => simp only [run, read, hra, ha]
  | skip a canonical iha =>
    intro s
    cases hra : a.run s with
    | mk reach out =>
      have ha : a.read s = out := (iha s).symm.trans (congrArg Prod.snd hra)
      cases out with
      | none => simp only [run, read, hra, ha]
      | some fa =>
        cases fa with
        | mk x s₁ => simp only [run, read, hra, ha]

/-- A reading stands on no text longer than its own. -/
theorem run_reach_le {α : Type} (g : Syn α) : ∀ s : List Char, (g.run s).1 ≤ s.length := by
  induction g with
  | eps => intro s; exact Nat.le_refl _
  | one set =>
    intro s
    cases s with
    | nil => exact Nat.le_refl _
    | cons c t =>
      simp only [run]
      split
      · exact Nat.le_succ _
      · exact Nat.le_refl _
  | seq a b iha ihb =>
    intro s
    have ha := iha s
    simp only [run]
    split <;> rename_i hra <;> rw [hra] at ha
    · exact ha
    · split
      · exact Nat.le_trans (Nat.min_le_left _ _) ha
      · exact Nat.le_trans (Nat.min_le_left _ _) ha
  | alt a b iha ihb =>
    intro s
    have ha := iha s
    simp only [run]
    split <;> rename_i hra <;> rw [hra] at ha
    · exact ha
    · split
      · exact Nat.le_trans (Nat.min_le_left _ _) ha
      · exact Nat.le_trans (Nat.min_le_left _ _) ha
  | many a iha =>
    intro s
    simp only [run]
    exact runMany_reach_le a.run iha s.length s
  | map to back hlaw a iha =>
    intro s
    have ha := iha s
    simp only [run]
    split <;> rename_i hra <;> rw [hra] at ha <;> exact ha
  | skip a canonical iha =>
    intro s
    have ha := iha s
    simp only [run]
    split <;> rename_i hra <;> rw [hra] at ha <;> exact ha

/-- A run that answers a value stood on the text it leaves. -/
theorem run_reach_le_of_some {α : Type} (g : Syn α) :
    ∀ (s : List Char) (reach : Nat) (v : α) (r : List Char),
      g.run s = (reach, some (v, r)) → reach ≤ r.length := by
  induction g with
  | eps =>
    intro s reach v r h
    simp only [run] at h
    cases h
    exact Nat.le_refl _
  | one set =>
    intro s reach v r h
    cases s with
    | nil => exact nomatch h
    | cons c t =>
      simp only [run] at h
      split at h
      · cases h; exact Nat.le_refl _
      · exact nomatch h
  | seq a b iha ihb =>
    intro s reach v r h
    simp only [run] at h
    split at h
    · exact nomatch h
    · split at h
      · exact nomatch h
      · next hrb =>
        cases h
        exact Nat.le_trans (Nat.min_le_right _ _) (ihb _ _ _ _ hrb)
  | alt a b iha ihb =>
    intro s reach v r h
    simp only [run] at h
    split at h
    · next hra => cases h; exact iha _ _ _ _ hra
    · split at h
      · next hrb => cases h; exact Nat.le_trans (Nat.min_le_right _ _) (ihb _ _ _ _ hrb)
      · exact nomatch h
  | many a iha =>
    intro s reach v r h
    have hmany := runMany_reach_le_rest a.run (run_reach_le a) s.length s
    simp only [run, Prod.mk.injEq, Option.some.injEq] at h
    rw [h.1, h.2] at hmany
    exact hmany
  | map to back hlaw a iha =>
    intro s reach v r h
    simp only [run] at h
    split at h
    · exact nomatch h
    · next hra => cases h; exact iha _ _ _ _ hra
  | skip a canonical iha =>
    intro s reach v r h
    simp only [run] at h
    split at h
    · exact nomatch h
    · next hra => cases h; exact iha _ _ _ _ hra

/-- A reading that succeeds stood on the text it leaves. -/
theorem run_reach_le_rest {α : Type} (g : Syn α) {s : List Char} {v : α} {r : List Char}
    (h : g.read s = some (v, r)) : (g.run s).1 ≤ r.length :=
  run_reach_le_of_some g s (g.run s).1 v r (Prod.ext rfl ((run_answer g s).trans h))

/-! ## The refusal -/

/-- Where a whole text is refused: the offset of the first character that no reading
continues. `none` when the text is a spelling the description reads in full. -/
def explain {α : Type} (g : Syn α) (s : List Char) : Option Nat :=
  match g.run s with
  | (_, some (_, [])) => none
  | (reach, _) => some (s.length - reach)

/-- The refusal is absent exactly when the check holds. -/
theorem explain_eq_none_iff {α : Type} (g : Syn α) (s : List Char) :
    g.explain s = none ↔ g.check s = true := by
  cases hr : g.run s with
  | mk reach out =>
    have hread : g.read s = out := (run_answer g s).symm.trans (congrArg Prod.snd hr)
    cases out with
    | none =>
      simp only [explain, check, readAll, hr, hread, Option.isSome_none]
      exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    | some found =>
      cases found with
      | mk v r =>
        cases r with
        | nil => simp only [explain, check, readAll, hr, hread, Option.isSome_some]
        | cons c t =>
          simp only [explain, check, readAll, hr, hread, Option.isSome_none]
          exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- A refusal's offset is the length of the text less the reach of its reading. -/
theorem explain_some {α : Type} (g : Syn α) {s : List Char} {n : Nat}
    (h : g.explain s = some n) : n = s.length - (g.run s).1 := by
  simp only [explain] at h
  split at h
  · exact nomatch h
  · next hr => cases h; rw [hr]

/-- The offset is a position of the text, its end included. -/
theorem explain_le {α : Type} (g : Syn α) {s : List Char} {n : Nat}
    (h : g.explain s = some n) : n ≤ s.length := by
  rw [explain_some g h]
  exact Nat.sub_le _ _

/-- When the reader leaves text, the offset is no earlier than the place where the reader
stopped. -/
theorem le_explain_of_read {α : Type} (g : Syn α) {s : List Char} {v : α} {r : List Char}
    {n : Nat} (hread : g.read s = some (v, r)) (h : g.explain s = some n) :
    s.length - r.length ≤ n := by
  rw [explain_some g h]
  exact Nat.sub_le_sub_left (run_reach_le_rest g hread) _

end Syn

/-! ## Locality -/

/-- A run of `runMany` depends only on the text it stood on, when each step does. The run on
`p ++ r` has a reach longer than `r`, so it never stood on `r`. The run on `p ++ r'` then finds
the same values and leaves the same part `q` of `p`. Each run has fuel for its whole text, and
the two amounts of fuel need not agree. -/
theorem runMany_local {α : Type} (step : List Char → Nat × Option (α × List Char))
    (hle : ∀ s, (step s).1 ≤ s.length) (r r' : List Char)
    (hloc : ∀ (p : List Char) (reach : Nat) (out : Option (α × List Char)),
      step (p ++ r) = (reach, out) → r.length < reach →
        (out = none ∧ step (p ++ r') = (reach - r.length + r'.length, none)) ∨
          ∃ v q, out = some (v, q ++ r) ∧
            step (p ++ r') = (reach - r.length + r'.length, some (v, q ++ r'))) :
    ∀ (fuel fuel' : Nat) (p : List Char) (reach : Nat) (xs : List α) (s₁ : List Char),
      (p ++ r).length ≤ fuel → (p ++ r').length ≤ fuel' →
      runMany step fuel (p ++ r) = (reach, (xs, s₁)) → r.length < reach →
        ∃ q, s₁ = q ++ r ∧
          runMany step fuel' (p ++ r') = (reach - r.length + r'.length, (xs, q ++ r'))
  | 0, _, p, reach, xs, s₁, hfuel, _, h, hlt => by
    simp only [runMany] at h
    cases h
    exact absurd (Nat.lt_of_lt_of_le hlt hfuel) (Nat.not_lt_zero _)
  | fuel + 1, 0, p, reach, xs, s₁, _, hfuel', h, hlt => by
    have hreach := runMany_reach_le step hle (fuel + 1) (p ++ r)
    rw [h, List.length_append] at hreach
    rw [List.length_append] at hfuel'
    exact absurd hlt (by omega)
  | fuel + 1, f' + 1, p, reach, xs, s₁, hfuel, hfuel', h, hlt => by
    rcases hstep : step (p ++ r) with ⟨reach₀, _ | ⟨x, s₂⟩⟩
    · simp only [runMany, hstep, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨_, hstep'⟩ | ⟨_, _, ⟨⟩, _⟩ := hloc p reach₀ none hstep hlt
      exact ⟨p, rfl, by simp only [runMany, hstep']⟩
    · cases hdec : decide (s₂.length < (p ++ r).length) with
      | false =>
        have hlen := of_decide_eq_false hdec
        simp only [runMany, hstep, if_neg hlen, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨⟨⟩, _⟩ | ⟨v, q, hout, hstep'⟩ := hloc p reach₀ _ hstep hlt
        cases hout
        rw [List.length_append, List.length_append] at hlen
        have hlen' : ¬ (q ++ r').length < (p ++ r').length := by
          rw [List.length_append, List.length_append]
          omega
        exact ⟨p, rfl, by simp only [runMany, hstep', if_neg hlen']⟩
      | true =>
        have hlen := of_decide_eq_true hdec
        rcases hmore : runMany step fuel s₂ with ⟨reach₁, ys, s₃⟩
        simp only [runMany, hstep, if_pos hlen, hmore, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [Nat.lt_min] at hlt
        obtain ⟨⟨⟩, _⟩ | ⟨v, q, hout, hstep'⟩ := hloc p reach₀ _ hstep hlt.1
        cases hout
        rw [List.length_append, List.length_append] at hlen
        rw [List.length_append] at hfuel hfuel'
        have hlen' : (q ++ r').length < (p ++ r').length := by
          rw [List.length_append, List.length_append]
          omega
        obtain ⟨q', rfl, hmore'⟩ := runMany_local step hle r r' hloc fuel f' q reach₁ ys s₃
          (by rw [List.length_append]; omega) (by rw [List.length_append]; omega) hmore hlt.2
        exact ⟨q', rfl, by
          simp only [runMany, hstep', if_pos hlen', hmore', Nat.add_min_add_right,
            Nat.sub_min_sub_right]⟩

namespace Syn

/-- The run lemma of node V6b: a run depends only on the text it stood on. If the reach of a
run on `p ++ r` is longer than `r`, the run never stood on `r`, and it examined no character of
`r`. So the run on `p ++ r'` is the same run. A refusal stays a refusal. An answer keeps its
value and leaves the same part `q` of `p`. The reach is longer than `r'` by as much as it was
longer than `r`.

The bound is strict. A run whose reach is the length of `r` stood on `r`: it may have refused
the first character of `r`, or found the end of the text there. -/
theorem run_local {α : Type} (g : Syn α) :
    ∀ (p r r' : List Char) (reach : Nat) (out : Option (α × List Char)),
      g.run (p ++ r) = (reach, out) → r.length < reach →
        (out = none ∧ g.run (p ++ r') = (reach - r.length + r'.length, none)) ∨
          ∃ v q, out = some (v, q ++ r) ∧
            g.run (p ++ r') = (reach - r.length + r'.length, some (v, q ++ r')) := by
  induction g with
  | eps =>
    intro p r r' reach out h hlt
    simp only [run] at h
    cases h
    exact Or.inr ⟨(), p, rfl, by simp only [run, List.length_append, Nat.add_sub_cancel]⟩
  | one set =>
    intro p r r' reach out h hlt
    cases p with
    | nil =>
      have hle := run_reach_le (.one set) ([] ++ r)
      rw [h] at hle
      exact absurd hlt (Nat.not_lt.mpr hle)
    | cons c p' =>
      cases hm : set.mem c with
      | true =>
        simp only [List.cons_append, run, hm, if_true] at h
        cases h
        exact Or.inr ⟨c, p', rfl, by
          simp only [List.cons_append, run, hm, if_true, List.length_append,
            Nat.add_sub_cancel]⟩
      | false =>
        simp only [List.cons_append, run, hm, Bool.false_eq_true, if_false] at h
        cases h
        refine Or.inl ⟨rfl, ?_⟩
        simp only [List.cons_append, run, hm, Bool.false_eq_true, if_false, List.length_cons,
          List.length_append, Prod.mk.injEq, and_true]
        omega
  | seq a b iha ihb =>
    intro p r r' reach out h hlt
    rcases hra : a.run (p ++ r) with ⟨reach₁, _ | ⟨x, s₁⟩⟩
    · simp only [run, hra, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, hra'⟩ | ⟨_, _, ⟨⟩, _⟩ := iha p r r' reach₁ none hra hlt
      exact Or.inl ⟨rfl, by simp only [run, hra']⟩
    · rcases hrb : b.run s₁ with ⟨reach₂, _ | ⟨y, s₂⟩⟩
      · simp only [run, hra, hrb, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Nat.lt_min] at hlt
        obtain ⟨⟨⟩, _⟩ | ⟨v, q, hout, hra'⟩ := iha p r r' reach₁ _ hra hlt.1
        cases hout
        obtain ⟨_, hrb'⟩ | ⟨_, _, ⟨⟩, _⟩ := ihb q r r' reach₂ none hrb hlt.2
        exact Or.inl ⟨rfl, by
          simp only [run, hra', hrb', Nat.add_min_add_right, Nat.sub_min_sub_right]⟩
      · simp only [run, hra, hrb, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Nat.lt_min] at hlt
        obtain ⟨⟨⟩, _⟩ | ⟨v, q, hout, hra'⟩ := iha p r r' reach₁ _ hra hlt.1
        cases hout
        obtain ⟨⟨⟩, _⟩ | ⟨w, q', hout, hrb'⟩ := ihb q r r' reach₂ _ hrb hlt.2
        cases hout
        exact Or.inr ⟨(x, y), q', rfl, by
          simp only [run, hra', hrb', Nat.add_min_add_right, Nat.sub_min_sub_right]⟩
  | alt a b iha ihb =>
    intro p r r' reach out h hlt
    rcases hra : a.run (p ++ r) with ⟨reach₁, _ | ⟨x, s₁⟩⟩
    · rcases hrb : b.run (p ++ r) with ⟨reach₂, _ | ⟨y, s₂⟩⟩
      · simp only [run, hra, hrb, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Nat.lt_min] at hlt
        obtain ⟨_, hra'⟩ | ⟨_, _, ⟨⟩, _⟩ := iha p r r' reach₁ none hra hlt.1
        obtain ⟨_, hrb'⟩ | ⟨_, _, ⟨⟩, _⟩ := ihb p r r' reach₂ none hrb hlt.2
        exact Or.inl ⟨rfl, by
          simp only [run, hra', hrb', Nat.add_min_add_right, Nat.sub_min_sub_right]⟩
      · simp only [run, hra, hrb, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Nat.lt_min] at hlt
        obtain ⟨_, hra'⟩ | ⟨_, _, ⟨⟩, _⟩ := iha p r r' reach₁ none hra hlt.1
        obtain ⟨⟨⟩, _⟩ | ⟨w, q, hout, hrb'⟩ := ihb p r r' reach₂ _ hrb hlt.2
        cases hout
        exact Or.inr ⟨.inr y, q, rfl, by
          simp only [run, hra', hrb', Nat.add_min_add_right, Nat.sub_min_sub_right]⟩
    · simp only [run, hra, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨⟨⟩, _⟩ | ⟨v, q, hout, hra'⟩ := iha p r r' reach₁ _ hra hlt
      cases hout
      exact Or.inr ⟨.inl x, q, rfl, by simp only [run, hra']⟩
  | many a iha =>
    intro p r r' reach out h hlt
    rcases hm : runMany a.run (p ++ r).length (p ++ r) with ⟨reach₀, xs, s₁⟩
    simp only [run, hm, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨q, rfl, hm'⟩ := runMany_local a.run (run_reach_le a) r r'
      (fun p => iha p r r') _ _ p reach₀ xs s₁ (Nat.le_refl _) (Nat.le_refl _) hm hlt
    exact Or.inr ⟨xs, q, rfl, by simp only [run, hm']⟩
  | map to back hlaw a iha =>
    intro p r r' reach out h hlt
    rcases hra : a.run (p ++ r) with ⟨reach₁, _ | ⟨x, s₁⟩⟩
    · simp only [run, hra, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, hra'⟩ | ⟨_, _, ⟨⟩, _⟩ := iha p r r' reach₁ none hra hlt
      exact Or.inl ⟨rfl, by simp only [run, hra']⟩
    · simp only [run, hra, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨⟨⟩, _⟩ | ⟨v, q, hout, hra'⟩ := iha p r r' reach₁ _ hra hlt
      cases hout
      exact Or.inr ⟨to x, q, rfl, by simp only [run, hra']⟩
  | skip a canonical iha =>
    intro p r r' reach out h hlt
    rcases hra : a.run (p ++ r) with ⟨reach₁, _ | ⟨x, s₁⟩⟩
    · simp only [run, hra, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, hra'⟩ | ⟨_, _, ⟨⟩, _⟩ := iha p r r' reach₁ none hra hlt
      exact Or.inl ⟨rfl, by simp only [run, hra']⟩
    · simp only [run, hra, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨⟨⟩, _⟩ | ⟨v, q, hout, hra'⟩ := iha p r r' reach₁ _ hra hlt
      cases hout
      exact Or.inr ⟨(), q, rfl, by simp only [run, hra']⟩

/-- Locality for a text in two parts: an offset inside `p` is a fact of `p`. If `p ++ r` is
refused at the offset of a character of `p`, then `p` followed by any text is refused at that
offset. -/
theorem explain_append_of_lt {α : Type} (g : Syn α) {p r : List Char} {n : Nat}
    (h : g.explain (p ++ r) = some n) (hn : n < p.length) (r' : List Char) :
    g.explain (p ++ r') = some n := by
  have hoff := explain_some g h
  have hle := run_reach_le g (p ++ r)
  rcases hr : g.run (p ++ r) with ⟨reach, out⟩
  rw [hr, List.length_append] at hoff hle
  have hlt : r.length < reach := by omega
  obtain ⟨rfl, hr'⟩ | ⟨v, q, rfl, hr'⟩ := run_local g p r r' reach out hr hlt
  · simp only [explain, hr', List.length_append, Option.some.injEq]
    omega
  · have hrest := run_reach_le_of_some g (p ++ r) reach v (q ++ r) hr
    cases q with
    | nil => exact absurd hlt (Nat.not_lt.mpr hrest)
    | cons c t =>
      simp only [explain, hr', List.cons_append, List.length_append, Option.some.injEq]
      omega

/-- Node V6b, locality: the offset of a refusal is a fact of the text up to it. If `s` is
refused at offset `n` and has a character there, then every text that agrees with `s` on its
first `n + 1` characters is refused at offset `n`.

The premise `hn` stands. A text that is refused at its end stopped too early, and a longer text
may be a spelling. -/
theorem explain_local {α : Type} (g : Syn α) {s s' : List Char} {n : Nat}
    (h : g.explain s = some n) (hn : n < s.length)
    (hs : s'.take (n + 1) = s.take (n + 1)) : g.explain s' = some n := by
  have hsplit' := List.take_append_drop (n + 1) s'
  rw [hs] at hsplit'
  rw [← List.take_append_drop (n + 1) s] at h
  rw [← hsplit']
  have hlt : n < (s.take (n + 1)).length := by
    rw [List.length_take, Nat.min_eq_left hn]
    exact n.lt_succ_self
  exact explain_append_of_lt g h hlt _

end Syn

/-! ## A grammar -/

namespace Grammar

variable {α : Type}

/-- Where a whole text is refused by the grammar: the offset of the first character that no
reading continues. `none` when the text is a spelling of some value. -/
def explain (g : Grammar α) (s : List Char) : Option Nat := g.syn.explain s

/-- The refusal is absent exactly when the check holds. -/
theorem explain_eq_none_iff (g : Grammar α) (s : List Char) :
    g.explain s = none ↔ g.check s = true := Syn.explain_eq_none_iff g.syn s

/-- The offset is a position of the text, its end included. -/
theorem explain_le (g : Grammar α) {s : List Char} {n : Nat} (h : g.explain s = some n) :
    n ≤ s.length := Syn.explain_le g.syn h

/-- Node V6b at a grammar, locality: a text that is refused at offset `n`, and has a character
there, shares the refusal with every text that agrees with it on the first `n + 1`
characters. -/
theorem explain_local (g : Grammar α) {s s' : List Char} {n : Nat} (h : g.explain s = some n)
    (hn : n < s.length) (hs : s'.take (n + 1) = s.take (n + 1)) : g.explain s' = some n :=
  Syn.explain_local g.syn h hn hs

/-- A printed value is not refused. -/
theorem explain_print (g : Grammar α) (v : α) : g.explain (g.print v) = none :=
  (g.explain_eq_none_iff _).mpr (g.check_print v)

end Grammar

end Whatwg.Svg.Value
