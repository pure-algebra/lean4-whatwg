import Whatwg.Svg.Value.Grammar

/-!
# Whatwg.Svg.Value.Grammar.Laws

Owner: the laws of a description, each proved once for every value of `Syn`
(`docs/SVG-PACKAGE-PLAN.md`, nodes V1, V2 and V3a; ruling SV-25; slice S4a). The definitions
are `Whatwg/Svg/Value/Grammar.lean`. The two were one module until slice S8, and the layout is
that of `Whatwg/Streams/Readable/Laws.lean`: the laws beside what they are about, in the same
namespace.

- `Syn.read_print` is the retraction (node V1): if `g.ok` and `g.valid v` hold, then `g.read`
  on the printed value, followed by a text that cannot continue it, answers the value and that
  text. A grammar discharges `g.ok` by one evaluation.
- `Syn.check_print` (node V2): a printed value passes the check.
- `Syn.read_sound` is the soundness of the reader (node V3a): what a successful read consumes
  is a text of the language of the description's expression. `Syn.print_matches` says that a
  printed value is one too.
- `Grammar.read_print`, `check_print`, `print_injective`, `matches_of_check` and
  `print_matches` are those laws at a grammar, with its two premises discharged.

What this module does not claim: that `read` accepts every text of the language. `ok` reads
what the printer writes, and a reader that commits to the longest match refuses a text that a
backtracking reader accepts: `WhatwgTest/Svg/Grammar.lean` holds one. Three modules build on
this one. `Whatwg/Svg/Value/Greedy.lean` states the reader's rule as a relation and proves
the reader against it (node V3b). `Whatwg/Svg/Value/Deterministic.lean` states the premise
under which that rule's language is the expression's (node V3c).
`Whatwg/Svg/Value/Refusal.lean` gives a refused text the offset at which no reading continues
(node V6).
-/

namespace Whatwg.Svg.Value

namespace Syn
/-! ## What a printed value opens with -/

/-- A printed value that is empty, or that opens with a character, is as the two computed
facts say. -/
theorem print_head {α : Type} (g : Syn α) : ∀ v : α, g.valid v = true →
    (g.print v = [] → g.printsEmpty = true) ∧
      (∀ c t, g.print v = c :: t → g.printFirst.mem c = true) := by
  induction g with
  | eps => intro _ _; exact ⟨fun _ => rfl, fun _ _ h => nomatch h⟩
  | one set =>
    intro c hv
    refine ⟨(fun h => nomatch h), fun c' t h => ?_⟩
    simp only [print, List.cons.injEq] at h
    rw [← h.1]
    exact hv
  | seq a b iha ihb =>
    intro v hv
    simp only [valid, Bool.and_eq_true] at hv
    obtain ⟨hae, haf⟩ := iha v.1 hv.1
    obtain ⟨hbe, hbf⟩ := ihb v.2 hv.2
    simp only [print, printsEmpty, printFirst]
    cases hpa : a.print v.1 with
    | nil =>
      have hea := hae hpa
      refine ⟨fun h => ?_, fun c t h => ?_⟩
      · rw [List.nil_append] at h
        rw [hea, hbe h]
        rfl
      · rw [List.nil_append] at h
        rw [hea, if_pos rfl, CharSet.mem_union, hbf c t h, Bool.or_true]
    | cons c' t' =>
      refine ⟨(fun h => nomatch h), fun c t h => ?_⟩
      rw [List.cons_append, List.cons.injEq] at h
      have hmem := haf c' t' hpa
      rw [h.1] at hmem
      cases a.printsEmpty with
      | false => exact hmem
      | true => rw [if_pos rfl, CharSet.mem_union, hmem, Bool.true_or]
  | alt a b iha ihb =>
    intro v hv
    cases v with
    | inl x =>
      obtain ⟨hae, haf⟩ := iha x hv
      refine ⟨fun h => ?_, fun c t h => ?_⟩
      · simp only [printsEmpty, hae h, Bool.true_or]
      · simp only [printFirst, CharSet.mem_union, haf c t h, Bool.true_or]
    | inr y =>
      obtain ⟨hbe, hbf⟩ := ihb y hv
      refine ⟨fun h => ?_, fun c t h => ?_⟩
      · simp only [printsEmpty, hbe h, Bool.or_true]
      · simp only [printFirst, CharSet.mem_union, hbf c t h, Bool.or_true]
  | many a iha =>
    intro xs hv
    refine ⟨fun _ => rfl, ?_⟩
    induction xs with
    | nil => intro c t h; exact nomatch h
    | cons x rest ihxs =>
      intro c t h
      simp only [valid, List.all_cons, Bool.and_eq_true] at hv
      simp only [print, List.flatMap_cons] at h
      cases hpx : a.print x with
      | nil =>
        rw [hpx, List.nil_append] at h
        exact ihxs hv.2 c t h
      | cons c' t' =>
        rw [hpx, List.cons_append, List.cons.injEq] at h
        have hmem := (iha x hv.1).2 c' t' hpx
        rw [h.1] at hmem
        exact hmem
  | map to back h a iha => intro v hv; exact iha (back v) hv
  | skip a canonical iha =>
    intro _ hv
    obtain ⟨_, haf⟩ := iha canonical hv
    simp only [print, printsEmpty, printFirst]
    cases hp : a.print canonical with
    | nil => exact ⟨fun _ => rfl, fun _ _ h => nomatch h⟩
    | cons c' t' =>
      refine ⟨(fun h => nomatch h), fun c t h => ?_⟩
      rw [List.cons.injEq] at h
      rw [← h.1]
      exact CharSet.mem_single_self (CharSet.lt_of_mem (haf c' t' hp))

/-! ## What a successful read opens with -/

/-- A run of `readMany` leaves the text as it was, or its first step consumed something. -/
theorem readMany_progress {α : Type} (step : List Char → Option (α × List Char)) :
    ∀ (fuel : Nat) (s : List Char), (readMany step fuel s).2 = s ∨
      ∃ x s₁, step s = some (x, s₁) ∧ s₁.length < s.length
  | 0, _ => Or.inl rfl
  | fuel + 1, s => by
    cases hstep : step s with
    | none => left; simp only [readMany, hstep]
    | some found =>
      cases hlt : decide (found.2.length < s.length) with
      | true => exact Or.inr ⟨found.1, found.2, rfl, of_decide_eq_true hlt⟩
      | false =>
        left
        simp only [readMany, hstep, if_neg (of_decide_eq_false hlt)]

/-- A successful read consumed nothing, or the text opens with a character of `readFirst`. -/
theorem read_head {α : Type} (g : Syn α) : ∀ (s : List Char) (v : α) (r : List Char),
    g.read s = some (v, r) →
      (r = s ∧ g.readsEmpty = true) ∨ ∃ c t, s = c :: t ∧ g.readFirst.mem c = true := by
  induction g with
  | eps =>
    intro s v r h
    simp only [read, Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨h.2.symm, rfl⟩
  | one set =>
    intro s v r h
    cases s with
    | nil => exact nomatch h
    | cons c t =>
      simp only [read] at h
      cases hm : set.mem c with
      | false => rw [hm] at h; exact nomatch h
      | true => exact Or.inr ⟨c, t, rfl, hm⟩
  | seq a b iha ihb =>
    intro s v r h
    simp only [read] at h
    cases ha : a.read s with
    | none => rw [ha] at h; exact nomatch h
    | some fa =>
      rw [ha] at h
      cases hb : b.read fa.2 with
      | none => simp only [hb] at h; exact nomatch h
      | some fb =>
        simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
        simp only [readsEmpty, readFirst]
        rcases iha s fa.1 fa.2 ha with ⟨hs, hae⟩ | ⟨c, t, hc, hm⟩
        · rw [hs] at hb
          rcases ihb s fb.1 fb.2 hb with ⟨hs', hbe⟩ | ⟨c, t, hc, hm⟩
          · exact Or.inl ⟨by rw [← h.2, hs'], by rw [hae, hbe]; rfl⟩
          · exact Or.inr ⟨c, t, hc, by rw [hae, if_pos rfl, CharSet.mem_union, hm, Bool.or_true]⟩
        · refine Or.inr ⟨c, t, hc, ?_⟩
          cases a.readsEmpty with
          | false => exact hm
          | true => rw [if_pos rfl, CharSet.mem_union, hm, Bool.true_or]
  | alt a b iha ihb =>
    intro s v r h
    simp only [read] at h
    simp only [readsEmpty, readFirst]
    cases ha : a.read s with
    | some fa =>
      simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
      rcases iha s fa.1 fa.2 ha with ⟨hs, hae⟩ | ⟨c, t, hc, hm⟩
      · exact Or.inl ⟨by rw [← h.2, hs], by rw [hae, Bool.true_or]⟩
      · exact Or.inr ⟨c, t, hc, by rw [CharSet.mem_union, hm, Bool.true_or]⟩
    | none =>
      rw [ha] at h
      cases hb : b.read s with
      | none => simp only [hb] at h; exact nomatch h
      | some fb =>
        simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
        rcases ihb s fb.1 fb.2 hb with ⟨hs, hbe⟩ | ⟨c, t, hc, hm⟩
        · exact Or.inl ⟨by rw [← h.2, hs], by rw [hbe, Bool.or_true]⟩
        · exact Or.inr ⟨c, t, hc, by rw [CharSet.mem_union, hm, Bool.or_true]⟩
  | many a iha =>
    intro s v r h
    simp only [read, Option.some.injEq] at h
    rcases readMany_progress a.read s.length s with hsame | ⟨x, s₁, hstep, hlt⟩
    · rw [h] at hsame
      exact Or.inl ⟨hsame, rfl⟩
    · rcases iha s x s₁ hstep with ⟨hs, _⟩ | found
      · rw [hs] at hlt
        exact absurd hlt (Nat.lt_irrefl _)
      · exact Or.inr found
  | map to back hlaw a iha =>
    intro s v r h
    simp only [read] at h
    cases ha : a.read s with
    | none => rw [ha] at h; exact nomatch h
    | some fa =>
      simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
      rcases iha s fa.1 fa.2 ha with ⟨hs, hae⟩ | found
      · exact Or.inl ⟨by rw [← h.2, hs], hae⟩
      · exact Or.inr found
  | skip a canonical iha =>
    intro s v r h
    simp only [read] at h
    cases ha : a.read s with
    | none => rw [ha] at h; exact nomatch h
    | some fa =>
      simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
      rcases iha s fa.1 fa.2 ha with ⟨hs, hae⟩ | found
      · exact Or.inl ⟨by rw [← h.2, hs], hae⟩
      · exact Or.inr found

/-- A reader that cannot succeed on nothing fails on a text that opens with no character of
`readFirst`. -/
theorem read_eq_none {α : Type} (g : Syn α) (hne : g.readsEmpty = false) {s : List Char}
    (hs : Stops g.readFirst s) : g.read s = none := by
  cases h : g.read s with
  | none => rfl
  | some found =>
    rcases read_head g s found.1 found.2 h with ⟨_, he⟩ | ⟨c, t, hc, hm⟩
    · rw [hne] at he; exact Bool.noConfusion he
    · rw [hs c t hc] at hm; exact Bool.noConfusion hm
/-! ## The retraction -/

/-- A part that never prints the empty text prints at least one character per value. -/
theorem length_le_flatMap_print {α : Type} (a : Syn α) (hpe : a.printsEmpty = false) :
    ∀ xs : List α, xs.all a.valid = true → xs.length ≤ (xs.flatMap a.print).length
  | [], _ => Nat.le_refl 0
  | x :: rest, hv => by
    simp only [List.all_cons, Bool.and_eq_true] at hv
    have ih := length_le_flatMap_print a hpe rest hv.2
    have hpos : 0 < (a.print x).length := by
      cases hp : a.print x with
      | nil =>
        have he := (print_head a x hv.1).1 hp
        rw [hpe] at he
        exact Bool.noConfusion he
      | cons c t => exact Nat.succ_pos _
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    exact Nat.le_trans (Nat.succ_le_succ ih) (by
      rw [Nat.add_comm]
      exact Nat.add_le_add_left hpos _)

/-- The repetition reads back a printed list, when its part reads back each value. -/
theorem readMany_print {α : Type} (a : Syn α)
    (hread : ∀ (v : α) (rest : List Char), a.valid v = true → Stops a.continues rest →
      a.read (a.print v ++ rest) = some (v, rest))
    (hre : a.readsEmpty = false) (hpe : a.printsEmpty = false)
    (hdis : a.continues.disjoint a.printFirst = true) :
    ∀ (xs : List α) (fuel : Nat) (rest : List Char), xs.all a.valid = true →
      xs.length ≤ fuel → Stops (a.continues.union a.readFirst) rest →
      readMany a.read fuel (xs.flatMap a.print ++ rest) = (xs, rest)
  | [], fuel, rest, _, _, hstops => by
    rw [List.flatMap_nil, List.nil_append]
    cases fuel with
    | zero => rfl
    | succ f => simp only [readMany, read_eq_none a hre hstops.of_union_right]
  | x :: xs, fuel, rest, hv, hfuel, hstops => by
    cases fuel with
    | zero => exact absurd hfuel (Nat.not_succ_le_zero _)
    | succ f =>
      have hvs := hv
      simp only [List.all_cons, Bool.and_eq_true] at hvs
      have htail : Stops a.continues (xs.flatMap a.print ++ rest) := by
        intro c t hc
        cases hfm : xs.flatMap a.print with
        | nil =>
          rw [hfm, List.nil_append] at hc
          exact hstops.of_union_left c t hc
        | cons c' t' =>
          rw [hfm, List.cons_append, List.cons.injEq] at hc
          have hmem := (print_head (.many a) xs hvs.2).2 c' t' hfm
          rw [hc.1] at hmem
          exact CharSet.not_mem_left_of_disjoint hdis hmem
      have hx := hread x (xs.flatMap a.print ++ rest) hvs.1 htail
      have hpos : 0 < (a.print x).length := by
        cases hp : a.print x with
        | nil =>
          have he := (print_head a x hvs.1).1 hp
          rw [hpe] at he
          exact Bool.noConfusion he
        | cons c t => exact Nat.succ_pos _
      have hlt : (xs.flatMap a.print ++ rest).length
          < (a.print x ++ (xs.flatMap a.print ++ rest)).length := by
        rw [List.length_append (as := a.print x)]
        exact Nat.lt_add_of_pos_left hpos
      have ih := readMany_print a hread hre hpe hdis xs f rest hvs.2 (Nat.le_of_succ_le_succ hfuel)
        hstops
      rw [List.flatMap_cons, List.append_assoc]
      simp only [readMany, hx, if_pos hlt, ih]

/-- Node V1, the retraction: the reader answers a printed value and the text after it, when
one character decides each choice (`ok`), the value is printable (`valid`), and the text after
it cannot continue the print. -/
theorem read_print {α : Type} (g : Syn α) : g.ok = true → ∀ (v : α) (rest : List Char),
    g.valid v = true → Stops g.continues rest → g.read (g.print v ++ rest) = some (v, rest) := by
  induction g with
  | eps => intro _ _ rest _ _; rfl
  | one set =>
    intro _ c rest hv _
    simp only [print, List.cons_append, List.nil_append, read]
    simp only [valid] at hv
    rw [if_pos hv]
  | seq a b iha ihb =>
    intro hok v rest hv hstops
    simp only [ok, Bool.and_eq_true] at hok
    simp only [valid, Bool.and_eq_true] at hv
    obtain ⟨⟨hoka, hokb⟩, hdis⟩ := hok
    have hb : Stops b.continues rest := by
      simp only [continues] at hstops
      cases hbe : b.printsEmpty with
      | false => rw [hbe] at hstops; exact hstops
      | true => rw [hbe, if_pos rfl] at hstops; exact hstops.of_union_left
    have ha : Stops a.continues (b.print v.2 ++ rest) := by
      intro c t hc
      cases hpb : b.print v.2 with
      | nil =>
        rw [hpb, List.nil_append] at hc
        have hbe := (print_head b v.2 hv.2).1 hpb
        simp only [continues, hbe, if_pos] at hstops
        exact hstops.of_union_right c t hc
      | cons c' t' =>
        rw [hpb, List.cons_append, List.cons.injEq] at hc
        have hmem := (print_head b v.2 hv.2).2 c' t' hpb
        rw [hc.1] at hmem
        exact CharSet.not_mem_left_of_disjoint hdis hmem
    simp only [print, read, List.append_assoc, iha hoka v.1 _ hv.1 ha, ihb hokb v.2 rest hv.2 hb]
  | alt a b iha ihb =>
    intro hok v rest hv hstops
    simp only [ok, Bool.and_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨hoka, hokb⟩, hre⟩, hdis⟩ := hok
    have hunion : Stops (a.continues.union b.continues) rest := by
      simp only [continues] at hstops
      cases hbe : b.printsEmpty with
      | false => rw [hbe] at hstops; exact hstops
      | true => rw [hbe, if_pos rfl] at hstops; exact hstops.of_union_left
    cases v with
    | inl x =>
      simp only [print, read, iha hoka x rest hv hunion.of_union_left]
    | inr y =>
      have hnone : a.read (b.print y ++ rest) = none := by
        refine read_eq_none a hre ?_
        intro c t hc
        cases hpb : b.print y with
        | nil =>
          rw [hpb, List.nil_append] at hc
          have hbe := (print_head b y hv).1 hpb
          simp only [continues, hbe, if_pos] at hstops
          exact hstops.of_union_right c t hc
        | cons c' t' =>
          rw [hpb, List.cons_append, List.cons.injEq] at hc
          have hmem := (print_head b y hv).2 c' t' hpb
          rw [hc.1] at hmem
          exact CharSet.not_mem_left_of_disjoint hdis hmem
      simp only [print, read, hnone, ihb hokb y rest hv hunion.of_union_right]
  | many a iha =>
    intro hok xs rest hv hstops
    simp only [ok, Bool.and_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨hoka, hre⟩, hpe⟩, hdis⟩ := hok
    simp only [valid] at hv
    have hfuel : xs.length ≤ (xs.flatMap a.print ++ rest).length := by
      rw [List.length_append]
      exact Nat.le_trans (length_le_flatMap_print a hpe xs hv) (Nat.le_add_right _ _)
    simp only [print, read]
    rw [readMany_print a (iha hoka) hre hpe hdis xs _ rest hv hfuel hstops]
  | map to back hlaw a iha =>
    intro hok v rest hv hstops
    simp only [print, read, iha hok (back v) rest hv hstops, hlaw]
  | skip a canonical iha =>
    intro hok _ rest _ hstops
    simp only [ok, Bool.and_eq_true] at hok
    simp only [print, read, iha hok.1 canonical rest hok.2 hstops]

/-- The retraction at the end of the text. -/
theorem read_print_nil {α : Type} (g : Syn α) (hok : g.ok = true) (v : α)
    (hv : g.valid v = true) : g.read (g.print v) = some (v, []) := by
  have h := read_print g hok v [] hv (Stops.nil _)
  rw [List.append_nil] at h
  exact h

/-! ## A whole text -/

/-- The retraction for a whole text: a printed value reads back as the value. -/
theorem readAll_print {α : Type} (g : Syn α) (hok : g.ok = true) (v : α)
    (hv : g.valid v = true) : g.readAll (g.print v) = some v := by
  simp only [readAll, read_print_nil g hok v hv]

/-- Node V2: a printed value passes the check. -/
theorem check_print {α : Type} (g : Syn α) (hok : g.ok = true) (v : α)
    (hv : g.valid v = true) : g.check (g.print v) = true := by
  simp only [check, readAll_print g hok v hv, Option.isSome_some]

/-! ## The reader is sound against the expression -/

/-- What `readMany` consumes is a text of the star of its part's language. -/
theorem readMany_sound {α : Type} (a : Syn α)
    (hread : ∀ (s : List Char) (v : α) (r : List Char), a.read s = some (v, r) →
      ∃ pre, s = pre ++ r ∧ a.erase.Matches pre) :
    ∀ (fuel : Nat) (s : List Char),
      ∃ pre, s = pre ++ (readMany a.read fuel s).2 ∧ (Regex.star a.erase).Matches pre
  | 0, s => ⟨[], rfl, .starNil⟩
  | fuel + 1, s => by
    cases hstep : a.read s with
    | none => exact ⟨[], by simp only [readMany, hstep, List.nil_append], .starNil⟩
    | some found =>
      cases hlt : decide (found.2.length < s.length) with
      | false =>
        exact ⟨[], by simp only [readMany, hstep, if_neg (of_decide_eq_false hlt), List.nil_append],
          .starNil⟩
      | true =>
        obtain ⟨pre₁, hs₁, hm₁⟩ := hread s found.1 found.2 hstep
        obtain ⟨pre₂, hs₂, hm₂⟩ := readMany_sound a hread fuel found.2
        refine ⟨pre₁ ++ pre₂, ?_, .starCons hm₁ hm₂⟩
        simp only [readMany, hstep, if_pos (of_decide_eq_true hlt)]
        rw [List.append_assoc, ← hs₂]
        exact hs₁

/-- Node V3a, the soundness of the reader: what a successful read consumes is a text of the
language of the description's expression. -/
theorem read_sound {α : Type} (g : Syn α) : ∀ (s : List Char) (v : α) (r : List Char),
    g.read s = some (v, r) → ∃ pre, s = pre ++ r ∧ g.erase.Matches pre := by
  induction g with
  | eps =>
    intro s v r h
    simp only [read, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by rw [List.nil_append, h.2], .eps⟩
  | one set =>
    intro s v r h
    cases s with
    | nil => exact nomatch h
    | cons c t =>
      simp only [read] at h
      cases hm : set.mem c with
      | false => rw [hm] at h; exact nomatch h
      | true =>
        simp only [hm, if_pos, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨[c], by rw [← h.2]; rfl, .set hm⟩
  | seq a b iha ihb =>
    intro s v r h
    simp only [read] at h
    cases ha : a.read s with
    | none => rw [ha] at h; exact nomatch h
    | some fa =>
      rw [ha] at h
      cases hb : b.read fa.2 with
      | none => simp only [hb] at h; exact nomatch h
      | some fb =>
        simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨pre₁, hs₁, hm₁⟩ := iha s fa.1 fa.2 ha
        obtain ⟨pre₂, hs₂, hm₂⟩ := ihb fa.2 fb.1 fb.2 hb
        refine ⟨pre₁ ++ pre₂, ?_, .seq hm₁ hm₂⟩
        rw [List.append_assoc, ← h.2, ← hs₂]
        exact hs₁
  | alt a b iha ihb =>
    intro s v r h
    simp only [read] at h
    cases ha : a.read s with
    | some fa =>
      simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨pre, hs, hm⟩ := iha s fa.1 fa.2 ha
      exact ⟨pre, by rw [← h.2]; exact hs, .altL hm⟩
    | none =>
      rw [ha] at h
      cases hb : b.read s with
      | none => simp only [hb] at h; exact nomatch h
      | some fb =>
        simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨pre, hs, hm⟩ := ihb s fb.1 fb.2 hb
        exact ⟨pre, by rw [← h.2]; exact hs, .altR hm⟩
  | many a iha =>
    intro s v r h
    simp only [read, Option.some.injEq] at h
    obtain ⟨pre, hs, hm⟩ := readMany_sound a iha s.length s
    rw [h] at hs
    exact ⟨pre, hs, hm⟩
  | map to back hlaw a iha =>
    intro s v r h
    simp only [read] at h
    cases ha : a.read s with
    | none => rw [ha] at h; exact nomatch h
    | some fa =>
      simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨pre, hs, hm⟩ := iha s fa.1 fa.2 ha
      exact ⟨pre, by rw [← h.2]; exact hs, hm⟩
  | skip a canonical iha =>
    intro s v r h
    simp only [read] at h
    cases ha : a.read s with
    | none => rw [ha] at h; exact nomatch h
    | some fa =>
      simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨pre, hs, hm⟩ := iha s fa.1 fa.2 ha
      exact ⟨pre, by rw [← h.2]; exact hs, hm⟩

/-- A text that passes the check is a text of the language of the description's expression. -/
theorem matches_of_check {α : Type} (g : Syn α) {s : List Char} (h : g.check s = true) :
    g.erase.Matches s := by
  simp only [check, readAll] at h
  cases hr : g.read s with
  | none => rw [hr] at h; exact Bool.noConfusion h
  | some found =>
    obtain ⟨pre, hs, hm⟩ := read_sound g s found.1 found.2 hr
    cases hrest : found.2 with
    | nil =>
      rw [hrest, List.append_nil] at hs
      rw [hs]
      exact hm
    | cons c t =>
      have hfound : found = (found.1, c :: t) := by rw [← hrest]
      rw [hr, hfound] at h
      exact Bool.noConfusion h

/-- A printed value is a text of the language of the description's expression. -/
theorem print_matches {α : Type} (g : Syn α) : ∀ v : α, g.valid v = true →
    g.erase.Matches (g.print v) := by
  induction g with
  | eps => intro _ _; exact .eps
  | one set => intro c hv; exact .set hv
  | seq a b iha ihb =>
    intro v hv
    simp only [valid, Bool.and_eq_true] at hv
    exact .seq (iha v.1 hv.1) (ihb v.2 hv.2)
  | alt a b iha ihb =>
    intro v hv
    cases v with
    | inl x => exact .altL (iha x hv)
    | inr y => exact .altR (ihb y hv)
  | many a iha =>
    intro xs hv
    induction xs with
    | nil => exact .starNil
    | cons x rest ihxs =>
      simp only [valid, List.all_cons, Bool.and_eq_true] at hv
      simp only [print, List.flatMap_cons]
      exact .starCons (iha x hv.1) (ihxs hv.2)
  | map to back hlaw a iha => intro v hv; exact iha (back v) hv
  | skip a canonical iha => intro _ hv; exact iha canonical hv

end Syn

/-! ## The laws at a grammar -/

namespace Grammar

variable {α : Type}

/-- Node V1 at a grammar, the retraction: a printed value reads back as the value. -/
theorem read_print (g : Grammar α) (v : α) : g.read (g.print v) = some v :=
  Syn.readAll_print g.syn g.ok v (g.total v)

/-- Node V2 at a grammar: a printed value passes the check. -/
theorem check_print (g : Grammar α) (v : α) : g.check (g.print v) = true :=
  Syn.check_print g.syn g.ok v (g.total v)

/-- The printer is an embedding: two values with one spelling are one value. -/
theorem print_injective (g : Grammar α) {v w : α} (h : g.print v = g.print w) : v = w := by
  have hv := g.read_print v
  rw [h, g.read_print w] at hv
  exact (Option.some.inj hv).symm

/-- Node V3a at a grammar: a text that passes the check is a text of the language of the
description's expression. -/
theorem matches_of_check (g : Grammar α) {s : List Char} (h : g.check s = true) :
    g.syn.erase.Matches s := Syn.matches_of_check g.syn h

/-- A printed value is a text of that language. -/
theorem print_matches (g : Grammar α) (v : α) : g.syn.erase.Matches (g.print v) :=
  Syn.print_matches g.syn v (g.total v)

end Grammar

end Whatwg.Svg.Value
