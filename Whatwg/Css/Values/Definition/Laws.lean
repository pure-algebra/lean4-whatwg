import Whatwg.Css.Values.Definition.Lex

/-!
# Whatwg.Css.Values.Definition.Laws

Owner: the round trip of the Value Definition Syntax (slice K3 of
`docs/CSS-PACKAGE-PLAN.md`; ruling CS-4).

- `Definition.read_print`: reading what the printer wrote for a tree with `wf` gives the tree
  back. A generated data module holds trees the reader gave, and this law says that the text
  a person reads in a report is a text of that same tree.
- `Definition.print_injective`: two trees with `wf` that print alike are one tree.
- `parse_lexemes`: the second half, from lexemes to the tree. The first half is `lex_render`
  of `Whatwg/Css/Values/Definition/Lex.lean`.
- `Definition.induct`: induction over a tree, with the parts of a combination as a list.

How the second half goes. `Definition.items` is one level of a tree as the reader sees it:
terms, marks and multipliers. `Builds` says that the reader, given the lexemes of a tree,
holds the items of that tree. `assemble_items` says that one level of items is read as the
tree: a level cut at the marks of a combinator has no such mark inside a piece, because a part
that stands under a combinator with no brackets binds more strongly.

What this module does not claim: that `read` gives a tree with `wf` for every text it takes
(`WhatwgTest/Css/Values.lean` checks it on every collected line), or that `print (read s)`
is `s`: the reader drops white space.
-/

namespace Whatwg.Css.Values

/-! ## Induction over a tree -/

mutual

/-- Induction over a definition: a combination's parts are given as a list. -/
theorem Definition.induct {P : Definition → Prop} (atom : ∀ a, P (.atom a))
    (nest : ∀ e x, P x → P (.nest e x))
    (combine : ∀ c ps, (∀ p ∈ ps, P p) → P (.combine c ps))
    (mult : ∀ x m, P x → P (.mult x m)) : ∀ d, P d
  | .atom a => atom a
  | .nest e x => nest e x (Definition.induct atom nest combine mult x)
  | .combine c ps => combine c ps (Definition.inductList atom nest combine mult ps)
  | .mult x m => mult x m (Definition.induct atom nest combine mult x)

/-- The same, for every definition of a list. -/
theorem Definition.inductList {P : Definition → Prop} (atom : ∀ a, P (.atom a))
    (nest : ∀ e x, P x → P (.nest e x))
    (combine : ∀ c ps, (∀ p ∈ ps, P p) → P (.combine c ps))
    (mult : ∀ x m, P x → P (.mult x m)) : ∀ ps : List Definition, ∀ p ∈ ps, P p
  | [], _, h => nomatch h
  | q :: qs, p, h => by
    cases h with
    | head => exact Definition.induct atom nest combine mult q
    | tail _ h => exact Definition.inductList atom nest combine mult qs p h

end

theorem Definition.lexemesList_eq (ps : List Definition) :
    Definition.lexemesList ps = ps.map Definition.lexemes := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [Definition.lexemesList, List.map_cons, ih]

theorem Definition.wfParts_iff (c : Combinator) (ps : List Definition) :
    Definition.wfParts c ps = true ↔ ∀ p ∈ ps, p.wf = true ∧ p.standsUnder c = true := by
  induction ps with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | cons q qs ih =>
    simp only [Definition.wfParts, Bool.and_eq_true, ih, List.mem_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ p (rfl | hp)
      · exact ⟨h1, h2⟩
      · exact h3 p hp
    · intro h
      exact ⟨h q (Or.inl rfl), fun p hp => h p (Or.inr hp)⟩

/-- What `wf` says of a combination. -/
theorem Definition.wf_combine {c : Combinator} {ps : List Definition}
    (h : (Definition.combine c ps).wf = true) :
    2 ≤ ps.length ∧ ∀ p ∈ ps, p.wf = true ∧ p.standsUnder c = true := by
  simp only [Definition.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, (Definition.wfParts_iff c ps).mp h.2⟩

/-- A part that takes a multiplier is no combination. -/
theorem canTake_standsUnder {x : Definition} {m : Multiplier} (h : canTake x m = true)
    (c : Combinator) : x.standsUnder c = true := by
  cases x with
  | combine c' ps => cases m <;> exact Bool.noConfusion h
  | atom a => rfl
  | nest e y => rfl
  | mult y n => rfl

/-! ## Joined lists -/

theorem mem_joined {α : Type} {sep : List α} {xs : List (List α)} {a : α}
    (h : a ∈ joined sep xs) : a ∈ sep ∨ ∃ x ∈ xs, a ∈ x := by
  cases xs with
  | nil => exact nomatch h
  | cons x xs =>
    simp only [joined, List.mem_append, List.mem_flatMap] at h
    rcases h with h | ⟨y, hy, h | h⟩
    · exact Or.inr ⟨x, List.mem_cons_self, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, List.mem_cons_of_mem x hy, h⟩

/-! ## One level of a tree, as the reader sees it -/

/-- The items between two parts of a combination: none for juxtaposition. -/
def Combinator.sepItems : Combinator → List Item
  | .seq => []
  | c => [.op c]

/-- What stands between two parts is the mark of the combinator. -/
theorem Combinator.mem_sepItems {c : Combinator} {i : Item} (h : i ∈ c.sepItems) :
    i = .op c := by
  cases c with
  | seq => exact nomatch h
  | all => exact List.mem_singleton.mp h
  | any => exact List.mem_singleton.mp h
  | one => exact List.mem_singleton.mp h

/-- The items of a multiplier: `#{A,B}` is `#` and `{A,B}`. -/
def Multiplier.items : Multiplier → List Item
  | .hash (some r) => [.mult (.hash none), .mult (.times r)]
  | m => [.mult m]

mutual

/-- One level of a definition: an atom and an enclosure are one term each. -/
def Definition.items : Definition → List Item
  | .atom a => [.term (.atom a)]
  | .nest e x => [.term (.nest e x)]
  | .combine c ps => joined c.sepItems (Definition.itemsList ps)
  | .mult x m => x.items ++ m.items

/-- The items of each definition of a list. -/
def Definition.itemsList : List Definition → List (List Item)
  | [] => []
  | p :: ps => p.items :: Definition.itemsList ps

end

theorem Definition.itemsList_eq (ps : List Definition) :
    Definition.itemsList ps = ps.map Definition.items := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [Definition.itemsList, List.map_cons, ih]

/-- No item of a multiplier is a mark. -/
theorem Multiplier.items_isOp (m : Multiplier) (c : Combinator) :
    ∀ i ∈ m.items, i.isOp c = false := by
  intro i hi
  cases m with
  | hash r =>
    cases r with
    | none => simp only [Multiplier.items, List.mem_singleton] at hi; rw [hi]; rfl
    | some r =>
      simp only [Multiplier.items, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> rfl
  | star => simp only [Multiplier.items, List.mem_singleton] at hi; rw [hi]; rfl
  | plus => simp only [Multiplier.items, List.mem_singleton] at hi; rw [hi]; rfl
  | opt => simp only [Multiplier.items, List.mem_singleton] at hi; rw [hi]; rfl
  | times r => simp only [Multiplier.items, List.mem_singleton] at hi; rw [hi]; rfl
  | req => simp only [Multiplier.items, List.mem_singleton] at hi; rw [hi]; rfl

/-- A definition that stands under a combinator has no mark of it at its own level. -/
theorem Definition.items_isOp (c : Combinator) : ∀ d : Definition, d.wf = true →
    d.standsUnder c = true → ∀ i ∈ d.items, i.isOp c = false := by
  intro d
  induction d using Definition.induct generalizing c with
  | atom a =>
    intro _ _ i hi
    simp only [Definition.items, List.mem_singleton] at hi
    rw [hi]; rfl
  | nest e x _ =>
    intro _ _ i hi
    simp only [Definition.items, List.mem_singleton] at hi
    rw [hi]; rfl
  | combine c' ps ih =>
    intro hwf hunder i hi
    have hparts := (Definition.wf_combine hwf).2
    have hrank : c'.rank < c.rank := by
      simpa only [Definition.standsUnder, decide_eq_true_eq] using hunder
    simp only [Definition.items, Definition.itemsList_eq] at hi
    rcases mem_joined hi with hsep | ⟨x, hx, hix⟩
    · rw [Combinator.mem_sepItems hsep]
      exact beq_eq_false_iff_ne.mpr fun e => by
        rw [e] at hrank
        exact Nat.lt_irrefl _ hrank
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      have hpu : p.standsUnder c = true := by
        have hp' := (hparts p hp).2
        cases p with
        | combine c'' qs =>
          simp only [Definition.standsUnder, decide_eq_true_eq] at hp' ⊢
          omega
        | atom a => rfl
        | nest e y => rfl
        | mult y n => rfl
      exact ih p hp c (hparts p hp).1 hpu i hix
  | mult x m ih =>
    intro hwf _ i hi
    simp only [Definition.wf, Bool.and_eq_true] at hwf
    simp only [Definition.items, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ih c hwf.1 (canTake_standsUnder hwf.2 c) i hi
    · exact Multiplier.items_isOp m c i hi

/-- A list of two or more is its first two and the others. -/
theorem two_parts {ps : List Definition} (h : 2 ≤ ps.length) : ∃ p q qs, ps = p :: q :: qs := by
  cases ps with
  | nil => exact absurd h (by decide)
  | cons p qs =>
    cases qs with
    | nil => exact absurd h (show ¬(2 ≤ 1) by decide)
    | cons q qs => exact ⟨p, q, qs, rfl⟩

/-! ## A juxtaposition -/

/-- A part that may take a multiplier takes it as it is. -/
theorem attach_of_canTake {x : Definition} {m : Multiplier} (h : canTake x m = true) :
    attach x m = some (.mult x m) := by
  unfold attach
  split
  · exact Bool.noConfusion h
  · rw [if_pos h]

/-- Whether `#` may follow a part does not depend on the repeat after it. -/
theorem canTake_hash (x : Definition) (r r' : Option Repeat) :
    canTake x (.hash r) = canTake x (.hash r') := by
  cases x with
  | atom a => rfl
  | nest e y => cases e <;> rfl
  | combine c ps => rfl
  | mult y n => cases n <;> rfl

/-- The items of a part, read as one part of a juxtaposition. -/
theorem factors_items : ∀ d : Definition, d.wf = true → d.standsUnder .seq = true →
    ∀ rest current done,
      factors (d.items ++ rest) current done = factors rest (some d) (push current done) := by
  intro d
  induction d using Definition.induct with
  | atom a => intro _ _ rest current done; rfl
  | nest e x _ => intro _ _ rest current done; rfl
  | combine c ps _ =>
    intro _ hu
    cases c <;> exact Bool.noConfusion hu
  | mult x m ih =>
    intro hwf _ rest current done
    simp only [Definition.wf, Bool.and_eq_true] at hwf
    have common : ∀ m' : Multiplier, m'.items = [.mult m'] → canTake x m' = true →
        factors (m'.items ++ rest) (some x) (push current done) =
          factors rest (some (.mult x m')) (push current done) := by
      intro m' hi hc
      rw [hi]
      simp only [List.cons_append, List.nil_append, factors, attach_of_canTake hc]
    simp only [Definition.items, List.append_assoc]
    rw [ih hwf.1 (canTake_standsUnder hwf.2 .seq)]
    cases m with
    | star => exact common _ rfl hwf.2
    | plus => exact common _ rfl hwf.2
    | opt => exact common _ rfl hwf.2
    | times r => exact common _ rfl hwf.2
    | req => exact common _ rfl hwf.2
    | hash r =>
      cases r with
      | none => exact common _ rfl hwf.2
      | some r =>
        have hc : canTake x (.hash none) = true := by
          rw [canTake_hash x none (some r)]
          exact hwf.2
        simp only [Multiplier.items, List.cons_append, List.nil_append, factors,
          attach_of_canTake hc]
        rfl

/-- The parts after the first, each read after the one before it. -/
theorem factors_parts : ∀ qs : List Definition,
    (∀ q ∈ qs, q.wf = true ∧ q.standsUnder .seq = true) → ∀ f done,
      factors ((qs.map Definition.items).flatMap ([] ++ ·)) (some f) done =
        some (done.reverse ++ f :: qs)
  | [], _, f, done => by
    simp only [List.map_nil, List.flatMap_nil, factors, push, List.reverse_cons]
  | q :: qs, h, f, done => by
    have hq := h q List.mem_cons_self
    show factors (q.items ++ (qs.map Definition.items).flatMap ([] ++ ·)) (some f) done = _
    rw [factors_items q hq.1 hq.2, push,
      factors_parts qs (fun p hp => h p (List.mem_cons_of_mem q hp))]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- A definition that is no combination, or a juxtaposition, is read from its items. -/
theorem readSeq_items (d : Definition) (hwf : d.wf = true) (hu : d.standsUnder .all = true) :
    readSeq d.items = some d := by
  have single : d.standsUnder .seq = true → readSeq d.items = some d := fun hs => by
    have h := factors_items d hwf hs [] none []
    rw [List.append_nil] at h
    simp only [readSeq, h, factors, push, List.reverse_cons, List.reverse_nil, List.nil_append]
  cases d with
  | atom a => exact single rfl
  | nest e x => exact single rfl
  | mult x m => exact single rfl
  | combine c ps =>
    obtain ⟨hlen, hparts⟩ := Definition.wf_combine hwf
    cases c with
    | all => exact Bool.noConfusion hu
    | any => exact Bool.noConfusion hu
    | one => exact Bool.noConfusion hu
    | seq =>
      obtain ⟨p, q, qs, rfl⟩ := two_parts hlen
      have hp := hparts p List.mem_cons_self
      have hrest := factors_parts (q :: qs)
        (fun x hx => hparts x (List.mem_cons_of_mem p hx)) p []
      have hitems : (Definition.combine .seq (p :: q :: qs)).items =
          p.items ++ ((q :: qs).map Definition.items).flatMap ([] ++ ·) := by
        simp only [Definition.items, Definition.itemsList_eq, Combinator.sepItems, joined,
          List.map_cons]
      rw [hitems, readSeq, factors_items p hp.1 hp.2, push, hrest]
      rfl

/-! ## One level of precedence -/

/-- Items with no mark of the combinator are one piece. -/
theorem split_clean (c : Combinator) : ∀ is : List Item, (∀ i ∈ is, i.isOp c = false) →
    split c is = (is, [])
  | [], _ => rfl
  | i :: is, h => by
    have ih := split_clean c is (fun j hj => h j (List.mem_cons_of_mem i hj))
    simp only [split, h i List.mem_cons_self, Bool.false_eq_true, if_false, ih]

/-- Items with no mark of the combinator stay in the first piece. -/
theorem split_append (c : Combinator) (rest : List Item) : ∀ x : List Item,
    (∀ i ∈ x, i.isOp c = false) →
      split c (x ++ rest) = (x ++ (split c rest).1, (split c rest).2)
  | [], _ => rfl
  | i :: x, h => by
    have ih := split_append c rest x (fun j hj => h j (List.mem_cons_of_mem i hj))
    simp only [List.cons_append, split, h i List.mem_cons_self, Bool.false_eq_true, if_false, ih]

/-- Pieces with no mark inside, each after a mark, are cut back into the pieces. -/
theorem split_pieces (c : Combinator) : ∀ ys : List (List Item),
    (∀ y ∈ ys, ∀ i ∈ y, i.isOp c = false) →
      split c (ys.flatMap ([Item.op c] ++ ·)) = ([], ys)
  | [], _ => rfl
  | y :: ys, h => by
    have ih := split_pieces c ys (fun z hz => h z (List.mem_cons_of_mem y hz))
    have hy := split_append c (ys.flatMap ([Item.op c] ++ ·)) y (h y List.mem_cons_self)
    have hop : (Item.op c).isOp c = true := by
      show (c == c) = true
      exact beq_self_eq_true c
    show split c (Item.op c :: (y ++ ys.flatMap ([Item.op c] ++ ·))) = ([], y :: ys)
    rw [split, if_pos hop, hy, ih]
    simp only [List.append_nil]

/-- A first piece and the pieces after it, each after a mark, are cut back into them. -/
theorem split_joined (c : Combinator) (x : List Item) (ys : List (List Item))
    (hx : ∀ i ∈ x, i.isOp c = false) (hys : ∀ y ∈ ys, ∀ i ∈ y, i.isOp c = false) :
    split c (x ++ ys.flatMap ([Item.op c] ++ ·)) = (x, ys) := by
  rw [split_append c _ x hx, split_pieces c ys hys, List.append_nil]

theorem mapAll_map {f : List Item → Option Definition} : ∀ ps : List Definition,
    (∀ p ∈ ps, f p.items = some p) → mapAll f (ps.map Definition.items) = some ps
  | [], _ => rfl
  | p :: ps, h => by
    have ih := mapAll_map ps (fun q hq => h q (List.mem_cons_of_mem p hq))
    simp only [List.map_cons, mapAll, h p List.mem_cons_self, ih]

/-- What stands between two parts of a combination that is no juxtaposition is its mark. -/
theorem Combinator.sepItems_eq {c : Combinator} (hc : c ≠ .seq) : c.sepItems = [.op c] := by
  cases c with
  | seq => exact absurd rfl hc
  | all => rfl
  | any => rfl
  | one => rfl

/-- One level reads a definition that stands under its combinator, by the level below, and a
combination by its combinator, part by part. -/
theorem level_items (c : Combinator) (hc : c ≠ .seq) (lower : List Item → Option Definition)
    (hlower : ∀ d : Definition, d.wf = true → d.standsUnder c = true → lower d.items = some d)
    (d : Definition) (hwf : d.wf = true)
    (hfit : d.standsUnder c = true ∨ ∃ ps, d = .combine c ps) :
    level c lower d.items = some d := by
  rcases hfit with hu | ⟨ps, rfl⟩
  · simp only [level, split_clean c d.items (Definition.items_isOp c d hwf hu), hlower d hwf hu]
  · obtain ⟨hlen, hparts⟩ := Definition.wf_combine hwf
    obtain ⟨p, q, qs, rfl⟩ := two_parts hlen
    have hclean : ∀ r ∈ p :: q :: qs, ∀ i ∈ r.items, i.isOp c = false := fun r hr =>
      Definition.items_isOp c r (hparts r hr).1 (hparts r hr).2
    have hsplit := split_joined c p.items ((q :: qs).map Definition.items)
      (hclean p List.mem_cons_self) (fun y hy i hi => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
        exact hclean r (List.mem_cons_of_mem p hr) i hi)
    have hall := mapAll_map (f := lower) (p :: q :: qs)
      (fun r hr => hlower r (hparts r hr).1 (hparts r hr).2)
    simp only [List.map_cons] at hsplit hall
    simp only [level, Definition.items, Definition.itemsList_eq, Combinator.sepItems_eq hc,
      joined, List.map_cons, hsplit, hall, Option.map_some]

theorem Definition.fits_all (d : Definition) (h : d.standsUnder .any = true) :
    d.standsUnder .all = true ∨ ∃ ps, d = .combine .all ps := by
  cases d with
  | atom a => exact Or.inl rfl
  | nest e x => exact Or.inl rfl
  | mult x m => exact Or.inl rfl
  | combine c ps =>
    cases c with
    | seq => exact Or.inl rfl
    | all => exact Or.inr ⟨ps, rfl⟩
    | any => exact Bool.noConfusion h
    | one => exact Bool.noConfusion h

theorem Definition.fits_any (d : Definition) (h : d.standsUnder .one = true) :
    d.standsUnder .any = true ∨ ∃ ps, d = .combine .any ps := by
  cases d with
  | atom a => exact Or.inl rfl
  | nest e x => exact Or.inl rfl
  | mult x m => exact Or.inl rfl
  | combine c ps =>
    cases c with
    | seq => exact Or.inl rfl
    | all => exact Or.inl rfl
    | any => exact Or.inr ⟨ps, rfl⟩
    | one => exact Bool.noConfusion h

theorem Definition.fits_one (d : Definition) :
    d.standsUnder .one = true ∨ ∃ ps, d = .combine .one ps := by
  cases d with
  | atom a => exact Or.inl rfl
  | nest e x => exact Or.inl rfl
  | mult x m => exact Or.inl rfl
  | combine c ps =>
    cases c with
    | seq => exact Or.inl rfl
    | all => exact Or.inl rfl
    | any => exact Or.inl rfl
    | one => exact Or.inr ⟨ps, rfl⟩

/-- One level of a tree, as items, is read as the tree. -/
theorem assemble_items (d : Definition) (hwf : d.wf = true) : assemble d.items = some d :=
  level_items .one (by decide) _
    (fun d hwf hu =>
      level_items .any (by decide) _
        (fun d hwf hu =>
          level_items .all (by decide) _ readSeq_items d hwf (d.fits_all hu))
        d hwf (d.fits_any hu))
    d hwf d.fits_one

/-! ## Lexemes to a tree -/

/-- The reader, given these lexemes, holds these items: they are put on the level being read,
whatever is read after them and whatever enclosures are open. -/
def Builds (ts : List Lexeme) (is : List Item) : Prop :=
  ∀ rest acc stack, build (ts ++ rest) acc stack = build rest (is.reverse ++ acc) stack

theorem Builds.nil : Builds [] [] := fun _ _ _ => rfl

theorem Builds.append {t₁ t₂ : List Lexeme} {i₁ i₂ : List Item} (h₁ : Builds t₁ i₁)
    (h₂ : Builds t₂ i₂) : Builds (t₁ ++ t₂) (i₁ ++ i₂) := fun rest acc stack => by
  rw [List.append_assoc, h₁, h₂, List.reverse_append, List.append_assoc]

theorem Builds.atom (a : Atom) : Builds [.atom a] [.term (.atom a)] := fun _ _ _ => rfl

theorem Builds.op (c : Combinator) : Builds [.op c] [.op c] := fun _ _ _ => rfl

theorem Builds.mult (m : Multiplier) : Builds [.mult m] [.mult m] := fun _ _ _ => rfl

/-- An enclosure whose inside is read as `d` is one term. -/
theorem Builds.nest (e : Enclosure) {ts : List Lexeme} {d : Definition} (h : Builds ts d.items)
    (ha : assemble d.items = some d) :
    Builds (.enter e :: ts ++ [.leave e.closer]) [.term (.nest e d)] := fun rest acc stack => by
  have step : build (.enter e :: (ts ++ (.leave e.closer :: rest))) acc stack =
      build (ts ++ (.leave e.closer :: rest)) [] ((e, acc) :: stack) := rfl
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rw [step, h]
  simp only [build, List.append_nil, List.reverse_reverse, ha, if_true, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append]

theorem Builds.sep (c : Combinator) : Builds c.sep c.sepItems := by
  cases c with
  | seq => exact Builds.nil
  | all => exact Builds.op _
  | any => exact Builds.op _
  | one => exact Builds.op _

theorem Builds.multiplier (m : Multiplier) : Builds m.lexemes m.items := by
  cases m with
  | star => exact Builds.mult _
  | plus => exact Builds.mult _
  | opt => exact Builds.mult _
  | times r => exact Builds.mult _
  | req => exact Builds.mult _
  | hash r =>
    cases r with
    | none => exact Builds.mult _
    | some r => exact Builds.append (Builds.mult (.hash none)) (Builds.mult (.times r))

/-- The parts after the first, each after the separator. -/
theorem Builds.rest {sepT : List Lexeme} {sepI : List Item} (hsep : Builds sepT sepI) :
    ∀ qs : List Definition, (∀ q ∈ qs, Builds q.lexemes q.items) →
      Builds ((qs.map Definition.lexemes).flatMap (sepT ++ ·))
        ((qs.map Definition.items).flatMap (sepI ++ ·))
  | [], _ => Builds.nil
  | q :: qs, h => by
    simp only [List.map_cons, List.flatMap_cons]
    exact Builds.append (Builds.append hsep (h q List.mem_cons_self))
      (Builds.rest hsep qs (fun p hp => h p (List.mem_cons_of_mem q hp)))

/-- The parts of a combination, joined. -/
theorem Builds.parts {sepT : List Lexeme} {sepI : List Item} (hsep : Builds sepT sepI)
    (ps : List Definition) (h : ∀ p ∈ ps, Builds p.lexemes p.items) :
    Builds (Values.joined sepT (ps.map Definition.lexemes))
      (Values.joined sepI (ps.map Definition.items)) := by
  cases ps with
  | nil => exact Builds.nil
  | cons p qs =>
    exact Builds.append (h p List.mem_cons_self)
      (Builds.rest hsep qs (fun q hq => h q (List.mem_cons_of_mem p hq)))

/-- The reader, given the lexemes of a tree, holds the items of that tree. -/
theorem builds_lexemes : ∀ d : Definition, d.wf = true → Builds d.lexemes d.items := by
  intro d
  induction d using Definition.induct with
  | atom a => intro _; exact Builds.atom a
  | nest e x ih =>
    intro hwf
    simp only [Definition.wf, Bool.and_eq_true] at hwf
    exact Builds.nest e (ih hwf.2) (assemble_items x hwf.2)
  | combine c ps ih =>
    intro hwf
    have hparts := (Definition.wf_combine hwf).2
    simp only [Definition.lexemes, Definition.items, Definition.lexemesList_eq,
      Definition.itemsList_eq]
    exact Builds.parts (Builds.sep c) ps (fun p hp => ih p hp (hparts p hp).1)
  | mult x m ih =>
    intro hwf
    simp only [Definition.wf, Bool.and_eq_true] at hwf
    exact Builds.append (ih hwf.1) (Builds.multiplier m)

/-- The second half of the round trip: the lexemes of a tree are read as the tree. -/
theorem parse_lexemes (d : Definition) (hwf : d.wf = true) : parse d.lexemes = some d := by
  have h := builds_lexemes d hwf [] [] []
  rw [List.append_nil, List.append_nil] at h
  show build d.lexemes [] [] = some d
  rw [h]
  show assemble d.items.reverse.reverse = some d
  rw [List.reverse_reverse]
  exact assemble_items d hwf

/-! ## The round trip -/

theorem Multiplier.lexemes_ok (m : Multiplier) : ∀ t ∈ m.lexemes, t.ok = true := by
  intro t ht
  cases m with
  | hash r =>
    cases r with
    | none => rw [List.mem_singleton.mp ht]; rfl
    | some r =>
      simp only [Multiplier.lexemes, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> rfl
  | star => rw [List.mem_singleton.mp ht]; rfl
  | plus => rw [List.mem_singleton.mp ht]; rfl
  | opt => rw [List.mem_singleton.mp ht]; rfl
  | times r => rw [List.mem_singleton.mp ht]; rfl
  | req => rw [List.mem_singleton.mp ht]; rfl

/-- Every lexeme of a tree with `wf` is one the reader takes whole. -/
theorem Definition.lexemes_ok : ∀ d : Definition, d.wf = true →
    ∀ t ∈ d.lexemes, t.ok = true := by
  intro d
  induction d using Definition.induct with
  | atom a =>
    intro hwf t ht
    rw [List.mem_singleton.mp ht]
    exact hwf
  | nest e x ih =>
    intro hwf t ht
    simp only [Definition.wf, Bool.and_eq_true] at hwf
    simp only [Definition.lexemes, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at ht
    rcases ht with (rfl | ht) | rfl
    · exact hwf.1
    · exact ih hwf.2 t ht
    · rfl
  | combine c ps ih =>
    intro hwf t ht
    have hparts := (Definition.wf_combine hwf).2
    simp only [Definition.lexemes, Definition.lexemesList_eq] at ht
    rcases mem_joined ht with hsep | ⟨x, hx, htx⟩
    · cases c with
      | seq => exact nomatch hsep
      | all => rw [List.mem_singleton.mp hsep]; rfl
      | any => rw [List.mem_singleton.mp hsep]; rfl
      | one => rw [List.mem_singleton.mp hsep]; rfl
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact ih p hp (hparts p hp).1 t htx
  | mult x m ih =>
    intro hwf t ht
    simp only [Definition.wf, Bool.and_eq_true] at hwf
    simp only [Definition.lexemes, List.mem_append] at ht
    rcases ht with ht | ht
    · exact ih hwf.1 t ht
    · exact Multiplier.lexemes_ok m t ht

/-- Reading what the printer wrote for a tree with `wf` gives the tree back. -/
theorem Definition.read_print (d : Definition) (hwf : d.wf = true) :
    Definition.read d.print = some d := by
  show (lex (String.ofList (render d.lexemes)).toList).bind parse = some d
  rw [String.toList_ofList, lex_render d.lexemes (d.lexemes_ok hwf)]
  exact parse_lexemes d hwf

/-- Two trees with `wf` that print alike are one tree. -/
theorem Definition.print_injective {d₁ d₂ : Definition} (h₁ : d₁.wf = true) (h₂ : d₂.wf = true)
    (h : d₁.print = d₂.print) : d₁ = d₂ := by
  have e := d₁.read_print h₁
  rw [h, d₂.read_print h₂] at e
  exact (Option.some.inj e).symm

end Whatwg.Css.Values
