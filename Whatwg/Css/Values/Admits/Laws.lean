import Whatwg.Css.Values.Admits

/-!
# Whatwg.Css.Values.Admits.Laws

Owner: the laws of `admits` (slice K3 of `docs/CSS-PACKAGE-PLAN.md`; ruling CS-5). They are
the steps of a proof that a writer's value is admitted by the grammar of its property: such a
proof walks the definition, and at each form it uses the law of that form.

- A keyword: `admits_keyword_iff`. It admits exactly one identifier of that name, ASCII
  case-insensitively.
- A bar: `admits_one`. It admits what one of its alternatives admits.
- A juxtaposition: `admits_seq_cons`, `admits_seq_nil` and `admits_seq`. It admits the values
  of its parts, one after the other, where no part is a comma of the grammar.
- `#`: `admits_hash`. It admits values of its part with one comma between two.
- `?`: `admits_opt`. It admits the empty value and what its part admits.
- A function: `admits_function_iff`. It admits one function of that name whose value is
  admitted by the arguments.
- A name: `admits_type_basic`, `admits_type_production`, `admits_functionType` and
  `admits_property`. A basic type is its test, and any other name is what it stands for, at
  one less of depth.
- `||` and `&&`: `admits_any_pick` and `admits_all_pick`. One part takes a first piece, and
  the other parts the rest.

A law that joins values holds for a part that is no combination (`Definition.isPart`): a tree
the reader gives has no other part in a juxtaposition or under a multiplier.

What this module does not claim: a law for a juxtaposition with a comma of the grammar, whose
commas may be left out; a law for `*`, `+`, `{A,B}` and `!`; the converse of a joining law,
that a value is admitted in no other way; or that a deeper `depth` admits more.
-/

namespace Whatwg.Css.Values

open Whatwg.Css.Syntax (Component Token)

/-! ## Cuts, picks and joined values -/

/-- A list is cut where two lists were put together. -/
theorem mem_splits_append {α : Type} : ∀ a b : List α, (a, b) ∈ splits (a ++ b)
  | [], [] => List.mem_cons_self
  | [], _ :: _ => List.mem_cons_self
  | _ :: a, b =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, b), mem_splits_append a b, rfl⟩)

/-- A pick leaves one member fewer. -/
theorem length_of_mem_picks {α : Type} : ∀ {ls : List α} {l : α} {rest : List α},
    (l, rest) ∈ picks ls → rest.length + 1 = ls.length
  | [], _, _, h => nomatch h
  | x :: xs, l, rest, h => by
    simp only [picks, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨q, hq, h⟩
    · cases h; rfl
    · cases h
      have ih := length_of_mem_picks (ls := xs) (l := q.1) (rest := q.2) hq
      simp only [List.length_cons, ih]

/-- The picks of a mapped list are the picks, mapped. -/
theorem picks_map {α β : Type} (f : α → β) : ∀ ls : List α,
    picks (ls.map f) = (picks ls).map fun p => (f p.1, p.2.map f)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, picks, picks_map f xs, List.map_map]
    rfl

theorem joined_cons_cons {α : Type} (sep : List α) (v w : List α) (ws : List (List α)) :
    joined sep (v :: w :: ws) = v ++ (sep ++ joined sep (w :: ws)) := by
  simp only [joined, List.flatMap_cons, List.append_assoc]

theorem strip_append (a b : List Component) : strip (a ++ b) = strip a ++ strip b := by
  simp only [strip, List.filter_append]

/-- Dropping white space from joined values is joining the values with theirs dropped. -/
theorem strip_joined : ∀ vs : List (List Component),
    strip (joined [Component.token .comma] vs) = joined [Component.token .comma] (vs.map strip)
  | [] => rfl
  | [v] => by simp only [joined, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
  | v :: w :: ws => by
    have ih := strip_joined (w :: ws)
    simp only [List.map_cons] at ih
    rw [joined_cons_cons, strip_append, strip_append, ih, List.map_cons, List.map_cons,
      joined_cons_cons]
    rfl

/-- Joined values are at least as long as their commas. -/
theorem length_le_joined (c : Component) : ∀ vs : List (List Component),
    vs.length ≤ (joined [c] vs).length + 1
  | [] => Nat.zero_le _
  | [v] => by simp only [List.length_cons, List.length_nil]; omega
  | v :: w :: ws => by
    have ih := length_le_joined c (w :: ws)
    rw [joined_cons_cons]
    simp only [List.length_cons, List.length_append, List.length_nil] at ih ⊢
    omega

/-! ## Languages -/

namespace Language

theorem just_iff (test : Component → Bool) (v : List Component) :
    just test v = true ↔ ∃ c, v = [c] ∧ test c = true := by
  unfold just
  split
  · rename_i c
    exact ⟨fun h => ⟨c, rfl, h⟩, fun ⟨c', hc, h⟩ => by cases hc; exact h⟩
  · rename_i hne
    exact ⟨fun h => Bool.noConfusion h, fun ⟨c, hc, _⟩ => absurd hc (hne c)⟩

/-- A juxtaposition admits a first piece of its first part, then the others' value. -/
theorem seq_cons_append {l : Language} {ls : List Language} {a b : List Component}
    (ha : l a = true) (hb : seq ls b = true) : seq (l :: ls) (a ++ b) = true := by
  simp only [seq, List.any_eq_true, Bool.and_eq_true]
  exact ⟨(a, b), mem_splits_append a b, ha, hb⟩

/-- A list admits values of its part with one comma between two, when it may hold as many. -/
theorem listUpTo_joined {l : Language} : ∀ (vs : List (List Component)) (n : Nat), vs ≠ [] →
    vs.length ≤ n → (∀ v ∈ vs, l v = true) →
      listUpTo l n (joined [Component.token .comma] vs) = true
  | [], _, hne, _, _ => absurd rfl hne
  | [v], n, _, hlen, h => by
    cases n with
    | zero => exact absurd hlen (show ¬(1 ≤ 0) by decide)
    | succ n =>
      simp only [joined, List.flatMap_nil, List.append_nil, listUpTo, h v List.mem_cons_self,
        Bool.true_or]
  | v :: w :: ws, n, _, hlen, h => by
    cases n with
    | zero => exact absurd hlen (by simp only [List.length_cons]; omega)
    | succ n =>
      have ih := listUpTo_joined (l := l) (w :: ws) n (List.cons_ne_nil w ws)
        (by simp only [List.length_cons] at hlen ⊢; omega)
        (fun x hx => h x (List.mem_cons_of_mem v hx))
      rw [joined_cons_cons]
      simp only [listUpTo, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      refine Or.inr ⟨(v, [Component.token .comma] ++ joined [Component.token .comma] (w :: ws)),
        mem_splits_append _ _, h v List.mem_cons_self, ?_⟩
      exact ih

/-- `||`: one part takes a first piece, and the rest is empty or taken by the others. -/
theorem anyOf_pick {ls : List Language} {l : Language} {rest : List Language}
    {a b : List Component} (hpick : (l, rest) ∈ picks ls) (ha : l a = true)
    (hb : b.isEmpty = true ∨ anyOf rest.length rest b = true) :
    anyOf ls.length ls (a ++ b) = true := by
  rw [← length_of_mem_picks hpick]
  simp only [anyOf, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨(l, rest), hpick, (a, b), mem_splits_append a b, ha, hb⟩

/-- `&&`: one part takes a first piece, and the others take the rest. -/
theorem allOf_pick {ls : List Language} {l : Language} {rest : List Language}
    {a b : List Component} (hpick : (l, rest) ∈ picks ls) (ha : l a = true)
    (hb : allOf rest.length rest b = true) : allOf ls.length ls (a ++ b) = true := by
  have hlen := length_of_mem_picks hpick
  cases ls with
  | nil => exact nomatch hpick
  | cons l₀ ls₀ =>
    simp only [List.length_cons] at hlen ⊢
    have hrest : rest.length = ls₀.length := by omega
    rw [hrest] at hb
    simp only [allOf, List.any_eq_true, Bool.and_eq_true]
    exact ⟨(l, rest), hpick, (a, b), mem_splits_append a b, ha, hb⟩

end Language

theorem isKeyword_iff (name : List Char) (c : Component) :
    isKeyword name c = true ↔ ∃ x, c = .token (.ident x) ∧ sameName x name = true := by
  unfold isKeyword
  split
  · rename_i x
    exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨x', hc, h⟩ => by cases hc; exact h⟩
  · rename_i hne
    exact ⟨fun h => Bool.noConfusion h, fun ⟨x, hc, _⟩ => absurd hc (hne x)⟩

/-! ## A definition as a language -/

theorem Definition.languages_eq (env : Env) (unfold : Definition → Language) (top : Bool) :
    ∀ ps : List Definition,
      Definition.languages env unfold ps top = ps.map fun p => p.language env unfold top
  | [] => by simp only [Definition.languages, List.map_nil]
  | p :: ps => by
    simp only [Definition.languages, List.map_cons, Definition.languages_eq env unfold top ps]

/-- A part that is no combination has one language, whether or not it stands where commas may
be left out: only a juxtaposition reads that. -/
theorem Definition.language_part (env : Env) (unfold : Definition → Language) {p : Definition}
    (h : p.isPart = true) (top : Bool) :
    p.language env unfold top = p.language env unfold false := by
  cases p with
  | atom a => simp only [Definition.language]
  | nest e x => simp only [Definition.language]
  | combine c ps => exact Bool.noConfusion h
  | mult x m => simp only [Definition.language]

/-! ## The laws -/

/-- A keyword admits a value that is one identifier of its name, ASCII case-insensitively, and
white space; and no other value. -/
theorem admits_keyword_iff (env : Env) (name : String) (value : List Component) (depth : Nat) :
    admits env (.keyword name) value depth = true ↔
      ∃ x, strip value = [.token (.ident x)] ∧ sameName x name.toList = true := by
  simp only [admits, Definition.keyword, Definition.language, Atom.language, Language.just_iff,
    isKeyword_iff]
  constructor
  · rintro ⟨c, hv, x, rfl, hx⟩
    exact ⟨x, hv, hx⟩
  · rintro ⟨x, hv, hx⟩
    exact ⟨_, hv, x, rfl, hx⟩

/-- `a | b` admits what one of its alternatives admits. -/
theorem admits_one (env : Env) (ps : List Definition) (value : List Component) (depth : Nat) :
    admits env (.one ps) value depth = ps.any fun p => admits env p value depth := by
  simp only [admits, Definition.one, Definition.language, Language.oneOf,
    Definition.languages_eq, List.any_map]
  rfl

/-- The empty juxtaposition admits the empty value. -/
theorem admits_seq_nil (env : Env) (value : List Component) (depth : Nat) :
    admits env (.seq []) value depth = (strip value).isEmpty := by
  simp only [admits, Definition.seq, Definition.language]
  rfl

/-- A juxtaposition admits a value of its first part followed by a value of the others, where
no part is a comma of the grammar. -/
theorem admits_seq_cons (env : Env) {p : Definition} {ps : List Definition}
    {v₁ v₂ : List Component} {depth : Nat} (hp : p.isPart = true)
    (hcomma : (p :: ps).any Definition.isComma = false)
    (h₁ : admits env p v₁ depth = true) (h₂ : admits env (.seq ps) v₂ depth = true) :
    admits env (.seq (p :: ps)) (v₁ ++ v₂) depth = true := by
  have hps : ps.any Definition.isComma = false := by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hcomma
    exact hcomma.2
  simp only [admits, Definition.seq, Definition.language, hps, hcomma, Bool.and_false,
    Bool.false_eq_true, if_false, Definition.languages, strip_append] at h₂ ⊢
  refine Language.seq_cons_append ?_ h₂
  rw [← Definition.language_part env _ hp true]
  exact h₁

/-- A juxtaposition admits the values of its parts, one after the other: given each part with
a value it admits, where each part is no combination and none is a comma of the grammar. -/
theorem admits_seq (env : Env) {depth : Nat} : ∀ pairs : List (Definition × List Component),
    (∀ pv ∈ pairs, pv.1.isPart = true ∧ admits env pv.1 pv.2 depth = true) →
    (pairs.map fun pv => pv.1).any Definition.isComma = false →
      admits env (.seq (pairs.map fun pv => pv.1)) (pairs.flatMap fun pv => pv.2) depth = true
  | [], _, _ => by
    rw [List.map_nil, List.flatMap_nil, admits_seq_nil]
    rfl
  | pv :: pairs, h, hcomma => by
    have hps : (pairs.map fun pv => pv.1).any Definition.isComma = false := by
      simp only [List.map_cons, List.any_cons, Bool.or_eq_false_iff] at hcomma
      exact hcomma.2
    rw [List.map_cons, List.flatMap_cons]
    exact admits_seq_cons env (h pv List.mem_cons_self).1 hcomma (h pv List.mem_cons_self).2
      (admits_seq env pairs (fun q hq => h q (List.mem_cons_of_mem pv hq)) hps)

/-- `x#` admits values of `x` with one comma between two of them. -/
theorem admits_hash (env : Env) {x : Definition} {vs : List (List Component)} {depth : Nat}
    (hx : x.isPart = true) (hne : vs ≠ []) (h : ∀ v ∈ vs, admits env x v depth = true) :
    admits env (.mult x (.hash none)) (joined [Component.token .comma] vs) depth = true := by
  simp only [admits, Definition.language, Language.mult, strip_joined]
  refine Language.listUpTo_joined (vs.map strip) _ ?_ ?_ ?_
  · intro e
    exact hne (List.map_eq_nil_iff.mp e)
  · exact length_le_joined _ _
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    rw [← Definition.language_part env _ hx true]
    exact h v hv

/-- `x?` admits the empty value, and what `x` admits. -/
theorem admits_opt (env : Env) {x : Definition} (hx : x.isPart = true) (value : List Component)
    (depth : Nat) :
    admits env (.mult x .opt) value depth =
      ((strip value).isEmpty || admits env x value depth) := by
  simp only [admits, Definition.language, Language.mult,
    Definition.language_part env _ hx true]

/-- A function admits a value that is one function of its name, ASCII case-insensitively,
whose value is admitted by the arguments; and no other value. -/
theorem admits_function_iff (env : Env) (name : String) (arguments : Definition)
    (value : List Component) (depth : Nat) :
    admits env (.function name arguments) value depth = true ↔
      ∃ x w, strip value = [.function x w] ∧ sameName x name.toList = true ∧
        admits env arguments w depth = true := by
  simp only [admits, Definition.function, Definition.language, Enclosure.language,
    Language.just_iff]
  constructor
  · rintro ⟨c, hv, hc⟩
    split at hc
    · rename_i x w
      simp only [Bool.and_eq_true] at hc
      exact ⟨x, w, hv, hc.1, hc.2⟩
    · exact Bool.noConfusion hc
  · rintro ⟨x, w, hv, hx, hw⟩
    exact ⟨_, hv, by simp only [hx, hw, Bool.and_self]⟩

/-- A name that is a basic type admits one component value that passes its test. -/
theorem admits_type_basic (env : Env) {name : String} {test : Option Range → Component → Bool}
    (h : env.type name = some (.basic test)) (range : Option Range) (value : List Component)
    (depth : Nat) :
    admits env (.type name range) value depth = Language.just (test range) (strip value) := by
  simp only [admits, Definition.type, Definition.language, Atom.language, h]

/-- A name that stands for a definition admits what the definition admits, at one less of
depth. -/
theorem admits_type_production (env : Env) {name : String} {d : Definition}
    (h : env.type name = some (.production d)) (value : List Component) (depth : Nat) :
    admits env (.type name none) value (depth + 1) = admits env d value depth := by
  simp only [admits, Definition.type, Definition.language, Atom.language, h, Option.isNone_none,
    if_true, unfoldAt]

/-- `<name()>` admits what the definition of the function admits, at one less of depth. -/
theorem admits_functionType (env : Env) {name : String} {d : Definition}
    (h : env.function name = some d) (value : List Component) (depth : Nat) :
    admits env (.functionType name) value (depth + 1) = admits env d value depth := by
  simp only [admits, Definition.functionType, Definition.language, Atom.language, h, unfoldAt]

/-- `<'name'>` admits what the property's grammar admits without its top-level `#`, at one
less of depth. -/
theorem admits_property (env : Env) {name : String} {d : Definition}
    (h : env.property name = some d) (value : List Component) (depth : Nat) :
    admits env (.property name) value (depth + 1) = admits env d.unlisted value depth := by
  simp only [admits, Definition.property, Definition.language, Atom.language, h, unfoldAt]

/-- `||`: a value of one part, then nothing or a value of `||` of the other parts. -/
theorem admits_any_pick (env : Env) {ps rest : List Definition} {p : Definition}
    {v₁ v₂ : List Component} {depth : Nat} (hpick : (p, rest) ∈ picks ps)
    (hp : p.isPart = true) (h₁ : admits env p v₁ depth = true)
    (h₂ : (strip v₂).isEmpty = true ∨ admits env (.any rest) v₂ depth = true) :
    admits env (.any ps) (v₁ ++ v₂) depth = true := by
  simp only [admits, Definition.any, Definition.language, Definition.languages_eq,
    strip_append] at h₂ ⊢
  have hmem : ((fun q : Definition => q.language env (unfoldAt env depth) false) p,
      rest.map fun q => q.language env (unfoldAt env depth) false) ∈
      picks (ps.map fun q => q.language env (unfoldAt env depth) false) := by
    rw [picks_map]
    exact List.mem_map.mpr ⟨(p, rest), hpick, rfl⟩
  have hfirst : p.language env (unfoldAt env depth) false (strip v₁) = true := by
    rw [← Definition.language_part env _ hp true]
    exact h₁
  have key := Language.anyOf_pick hmem (a := strip v₁) (b := strip v₂) hfirst
    (by simpa only [List.length_map] using h₂)
  simpa only [List.length_map] using key

/-- `&&`: a value of one part, then a value of `&&` of the other parts. -/
theorem admits_all_pick (env : Env) {ps rest : List Definition} {p : Definition}
    {v₁ v₂ : List Component} {depth : Nat} (hpick : (p, rest) ∈ picks ps)
    (hp : p.isPart = true) (h₁ : admits env p v₁ depth = true)
    (h₂ : admits env (.all rest) v₂ depth = true) :
    admits env (.all ps) (v₁ ++ v₂) depth = true := by
  simp only [admits, Definition.all, Definition.language, Definition.languages_eq,
    strip_append] at h₂ ⊢
  have hmem : ((fun q : Definition => q.language env (unfoldAt env depth) false) p,
      rest.map fun q => q.language env (unfoldAt env depth) false) ∈
      picks (ps.map fun q => q.language env (unfoldAt env depth) false) := by
    rw [picks_map]
    exact List.mem_map.mpr ⟨(p, rest), hpick, rfl⟩
  have hfirst : p.language env (unfoldAt env depth) false (strip v₁) = true := by
    rw [← Definition.language_part env _ hp true]
    exact h₁
  have key := Language.allOf_pick hmem (a := strip v₁) (b := strip v₂) hfirst
    (by simpa only [List.length_map] using h₂)
  simpa only [List.length_map] using key

end Whatwg.Css.Values
