import Whatwg.Html.Content.Valid
import Whatwg.Html.Node.Svg

/-!
# Whatwg.Html.Node.SvgKeys

Owner: the attribute list of a typed SVG element, judged by its keys (slice S6 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-36). The checker's test of an attribute list,
`Content.svgAttrsOk`, reads names: it decodes each name to its characters, looks the name up,
and compares every two names as strings. A typed attribute already holds what its name is. Its
`Key` says so with no text for an attribute of the schema: the attribute itself, a custom data
attribute's key, or one of the two namespace declarations.

`SvgAttr.allOk` judges a typed attribute list in one pass over its keys. Each attribute must be
one the element takes, and its key must not have been met before. The keys met so far are a
mask of schema attributes, a list of data keys and two bits, so the pass does one membership
test and one insertion for each attribute of the schema, and reads a string only at a custom
data attribute.

`SvgAttr.svgAttrsOk_toPairs` is the law: the checker's test of the written pairs is this pass.
It rests on three facts. A key's name is the name `toPair` writes (`toPair_fst`), and the name
is injective in the key (`Key.name_injective`): no attribute of the schema is named `xmlns` or
`xmlns:xlink`, and none opens with `data-`. The checker's test of one written name is the key's
test (`attrOk_toPair`). And a list has as many names after duplicates are erased as before
exactly when no name repeats (`eraseDups_length_eq_iff`).

`SvgAttr.allOk_iff` says what the pass decides: the element takes every attribute, and no key
repeats. It is `okFrom_iff` at the empty state. `okFrom_iff` speaks of any state, by a
predicate that says which keys the state holds.

What this module does not claim: anything about a value. `Whatwg/Html/Node/Svg.lean` gives the
values of a typed tree by their types.
-/

namespace Whatwg.Html

open Whatwg.Svg.Data (Mask)
open Whatwg.Svg.Schema (Tag Attr)

namespace SvgAttr

variable {t : Tag}

/-- What names an attribute of an SVG element: an attribute of the schema, the key of a custom
data attribute, or one of the two namespace declarations. -/
inductive Key where
  /-- An attribute of the schema. -/
  | attr (a : Attr)
  /-- A custom data attribute, `data-<key>`. -/
  | data (key : String)
  /-- `xmlns`. -/
  | xmlns
  /-- `xmlns:xlink`. -/
  | xmlnsXlink
  deriving DecidableEq, Repr

/-- The key of a typed attribute. -/
def key : SvgAttr t → Key
  | .attr a _ => .attr a
  | .data k _ => .data k
  | .xmlns => .xmlns
  | .xmlnsXlink => .xmlnsXlink

/-- The name that a key writes. -/
def Key.name : Key → String
  | .attr a => a.name
  | .data k => "data-" ++ k
  | .xmlns => "xmlns"
  | .xmlnsXlink => "xmlns:xlink"

/-- What follows `data-` makes a custom data attribute's name: at least one character, and no
ASCII upper-case letter (`Whatwg.Svg.Content.isDataName`). -/
def dataKeyOk (k : String) : Bool :=
  match k.toList with
  | c :: rest => (c :: rest).all fun ch => !ch.isUpper
  | [] => false

/-- The element takes an attribute of this key: an attribute of the schema that the definitions
give the element, a custom data attribute with a good key, or a namespace declaration. -/
def Key.okOn (t : Tag) : Key → Bool
  | .attr a => t.attrs.mem a
  | .data k => dataKeyOk k
  | .xmlns => true
  | .xmlnsXlink => true

/-- One pass over an attribute list, from the keys met so far: the schema attributes `seen`,
the data keys `keys`, and whether `xmlns` and `xmlns:xlink` were met. Each attribute is one the
element takes, and its key was not met before. -/
def okFrom (seen : Mask Attr) (keys : List String) (ns xlink : Bool) : List (SvgAttr t) → Bool
  | [] => true
  | .attr a _ :: rest =>
    t.attrs.mem a && !seen.mem a && okFrom (seen.insert a) keys ns xlink rest
  | .data k _ :: rest =>
    dataKeyOk k && !keys.contains k && okFrom seen (k :: keys) ns xlink rest
  | .xmlns :: rest => !ns && okFrom seen keys true xlink rest
  | .xmlnsXlink :: rest => !xlink && okFrom seen keys ns true rest

/-- The attribute list of a typed element is right by its keys: every attribute is one the
element takes, and no key repeats. One pass, which reads no name. -/
def allOk (attrs : List (SvgAttr t)) : Bool := okFrom .empty [] false false attrs

/-! ## A key and its name -/

/-- The name that `toPair` writes is the name of the attribute's key. -/
theorem toPair_fst (p : SvgAttr t) : p.toPair.1 = p.key.name := by
  cases p <;> rfl

/-- The characters of a custom data attribute's name: `data-`, then the key. -/
theorem Key.toList_name_data (k : String) :
    (Key.data k).name.toList = 'd' :: 'a' :: 't' :: 'a' :: '-' :: k.toList := by
  show ("data-" ++ k).toList = _
  rw [String.toList_append]
  rfl

/-- A key whose name is the name of an attribute of the schema is that attribute. No attribute
of the schema is named `xmlns` or `xmlns:xlink`, and none opens with `data-`. -/
theorem Key.eq_attr_of_name {k : Key} {a : Attr} (h : k.name = a.name) : k = .attr a := by
  have hread : Attr.ofChars? k.name.toList = some a := by
    rw [h, Attr.name, String.toList_ofList, Attr.ofChars?_chars]
  cases k with
  | attr b =>
    rw [show (Key.attr b).name.toList = b.chars from String.toList_ofList,
      Attr.ofChars?_chars] at hread
    exact congrArg Key.attr (Option.some.inj hread)
  | data k =>
    rw [Key.toList_name_data, Whatwg.Svg.Value.Attr.ofChars?_data] at hread
    exact nomatch hread
  | xmlns =>
    have hnone := SvgAttr.ofChars?_xmlns
    exact nomatch hnone.symm.trans hread
  | xmlnsXlink =>
    have hnone := SvgAttr.ofChars?_xmlnsXlink
    exact nomatch hnone.symm.trans hread

/-- The name is injective in the key: two keys with one name are one key. -/
theorem Key.name_injective {k k' : Key} (h : k.name = k'.name) : k = k' := by
  -- The name of a custom data attribute opens with `d`. A namespace declaration opens with `x`.
  have hdata : ∀ (key : String) {s : String}, s.toList.head? = some 'x' →
      (Key.data key).name ≠ s := by
    intro key s hs hname
    have hhead : (Key.data key).name.toList.head? = some 'x' := by rw [hname, hs]
    rw [Key.toList_name_data] at hhead
    exact absurd (Option.some.inj hhead) (by decide)
  cases k' with
  | attr a => exact eq_attr_of_name h
  | data key' =>
    cases k with
    | attr a => exact (eq_attr_of_name h.symm).symm
    | data key => exact congrArg Key.data ((String.append_right_inj "data-").mp h)
    | xmlns => exact absurd h.symm (hdata key' (by decide +kernel))
    | xmlnsXlink => exact absurd h.symm (hdata key' (by decide +kernel))
  | xmlns =>
    cases k with
    | attr a => exact (eq_attr_of_name h.symm).symm
    | data key => exact absurd h (hdata key (by decide +kernel))
    | xmlns => rfl
    | xmlnsXlink => exact absurd h (by decide)
  | xmlnsXlink =>
    cases k with
    | attr a => exact (eq_attr_of_name h.symm).symm
    | data key => exact absurd h (hdata key (by decide +kernel))
    | xmlns => exact absurd h (by decide)
    | xmlnsXlink => rfl

/-! ## The checker's test of one name -/

/-- The name of a key other than the two namespace declarations declares no namespace,
whatever the value. -/
theorem Key.namespaceAttrOk_name {k : Key} (hns : k ≠ .xmlns) (hxlink : k ≠ .xmlnsXlink)
    (value : String) : Content.namespaceAttrOk k.name value = false := by
  cases hok : Content.namespaceAttrOk k.name value with
  | false => rfl
  | true =>
    simp only [Content.namespaceAttrOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
    rcases hok with ⟨h, _⟩ | ⟨h, _⟩
    · exact absurd (Key.name_injective (k' := .xmlns) (String.toList_injective h)) hns
    · exact absurd (Key.name_injective (k' := .xmlnsXlink) (String.toList_injective h)) hxlink

/-- The checker's test of the name and the text that an attribute writes is the test of its
key. -/
theorem attrOk_toPair (p : SvgAttr t) :
    (Whatwg.Svg.Content.attrOk t p.toPair.1.toList ||
      Content.namespaceAttrOk p.toPair.1 p.toPair.2) = p.key.okOn t := by
  cases p with
  | attr a value =>
    -- No attribute of the schema has a custom data attribute's name.
    have hdata : Whatwg.Svg.Content.isDataName a.chars = false := by
      have hread := Attr.ofChars?_chars a
      generalize a.chars = s at hread
      unfold Whatwg.Svg.Content.isDataName
      split
      · rw [Whatwg.Svg.Value.Attr.ofChars?_data] at hread
        exact nomatch hread
      · rfl
    show (Whatwg.Svg.Content.attrOk t (Key.attr a).name.toList ||
      Content.namespaceAttrOk (Key.attr a).name _) = t.attrs.mem a
    rw [Key.namespaceAttrOk_name (k := .attr a) nofun nofun, Bool.or_false,
      show (Key.attr a).name.toList = a.chars from String.toList_ofList,
      Whatwg.Svg.Content.attrOk, hdata, Attr.ofChars?_chars, Bool.false_or]
  | data k value =>
    show (Whatwg.Svg.Content.attrOk t (Key.data k).name.toList ||
      Content.namespaceAttrOk (Key.data k).name value) = dataKeyOk k
    rw [Key.namespaceAttrOk_name (k := .data k) nofun nofun, Bool.or_false, Key.toList_name_data,
      Whatwg.Svg.Content.attrOk, Whatwg.Svg.Value.Attr.ofChars?_data, Bool.or_false, dataKeyOk]
    cases k.toList <;> rfl
  | xmlns =>
    have hns : Content.namespaceAttrOk "xmlns" svgNamespace = true := by decide +kernel
    show (Whatwg.Svg.Content.attrOk t "xmlns".toList ||
      Content.namespaceAttrOk "xmlns" svgNamespace) = true
    rw [hns, Bool.or_true]
  | xmlnsXlink =>
    have hns : Content.namespaceAttrOk "xmlns:xlink" xlinkNamespace = true := by decide +kernel
    show (Whatwg.Svg.Content.attrOk t "xmlns:xlink".toList ||
      Content.namespaceAttrOk "xmlns:xlink" xlinkNamespace) = true
    rw [hns, Bool.or_true]

end SvgAttr

/-! ## A list with no repeat -/

/-- Erasing duplicates leaves no more elements than the list had. -/
theorem eraseDups_length_le {α : Type} [BEq α] (l : List α) :
    l.eraseDups.length ≤ l.length := by
  -- By induction on a bound of the length: the step erases from a filtered list.
  have bounded : ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.length ≤ l.length := by
    intro n
    induction n with
    | zero =>
      intro l h
      cases l with
      | nil => exact Nat.le_refl 0
      | cons a as => exact absurd h (Nat.not_succ_le_zero _)
    | succ n ih =>
      intro l h
      cases l with
      | nil => exact Nat.le_refl 0
      | cons a as =>
        have hfilter := List.length_filter_le (fun b => !b == a) as
        have hrest := ih (as.filter fun b => !b == a)
          (Nat.le_trans hfilter (Nat.le_of_succ_le_succ h))
        rw [List.eraseDups_cons, List.length_cons, List.length_cons]
        omega
  exact bounded l.length l (Nat.le_refl _)

/-- A list has as many elements after its duplicates are erased as before exactly when no
element repeats. -/
theorem eraseDups_length_eq_iff {α : Type} [BEq α] [LawfulBEq α] :
    ∀ l : List α, l.eraseDups.length = l.length ↔ l.Nodup
  | [] => ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | a :: as => by
    have hle := eraseDups_length_le (as.filter fun b => !b == a)
    have hfilter := List.length_filter_le (fun b => !b == a) as
    rw [List.eraseDups_cons, List.length_cons, List.length_cons, List.nodup_cons,
      Nat.add_right_cancel_iff]
    constructor
    · intro h
      have hall : ∀ b ∈ as, (!b == a) = true :=
        List.length_filter_eq_length_iff.mp (by omega)
      rw [List.filter_eq_self.mpr hall] at h
      refine ⟨fun hmem => ?_, (eraseDups_length_eq_iff as).mp h⟩
      have hself := hall a hmem
      rw [beq_self_eq_true] at hself
      exact Bool.noConfusion hself
    · intro ⟨hfresh, hnodup⟩
      have hall : ∀ b ∈ as, (!b == a) = true := by
        intro b hb
        rw [Bool.not_eq_true', beq_eq_false_iff_ne]
        intro hba
        exact hfresh (hba ▸ hb)
      rw [List.filter_eq_self.mpr hall]
      exact (eraseDups_length_eq_iff as).mpr hnodup

namespace SvgAttr

variable {t : Tag}

/-! ## The pass -/

/-- One step of the pass, in the words of the keys met. `isMet` is the state's test of the key
of `p`. `tail` is the pass over the rest, from the state that holds that key too. -/
theorem okFrom_step (met : Key → Prop) (p : SvgAttr t) {rest : List (SvgAttr t)}
    {isMet tail : Bool} (hmet : isMet = true ↔ met p.key)
    (htail : tail = true ↔ (∀ q ∈ rest, q.key.okOn t = true) ∧ (rest.map key).Nodup ∧
      ∀ q ∈ rest, ¬(met q.key ∨ p.key = q.key)) :
    (p.key.okOn t && !isMet && tail) = true ↔
      (∀ q ∈ p :: rest, q.key.okOn t = true) ∧ ((p :: rest).map key).Nodup ∧
        ∀ q ∈ p :: rest, ¬met q.key := by
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, hmet, htail]
  simp only [List.forall_mem_cons, List.map_cons, List.nodup_cons, List.mem_map]
  constructor
  · intro ⟨⟨hok, hnew⟩, hoks, hnodup, hrest⟩
    exact ⟨⟨hok, hoks⟩, ⟨fun ⟨q, hq, hkey⟩ => hrest q hq (Or.inr hkey.symm), hnodup⟩, hnew,
      fun q hq hm => hrest q hq (Or.inl hm)⟩
  · intro ⟨⟨hok, hoks⟩, ⟨hfresh, hnodup⟩, hnew, hrest⟩
    exact ⟨⟨hok, hnew⟩, hoks, hnodup,
      fun q hq h => h.elim (hrest q hq) fun hkey => hfresh ⟨q, hq, hkey.symm⟩⟩

/-- The pass from any state, where `met` says which keys the state holds. It holds exactly when
the element takes every attribute, no key of the list repeats, and no key of the list was met
before. -/
theorem okFrom_iff {met : Key → Prop} {seen : Mask Attr} {keys : List String} {ns xlink : Bool}
    (hattr : ∀ a, seen.mem a = true ↔ met (.attr a)) (hdata : ∀ k, k ∈ keys ↔ met (.data k))
    (hns : ns = true ↔ met .xmlns) (hxlink : xlink = true ↔ met .xmlnsXlink)
    (attrs : List (SvgAttr t)) :
    okFrom seen keys ns xlink attrs = true ↔
      (∀ p ∈ attrs, p.key.okOn t = true) ∧ (attrs.map key).Nodup ∧ ∀ p ∈ attrs, ¬met p.key := by
  induction attrs generalizing met seen keys ns xlink with
  | nil =>
    exact ⟨fun _ => ⟨(fun _ h => nomatch h), List.nodup_nil, (fun _ h => nomatch h)⟩,
      fun _ => rfl⟩
  | cons p rest ih =>
    -- In each case the next state holds the keys met and the key of `p`.
    cases p with
    | attr a value =>
      exact okFrom_step met (.attr a value) (hattr a)
        (ih (met := fun k => met k ∨ Key.attr a = k)
          (fun b => by rw [Mask.mem_insert, hattr b, Key.attr.injEq])
          (fun k => (hdata k).trans (or_iff_left nofun).symm)
          (hns.trans (or_iff_left nofun).symm) (hxlink.trans (or_iff_left nofun).symm))
    | data k value =>
      exact okFrom_step met (.data k value) (List.contains_iff_mem.trans (hdata k))
        (ih (met := fun k' => met k' ∨ Key.data k = k')
          (fun b => (hattr b).trans (or_iff_left nofun).symm)
          (fun k' => by rw [List.mem_cons, hdata k', Key.data.injEq, or_comm, eq_comm])
          (hns.trans (or_iff_left nofun).symm) (hxlink.trans (or_iff_left nofun).symm))
    | xmlns =>
      exact okFrom_step met .xmlns hns
        (ih (met := fun k => met k ∨ Key.xmlns = k)
          (fun b => (hattr b).trans (or_iff_left nofun).symm)
          (fun k => (hdata k).trans (or_iff_left nofun).symm)
          (iff_of_true rfl (Or.inr rfl)) (hxlink.trans (or_iff_left nofun).symm))
    | xmlnsXlink =>
      exact okFrom_step met .xmlnsXlink hxlink
        (ih (met := fun k => met k ∨ Key.xmlnsXlink = k)
          (fun b => (hattr b).trans (or_iff_left nofun).symm)
          (fun k => (hdata k).trans (or_iff_left nofun).symm)
          (hns.trans (or_iff_left nofun).symm) (iff_of_true rfl (Or.inr rfl)))

/-- What the pass decides: the element takes every attribute, and no key repeats. -/
theorem allOk_iff (attrs : List (SvgAttr t)) :
    allOk attrs = true ↔ (∀ p ∈ attrs, p.key.okOn t = true) ∧ (attrs.map key).Nodup := by
  -- The empty state holds no key.
  have h := okFrom_iff (t := t) (met := fun _ => False) (seen := .empty) (keys := [])
    (ns := false) (xlink := false) (fun a => by rw [Mask.mem_empty]; exact ⟨nofun, False.elim⟩)
    (fun _ => ⟨nofun, False.elim⟩) ⟨nofun, False.elim⟩ ⟨nofun, False.elim⟩ attrs
  rw [allOk, h]
  exact ⟨fun ⟨hok, hnodup, _⟩ => ⟨hok, hnodup⟩, fun ⟨hok, hnodup⟩ => ⟨hok, hnodup, fun _ _ => id⟩⟩

/-- The law of the pass: the checker's test of the pairs that a typed attribute list writes is
the pass over its keys. -/
theorem svgAttrsOk_toPairs (attrs : List (SvgAttr t)) :
    Content.svgAttrsOk t (attrs.map toPair) = allOk attrs := by
  have hnames : (attrs.map toPair).map (·.1) = (attrs.map key).map Key.name := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun p _ => toPair_fst p
  have hlen : (attrs.map toPair).length = ((attrs.map key).map Key.name).length := by
    rw [List.length_map, List.length_map, List.length_map]
  -- The names repeat exactly when the keys do: the name is injective in the key.
  have hnodup : ((attrs.map key).map Key.name).Nodup ↔ (attrs.map key).Nodup :=
    List.pairwise_map.trans
      ⟨List.Pairwise.imp fun h e => h (congrArg Key.name e),
        List.Pairwise.imp fun h e => h (Key.name_injective e)⟩
  rw [Bool.eq_iff_iff, allOk_iff, Content.svgAttrsOk, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq, hnames, hlen, eraseDups_length_eq_iff, hnodup, List.forall_mem_map]
  simp only [attrOk_toPair]

end SvgAttr

end Whatwg.Html
