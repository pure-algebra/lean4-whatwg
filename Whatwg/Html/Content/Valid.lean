import Whatwg.Html.Content.Admission
import Whatwg.Html.Content.Sequence
import Whatwg.Html.Node.Walk
import Whatwg.Html.Svg

/-!
# Whatwg.Html.Content.Valid

The content model as one decidable checker over raw trees (ruling HP-13):
`validIn ctx n` says the raw node `n` may stand at the position `ctx` and its
subtree is valid, and `Doc ctx` is the raw trees the checker accepts. This
is the definition the typed tree of `Whatwg.Html.Node.Typed` is proven sound
against (`Element.valid`), the definition a parser's output will be checked
by, and the definition the print theorems apply to.

Since slice S3b of `docs/SVG-PACKAGE-PLAN.md` the checker is one algebra of
the walk of `Whatwg.Html.Node.Walk`: `check : Walk Pos Bool`, whose state is
the seam's position (`Whatwg.Html.Svg`). `validIn ctx n` is its run from the
HTML position `ctx`. A tree may hold an `svg` element where the position
admits the foreign tag `svg`, and the subtree below it is checked by the SVG
schema, back to HTML below `foreignObject`, `desc` and `title`. Two equations
bound the change: `validIn_element_eq` says that at an HTML element name the
checker is the conjunction it was, and `validIn_unknown` that any other name
but `svg` is refused. `validIn_svg` is the third case.

An element is valid at a position when its name is an element of the
standard, the position admits it given its attributes (`Ctx.admitsWith`:
an `a` without `href` is not interactive content), its attributes are
admitted on it with
values of the kinds the attribute index gives them and no name repeated,
its children follow its ordered model when it has one (`seqOk`), and every
child is valid at `ctx.child t`. Text and entities are valid where
the base names text; a comment is valid wherever the base is not `nothing`
(a void element, or an element whose content is nothing, holds no comment
in the HTML syntax). An element whose name is not the standard's is never
valid.

Attribute values: a boolean attribute takes the empty string or its own
name; a closed keyword list its keywords (and the empty string when the
index admits it); an integer or non-negative integer digits; anything else
any string. The custom data and ARIA prefixes are admitted on every
element with any value.
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema
open Whatwg.Html (RawNode)

/-! ## Attributes -/

/-! The string tests below are spelled over `String.toList`, because the
kernel evaluates these definitions (`html!` hands it `Eq.refl true`) and
`String.startsWith`, `String.all` and `String.isEmpty` reach byte-level
primitives it cannot unfold, while a literal's character list it can. -/

/-- Digits only, at least one. -/
def isDigitsList (cs : List Char) : Bool := !cs.isEmpty && cs.all Char.isDigit

/-- Digits only, at least one. -/
def isDigits (s : String) : Bool := isDigitsList s.toList

/-- The empty string. -/
def isEmptyStr (s : String) : Bool := s.toList.isEmpty

/-- `pre` begins `s`. -/
def hasPrefix (pre s : String) : Bool := pre.toList.isPrefixOf s.toList

/-- The index rows of an attribute that apply to an element: the rows
naming it, else the global rows. -/
def rowsFor (a : Attr) (t : Tag) : List AttrRow :=
  let rows := a.indexRows
  let named := rows.filter fun r => r.elements.contains t
  if named.isEmpty then rows.filter (·.global) else named

/-- The value conforms to the kind its row gives it. -/
def valueOk (a : Attr) (t : Tag) (markup value : String) : Bool :=
  match rowsFor a t with
  | [] => true
  | row :: _ =>
    match row.kind with
    | .boolean => isEmptyStr value || value == markup
    | .keywords false => row.keywords.contains value || (row.allowEmpty && isEmptyStr value)
    | .integer => isDigits value || (value.toList.head? == some '-' && isDigitsList (value.toList.drop 1))
    | .nonNegInteger => isDigits value
    | _ => true

/-- Why a value does not conform, in words; `none` when it does. -/
def valueProblem? (a : Attr) (t : Tag) (markup value : String) : Option String :=
  match rowsFor a t with
  | [] => none
  | row :: _ =>
    if valueOk a t markup value then none else
    match row.kind with
    | .boolean => some ("attribute `" ++ markup ++ "` is a boolean attribute: write it bare, or with the empty string or its own name as its value")
    | .keywords _ => some ("attribute `" ++ markup ++ "` on <" ++ t.markupText ++ "> takes one of "
        ++ ", ".intercalate (row.keywords.map fun k => "`" ++ k ++ "`")
        ++ (if row.allowEmpty then ", or the empty string" else "") ++ ", not `" ++ value ++ "`")
    | .integer => some ("attribute `" ++ markup ++ "` takes a valid integer, not `" ++ value ++ "`")
    | .nonNegInteger => some ("attribute `" ++ markup ++ "` takes a valid non-negative integer, not `" ++ value ++ "`")
    | _ => none

/-- The prefixed attributes, admitted on every element with any value. -/
def isPrefixed (name : String) : Bool := hasPrefix "data-" name || hasPrefix "aria-" name

/-- One attribute is admitted on the element with a conforming value. -/
def attrOk (t : Tag) (name value : String) : Bool :=
  isPrefixed name ||
  match Attr.ofName? name with
  | some a =>
    (match t.attribs? with
      | some set => set.contains a
      | none => false) && valueOk a t name value
  | none => false

/-- Why an attribute is not admitted, in words; `none` when it is. -/
def attrProblem? (t : Tag) (name value : String) : Option String :=
  if isPrefixed name then none else
  match Attr.ofName? name with
  | none => some ("unknown attribute `" ++ name ++ "`")
  | some a =>
    match t.attribs? with
    | none => some ("<" ++ t.markupText ++ "> takes no attributes")
    | some set =>
      if !set.contains a then
        some ("attribute `" ++ name ++ "` is not admitted on <" ++ t.markupText ++ ">: the attribute set `"
          ++ set.name ++ "` does not name it")
      else valueProblem? a t name value

/-- Every attribute is admitted with a conforming value, and no name repeats. -/
def attrsOk (t : Tag) (attrs : List (String × String)) : Bool :=
  attrs.all (fun p => attrOk t p.1 p.2) && (attrs.map (·.1)).eraseDups.length == attrs.length

/-! ## SVG attributes -/

/-- A namespace declaration that the HTML syntax allows on an SVG element: `xmlns` with the
SVG namespace, or `xmlns:xlink` with the XLink namespace (ruling SV-12). The tree
construction calls any other value a parse error ("create an element for a token"); the two
namespaces are those of the Infra Standard's section `namespaces`. -/
def namespaceAttrOk (name value : String) : Bool :=
  (name.toList == "xmlns".toList && value.toList == "http://www.w3.org/2000/svg".toList) ||
    (name.toList == "xmlns:xlink".toList &&
      value.toList == "http://www.w3.org/1999/xlink".toList)

/-- Every attribute is one the SVG element takes, or an allowed namespace declaration, and no
name repeats. A value is not judged before slice S4 (ruling SV-13). -/
def svgAttrsOk (t : Whatwg.Svg.Schema.Tag) (attrs : List (String × String)) : Bool :=
  attrs.all (fun p => Whatwg.Svg.Content.attrOk t p.1.toList || namespaceAttrOk p.1 p.2) &&
    (attrs.map (·.1)).eraseDups.length == attrs.length

/-- The SVG tag of an element node whose name is an SVG element's. -/
def RawNode.svgTag? : RawNode → Option Whatwg.Svg.Schema.Tag
  | .element name _ _ => Whatwg.Svg.Schema.Tag.ofChars? name.toList
  | _ => none

/-- The SVG tags of a child list: what a count of the SVG content model reads. -/
def svgChildTags (children : List RawNode) : List Whatwg.Svg.Schema.Tag :=
  children.filterMap RawNode.svgTag?

/-- The two obligations of an SVG element apart from its admission: its attributes and the
counts of its content model. -/
def svgElementOk (t : Whatwg.Svg.Schema.Tag) (attrs : List (String × String))
    (children : List RawNode) : Bool :=
  svgAttrsOk t attrs && Whatwg.Svg.Content.boundsOk t (svgChildTags children)

/-! ## The checker -/

namespace Pos

/-- The test of one element at a position: the position admits it, and its own obligations
hold. It reads the children's names and no subtree. -/
def elementOk : Pos → String → List (String × String) → List RawNode → Bool
  | .html c, name, attrs, children =>
    match Tag.ofName? name with
    | some t => c.admitsWith t attrs && attrsOk t attrs && seqOk (c.child t) t children
    | none =>
      match Tag.ofForeignName? name with
      | some .svg => c.admitsWith .svg attrs && svgElementOk .svg attrs children
      | _ => false
  | .svg c _, name, attrs, children =>
    match Whatwg.Svg.Schema.Tag.ofChars? name.toList with
    | some t => c.admits t && svgElementOk t attrs children
    | none => false

/-- Character data may stand at the position. -/
def textOk : Pos → Bool
  | .html c => c.admits .pcdata
  | .svg c _ => c.admitsText

/-- A comment may stand at the position: anywhere in SVG, and in HTML wherever the base is
not `nothing`. -/
def commentOk : Pos → Bool
  | .html c => c.base != .nothing
  | .svg _ _ => true

end Pos

/-- Node X2: the test of an element is antitone in the HTML exclusions of its position, in
both namespaces. Larger exclusions refuse more, and never admit more. -/
theorem Pos.elementOk_antitone {x y : Exclusions} (h : x.le y = true) (p : Pos) (name : String)
    (attrs : List (String × String)) (children : List RawNode)
    (hy : (p.withExcl y).elementOk name attrs children = true) :
    (p.withExcl x).elementOk name attrs children = true := by
  cases p with
  | svg c z => exact hy
  | html c =>
    simp only [Pos.withExcl, Pos.elementOk] at hy ⊢
    cases ht : Tag.ofName? name with
    | some t =>
      simp only [ht, Bool.and_eq_true] at hy ⊢
      exact ⟨⟨admitsWith_antitone h c.base c.extra t attrs hy.1.1, hy.1.2⟩, hy.2⟩
    | none =>
      simp only [ht] at hy ⊢
      split at hy
      · next hf =>
        simp only [Bool.and_eq_true] at hy ⊢
        exact ⟨admitsWith_antitone h c.base c.extra .svg attrs hy.1, hy.2⟩
      · exact Bool.noConfusion hy

/-- The checker as an algebra of the walk: a node's test, and every child's result. -/
def check : Walk Pos Bool where
  step := Pos.child
  element := fun p name attrs children results =>
    p.elementOk name attrs children && results.all id
  text := fun p _ => p.textOk
  entity := fun p _ => p.textOk
  comment := fun p _ => p.commentOk

/-- The raw node may stand at the position and its subtree is valid. -/
def validAt (p : Pos) (n : RawNode) : Bool := check.run p n

/-- Every node of the list is valid at the position. -/
def validAllAt (p : Pos) (ns : List RawNode) : Bool := (check.runAll p ns).all id

/-- The raw node may stand at the HTML position and its subtree is valid. -/
def validIn (ctx : Ctx) (n : RawNode) : Bool := validAt (.html ctx) n

/-- Every node of the list is valid at the HTML position. -/
def validAll (ctx : Ctx) (ns : List RawNode) : Bool := validAllAt (.html ctx) ns

/-- The two obligations of an element at once: its attributes and its ordered
model. One auto-parameter per combinator instead of two (performance review
§6). -/
def elementOk (c : Ctx) (t : Tag) (attrs : List (String × String)) (children : List RawNode) : Bool :=
  attrsOk t attrs && seqOk (c.child t) t children

theorem elementOk_iff (c : Ctx) (t : Tag) (attrs : List (String × String)) (children : List RawNode) :
    elementOk c t attrs children = true ↔ attrsOk t attrs = true ∧ seqOk (c.child t) t children = true := by
  simp only [elementOk, Bool.and_eq_true]

/-- The raw trees valid at a position. -/
def Doc (ctx : Ctx) : Type := { n : RawNode // validIn ctx n = true }

/-! ## The checker at each kind of node -/

theorem validAt_element (p : Pos) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    validAt p (.element name attrs children) =
      (p.elementOk name attrs children && validAllAt (p.child name) children) := by
  simp only [validAt, validAllAt, Walk.run_element, check]

theorem validAllAt_nil (p : Pos) : validAllAt p [] = true := by
  simp only [validAllAt, Walk.runAll_nil, List.all_nil]

theorem validAllAt_cons (p : Pos) (n : RawNode) (ns : List RawNode) :
    validAllAt p (n :: ns) = (validAt p n && validAllAt p ns) := by
  simp only [validAllAt, validAt, Walk.runAll_cons, List.all_cons, id]

theorem validAt_text (p : Pos) (s : String) : validAt p (.text s) = p.textOk := by
  simp only [validAt, Walk.run, check]

theorem validAt_entity (p : Pos) (s : String) : validAt p (.entity s) = p.textOk := by
  simp only [validAt, Walk.run, check]

theorem validAt_comment (p : Pos) (s : String) : validAt p (.comment s) = p.commentOk := by
  simp only [validAt, Walk.run, check]

/-- Node C1: at the name of an HTML element, the checker is the conjunction it was before the
seam: the admission, the attributes, the ordered model, and every child. -/
theorem validIn_element_eq (ctx : Ctx) {name : String} {t : Tag} (h : Tag.ofName? name = some t)
    (attrs : List (String × String)) (children : List RawNode) :
    validIn ctx (.element name attrs children) =
      (ctx.admitsWith t attrs && attrsOk t attrs && seqOk (ctx.child t) t children &&
        validAll (ctx.child t) children) := by
  simp only [validIn, validAll, validAt_element, Pos.elementOk, h, Pos.child_html_element h]

/-- Node C2: a name that is neither an HTML element nor `svg` is refused. -/
theorem validIn_unknown (ctx : Ctx) {name : String} (h : Tag.ofName? name = none)
    (hf : Tag.ofForeignName? name ≠ some .svg) (attrs : List (String × String))
    (children : List RawNode) : validIn ctx (.element name attrs children) = false := by
  simp only [validIn, validAt_element, Pos.elementOk, h, Bool.false_and]

/-- The third case: at `svg`, the position admits the foreign tag, the element's own
obligations hold under the SVG schema, and every child is valid at the SVG position. -/
theorem validIn_svg (ctx : Ctx) {name : String} (h : Tag.ofName? name = none)
    (hf : Tag.ofForeignName? name = some .svg) (attrs : List (String × String))
    (children : List RawNode) :
    validIn ctx (.element name attrs children) =
      (ctx.admitsWith .svg attrs && svgElementOk .svg attrs children &&
        validAllAt (.svg (Whatwg.Svg.Content.Ctx.outside.child .svg) (ctx.child .svg).excl)
          children) := by
  simp only [validIn, validAt_element, Pos.elementOk, h, hf, Pos.child_html_svg h hf]

theorem validAll_nil (ctx : Ctx) : validAll ctx [] = true := validAllAt_nil _

theorem validAll_cons_iff (ctx : Ctx) (n : RawNode) (ns : List RawNode) :
    validAll ctx (n :: ns) = true ↔ validIn ctx n = true ∧ validAll ctx ns = true := by
  simp only [validAll, validIn, validAllAt_cons, Bool.and_eq_true]

theorem validAll_cons (ctx : Ctx) (n : RawNode) (ns : List RawNode)
    (h1 : validIn ctx n = true) (h2 : validAll ctx ns = true) : validAll ctx (n :: ns) = true :=
  (validAll_cons_iff ctx n ns).mpr ⟨h1, h2⟩

theorem validIn_text (ctx : Ctx) (s : String) (h : ctx.admits .pcdata = true) :
    validIn ctx (.text s) = true := by
  simp only [validIn, validAt_text, Pos.textOk, h]

theorem validIn_entity (ctx : Ctx) (s : String) (h : ctx.admits .pcdata = true) :
    validIn ctx (.entity s) = true := by
  simp only [validIn, validAt_entity, Pos.textOk, h]

theorem validIn_element (ctx : Ctx) (t : Tag) (m : String) (hm : t.markupName = some m)
    (attrs : List (String × String)) (children : List RawNode)
    (h : ctx.admitsWith t attrs = true) (ha : attrsOk t attrs = true) (hs : seqOk (ctx.child t) t children = true)
    (hc : validAll (ctx.child t) children = true) :
    validIn ctx (.element m attrs children) = true := by
  rw [validIn_element_eq ctx (ofName?_markupName t m hm), h, ha, hs, hc]
  rfl

/-- A void element has no valid children at all. -/
theorem validAll_void_nil (c : Ctx) (t : Tag) (hv : t.isVoid = true) (children : List RawNode)
    (h : validAll (c.child t) children = true) : children = [] := by
  cases children with
  | nil => rfl
  | cons n ns =>
    exfalso
    have h1 := (validAll_cons_iff _ _ _).mp h |>.1
    cases n with
    | element name attrs cs =>
      cases hn : Tag.ofName? name with
      | some tag =>
        rw [validIn_element_eq _ hn, void_child_admitsWith_none c t hv tag] at h1
        exact Bool.noConfusion h1
      | none =>
        cases hd : decide (Tag.ofForeignName? name = some .svg) with
        | true =>
          rw [validIn_svg _ hn (of_decide_eq_true hd), void_child_admitsWith_none c t hv .svg] at h1
          exact Bool.noConfusion h1
        | false =>
          rw [validIn_unknown _ hn (of_decide_eq_false hd)] at h1
          exact Bool.noConfusion h1
    | text s =>
      rw [validIn, validAt_text, Pos.textOk, void_child_admits_none c t hv] at h1
      exact Bool.noConfusion h1
    | entity s =>
      rw [validIn, validAt_entity, Pos.textOk, void_child_admits_none c t hv] at h1
      exact Bool.noConfusion h1
    | comment s =>
      rw [validIn, validAt_comment] at h1
      simp only [Pos.commentOk, Ctx.child, void_not_transparent t hv, void_ownBase_nothing t hv,
        Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at h1

end Whatwg.Html.Content