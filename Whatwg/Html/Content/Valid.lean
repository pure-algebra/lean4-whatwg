import Whatwg.Html.Content.Admission
import Whatwg.Html.Content.Sequence

/-!
# Whatwg.Html.Content.Valid

The content model as one decidable checker over raw trees (ruling HP-13):
`validIn ctx n` says the raw node `n` may stand at the position `ctx` and its
subtree is valid, and `Doc ctx` is the raw trees the checker accepts. This
is the definition the typed tree of `Whatwg.Html.Node.Typed` is proven sound
against (`Element.valid`), the definition a parser's output will be checked
by, and the definition the print theorems apply to.

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

/-! ## The checker -/

mutual
/-- The raw node may stand at the position and its subtree is valid. -/
def validIn (ctx : Ctx) : RawNode → Bool
  | .element name attrs children =>
    match Tag.ofName? name with
    | some t => ctx.admitsWith t attrs && attrsOk t attrs && seqOk (ctx.child t) t children && validAll (ctx.child t) children
    | none => false
  | .text _ => ctx.admits .pcdata
  | .entity _ => ctx.admits .pcdata
  | .comment _ => ctx.base != .nothing
/-- Every node of the list is valid at the position. -/
def validAll (ctx : Ctx) : List RawNode → Bool
  | [] => true
  | n :: ns => validIn ctx n && validAll ctx ns
end

/-- The two obligations of an element at once: its attributes and its ordered
model. One auto-parameter per combinator instead of two (performance review
§6). -/
def elementOk (c : Ctx) (t : Tag) (attrs : List (String × String)) (children : List RawNode) : Bool :=
  attrsOk t attrs && seqOk (c.child t) t children

theorem elementOk_iff (c : Ctx) (t : Tag) (attrs : List (String × String)) (children : List RawNode) :
    elementOk c t attrs children = true ↔ attrsOk t attrs = true ∧ seqOk (c.child t) t children = true := by
  simp [elementOk]

/-- The raw trees valid at a position. -/
def Doc (ctx : Ctx) : Type := { n : RawNode // validIn ctx n = true }

theorem validAll_nil (ctx : Ctx) : validAll ctx [] = true := rfl

theorem validAll_cons (ctx : Ctx) (n : RawNode) (ns : List RawNode)
    (h1 : validIn ctx n = true) (h2 : validAll ctx ns = true) : validAll ctx (n :: ns) = true := by
  simp [validAll, h1, h2]

theorem validAll_cons_iff (ctx : Ctx) (n : RawNode) (ns : List RawNode) :
    validAll ctx (n :: ns) = true ↔ validIn ctx n = true ∧ validAll ctx ns = true := by
  simp [validAll]

theorem validIn_text (ctx : Ctx) (s : String) (h : ctx.admits .pcdata = true) :
    validIn ctx (.text s) = true := by simp [validIn, h]

theorem validIn_entity (ctx : Ctx) (s : String) (h : ctx.admits .pcdata = true) :
    validIn ctx (.entity s) = true := by simp [validIn, h]

theorem validIn_element (ctx : Ctx) (t : Tag) (m : String) (hm : t.markupName = some m)
    (attrs : List (String × String)) (children : List RawNode)
    (h : ctx.admitsWith t attrs = true) (ha : attrsOk t attrs = true) (hs : seqOk (ctx.child t) t children = true)
    (hc : validAll (ctx.child t) children = true) :
    validIn ctx (.element m attrs children) = true := by
  simp [validIn, ofName?_markupName t m hm, h, ha, hs, hc]

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
      simp only [validIn] at h1
      cases hn : Tag.ofName? name with
      | none => simp [hn] at h1
      | some tag => simp [hn, void_child_admitsWith_none c t hv tag] at h1
    | text s => simp [validIn, void_child_admits_none c t hv] at h1
    | entity s => simp [validIn, void_child_admits_none c t hv] at h1
    | comment s =>
      simp [validIn, Ctx.child, void_not_transparent t hv, void_ownBase_nothing t hv] at h1

end Whatwg.Html.Content
