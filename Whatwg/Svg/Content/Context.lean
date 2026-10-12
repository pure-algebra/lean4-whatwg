import Whatwg.Svg.Schema.Universe

/-!
# Whatwg.Svg.Content.Context

Owner: the position in an SVG subtree, its transition, and the judgments of one node (point T3
of `docs/SVG-PACKAGE-PLAN.md`, section 3.1; slice S3a). The seam `Whatwg/Html/Svg.lean` makes
this position one summand of the walk's state.

A content model is a set of tags with a text bit. The SVG `a` element is transparent: its
sealed sentence admits "any element or text allowed by its parent's content model, except for
another a element", and under a `switch` it reads the model of "the nearest ancestor that isn't
a switch". So a position holds two models. `model` is what the children of the position's
element may be. `outer` is the model in force at the nearest ancestor-or-self that is not a
`switch`. An inheriting child reads `outer` in both of the sentence's cases: its parent's
model is `outer` when the parent is no `switch`, and the skipped model is `outer` when it is.

"Except for another a element" removes `a` from the model of that `a`. It excludes no
descendant: the model of a `g` inside the `a` lists `a` again. This is the seat's reading of
the sentence, and `child_model_mem` states it.

The judgments of one node take no tree: `Ctx.admits`, `Ctx.admitsText`, `boundsOk` and
`attrOk`. The value of an attribute is not judged here (ruling SV-13).

What this module does not claim: that the definitions' index is the whole content model of
SVG 2. A sentence of a chapter that narrows a model is not read, apart from the four readings
of `Whatwg/Svg/Schema/Readings.lean`.
-/

namespace Whatwg.Svg.Content

open Whatwg.Svg.Data
open Whatwg.Svg.Schema

/-- What may stand at a position: the admitted elements, and whether character data may. -/
structure Content where
  tags : Mask Tag
  text : Bool
  deriving DecidableEq, Repr, Inhabited

namespace Content

/-- Nothing may stand. -/
def none : Content := ⟨.empty, false⟩

/-- What either admits. -/
def union (a b : Content) : Content := ⟨a.tags.union b.tags, a.text || b.text⟩

/-- The content without the elements of a set. -/
def without (a : Content) (m : Mask Tag) : Content := ⟨a.tags.diff m, a.text⟩

end Content

/-- The content that an element's own model states. -/
def own (t : Tag) : Content := ⟨t.model.tags, t.model.text⟩

/-- A position in an SVG subtree. `model` is what the children of the position's element may
be. `outer` is the model in force at the nearest ancestor-or-self that is not an element of
`handsOn`: at this pin, that is not a `switch`. -/
structure Ctx where
  model : Content
  outer : Content
  deriving DecidableEq, Repr, Inhabited

namespace Ctx

/-- Where an outermost `svg` stands: no SVG model is in force. The children of that `svg`
stand at `Ctx.outside.child .svg`. -/
def outside : Ctx := ⟨.none, .none⟩

/-- The position of an element's children: the element's own content, with the outer model
if the element inherits, and without what the element removes. An element of `handsOn` keeps
the outer model for its own children. -/
def child (c : Ctx) (t : Tag) : Ctx :=
  let inherited : Content := if t.model.inherits then c.outer else .none
  let model : Content := ((own t).union inherited).without t.model.excluded
  { model, outer := if handsOn.mem t then c.outer else model }

/-- The element may stand at the position. -/
def admits (c : Ctx) (t : Tag) : Bool := c.model.tags.mem t

/-- Character data may stand at the position. -/
def admitsText (c : Ctx) : Bool := c.model.text

end Ctx

/-- Each interval of the element's model holds the count of the children that it names. The
test reads the multiset of the children's tags, in no order. -/
def boundsOk (t : Tag) (children : List Tag) : Bool :=
  t.model.bounds.all fun b =>
    decide (b.atLeast ≤ b.tags.count children) && decide (b.tags.count children ≤ b.atMost)

/-- A character that the name of a custom data attribute may hold after `data-`. The HTML
Standard asks that the name is a valid attribute local name and holds no ASCII upper-case
letter: so no ASCII white space, no NUL, and none of `/`, `=` and `>`. The three characters
`"`, `'` and `<` are refused as well: the syntax of an attribute name in markup has none of
them, and a name that held one would not be written as one attribute. -/
def dataNameChar (c : Char) : Bool :=
  !c.isUpper &&
    !(c == ' ' || c == '\t' || c == '\n' || c == '\x0c' || c == '\r' || c == '\x00' ||
      c == '"' || c == '\'' || c == '/' || c == '<' || c == '=' || c == '>')

/-- A custom data attribute's name: `data-`, then at least one character, each a
`dataNameChar`. Every SVG element takes one (`master/struct.html`, `DataAttributes`, which
cites the HTML requirement on the name). -/
def isDataName : List Char → Bool
  | 'd' :: 'a' :: 't' :: 'a' :: '-' :: c :: rest => (c :: rest).all dataNameChar
  | _ => false

/-- The element takes an attribute of this name: a custom data attribute, or an attribute
that the definitions give to the element. -/
def attrOk (t : Tag) (name : List Char) : Bool :=
  isDataName name ||
    match Attr.ofChars? name with
    | some a => t.attrs.mem a
    | none => false

/-! ## What the transition does to membership -/

/-- The children's model, read as membership: an element may be a child when the parent's own
model names it, or the parent inherits and the outer model names it, and the parent does not
remove it. -/
theorem Ctx.child_model_mem (c : Ctx) (t u : Tag) :
    (c.child t).admits u =
      ((t.model.tags.mem u || (t.model.inherits && c.outer.tags.mem u)) &&
        !t.model.excluded.mem u) := by
  simp only [Ctx.admits, Ctx.child, Content.without, Content.union, own, Mask.mem_diff,
    Mask.mem_union]
  cases t.model.inherits
  · simp only [Bool.false_eq_true, ↓reduceIte, Content.none, Mask.mem_empty, Bool.or_false,
      Bool.false_and]
  · simp only [↓reduceIte, Bool.true_and]

/-- Character data below an element: the parent's own text bit, or the outer one if the
parent inherits. -/
theorem Ctx.child_admitsText (c : Ctx) (t : Tag) :
    (c.child t).admitsText = (t.model.text || (t.model.inherits && c.outer.text)) := by
  simp only [Ctx.admitsText, Ctx.child, Content.without, Content.union, own]
  cases t.model.inherits
  · simp only [Bool.false_eq_true, ↓reduceIte, Content.none, Bool.or_false, Bool.false_and]
  · simp only [↓reduceIte, Bool.true_and]

/-- An element of `handsOn` keeps the outer model for its children. -/
theorem Ctx.child_outer_of_handsOn (c : Ctx) (t : Tag) (h : handsOn.mem t = true) :
    (c.child t).outer = c.outer := by
  simp only [Ctx.child, h, ↓reduceIte]

/-- Any other element's own children's model is the outer model below it. -/
theorem Ctx.child_outer_of_not_handsOn (c : Ctx) (t : Tag) (h : handsOn.mem t = false) :
    (c.child t).outer = (c.child t).model := by
  simp only [Ctx.child, h, Bool.false_eq_true, ↓reduceIte]

/-- An element that neither inherits nor hands on gives its children one position, whatever
stands around it: that position reads the element's own model and nothing else. `svg`, `g`,
`defs`, `clipPath` and `text` are such elements. -/
theorem Ctx.child_eq_of_plain {t : Tag} (hi : t.model.inherits = false)
    (hh : handsOn.mem t = false) (c c' : Ctx) : c.child t = c'.child t := by
  simp only [Ctx.child, hi, hh, Bool.false_eq_true, ↓reduceIte]

/-- An element whose model states no count admits every multiset of children's tags. -/
theorem boundsOk_of_bounds_nil {t : Tag} (h : t.model.bounds = []) (children : List Tag) :
    boundsOk t children = true := by
  rw [boundsOk, h, List.all_nil]

end Whatwg.Svg.Content
