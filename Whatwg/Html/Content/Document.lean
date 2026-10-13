import Std.Data.HashMap
import Std.Data.HashSet
import Whatwg.Html.Content.Values

/-!
# Whatwg.Html.Content.Document

Owner: the rules that hold of a whole tree and of no single position (slice S17; entry W2 of
`docs/research/2026-10-12-whatwg-requests.md`). The checker `validIn` judges each node where it
stands. It cannot see that two elements carry one identifier, that a link names an identifier
no element has, that a page holds two `main` elements, or that a heading skips a level. This
module reads those facts from a raw tree and reports what is wrong with them, each problem at
the path of its element, as `Content.Refusal` locates a refused node.

What it gives:

- `facts`, the facts of a tree in tree order, each at its path: an identifier (`id`), a
  reference to an identifier, a `main` with whether it is hidden, a heading with its level. It
  is an algebra of the walk (`Whatwg/Html/Node/Walk.lean`), beside the checker; its state is
  the namespace. `ids`, `refs`, `mains` and `headings` are its four parts.
- `Problem`, one constructor for each kind of problem, and `problems`, the problems of a tree.
  `Problem.describe` writes one in words; `trail` writes a path as the names along it.
- `Problem.basis`, what the rule rests on: a requirement that a sealed text states, with the
  heading above its sentence; a convention of this module, which no sealed text states; or
  advice. `errors` are the problems of the first two classes, and `advice` the third.
- `Sound`, the plain statement that a tree has no error, and `Page`, a document that the
  checker accepts at the root and that is `Sound`.
- `Closed` and `ClosedAll`, the part of `Sound` that composes: a node, or a list of nodes,
  defines no identifier twice and refers only to identifiers it defines.

`Whatwg/Html/Content/Document/Laws.lean` proves that `errors` is empty exactly for a `Sound`
tree, and that two closed parts with no identifier in common make a closed whole.
`Whatwg/Html/Node/SvgDocument.lean` says what these facts are for a typed SVG tree.

`Content.Doc ctx` is something else: a raw tree that `validIn` accepts at one position. A
`Page` is a `Doc` at the root with the rules of this module besides.

## What each rule rests on

Requirements of the sealed HTML Standard (`vendor/whatwg-html-746f2ede/source`; the line of
each sentence at the pin is given):

- An identifier is unique, is not empty and holds no white space: "the `id` attribute value
  must be unique amongst all the IDs in the element's tree and must contain at least one
  character. The value must not contain any ASCII whitespace" (section "Global attributes",
  line 14407). The sentence speaks of HTML elements. For an SVG element the sealed chapter
  Document Structure of SVG 2 says the same (`vendor/w3c-svgwg-47e645ef/master/struct.html`,
  section "Attributes common to all elements: id", line 2130).
- `for` of `label` "must be the ID of a labelable element in the same tree" (section "The
  label element", line 49305). `list` of `input`, `form` of a listed element, `popovertarget`
  and `commandfor` are each the identifier of an element (lines 55663, 60626, 92903, 56718).
  Each token of `headers`, of `for` of `output` and of `itemref` is one too (lines 46994,
  59324, 81516). This module checks that the identifier exists. It does not check the rest of
  each sentence: that the element is labelable, a `datalist`, a `form`, a `th` of the same
  table, or has a `popover` attribute.
- "A document must not have more than one `main` element that does not have the `hidden`
  attribute specified" (section "The main element", line 22918).
- "Each heading following another heading lead in the outline must have a heading level that
  is less than, equal to, or 1 greater than lead's heading level" (section "Headings and
  outlines", line 20674). The outline is the headings in tree order, and a level is the
  computed heading level of section "Heading levels & offsets" (line 20718), which adds the
  `headingoffset` of every ancestor up to the nearest `headingreset`.

Advice of the same section: a document with a heading "should" have one of level 1 (line
20669).

Conventions of this module, which are not claims about a standard:

- A hyperlink `href="#x"` names an identifier. The standard says how a fragment is found
  (section "Scrolling to a fragment", line 112697: the identifier as written, then the
  identifier after percent-decoding, then `top`), and `Ref.NamesIn` follows those steps. It
  states no requirement that a fragment be found.
- Each token of `aria-labelledby` and of `aria-describedby` names an identifier. ARIA is not
  sealed in this repository: the rule is the consumer's.
- `url(#x)` in an SVG presentation attribute, and `href="#x"` on an SVG element, name an
  identifier. The linking chapter of SVG 2 is not sealed. The sealed chapter says only that a
  `use` whose reference is not resolved "is not rendered" (`struct.html`, line 627).

## What this module does not claim

- Anything `validIn` judges. A tree may pass here and be refused there, and the reverse.
- That an `href` is read as the URL Standard reads it. A reference is a value whose first
  character is `#`; white space before it, a `base` element that moves the document's address,
  and a relative address that happens to name this page are not read (entry W6).
- The obsolete `name` of `a`, which the standard's search for a fragment also accepts. The
  checker refuses that attribute, so a tree it accepts has none.
- A reference inside `style`, a quoted or padded `url( "#x" )`, a second paint after
  `url(#x)`, and the timing attributes of SVG animation.
- That every `main` stands where one may ("hierarchically correct", line 22922): that rule
  reads the accessible name of a `form`, which ARIA owns.
- `aria-level`, by which ARIA gives a heading another level: a level here is the standard's.
- The contents of a `template`. They are a `DocumentFragment` of their own and "have no
  conformance requirements" (section "The template element", line 69322), so nothing below a
  `template` is read.
- A cost in a tree of great depth. A fact is copied once at each ancestor, so the pass takes
  time in the number of nodes, and in the number of facts times the depth. A page is shallow.

`unescapeBytes` is the percent-decoding of the URL Standard, written again here because the
HTML library does not import the URL library. `Whatwg.Url.PercentEncoding.percentDecodeBytes`
is its owner, and `WhatwgTest/Html/Document.lean` holds the theorem that the two are one
function.
-/

namespace Whatwg.Html.Content.Document

open Whatwg.Html (RawNode Walk)
open Whatwg.Html.Schema (Condition)

/-! ## Reading a value -/

/-- ASCII white space, as the Infra Standard lists it: tab, line feed, form feed, carriage
return and space. -/
def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == Char.ofNat 0x0C

/-- The tokens of the characters `rest`, after the characters `word` of a token that has
begun, last first. -/
def tokensFrom : List Char → List Char → List String
  | word, [] => if word.isEmpty then [] else [String.ofList word.reverse]
  | word, c :: rest =>
    if isSpace c then
      if word.isEmpty then tokensFrom [] rest
      else String.ofList word.reverse :: tokensFrom [] rest
    else tokensFrom (c :: word) rest

/-- The tokens of a value that white space separates: what a list of identifiers holds. -/
def tokens (value : String) : List String := tokensFrom [] value.toList

/-- The fragment of a value that is a fragment alone: what follows `#`. A value that does not
begin with `#` gives none. -/
def fragmentOf? (value : String) : Option String :=
  match value.toList with
  | '#' :: rest => some (String.ofList rest)
  | _ => none

/-- The identifier of `url(#id)`, written exactly so: what stands between `url(#` and the last
`)`. Any other text gives none. -/
def urlTarget? (value : String) : Option String :=
  match value.toList with
  | 'u' :: 'r' :: 'l' :: '(' :: '#' :: rest =>
    match rest.reverse with
    | ')' :: body => some (String.ofList body.reverse)
    | _ => none
  | _ => none

/-- An identifier has at least one character and no white space. -/
def idOk (id : String) : Bool := !id.toList.isEmpty && id.toList.all fun c => !isSpace c

/-- The digits at the front of a list, read as a number in base ten after `acc`. -/
def leadingNat (acc : Nat) : List Char → Nat
  | [] => acc
  | c :: rest => if c.isDigit then leadingNat (acc * 10 + (c.toNat - 48)) rest else acc

/-- The standard's "rules for parsing non-negative integers" (section "Non-negative integers",
over "rules for parsing integers" of section "Signed integers"): white space is skipped, a
sign is read, the digits that follow are the number, and what follows them is ignored. A value
with no digit there, and a negative number, give none. -/
def parseNonNegative (value : String) : Option Nat :=
  match value.toList.dropWhile isSpace with
  | '-' :: c :: rest =>
    if c.isDigit && leadingNat 0 (c :: rest) == 0 then some 0 else none
  | '+' :: c :: rest => if c.isDigit then some (leadingNat 0 (c :: rest)) else none
  | c :: rest => if c.isDigit then some (leadingNat 0 (c :: rest)) else none
  | [] => none

/-! ## Percent-decoding -/

/-- A byte is an ASCII hexadecimal digit, in either case. -/
def isHex (b : UInt8) : Bool :=
  decide (0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39) || decide (0x41 ≤ b.toNat ∧ b.toNat ≤ 0x46) ||
    decide (0x61 ≤ b.toNat ∧ b.toNat ≤ 0x66)

/-- The value of a hexadecimal digit. -/
def hexValue (b : UInt8) : Nat :=
  if b.toNat ≤ 0x39 then b.toNat - 0x30
  else if b.toNat ≤ 0x46 then b.toNat - 0x37
  else b.toNat - 0x57

/-- The URL Standard's percent-decoding of bytes: `%` and two hexadecimal digits become one
byte, and every other byte stays. It is `Whatwg.Url.PercentEncoding.percentDecodeBytes`,
written again (see the header). -/
def unescapeBytes : List UInt8 → List UInt8
  | [] => []
  | [b] => [b]
  | [b, c] => [b, c]
  | b :: hi :: lo :: tail =>
    if b ≠ 0x25 then b :: unescapeBytes (hi :: lo :: tail)
    else if !(isHex hi && isHex lo) then b :: unescapeBytes (hi :: lo :: tail)
    else UInt8.ofNat (hexValue hi * 16 + hexValue lo) :: unescapeBytes tail

/-- A fragment with each `%XX` read as a byte, and the bytes read as UTF-8: steps 6 and 7 of
"select the indicated part". None when the bytes are no UTF-8; the standard's decoder would
put U+FFFD there, and no identifier is expected to hold that character. -/
def unescape (fragment : String) : Option String :=
  String.fromUTF8? (ByteArray.mk (unescapeBytes fragment.toUTF8.toList).toArray)

/-- The text is `top`, in any case of its letters. -/
def isTop (text : String) : Bool := text.toList.map Char.toLower == ['t', 'o', 'p']

/-! ## A reference -/

/-- How a reference names its identifier, which is also what the rule about it rests on. -/
inductive RefKind where
  /-- The fragment of a hyperlink: `href="#x"` on `a` or `area`, in HTML or in SVG. -/
  | fragment
  /-- An HTML attribute whose value is one identifier: `for` of `label`, `form`, `list`,
  `popovertarget`, `commandfor`. -/
  | idref
  /-- A token of an HTML attribute whose value is a list of identifiers: `headers`, `for` of
  `output`, `itemref`. -/
  | idrefs
  /-- A token of `aria-labelledby` or `aria-describedby`. -/
  | aria
  /-- `url(#x)` in a presentation attribute of an SVG element: `clip-path`, `mask`, `filter`,
  `fill`, `stroke` and the three marker properties. -/
  | svgUrl
  /-- `href="#x"` or `xlink:href="#x"` on an SVG element that is no hyperlink: `use`, a
  gradient, `textPath`. -/
  | svgHref
  deriving DecidableEq, Repr, Inhabited

/-- A reference: the element and the attribute that make it, its kind, and the identifier it
names, as written. -/
structure Ref where
  element : String
  attr : String
  kind : RefKind
  target : String
  deriving DecidableEq, Repr, Inhabited

namespace Ref

/-- The reference names something, given a test of what is an identifier. Every kind names the
identifier it writes. A fragment besides follows "select the indicated part": the empty
fragment is the top of the document; the fragment after percent-decoding may be an identifier;
and `top`, in any case, is the top of the document. -/
def namesBy (r : Ref) (known : String → Bool) : Bool :=
  known r.target ||
    (r.kind == .fragment &&
      (r.target == "" ||
        match unescape r.target with
        | some decoded => known decoded || isTop decoded
        | none => false))

/-- The reference names something among the identifiers `names`: the plain statement of
`namesBy`. -/
def NamesIn (r : Ref) (names : List String) : Prop :=
  r.target ∈ names ∨
    (r.kind = .fragment ∧
      (r.target = "" ∨ ∃ decoded, unescape r.target = some decoded ∧
        (decoded ∈ names ∨ isTop decoded = true)))

end Ref

/-! ## Facts -/

/-- A heading as its ancestors leave it: the level of its name, from 1 to 6; the sum of the
`headingoffset` read so far; and whether a `headingreset` was met, after which no ancestor
counts. -/
structure Level where
  base : Nat
  offset : Nat
  closed : Bool
  deriving DecidableEq, Repr, Inhabited

namespace Level

/-- The heading level: the level of the name and the offset, and 9 at most ("get an element's
computed heading level"). At the root of a tree every ancestor was read. -/
def value (l : Level) : Nat := min 9 (l.base + l.offset)

/-- The level after one more ancestor, with that ancestor's offset and whether it resets. -/
def under (offset : Nat) (reset : Bool) (l : Level) : Level :=
  if l.closed then l else ⟨l.base, l.offset + offset, reset⟩

end Level

/-- One fact of a document. -/
inductive Fact where
  /-- An element has this `id`. -/
  | ident (id : String)
  /-- An attribute refers to an identifier. -/
  | ref (r : Ref)
  /-- A `main` element, and whether it has the `hidden` attribute. -/
  | main (hidden : Bool)
  /-- A heading, `h1` to `h6`. -/
  | heading (level : Level)
  deriving DecidableEq, Repr, Inhabited

namespace Fact

/-- The identifier, when the fact is one. -/
def ident? : Fact → Option String
  | .ident id => some id
  | _ => none

/-- The reference, when the fact is one. -/
def ref? : Fact → Option Ref
  | .ref r => some r
  | _ => none

/-- Whether the `main` is hidden, when the fact is a `main`. -/
def main? : Fact → Option Bool
  | .main hidden => some hidden
  | _ => none

/-- The heading, when the fact is one. -/
def heading? : Fact → Option Level
  | .heading level => some level
  | _ => none

/-- The fact after one more ancestor: a heading takes the ancestor's offset, and nothing else
changes. -/
def under (offset : Nat) (reset : Bool) : Fact → Fact
  | .heading level => .heading (level.under offset reset)
  | fact => fact

end Fact

/-- A thing at the path of its element: the child indices from the root, as in
`Content.Refusal`. -/
structure Placed (α : Type) where
  path : List Nat
  it : α
  deriving DecidableEq, Repr, Inhabited

namespace Placed

variable {α β : Type}

/-- The same thing seen from the parent, whose child at `index` holds it. -/
def under (index : Nat) (p : Placed α) : Placed α := ⟨index :: p.path, p.it⟩

/-- A part of the thing, at the same path, when it has that part. -/
def pick (f : α → Option β) (p : Placed α) : Option (Placed β) := (f p.it).map fun b => ⟨p.path, b⟩

end Placed

/-! ## The facts of one element -/

/-- The identifier that an attribute gives its element. -/
def identOf? (attr : String × String) : Option String :=
  if attr.1 == "id" then some attr.2 else none

/-- The references of one attribute of an HTML element. -/
def htmlLinks (element : String) (attr : String × String) : List Ref :=
  let one (kind : RefKind) : List Ref := [⟨element, attr.1, kind, attr.2⟩]
  let each (kind : RefKind) : List Ref := (tokens attr.2).map fun t => ⟨element, attr.1, kind, t⟩
  match attr.1 with
  | "href" =>
    if element == "a" || element == "area" then
      (fragmentOf? attr.2).toList.map fun t => ⟨element, attr.1, .fragment, t⟩
    else []
  | "for" => if element == "label" then one .idref else if element == "output" then each .idrefs else []
  | "form" => one .idref
  | "list" => one .idref
  | "popovertarget" => one .idref
  | "commandfor" => one .idref
  | "headers" => each .idrefs
  | "itemref" => each .idrefs
  | "aria-labelledby" => each .aria
  | "aria-describedby" => each .aria
  | _ => []

/-- The references of one attribute of an SVG element. -/
def svgLinks (element : String) (attr : String × String) : List Ref :=
  let url : List Ref := (urlTarget? attr.2).toList.map fun t => ⟨element, attr.1, .svgUrl, t⟩
  let link : List Ref := (fragmentOf? attr.2).toList.map fun t =>
    ⟨element, attr.1, if element == "a" then .fragment else .svgHref, t⟩
  let each (kind : RefKind) : List Ref := (tokens attr.2).map fun t => ⟨element, attr.1, kind, t⟩
  match attr.1 with
  | "href" => link
  | "xlink:href" => link
  | "clip-path" => url
  | "mask" => url
  | "filter" => url
  | "fill" => url
  | "stroke" => url
  | "marker-start" => url
  | "marker-mid" => url
  | "marker-end" => url
  | "aria-labelledby" => each .aria
  | "aria-describedby" => each .aria
  | _ => []

/-- The references of one attribute, by the namespace of its element. -/
def linksOf (ns : Ns) (element : String) (attr : String × String) : List Ref :=
  match ns with
  | .html => htmlLinks element attr
  | .svg => svgLinks element attr

/-- The level of a heading's name. -/
def headingBase? (name : String) : Option Nat :=
  match name with
  | "h1" => some 1
  | "h2" => some 2
  | "h3" => some 3
  | "h4" => some 4
  | "h5" => some 5
  | "h6" => some 6
  | _ => none

/-- What an HTML element is besides its attributes: a `main`, or a heading. -/
def markFacts (element : String) (attrs : List (String × String)) : List Fact :=
  (if element == "main" then [Fact.main (Condition.lookup attrs "hidden").isSome] else []) ++
    match headingBase? element with
    | some base => [Fact.heading ⟨base, 0, false⟩]
    | none => []

/-- The facts of one element, from its namespace, its name and its attributes: each `id`, each
reference, and for an HTML element whether it is a `main` or a heading. -/
def ownFacts (ns : Ns) (element : String) (attrs : List (String × String)) : List Fact :=
  attrs.flatMap (fun attr =>
      (identOf? attr).toList.map Fact.ident ++ (linksOf ns element attr).map Fact.ref) ++
    match ns with
    | .html => markFacts element attrs
    | .svg => []

/-- The `headingoffset` of an element: its value read as a non-negative integer, and 0 when
the attribute is absent or is no such number. -/
def headingOffset (attrs : List (String × String)) : Nat :=
  ((Condition.lookup attrs "headingoffset").bind parseNonNegative).getD 0

/-- The element has `headingreset`. -/
def headingReset (attrs : List (String × String)) : Bool :=
  (Condition.lookup attrs "headingreset").isSome

/-- The facts of an element and of what stands below it, after the element itself is counted
as an ancestor of each heading among them. Only an HTML element has a heading offset. -/
def settle (ns : Ns) (attrs : List (String × String)) (facts : List (Placed Fact)) :
    List (Placed Fact) :=
  match ns with
  | .html => facts.map fun p => ⟨p.path, p.it.under (headingOffset attrs) (headingReset attrs)⟩
  | .svg => facts

/-- The facts of a list of children, each seen from the parent. `index` is the index of the
first child. -/
def gather : Nat → List (List (Placed Fact)) → List (Placed Fact)
  | _, [] => []
  | index, facts :: rest => facts.map (Placed.under index) ++ gather (index + 1) rest

/-- The children of this element are another tree: the contents of a `template`. -/
def holdsOtherTree (ns : Ns) (element : String) : Bool := ns == .html && element == "template"

/-! ## The facts of a tree -/

/-- The facts as an algebra of the walk: an element's own facts at the empty path, then those
of its children, each under its index. The state is the namespace an element stands in. -/
def factsWalk : Walk Ns (List (Placed Fact)) where
  step := Ns.step
  element := fun ns name attrs _ results =>
    settle (ns.ofElement name) attrs
      ((ownFacts (ns.ofElement name) name attrs).map (fun fact => ⟨[], fact⟩) ++
        if holdsOtherTree (ns.ofElement name) name then [] else gather 0 results)
  text := fun _ _ => []
  entity := fun _ _ => []
  comment := fun _ _ => []

/-- The facts of a node that stands in the namespace `ns`, in tree order. -/
def factsAt (ns : Ns) (node : RawNode) : List (Placed Fact) := factsWalk.run ns node

/-- The facts of a list of nodes that stand in `ns`, the first under `index`. -/
def factsAllAt (ns : Ns) (index : Nat) (nodes : List RawNode) : List (Placed Fact) :=
  gather index (factsWalk.runAll ns nodes)

/-- The facts of a tree, in tree order. -/
def facts (tree : RawNode) : List (Placed Fact) := factsAt .html tree

/-- The identifiers among some facts, each at the path of its element. -/
def idsOf (facts : List (Placed Fact)) : List (Placed String) :=
  facts.filterMap (Placed.pick Fact.ident?)

/-- The references among some facts, each at the path of its element. -/
def refsOf (facts : List (Placed Fact)) : List (Placed Ref) :=
  facts.filterMap (Placed.pick Fact.ref?)

/-- The `main` elements among some facts, each with whether it is hidden. -/
def mainsOf (facts : List (Placed Fact)) : List (Placed Bool) :=
  facts.filterMap (Placed.pick Fact.main?)

/-- The headings among some facts: the outline. -/
def headingsOf (facts : List (Placed Fact)) : List (Placed Level) :=
  facts.filterMap (Placed.pick Fact.heading?)

/-- The identifiers among some facts, as texts. -/
def namesOf (facts : List (Placed Fact)) : List String := facts.filterMap fun p => p.it.ident?

/-- The references among some facts, without their paths. -/
def linksIn (facts : List (Placed Fact)) : List Ref := facts.filterMap fun p => p.it.ref?

/-- The identifiers a tree defines, in tree order, each at the path of its element. -/
def ids (tree : RawNode) : List (Placed String) := idsOf (facts tree)

/-- The references a tree makes, in tree order. A list of identifiers gives one for each
token. -/
def refs (tree : RawNode) : List (Placed Ref) := refsOf (facts tree)

/-- The `main` elements of a tree, each with whether it has `hidden`. -/
def mains (tree : RawNode) : List (Placed Bool) := mainsOf (facts tree)

/-- The outline of a tree: its headings in tree order. `Level.value` is a heading's level. -/
def headings (tree : RawNode) : List (Placed Level) := headingsOf (facts tree)

/-- The identifiers a tree defines, as texts. -/
def names (tree : RawNode) : List String := namesOf (facts tree)

/-! ## Problems -/

/-- A sentence of a sealed text, by the text and the heading above the sentence. The header of
this module gives the line of each. -/
structure Anchor where
  text : String
  heading : String
  deriving DecidableEq, Repr, Inhabited

/-- A heading of the sealed HTML Standard. -/
def Anchor.html (heading : String) : Anchor := ⟨"HTML Standard", heading⟩

/-- What a rule rests on. -/
inductive Basis where
  /-- A sealed text states the rule as a requirement on a document. -/
  | requirement (stated : Anchor)
  /-- No sealed text states the rule: it is a convention of this module, for a link or a
  reference that would otherwise name nothing. -/
  | convention
  /-- A sealed text recommends it. -/
  | advice (stated : Anchor)
  deriving DecidableEq, Repr, Inhabited

/-- A requirement and a convention are errors; advice is not. -/
def Basis.isError : Basis → Bool
  | .advice _ => false
  | _ => true

/-- The section of the HTML Standard that requires the value of an attribute to be the
identifier of an element; none for an attribute this module does not read so. -/
def stated? (element attr : String) : Option Anchor :=
  match attr with
  | "for" =>
    if element == "label" then some (.html "The label element")
    else if element == "output" then some (.html "The output element")
    else none
  | "form" => some (.html "Association of controls and forms")
  | "list" => some (.html "The list attribute")
  | "popovertarget" => some (.html "The popover target attributes")
  | "commandfor" => some (.html "The button element")
  | "headers" => some (.html "Attributes common to td and th elements")
  | "itemref" => some (.html "Items")
  | _ => none

/-- What the rule "this reference names an identifier" rests on: a requirement for an HTML
attribute whose value the standard says is an identifier, and a convention for a fragment, for
ARIA and for SVG. -/
def Ref.basis (r : Ref) : Basis :=
  match r.kind, stated? r.element r.attr with
  | .idref, some anchor => .requirement anchor
  | .idrefs, some anchor => .requirement anchor
  | _, _ => .convention

/-- What is wrong with a tree, across it. -/
inductive Problem where
  /-- An `id` is empty or holds white space. -/
  | malformedId (path : List Nat) (id : String)
  /-- Two elements have one identifier: the first in tree order, and a later one. -/
  | duplicateId (id : String) (first second : List Nat)
  /-- A reference names no identifier of the tree. -/
  | dangling (path : List Nat) (ref : Ref)
  /-- A `main` that is not hidden stands after another: the first, and this one. -/
  | secondMain (first second : List Nat)
  /-- A heading is more than one level below the heading before it in the outline. -/
  | headingSkip (lead : List Nat) (leadLevel : Nat) (path : List Nat) (level : Nat)
  /-- The tree has headings and none of level 1. The path is the first heading's. -/
  | noTopHeading (first : List Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Problem

/-- Where the problem is: the later of two elements, where it names two. -/
def path : Problem → List Nat
  | .malformedId path _ => path
  | .duplicateId _ _ second => second
  | .dangling path _ => path
  | .secondMain _ second => second
  | .headingSkip _ _ path _ => path
  | .noTopHeading first => first

/-- What the rule rests on. -/
def basis : Problem → Basis
  | .malformedId _ _ => .requirement (.html "Global attributes")
  | .duplicateId _ _ _ => .requirement (.html "Global attributes")
  | .dangling _ ref => ref.basis
  | .secondMain _ _ => .requirement (.html "The main element")
  | .headingSkip _ _ _ _ => .requirement (.html "Headings and outlines")
  | .noTopHeading _ => .advice (.html "Headings and outlines")

/-- The problem is an error: its rule is a requirement or a convention, and not advice. -/
def isError (p : Problem) : Bool := p.basis.isError

/-- The problem in words, for a message. `place` writes a path; by default it writes the
child indices. No judgment reads this text. -/
def describe (p : Problem)
    (place : List Nat → String := fun path => "the child path " ++ toString path) : String :=
  match p with
  | .malformedId path id =>
    (if id == "" then "an `id` is empty" else "the identifier `" ++ id ++ "` holds white space") ++
      ": at " ++ place path
  | .duplicateId id first second =>
    "the identifier `" ++ id ++ "` is defined twice: at " ++ place first ++ " and at " ++
      place second
  | .dangling path ref =>
    (match ref.kind with
      | .fragment => "the link `#" ++ ref.target ++ "` names no identifier of the document"
      | .svgUrl =>
        "`" ++ ref.attr ++ "` of `" ++ ref.element ++ "` refers to `url(#" ++ ref.target ++
          ")`, and no element has that identifier"
      | .svgHref =>
        "`" ++ ref.attr ++ "` of `" ++ ref.element ++ "` refers to `#" ++ ref.target ++
          "`, and no element has that identifier"
      | _ =>
        "`" ++ ref.attr ++ "` of `" ++ ref.element ++ "` names `" ++ ref.target ++
          "`, and no element has that identifier") ++ ": at " ++ place path
  | .secondMain first second =>
    "a second `main` that is not hidden: at " ++ place second ++ ", after the one at " ++
      place first
  | .headingSkip lead leadLevel path level =>
    "a heading of level " ++ toString level ++ " follows one of level " ++ toString leadLevel ++
      ": at " ++ place path ++ ", after the heading at " ++ place lead
  | .noTopHeading first =>
    "no heading of the document has level 1: the first heading is at " ++ place first

end Problem

/-- The element names along a path, each below the root with its index among its parent's
children: `html/body[1]/main[2]`. -/
def namesAlong : RawNode → List Nat → List String
  | .element name _ _, [] => [name]
  | .element name _ children, index :: rest =>
    name ::
      match children[index]? with
      | some child =>
        match namesAlong child rest with
        | [] => []
        | first :: more => (first ++ "[" ++ toString index ++ "]") :: more
      | none => []
  | .text _, _ => []
  | .entity _, _ => []
  | .comment _, _ => []

/-- A path of a tree as the element names along it, for `Problem.describe`. -/
def trail (tree : RawNode) (path : List Nat) : String := "/".intercalate (namesAlong tree path)

/-! ## The check -/

/-- Each `id` that is empty or holds white space. -/
def malformed (ids : List (Placed String)) : List Problem :=
  (ids.filter fun d => !idOk d.it).map fun d => .malformedId d.path d.it

/-- Each identifier that was defined before, in one pass. `seen` holds every identifier met so
far, with the path of its first element. -/
def duplicatesFrom (seen : Std.HashMap String (List Nat)) : List (Placed String) → List Problem
  | [] => []
  | d :: rest =>
    match seen[d.it]? with
    | some first => .duplicateId d.it first d.path :: duplicatesFrom seen rest
    | none => duplicatesFrom (seen.insert d.it d.path) rest

/-- Each identifier that is defined a second time or more, with the path of its first
element. -/
def duplicates (ids : List (Placed String)) : List Problem := duplicatesFrom ∅ ids

/-- Each reference that names none of the identifiers. The identifiers are put in a set once,
so that a reference costs one look. -/
def dangling (names : List String) (refs : List (Placed Ref)) : List Problem :=
  let known := Std.HashSet.ofList names
  (refs.filter fun r => !r.it.namesBy known.contains).map fun r => .dangling r.path r.it

/-- Each `main` that is not hidden, after the first such. -/
def extraMains (mains : List (Placed Bool)) : List Problem :=
  match mains.filter fun m => !m.it with
  | [] => []
  | first :: rest => rest.map fun m => .secondMain first.path m.path

/-- Each heading that is more than one level below the heading before it. -/
def skips (headings : List (Placed Level)) : List Problem :=
  ((headings.zip headings.tail).filter fun p => p.1.it.value + 1 < p.2.it.value).map fun p =>
    .headingSkip p.1.path p.1.it.value p.2.path p.2.it.value

/-- The advice that an outline with a heading have one of level 1. -/
def topless (headings : List (Placed Level)) : List Problem :=
  match headings with
  | [] => []
  | first :: _ =>
    if headings.any fun h => h.it.value == 1 then [] else [.noTopHeading first.path]

/-- The problems of some facts: the identifiers that are malformed, those defined twice, the
references that name nothing, the second `main`, the headings that skip, and the advice. -/
def problemsOf (facts : List (Placed Fact)) : List Problem :=
  malformed (idsOf facts) ++ duplicates (idsOf facts) ++ dangling (namesOf facts) (refsOf facts) ++
    extraMains (mainsOf facts) ++ skips (headingsOf facts) ++ topless (headingsOf facts)

/-- The problems of a tree, across it. The tree is read once, and each identifier and each
reference is looked up once in a table. -/
def problems (tree : RawNode) : List Problem := problemsOf (facts tree)

/-- The problems that are errors: a requirement of a sealed text or a convention of this
module is not kept. A build fails on these. -/
def errors (tree : RawNode) : List Problem := (problems tree).filter Problem.isError

/-- The problems that are advice. A build prints these. -/
def advice (tree : RawNode) : List Problem := (problems tree).filter fun p => !p.isError

/-- The tree has no error across it. -/
def ok (tree : RawNode) : Bool := (errors tree).isEmpty

/-! ## The plain statement -/

/-- A tree has no error across it, stated on its facts with no table: every `id` is well
formed; no identifier is defined twice; every reference names an identifier; at most one
`main` is not hidden; and no heading is more than one level below the heading before it.
`ok_iff` of the laws says that `ok` decides this. -/
structure Sound (tree : RawNode) : Prop where
  wellFormed : ∀ d ∈ ids tree, idOk d.it = true
  distinct : (names tree).Nodup
  closed : ∀ r ∈ refs tree, r.it.NamesIn (names tree)
  oneMain : ((mains tree).filter fun m => !m.it).length ≤ 1
  steps : ∀ p ∈ (headings tree).zip (headings tree).tail, p.2.it.value ≤ p.1.it.value + 1

/-! ## A part of a document -/

/-- The identifiers that a node defines where it stands in `ns`, as texts. -/
def namesAt (ns : Ns) (node : RawNode) : List String := namesOf (factsAt ns node)

/-- The references that a node makes where it stands in `ns`, without their paths. -/
def linksAt (ns : Ns) (node : RawNode) : List Ref := linksIn (factsAt ns node)

/-- The identifiers that a list of nodes defines. -/
def namesAllAt (ns : Ns) (nodes : List RawNode) : List String := nodes.flatMap (namesAt ns)

/-- The references that a list of nodes makes. -/
def linksAllAt (ns : Ns) (nodes : List RawNode) : List Ref := nodes.flatMap (linksAt ns)

/-- A node is closed: it defines no identifier twice, and each of its references names an
identifier that it defines. A closed node asks nothing of the document around it but that its
identifiers be used nowhere else. -/
def Closed (ns : Ns) (node : RawNode) : Prop :=
  (namesAt ns node).Nodup ∧ ∀ r ∈ linksAt ns node, r.NamesIn (namesAt ns node)

/-- A list of nodes is closed, taken together: a reference of one may name an identifier of
another. -/
def ClosedAll (ns : Ns) (nodes : List RawNode) : Prop :=
  (namesAllAt ns nodes).Nodup ∧ ∀ r ∈ linksAllAt ns nodes, r.NamesIn (namesAllAt ns nodes)

/-! ## A checked document -/

/-- A document that the checker accepts at the root and that has no error across it. -/
structure Page where
  /-- The tree: an `html` element. -/
  tree : RawNode
  /-- Every node may stand where it stands. -/
  valid : validIn Ctx.document tree = true
  /-- The rules across the document hold. -/
  sound : Sound tree

/-- A page is a document of the checker. -/
def Page.toDoc (page : Page) : Doc Ctx.document := ⟨page.tree, page.valid⟩

end Whatwg.Html.Content.Document
