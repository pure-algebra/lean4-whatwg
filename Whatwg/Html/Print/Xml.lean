import Whatwg.Html.Node.Raw
import Whatwg.Html.Print.Xml.Productions
import Whatwg.Html.Svg

/-!
# Whatwg.Html.Print.Xml

Owner: the XML serialization of a tree (slice S8 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-40;
debt D104 of ruling R-S21). The printer of `Whatwg/Html/Print/Render.lean` writes the HTML
serialization, which is what a page holds. A file that holds one picture, `picture.svg`, is
XML, and this module writes that.

The authority is the section "XML Serialization" of DOM Parsing and Serialization, sealed at
`vendor/w3c-dom-parsing-aefb90de/index.html`: the pinned HTML Standard names "XML
serialization" and gives it to that document. Its algorithm is stated of a DOM, where each
element and each attribute has a namespace, a prefix and a local name. A tree of this package
holds written names, and the tree construction of the HTML Standard says which DOM they make:
an element below `svg` is in the SVG namespace, any other is in the HTML namespace, no element
has a prefix, and on an SVG element "adjust foreign attributes" places eleven names in a
namespace (`Whatwg.Html.Schema.Foreign.foreignAttrs`, generated from the sealed standard).
`nodeAt` is the algorithm at such a DOM. What each step becomes there:

- **The namespace of an element.** The algorithm's `namespace` is the default namespace in
  scope: none at the root, and the parent's namespace below an element. An element in that
  namespace is written by its name. An element in another one has no prefix and finds none in
  the prefix map, so the algorithm writes ` xmlns="…"` after its name, unless the element
  declares that same namespace itself with an `xmlns` attribute; then that attribute is
  written in its place among the others. So the root of a picture carries the SVG namespace,
  an HTML element below `foreignObject` the HTML namespace, and an `svg` inside it the SVG
  namespace again.
- **The prefix map.** It starts with `xml`. A tree that passes `ok` adds one prefix at most,
  `xlink` for the XLink namespace, by an `xmlns:xlink` attribute or by the algorithm itself:
  an attribute such as `xlink:href` on an element where `xlink` is not in the map is written
  after a generated ` xmlns:xlink="…"`. `State.xlink` is that entry of the map. An
  `xmlns:xlink` attribute that an ancestor has made already is dropped, as the algorithm
  drops it.
- **An attribute.** Each is ` name="value"` with the name as it is written: the prefix that
  the algorithm retrieves for `xlink:href`, `xml:space` and `xmlns:xlink` is the one written.
- **A value and a text.** In a value `&`, `"`, `<`, a tab, a line feed and a carriage return
  are replaced; in a text `&`, `<` and `>`. Nothing else is: U+00A0 is written as itself,
  where the HTML serialization writes `&nbsp;`.
- **The end of an element.** An element with no child that is not an HTML element is written
  `<name/>`. An HTML element with no child is ` />` if it is one of the algorithm's nineteen
  void names, and has its end tag otherwise.

`ok` is the tree for which the algorithm, run with "require well-formed", throws no exception
and for which the reading above holds: each local name is a `Name` with no colon, no attribute
name repeats, each value, text and comment is of the production `Char`, a comment holds no
`--` and does not end with `-`, an `xmlns:xlink` attribute holds the XLink namespace, and no
node is a named character reference, which XML does not define. `Name` and `Char` are the
productions of XML 1.0 that the algorithm cites: `isName` and `isChar` of
`Whatwg/Html/Print/Xml/Productions.lean`, which the gate `lake exe whatwg_xmlproductions`
compares with the sealed document.

What is proved here is of the two escapers, as for the HTML ones: no `<` survives in a text,
no `<` or `"` in a value, and each output decodes to its input, so each escaper is an
embedding.

What this module does not claim:

- that `nodeAt` is the algorithm. The reading above is an argument, and the algorithm over a
  DOM is not transcribed: debt D106. A browser's `XMLSerializer` on the same tree is the host
  observation that would test it, and none is recorded.
- that a text which `render` writes is well-formed XML. No reader of XML is in this package's
  library, so no retraction is stated: debt D107. `WhatwgTest/Html/SvgXml.lean` reads each
  ASCII fixture back with the reader of the gates, `Gates.Xml.read`, which is a finite check.
- anything of a tree that `ok` refuses. `render` still answers a text there.

Copyright (c) 2026 World Wide Web Consortium. This file includes material copied from or
derived from DOM Parsing and Serialization, https://w3c.github.io/DOM-Parsing/, under the W3C
Software and Document License, https://www.w3.org/copyright/software-license-2023/
-/

namespace Whatwg.Html.Print.Xml

open Whatwg.Html (RawNode)
open Whatwg.Html.Content (Ns)

/-! ## A name under "require well-formed" -/

/-- A local name that the algorithm serializes under "require well-formed": a `Name` that
holds no colon. -/
def localNameOk (name : List Char) : Bool := isName name && !name.contains ':'

/-! ## The two escapers -/

/-- A text, one character at a time: the three replacements of "XML serializing a Text
node". The `if` chain is as in `Whatwg/Html/Print/Escape.lean`: `split` gives usable
disequalities from it. -/
def escapeTextChar (c : Char) : List Char :=
  if c = '&' then ['&', 'a', 'm', 'p', ';']
  else if c = '<' then ['&', 'l', 't', ';']
  else if c = '>' then ['&', 'g', 't', ';']
  else [c]

/-- A text as the algorithm writes it. -/
def escapeText (l : List Char) : List Char := l.flatMap escapeTextChar

/-- A value, one character at a time: the six replacements of "serializing an attribute
value". A tab, a line feed and a carriage return are written as character references, so a
reader that normalizes the white space of a value reads the value back. -/
def escapeAttrChar (c : Char) : List Char :=
  if c = '&' then ['&', 'a', 'm', 'p', ';']
  else if c = '"' then ['&', 'q', 'u', 'o', 't', ';']
  else if c = '<' then ['&', 'l', 't', ';']
  else if c = '\t' then ['&', '#', '9', ';']
  else if c = '\n' then ['&', '#', 'x', 'A', ';']
  else if c = '\r' then ['&', '#', 'x', 'D', ';']
  else [c]

/-- A value as the algorithm writes it. -/
def escapeAttr (l : List Char) : List Char := l.flatMap escapeAttrChar

/-! ## No delimiter survives -/

theorem escapeTextChar_no_lt (c : Char) : '<' ∉ escapeTextChar c := by
  unfold escapeTextChar
  split
  · decide
  split
  · decide
  split
  · decide
  · rename_i _ h _
    simp only [List.mem_singleton]
    exact fun he => h he.symm

/-- No `<` is in a written text: a text ends where the next tag opens. -/
theorem escapeText_no_lt (l : List Char) : '<' ∉ escapeText l := by
  simp only [escapeText, List.mem_flatMap, not_exists, not_and]
  exact fun c _ hc => escapeTextChar_no_lt c hc

theorem escapeAttrChar_no_delim (c d : Char) (hd : d = '<' ∨ d = '"') : d ∉ escapeAttrChar c := by
  unfold escapeAttrChar
  split
  · rcases hd with rfl | rfl <;> decide
  split
  · rcases hd with rfl | rfl <;> decide
  split
  · rcases hd with rfl | rfl <;> decide
  split
  · rcases hd with rfl | rfl <;> decide
  split
  · rcases hd with rfl | rfl <;> decide
  split
  · rcases hd with rfl | rfl <;> decide
  · rename_i _ hq hl _ _ _
    simp only [List.mem_singleton]
    rcases hd with rfl | rfl
    · exact fun he => hl he.symm
    · exact fun he => hq he.symm

/-- No `<` and no `"` is in a written value: a value ends at its closing quote. -/
theorem escapeAttr_no_delim (l : List Char) (d : Char) (hd : d = '<' ∨ d = '"') :
    d ∉ escapeAttr l := by
  simp only [escapeAttr, List.mem_flatMap, not_exists, not_and]
  exact fun c _ hc => escapeAttrChar_no_delim c d hd hc

/-! ## The decoder for the escapers' own alphabet -/

/-- The seven references that the two escapers write, read back. It is a decoder for their
alphabet and no reader of XML. Structural: each call is on a proper tail. -/
def unescape : List Char → List Char
  | [] => []
  | '&' :: 'l' :: 't' :: ';' :: rest => '<' :: unescape rest
  | '&' :: 'g' :: 't' :: ';' :: rest => '>' :: unescape rest
  | '&' :: 'a' :: 'm' :: 'p' :: ';' :: rest => '&' :: unescape rest
  | '&' :: 'q' :: 'u' :: 'o' :: 't' :: ';' :: rest => '"' :: unescape rest
  | '&' :: '#' :: '9' :: ';' :: rest => '\t' :: unescape rest
  | '&' :: '#' :: 'x' :: 'A' :: ';' :: rest => '\n' :: unescape rest
  | '&' :: '#' :: 'x' :: 'D' :: ';' :: rest => '\r' :: unescape rest
  | c :: rest => c :: unescape rest

/-- Outside a reference the decoder copies a character. -/
theorem unescape_cons_of_ne_amp {c : Char} (h : c ≠ '&') (t : List Char) :
    unescape (c :: t) = c :: unescape t := by
  rw [unescape]
  all_goals exact fun _ hc _ => h hc

theorem unescape_escapeTextChar (c : Char) (rest : List Char) :
    unescape (escapeTextChar c ++ rest) = c :: unescape rest := by
  unfold escapeTextChar
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  · rename_i h1 _ _
    exact unescape_cons_of_ne_amp h1 rest

/-- A written text decodes to the text. -/
theorem unescape_escapeText (l : List Char) : unescape (escapeText l) = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [escapeText, List.flatMap_cons] at *
    rw [unescape_escapeTextChar, ih]

/-- The text escaper is an embedding. -/
theorem escapeText_injective {l₁ l₂ : List Char} (h : escapeText l₁ = escapeText l₂) :
    l₁ = l₂ := by
  have hd := congrArg unescape h
  rwa [unescape_escapeText, unescape_escapeText] at hd

theorem unescape_escapeAttrChar (c : Char) (rest : List Char) :
    unescape (escapeAttrChar c ++ rest) = c :: unescape rest := by
  unfold escapeAttrChar
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  · rename_i h1 _ _ _ _ _
    exact unescape_cons_of_ne_amp h1 rest

/-- A written value decodes to the value. -/
theorem unescape_escapeAttr (l : List Char) : unescape (escapeAttr l) = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [escapeAttr, List.flatMap_cons] at *
    rw [unescape_escapeAttrChar, ih]

/-- The value escaper is an embedding. -/
theorem escapeAttr_injective {l₁ l₂ : List Char} (h : escapeAttr l₁ = escapeAttr l₂) :
    l₁ = l₂ := by
  have hd := congrArg unescape h
  rwa [unescape_escapeAttr, unescape_escapeAttr] at hd

/-! ## Namespaces -/

/-- The namespace of an element, as the tree construction gives it: an element of an SVG
subtree is an SVG element, and so is `svg` in HTML. -/
def elementNs : Ns → String → Ns
  | .svg, _ => .svg
  | .html, name => Ns.step .html name

/-- The HTML namespace and the SVG namespace (the Infra Standard, "Namespaces"). -/
def namespaceOf : Ns → String
  | .html => "http://www.w3.org/1999/xhtml"
  | .svg => "http://www.w3.org/2000/svg"

/-- The XLink namespace. -/
def xlinkNamespace : String := "http://www.w3.org/1999/xlink"

/-- The XML namespace. -/
def xmlNamespace : String := "http://www.w3.org/XML/1998/namespace"

/-- How the algorithm sees an attribute of an element: its namespace, and its local name
where that is not the whole name. -/
inductive AttrKind where
  /-- No namespace: the written name is the local name. -/
  | plain
  /-- The XLink namespace, with the prefix `xlink`. -/
  | xlink (localName : List Char)
  /-- The XML namespace, with the prefix `xml`. -/
  | xml (localName : List Char)
  /-- `xmlns`: a default namespace declaration. -/
  | xmlnsDefault
  /-- `xmlns:p`: the declaration of the prefix `p`. -/
  | xmlnsPrefix (declared : List Char)
  deriving DecidableEq, Repr

/-- The kind of an attribute on an element of a namespace. "Adjust foreign attributes" names
the attributes of a foreign element that are in a namespace; an attribute of an HTML element
is in none. -/
def attrKind (ns : Ns) (name : String) : AttrKind :=
  match ns with
  | .html => .plain
  | .svg =>
    match Schema.Foreign.foreignAttrs.find? fun row => row.1 == name with
    | none => .plain
    | some row =>
      if row.2 == "XLink namespace" then .xlink (name.toList.drop 6)
      else if row.2 == "XML namespace" then .xml (name.toList.drop 4)
      else if name == "xmlns" then .xmlnsDefault
      else .xmlnsPrefix (name.toList.drop 6)

/-- The prefix that the algorithm may add to its map. -/
def xlinkPrefix : List Char := ['x', 'l', 'i', 'n', 'k']

/-- "Recording the namespace information": the value of the element's default namespace
declaration, if it has one. A later one replaces an earlier one. -/
def localDefault (ns : Ns) (attrs : List (String × String)) : Option String :=
  attrs.foldl (fun found a => if attrKind ns a.1 = .xmlnsDefault then some a.2 else found) none

/-- "Recording the namespace information": the element declares `xlink` for the XLink
namespace. -/
def declaresXlink (ns : Ns) (attrs : List (String × String)) : Bool :=
  attrs.any fun a => attrKind ns a.1 == .xmlnsPrefix xlinkPrefix && a.2 == xlinkNamespace

/-! ## The writer -/

/-- The algorithm's state at a node. `ns` is the namespace of the position, which moves by
`Ns.step` as the HTML printer's does. `inherited` is the algorithm's `namespace`: the default
namespace in scope, none at the root. `xlink` says that the prefix map holds `xlink` for the
XLink namespace. -/
structure State where
  ns : Ns
  inherited : Option Ns
  xlink : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The state at the root of a tree: an HTML position, no default namespace, and the prefix
map that holds `xml` alone. -/
def State.root : State := ⟨.html, none, false⟩

/-- One attribute: a space, the name, and the value in double quotes. -/
def attr (name value : List Char) : List Char :=
  ' ' :: (name ++ '=' :: '"' :: (escapeAttr value ++ ['"']))

/-- "XML serialization of the attributes" from a point of the list: the text, and whether
`xlink` is in the prefix map after it. `ignoreDefault` is the algorithm's "ignore namespace
definition attribute", and `inheritedXlink` says that an ancestor declared `xlink`. -/
def attrsFrom (ns : Ns) (ignoreDefault inheritedXlink : Bool) :
    Bool → List (String × String) → List Char × Bool
  | xlink, [] => ([], xlink)
  | xlink, a :: rest =>
    match attrKind ns a.1 with
    | .xmlnsDefault =>
      if a.2 == xmlNamespace || ignoreDefault then
        attrsFrom ns ignoreDefault inheritedXlink xlink rest
      else
        let after := attrsFrom ns ignoreDefault inheritedXlink xlink rest
        (attr a.1.toList a.2.toList ++ after.1, after.2)
    | .xmlnsPrefix declared =>
      if a.2 == xmlNamespace ||
          (inheritedXlink && declared == xlinkPrefix && a.2 == xlinkNamespace) then
        attrsFrom ns ignoreDefault inheritedXlink xlink rest
      else
        let after := attrsFrom ns ignoreDefault inheritedXlink xlink rest
        (attr a.1.toList a.2.toList ++ after.1, after.2)
    | .xlink _ =>
      let after := attrsFrom ns ignoreDefault inheritedXlink true rest
      if xlink then (attr a.1.toList a.2.toList ++ after.1, after.2)
      else
        (attr ('x' :: 'm' :: 'l' :: 'n' :: 's' :: ':' :: xlinkPrefix) xlinkNamespace.toList ++
          (attr a.1.toList a.2.toList ++ after.1), after.2)
    | _ =>
      let after := attrsFrom ns ignoreDefault inheritedXlink xlink rest
      (attr a.1.toList a.2.toList ++ after.1, after.2)

/-- The nineteen HTML elements that the algorithm writes with ` />` when they have no
child. -/
def voidNames : List String :=
  ["area", "base", "basefont", "bgsound", "br", "col", "embed", "frame", "hr", "img", "input",
   "keygen", "link", "menuitem", "meta", "param", "source", "track", "wbr"]

/-- An end tag. -/
def close (name : String) : List Char := '<' :: '/' :: (name.toList ++ ['>'])

mutual

/-- "XML serializing" a node at a state. -/
def nodeAt (s : State) : RawNode → List Char
  | .element name attrs children =>
    let ns := elementNs s.ns name
    let same := s.inherited == some ns
    let declared := localDefault ns attrs == some (namespaceOf ns)
    let ignoreDefault := if same then (localDefault ns attrs).isSome else !declared
    let generated :=
      if same || declared then [] else attr ['x', 'm', 'l', 'n', 's'] (namespaceOf ns).toList
    let written := attrsFrom ns ignoreDefault s.xlink (s.xlink || declaresXlink ns attrs) attrs
    let inner := forestAt ⟨s.ns.step name, some ns, written.2⟩ children
    let opened := '<' :: (name.toList ++ generated ++ written.1)
    if children.isEmpty then
      if ns == .html then
        if voidNames.contains name then opened ++ [' ', '/', '>'] else opened ++ '>' :: close name
      else opened ++ ['/', '>']
    else opened ++ '>' :: (inner ++ close name)
  | .text content => escapeText content.toList
  | .entity name => '&' :: (name.toList ++ [';'])
  | .comment content => '<' :: '!' :: '-' :: '-' :: (content.toList ++ ['-', '-', '>'])

/-- A forest at a state, in order and with nothing between. -/
def forestAt (s : State) : List RawNode → List Char
  | [] => []
  | node :: rest => nodeAt s node ++ forestAt s rest

end

/-- The XML serialization of a tree, at `List Char`. -/
def renderChars (node : RawNode) : List Char := nodeAt .root node

/-- The XML serialization of a tree: the text of a file that holds it. -/
def render (node : RawNode) : String := String.ofList (renderChars node)

theorem toList_render (node : RawNode) : (render node).toList = renderChars node :=
  String.toList_ofList

/-! ## The tree that serializes with no exception -/

/-- The text holds `--`. -/
def hasDoubleHyphen : List Char → Bool
  | '-' :: '-' :: _ => true
  | _ :: rest => hasDoubleHyphen rest
  | [] => false

/-- No name of the list repeats. -/
def distinct : List String → Bool
  | [] => true
  | name :: rest => !rest.contains name && distinct rest

/-- One attribute passes the checks of "require well-formed", and an `xmlns:` declaration is
the one this module reads: `xlink` for the XLink namespace. -/
def attrOk (ns : Ns) (a : String × String) : Bool :=
  a.2.toList.all isChar &&
    match attrKind ns a.1 with
    | .plain => localNameOk a.1.toList && a.1 != "xmlns"
    | .xlink localName => localNameOk localName
    | .xml localName => localNameOk localName
    | .xmlnsDefault => true
    | .xmlnsPrefix declared => declared == xlinkPrefix && a.2 == xlinkNamespace

mutual

/-- The algorithm, run with "require well-formed" on the node at a position's namespace,
throws no exception, and the node is one this module's reading covers. -/
def okAt (ns : Ns) : RawNode → Bool
  | .element name attrs children =>
    localNameOk name.toList && attrs.all (attrOk (elementNs ns name)) &&
      distinct (attrs.map (·.1)) && okAllAt (ns.step name) children
  | .text content => content.toList.all isChar
  | .entity _ => false
  | .comment content =>
    content.toList.all isChar && !hasDoubleHyphen content.toList &&
      content.toList.getLast? != some '-'

/-- Every node of the forest passes. -/
def okAllAt (ns : Ns) : List RawNode → Bool
  | [] => true
  | node :: rest => okAt ns node && okAllAt ns rest

end

/-- The tree serializes as XML with no exception. -/
def ok (node : RawNode) : Bool := okAt .html node

/-- The text of a tree that passes `ok`, and nothing for one that does not. -/
def render? (node : RawNode) : Option String := if ok node then some (render node) else none

end Whatwg.Html.Print.Xml
