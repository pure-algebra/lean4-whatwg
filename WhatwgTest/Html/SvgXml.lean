import Whatwg.Html.Print.Xml
import Whatwg.Html.Print.Render
import Whatwg.Html.Node.SvgValid
import WhatwgGates.Xml
import WhatwgTest.Html.SvgPicture

/-!
# WhatwgTest.Html.SvgXml

Readers, controls and finite evaluations of the XML serialization of a tree (slice S8 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-40): `Whatwg/Html/Print/Xml.lean`.

The first tree is the consumer's picture of `WhatwgTest/Html/SvgPicture.lean`, written as the
file `tools/Drivers/View.lean` of lean4-effect4 writes it. The others show one step of the
algorithm each: where a namespace is declared, what an escaper replaces, how an element ends.

A reader applies a law of an escaper at a text that is a variable. A control is a tree that
`Xml.ok` refuses, or the HTML serialization of the same tree where the two differ. A finite
evaluation writes a closed tree.

The last section reads each written text back with `Gates.Xml.read`, the reader of the gates.
It was written for the sealed definitions files, by another hand than the writer. It is a
check on fixtures and no law: that reader takes ASCII alone, drops comments, and knows the
five named references and no numeric one.

What this battery does not claim: that the writer is the algorithm of the sealed document on
every tree, or that a browser reads a written text as the tree.
-/

namespace WhatwgTest.Html.SvgXml

open Whatwg.Html
open Whatwg.Html.Print
open Whatwg.Html.Content
open Whatwg.Svg.Value
open WhatwgTest.Html.SvgPicture (picture plain sample)

/-- A raw element. -/
def el (name : String) (attrs : List (String × String)) (children : List RawNode) : RawNode :=
  .element name attrs children

/-- A no-break space, U+00A0. -/
def nbsp : String := String.singleton (Char.ofNat 0xA0)

/-! ## A picture as a file -/

-- The picture of seven device calls, as XML. An element with no child is `<name/>`, and a
-- key's `>` stays as it is in a value, where the HTML serialization writes `&gt;`.
#guard Xml.render (picture plain 40 20 2 sample).toRaw ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\" class=\"e4-view\" data-look=\"plain\" " ++
  "width=\"40\" height=\"20\" viewBox=\"0 0 80 40\">" ++
  "<rect class=\"e4-fill-ground\" x=\"0\" y=\"0\" width=\"40\" height=\"20\" " ++
  "fill=\"#14110d\" fill-opacity=\"1\" data-key=\"n1\"/>" ++
  "<rect class=\"e4-fill-ink\" x=\"2\" y=\"2\" width=\"36\" height=\"16\" " ++
  "fill=\"#f3f4f6\" fill-opacity=\"0.5\"/>" ++
  "<path class=\"e4-stroke-ink\" d=\"M10,20C10,30 30,30 30,40\" fill=\"none\" " ++
  "stroke=\"#f3f4f6\" stroke-width=\"2\" data-key=\"e&lt;1>\"/>" ++
  "<clipPath id=\"c3\"><rect x=\"0\" y=\"0\" width=\"40\" height=\"20\"/></clipPath>" ++
  "<g clip-path=\"url(#c3)\"><text x=\"4\" y=\"14\" class=\"e4-text\" fill=\"#f3f4f6\" " ++
  "transform=\"scale(2)\" xml:space=\"preserve\" data-key=\"n1\">a&lt;b &amp; c</text></g>" ++
  "<rect x=\"0\" y=\"0\" width=\"40\" height=\"20\" fill=\"none\" pointer-events=\"all\" " ++
  "data-key=\"n1\"/>" ++
  "<path class=\"e4-fill-host\" d=\"M0,0C1,0 2.5,0.5 3.005,1C2,1.5 1,2 0,0Z" ++
  "M0.5,0.5C0.6,0.5 0.7,0.6 0.5,0.5Z\" fill-rule=\"evenodd\" fill=\"#c0851f\" " ++
  "fill-opacity=\"0.35\" data-key=\"s\"/></svg>"

-- The picture serializes with no exception, and `render?` answers its text.
#guard Xml.ok (picture plain 40 20 2 sample).toRaw
#guard (Xml.render? (picture plain 40 20 2 sample).toRaw).isSome

/-! ## Where a namespace is declared -/

-- A root with no declaration of its own is given one: the algorithm's default namespace is
-- none at the root.
#guard Xml.render (el "svg" [("viewBox", "0 0 1 1")] [el "g" [] []]) ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 1 1\"><g/></svg>"

-- A root that declares its namespace keeps the declaration where it wrote it.
#guard Xml.render (el "svg" [("viewBox", "0 0 1 1"), ("xmlns", "http://www.w3.org/2000/svg")] []) ==
  "<svg viewBox=\"0 0 1 1\" xmlns=\"http://www.w3.org/2000/svg\"/>"

-- Control: a declaration of another namespace on an SVG element is replaced, since the
-- element is an SVG element whatever the attribute says.
#guard Xml.render (el "svg" [("xmlns", "urn:other")] []) ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\"/>"

-- An attribute in the XLink namespace declares its prefix where none is in scope, on each
-- element that needs one.
#guard Xml.render (el "svg" [] [el "use" [("xlink:href", "#a"), ("xlink:title", "t")] []]) ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\"><use " ++
  "xmlns:xlink=\"http://www.w3.org/1999/xlink\" xlink:href=\"#a\" xlink:title=\"t\"/></svg>"

-- A declaration on an ancestor is in scope below it, and one that repeats it is dropped.
#guard Xml.render (el "svg" [("xmlns:xlink", "http://www.w3.org/1999/xlink")]
    [el "use" [("xlink:href", "#a"), ("xmlns:xlink", "http://www.w3.org/1999/xlink")] []]) ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\" xmlns:xlink=\"http://www.w3.org/1999/xlink\">" ++
  "<use xlink:href=\"#a\"/></svg>"

-- The prefix `xml` needs no declaration.
#guard Xml.render (el "svg" [] [el "text" [("xml:space", "preserve")] [.text "a  b"]]) ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\"><text xml:space=\"preserve\">a  b</text></svg>"

-- Below an integration point an element is an HTML element and declares the HTML namespace.
-- An `svg` inside it declares the SVG namespace again.
#guard Xml.render (el "svg" [] [el "foreignObject" []
    [el "p" [("class", "n")] [.text "x", el "br" [] [], el "svg" [] [el "rect" [] []],
      el "span" [] []]]]) ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\"><foreignObject>" ++
  "<p xmlns=\"http://www.w3.org/1999/xhtml\" class=\"n\">x<br />" ++
  "<svg xmlns=\"http://www.w3.org/2000/svg\"><rect/></svg><span></span></p>" ++
  "</foreignObject></svg>"

-- The element's namespace is the one the value judgment reads: one function, written twice.
example (ns : Ns) (name : String) : Xml.elementNs ns name = Ns.ofElement ns name := by
  cases ns <;> rfl

-- The two namespaces that the typed attribute writes are the ones the writer compares with.
example : Xml.namespaceOf .svg = svgNamespace := rfl
example : Xml.xlinkNamespace = xlinkNamespace := rfl

/-! ## How an element ends -/

-- An HTML element with no child has its end tag, or ` />` if it is void. An SVG element with
-- no child is an empty-element tag. A whole HTML document is XML too.
#guard Xml.render (el "html" [("lang", "en")] [el "head" [] [el "meta" [("charset", "utf-8")] []],
    el "body" [] [el "p" [] [], .comment " c "]]) ==
  "<html xmlns=\"http://www.w3.org/1999/xhtml\" lang=\"en\"><head><meta charset=\"utf-8\" />" ++
  "</head><body><p></p><!-- c --></body></html>"

-- Control: the HTML serialization of an SVG element with no child has an end tag.
#guard Print.render (el "svg" [] [el "rect" [] []]) == "<svg><rect></rect></svg>"

/-! ## What the escapers replace -/

-- A text: `&`, `<` and `>`. A value: `&`, `"`, `<`, a tab, a line feed and a carriage return.
#guard Xml.render (el "svg" [] [el "title" [("data-k", "a\tb\nc\rd \"q\" <&>")] [.text "<&>\"'"]]) ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\"><title data-k=\"a&#9;b&#xA;c&#xD;d &quot;q&quot; " ++
  "&lt;&amp;>\">&lt;&amp;&gt;\"'</title></svg>"

-- Control: a no-break space is written as itself, where the HTML serialization writes a
-- reference that XML does not define.
#guard Xml.render (el "svg" [] [el "text" [] [.text nbsp]]) ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\"><text>" ++ nbsp ++ "</text></svg>"
#guard Print.render (el "svg" [] [el "text" [] [.text nbsp]]) == "<svg><text>&nbsp;</text></svg>"

-- Reader of the retraction of the value escaper at a key that is a variable: what is written
-- decodes to the key, whatever it holds.
example (key : String) : Xml.unescape (Xml.escapeAttr key.toList) = key.toList :=
  Xml.unescape_escapeAttr _

-- Reader of the embedding at two typed values: two paths that are written alike in a value
-- have one text, so by the grammar's own embedding they are one path.
example (p q : PathData)
    (h : Xml.escapeAttr (PathData.grammar.print p) = Xml.escapeAttr (PathData.grammar.print q)) :
    PathData.grammar.print p = PathData.grammar.print q :=
  Xml.escapeAttr_injective h

-- Reader of the delimiter law: no key closes its own value, and no text opens a tag.
example (key : String) : '"' ∉ Xml.escapeAttr key.toList :=
  Xml.escapeAttr_no_delim _ '"' (Or.inr rfl)
example (content : String) : '<' ∉ Xml.escapeText content.toList := Xml.escapeText_no_lt _

/-! ## What `ok` refuses -/

-- Controls of "require well-formed": a named character reference, which XML does not define;
-- a comment that holds `--` or ends with `-`; a name that is no `Name`; a character that is
-- no `Char`; a name that repeats.
#guard !Xml.ok (el "svg" [] [.entity "amp"])
#guard !Xml.ok (el "svg" [] [.comment "a--b"]) && !Xml.ok (el "svg" [] [.comment "a-"])
#guard Xml.ok (el "svg" [] [.comment "a - b"])
#guard !Xml.ok (el "svg" [] [el "rect" [("data-a b", "k")] []])
#guard !Xml.ok (el "svg" [] [.text (String.singleton (Char.ofNat 1))])
#guard !Xml.ok (el "svg" [("class", "a"), ("class", "b")] [])

-- Control: on an HTML element a name with a colon is no local name, so `xml:lang` there is
-- refused; on an SVG element it is an attribute of the XML namespace.
#guard !Xml.ok (el "p" [("xml:lang", "en")] []) && Xml.ok (el "svg" [("xml:lang", "en")] [])

-- Control: a prefix declaration other than `xlink` for the XLink namespace is outside what
-- the writer reads.
#guard !Xml.ok (el "svg" [("xmlns:xlink", "urn:other")] [])

-- Control: `render` answers a text for a tree that `ok` refuses, and `render?` does not.
#guard (Xml.render? (el "svg" [] [.entity "amp"])).isNone
#guard Xml.render (el "svg" [] [.entity "amp"]) ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\">&amp;</svg>"

/-! ## The names of the two schemas -/

-- Every element name of the SVG schema is a local name of XML, and so is every attribute
-- name of it on an SVG element, with its prefix where it has one.
#guard Whatwg.Svg.Schema.Tag.all.all fun t => Xml.localNameOk t.chars
#guard Whatwg.Svg.Schema.Attr.all.all fun a => Xml.attrOk .svg (a.name, "")

-- The eleven names that "adjust foreign attributes" places in a namespace, as the writer
-- reads them: seven of XLink, two of XML, and the two declarations.
#guard (Schema.Foreign.foreignAttrs.map fun row => Xml.attrKind .svg row.1) ==
  [.xlink "actuate".toList, .xlink "arcrole".toList, .xlink "href".toList, .xlink "role".toList,
   .xlink "show".toList, .xlink "title".toList, .xlink "type".toList, .xml "lang".toList,
   .xml "space".toList, .xmlnsDefault, .xmlnsPrefix "xlink".toList]

-- Control: on an HTML element no attribute is in a namespace.
#guard Schema.Foreign.foreignAttrs.all fun row => Xml.attrKind .html row.1 == .plain

/-! ## An independent reader -/

mutual

/-- The tree that the gates' reader answers, as a raw tree: its offsets are dropped. -/
def back : Gates.Xml.Node → RawNode
  | .element name attrs children _ _ => .element name attrs (backAll children)
  | .text content => .text content

/-- The same over a forest. -/
def backAll : List Gates.Xml.Node → List RawNode
  | [] => []
  | node :: rest => back node :: backAll rest

end

/-- The written text of a tree, read by the gates' reader. -/
def readBack (tree : RawNode) : Option RawNode :=
  match Gates.Xml.read (Xml.render tree) with
  | .ok node => some (back node)
  | .error _ => none

/-- A tree whose root declares its namespace: a group, a key with the three characters that a
value escapes, a text with two that a text escapes, and a title. -/
def fixture : RawNode :=
  el "svg" [("xmlns", "http://www.w3.org/2000/svg"), ("viewBox", "0 0 4 4")]
    [el "g" [("class", "a b")]
      [el "rect" [("x", "1"), ("data-key", "k<1> & \"q\"")] [],
        el "text" [("xml:space", "preserve")] [.text "a < b & c"]],
      el "title" [] [.text "t"]]

-- The reader of the gates reads the written text back as the tree.
#guard readBack fixture == some fixture

-- It reads the consumer's picture back too: every name, value and text of it.
#guard readBack (picture plain 40 20 2 sample).toRaw == some (picture plain 40 20 2 sample).toRaw

-- A generated declaration is an attribute to that reader, which knows no namespace: the
-- tree read back has it first.
#guard readBack (el "svg" [("viewBox", "0 0 1 1")] [el "g" [] []]) ==
  some (el "svg" [("xmlns", "http://www.w3.org/2000/svg"), ("viewBox", "0 0 1 1")] [el "g" [] []])

-- Control: the HTML serialization of the same tree is no XML to that reader where a void
-- element has no end tag.
#guard (Gates.Xml.read (Print.render (el "p" [] [el "br" [] []]))).toOption.isNone
#guard (readBack (el "p" [] [el "br" [] []])).isSome

end WhatwgTest.Html.SvgXml
