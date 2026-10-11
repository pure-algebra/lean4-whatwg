import Whatwg.Html.Print.Render
import WhatwgTest.Html.Builders

/-!
# WhatwgTest.Html.Print

Probes for the printer (slices H4 and H7.2): the escaper, the serializer on
the standard's fragment serialization algorithm, and the decoder that
inverts the serializer on the sublanguage `Whatwg.Html.Print.wf` names. Each
`example` is a closed evaluation, so the file failing to elaborate is the
gate; the quantified statements live in `Whatwg.Html.Print.Escape` and
`Whatwg.Html.Print.Render`.

Control characters are written `Char.ofNat n` rather than as literals, so
that no source file of this repository carries one.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits
every declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.Print

open Whatwg.Html
open Whatwg.Html.Print
open Whatwg.Html.Schema (Tag Attr)
open Whatwg.Html.Content (Ctx)

/-! ## The escaper -/

/-- The four references of "escaping a string" outside attribute mode; `"`
passes through. -/
example : escapeString "a<b>c&d\"e" = "a&lt;b&gt;c&amp;d\"e" := by decide

/-- U+00A0 becomes `&nbsp;`. -/
example : escapeString (String.ofList ['a', nbsp, 'b']) = "a&nbsp;b" := by decide

/-- A control character is not escaped. -/
example : escapeString (String.ofList ['a', Char.ofNat 1, 'b']) = String.ofList ['a', Char.ofNat 1, 'b'] := by
  decide

/-- Attribute mode escapes `"` as well. -/
example : escapeAttrString "a<b>c&d\"e" = "a&lt;b&gt;c&amp;d&quot;e" := by decide

/-- The escaper's output decodes back, at a point. -/
example : unescape (escape "a<b&c".toList) = "a<b&c".toList := by decide
example : unescape (escapeAttr (String.ofList ['"', nbsp]).toList) = ['"', nbsp] := by decide

/-! ## The serializer -/

example : render (.element "div" [("class", "card")] [.element "p" [] [.text "Hi & bye"]])
    = "<div class=\"card\"><p>Hi &amp; bye</p></div>" := by decide

/-- A void element has no end tag and no solidus. -/
example : render (.element "br" [] []) = "<br>" := by decide
example : render (.element "br" [("class", "spacer")] []) = "<br class=\"spacer\">" := by decide

/-- A non-void element with no children gets a closing tag. -/
example : render (.element "span" [] []) = "<span></span>" := by decide

/-- An attribute value is escaped in attribute mode and double-quoted. -/
example : render (.element "input" [("value", "a\"b")] []) = "<input value=\"a&quot;b\">" := by decide

/-- A `"` in text passes through; a `>` is escaped. -/
example : render (.element "p" [] [.text "say \"x\" > y"]) = "<p>say \"x\" &gt; y</p>" := by decide

/-- The text of a raw-text element is written literally. -/
example : render (.element "script" [] [.text "if (a < b && c) {}"])
    = "<script>if (a < b && c) {}</script>" := by decide
example : render (.element "style" [] [.text "a > b {}"]) = "<style>a > b {}</style>" := by decide

/-- An entity reference is written as written (an extension of the raw layer,
not a DOM node). -/
example : render (.entity "nbsp") = "&nbsp;" := by decide

/-- A comment's data is written literally. -/
example : render (.comment "a < b") = "<!--a < b-->" := by decide

example : isVoidName "img" = true := by decide
example : isVoidName "p" = false := by decide
example : isRawText "script" = true ∧ isRawText "p" = false := by decide

/-! ## A whole document, from the typed builders -/

/-- The document of `WhatwgTest.Html.Builders`, shortened by one metadata
child. Those probes are anonymous `example`s, so the construction is repeated
here rather than referenced; the import above is what pins the two to the
same combinators. -/
def document : Element .html Ctx.document :=
  E.html
    [E.el (E.head
      [E.el (E.title [E.txt "Slice H4"]),
       E.el (E.«meta» [A.a_charset "utf-8"])]),
     E.el (E.body
      [E.el (E.h1 [E.txt "Content models"]),
       E.el (E.p [E.txt "A & B", E.el (E.br)])])]

set_option maxRecDepth 4000 in
/-- Rendered end to end through erasure. The `maxRecDepth` bump is the
elaborator's stack, not a heartbeat budget: `decide` reduces a 130-byte
`String` equality here. -/
example : document.render
    = "<html><head><title>Slice H4</title><meta charset=\"utf-8\"></head>"
      ++ "<body><h1>Content models</h1><p>A &amp; B<br></p></body></html>" := by decide

set_option maxRecDepth 4000 in
/-- With the document type the algorithm writes for a `DocumentType` named
`html`, and nothing between it and the tree. -/
example : document.renderDoc
    = "<!DOCTYPE html>"
      ++ "<html><head><title>Slice H4</title><meta charset=\"utf-8\"></head>"
      ++ "<body><h1>Content models</h1><p>A &amp; B<br></p></body></html>" := by decide

/-- A child renders through the raw node it carries. -/
example : (Child.of (ctx := Ctx.flow) (E.p [E.txt "x"])).render = "<p>x</p>" := by decide

/-! ## The decoder -/

/-- The document is in the sublanguage the decoder inverts. -/
example : wf document.toRaw = true := by decide

/-- And it decodes back from its own rendering. -/
example : decodeNode? (weight document.toRaw) (renderChars document.toRaw)
    = some (document.toRaw, []) := decodeNode?_render (by decide)

/-- A tree with an entity node is outside that sublanguage: `&amp;` is
already the escaping of a text `&`. -/
example : wf (.element "p" [] [.entity "amp"]) = false := by decide

/-- So is a tree with two adjacent text runs. -/
example : wf (.element "p" [] [.text "a", .text "b"]) = false := by decide

/-- And so is an empty text run. -/
example : wf (.text "") = false := by decide

/-- A void element with a child, a raw-text element with two text children
or a `<` in its text, and a comment containing `>` are outside it too. -/
example : wf (.element "br" [] [.text "x"]) = false := by decide
example : wf (.element "script" [] [.text "a", .text "b"]) = false := by decide
example : wf (.element "script" [] [.text "a </script>"]) = false := by decide
example : wf (.comment "a > b") = false := by decide
/-- A raw-text element with one text child decodes back. -/
example : wf (.element "script" [] [.text "a && b"]) = true := by decide
example : decodeNode? (weight (RawNode.element "script" [] [.text "a && b"]))
      (renderChars (RawNode.element "script" [] [.text "a && b"]))
    = some (RawNode.element "script" [] [.text "a && b"], []) :=
  decodeNode?_render (node := RawNode.element "script" [] [.text "a && b"]) (by decide)

end WhatwgTest.Html.Print
