import Whatwg.Html.Node.Svg
import Whatwg.Html.Print.Render
import Whatwg.Html.Print.Xml

/-!
# Whatwg.Html.Print.Picture

Owner: the text of a typed picture in one call (slice S10 of `docs/SVG-PACKAGE-PLAN.md`; ruling
SV-47). A typed tree is printed through its raw tree, and a caller wrote
`Print.render n.toRaw`. The three functions here are those two steps:

- `SvgNode.render` is the markup of the picture in an HTML page: the HTML serialization.
- `SvgNode.renderXml?` is the text of a file that holds the picture alone, the XML
  serialization, for a tree that it accepts under "require well-formed", and nothing for any
  other. A text with a control character, a named character reference, or a data key that is
  no XML name is refused, though the structure test passes it.
- `SvgNode.renderXmlUnchecked` is the same text with no check.

Nothing is proved here: the laws of the two printers are stated of raw trees, in
`Whatwg/Html/Print/Render.lean` and `Whatwg/Html/Print/Xml.lean`, and they read these
functions by unfolding them.
-/

namespace Whatwg.Html.SvgNode

/-- The markup of a picture in an HTML page. -/
def render (node : SvgNode) : String := Print.render node.toRaw

/-- The XML text of a picture with no check: for a tree that `Print.Xml.ok` refuses it is no
XML. A program that writes a file calls `renderXml?`. -/
def renderXmlUnchecked (node : SvgNode) : String := Print.Xml.render node.toRaw

/-- The text of a file that holds the picture alone, for a tree that the XML serialization
accepts under "require well-formed". -/
def renderXml? (node : SvgNode) : Option String := Print.Xml.render? node.toRaw

end Whatwg.Html.SvgNode
