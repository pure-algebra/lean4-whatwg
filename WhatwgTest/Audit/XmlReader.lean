import WhatwgGates.Xml

/-!
# WhatwgTest.Audit.XmlReader

Finite evaluations and controls of `Gates.Xml.read`, the reader of the sealed svgwg definitions
(slice S2 of `docs/SVG-PACKAGE-PLAN.md`). Each line is a finite evaluation of the reader on a
small document, or a control: a construct outside the reader's subset, refused at its offset.

What this battery does not claim: that the reader reads XML. It reads the subset its module
names, and `lake exe whatwg_svgdefinitions` is the check that the sealed files are inside it.
-/

namespace WhatwgTest.Audit.XmlReader

open Gates.Xml

mutual

/-- A read node as text: the name, the attributes, the offsets, then the children. -/
def outline : Node → String
  | .element name attrs children start stop =>
    name ++ "[" ++ ", ".intercalate (attrs.map fun attr => attr.1 ++ "=" ++ attr.2) ++ "]@" ++
      toString start ++ "-" ++ toString stop ++ "(" ++ outlineList children ++ ")"
  | .text content => content.quote

def outlineList : List Node → String
  | [] => ""
  | [node] => outline node
  | node :: rest => outline node ++ " " ++ outlineList rest

end

/-- The reader's answer on a document: the outline, or the refusal. -/
def outcome (text : String) : String :=
  match read text with
  | .ok node => outline node
  | .error why => "refused: " ++ why

-- Elements, attributes in either quote, and the offsets of each element.
#guard outcome "<a/>" == "a[]@0-4()"
#guard outcome "<a x='1' y=\"two\"><b/>t</a>" == "a[x=1, y=two]@0-26(b[]@17-21() \"t\")"
#guard outcome "<a\n  b='1'\n/>" == "a[b=1]@0-13()"
#guard outcome "<a></a >" == "a[]@0-8()"

-- A name keeps its prefix as written: the definitions' `x:contentmodel`.
#guard outcome "<x:m xmlns:x='u'>s</x:m>" == "x:m[xmlns:x=u]@0-24(\"s\")"

-- Comments are dropped: before the root, inside it, and after it. Markup inside one is not read.
#guard outcome "<!-- c --><r><!-- <x/> --><k n='v'/> </r><!-- d -->" ==
  "r[]@10-41(k[n=v]@26-36() \" \")"

-- The five named references, in character data and in an attribute value.
#guard outcome "<a>&lt;&amp;&gt;&quot;&apos;</a>" == "a[]@0-32(\"<&>\\\"'\")"
#guard outcome "<a v='&lt;b&gt;'/>" == "a[v=<b>]@0-18()"

-- An attribute value is normalised: each white-space character becomes a space (XML 1.0,
-- section 3.3.3). Character data is kept as written.
#guard outcome "<a v='x\ny\tz'/>" == "a[v=x y z]@0-14()"
#guard outcome "<a>x\ny</a>" == "a[]@0-10(\"x\\ny\")"

-- A name opens with a letter, `_` or `:`.
#guard outcome "<_a :b='x'/>" == "_a[:b=x]@0-12()"

-- The accessors the projection reads through. Character data has no offsets.
#guard (read "<e name='n' href='h'><k/>t<k/></e>").toOption.map (·.attr "name") == some "n"
#guard (read "<e name='n'/>").toOption.map (·.attr "href") == some ""
#guard (read "<e><k/>t<k/><j/></e>").toOption.map (fun n => (n.childrenNamed "k").length) == some 2
#guard (read "<e>one <a>two</a> three</e>").toOption.map (·.textContent) == some "one two three"
#guard (read "<e>t</e>").toOption.map (·.span?) == some (some (0, 8))
#guard (read "<e>t</e>").toOption.map (fun n => n.children.map (·.span?)) == some [none]

-- Control: a character outside ASCII is refused first, so an offset is a byte offset.
#guard outcome "<a>é</a>" == "refused: offset 3: a character outside ASCII"

-- Controls: a name that opens with a digit is no name.
#guard outcome "<1a/>" == "refused: offset 1: an element name is expected"
#guard outcome "<a 1b='x'/>" == "refused: offset 3: an attribute name is expected"

-- Controls: what the reader does not know, it refuses at its offset.
#guard outcome "<?xml version='1.0'?><a/>" == "refused: offset 0: a processing instruction"
#guard outcome "<a><?p?></a>" == "refused: offset 3: a processing instruction"
#guard outcome "<!DOCTYPE a><a/>" == "refused: offset 0: a declaration"
#guard outcome "<a><![CDATA[x]]></a>" == "refused: offset 3: a CDATA section"
#guard outcome "<a>&nbsp;</a>" ==
  "refused: offset 3: a character reference that is not one of lt, gt, amp, quot, apos"
#guard outcome "<a>&#65;</a>" ==
  "refused: offset 3: a character reference that is not one of lt, gt, amp, quot, apos"

-- Controls: a document that is not well formed.
#guard outcome "<a b='1' b='2'/>" == "refused: offset 9: the attribute `b` is given twice"
#guard outcome "<a b='<'/>" == "refused: offset 5: `<` in an attribute value"
#guard outcome "<a b=1/>" == "refused: offset 5: an attribute value without a quote"
#guard outcome "<a b/>" == "refused: offset 4: `=` is expected after the attribute name `b`"
#guard outcome "<a><!-- x</a>" == "refused: offset 13: a comment that does not end"
#guard outcome "<a><b></a>" == "refused: offset 6: the end tag `</b>` is expected"
#guard outcome "<a/><b/>" == "refused: offset 4: content after the root element"
#guard outcome "<a" == "refused: offset 2: the input ends inside a start tag"
#guard outcome "" == "refused: offset 0: an element is expected"
#guard outcome "text" == "refused: offset 0: an element is expected"

end WhatwgTest.Audit.XmlReader
