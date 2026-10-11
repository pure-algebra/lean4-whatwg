/-!
# Whatwg.Html.Schema.Readings

The authored interpretation of the HTML Standard's content models, and
nothing else: the one place under `Whatwg/` where a sentence of the
standard is read as a structure. `WhatwgGates/HtmlStandardEmit.lean` imports this
module and generates the schema from it and the projection; the gate
refuses a reading whose block digest no longer matches the projection, so
a re-pin that changes a definition fails until the reading is re-examined.
Nothing here is generated, and nothing here is a proof.

A `Model` is a base (flow, phrasing, text, nothing, metadata, or a list of
named elements with or without the script-supporting elements), the tags
and categories the element admits besides, and the tags and categories it
excludes from all its descendants. Descendant exclusions carry through
every element (ruling HP-13): the flags of `Whatwg.Html.Schema.Exclusions`.

- `sentenceModel` reads the exact sentences that recur (twenty-one at the
  pin) mechanically; a sentence not listed has no mechanical reading.
- `readings` are the child-level readings of the sentences that are
  conditional or ordered prose, each pinned to its block digest, with the
  reason. An ordered model is read as membership here; order and counts
  are the sequence readings of a later slice.
- `transparents` are the elements whose content is their context's, with
  what they exclude; `audio`, `video` and `noscript` are transparent by
  their conditional sentences.
- `labelled` are the direct children a sentence admits first and outside
  any base (`source` and `track` under `audio` and `video`, `area` under
  `map`).
- `baseOverrides`: `noscript` in `head` takes `link`, `style` and `meta`.
- `extraAttrs`: attributes the standard defines outside its index.
-/

namespace Whatwg.Html.Schema.Readings

/-- The base of a model. -/
inductive BaseKind where
  | flow | phrasing | text | nothing | metadata
  | only (names : List String) (scriptSupporting : Bool)
  deriving BEq, Repr, Inhabited

/-- A reading of a content model: the base, the tags and categories admitted
besides, the tags and categories excluded from every descendant. Category
names are `interactive`, `media`, `heading`, `sectioning`. -/
structure Model where
  base : BaseKind
  plusTags : List String := []
  plusCats : List String := []
  minusTags : List String := []
  minusCats : List String := []
  deriving BEq, Repr, Inhabited

/-- The twenty-one sentences read mechanically. -/
def sentenceModel : List String → Option Model
  | ["Phrasing content."] => some { base := .phrasing }
  | ["Flow content."] => some { base := .flow }
  | ["Nothing."] => some { base := .nothing }
  | ["Nothing (for clarification, see example)."] => none
  | ["Text."] => some { base := .text }
  | ["Text that is not inter-element whitespace."] => some { base := .text }
  | ["Text that gives a conformant style sheet."] => some { base := .text }
  | ["Zero or more tr and script-supporting elements."] => some { base := .only ["tr"] true }
  | ["Zero or more li and script-supporting elements."] => some { base := .only ["li"] true }
  | ["Zero or more td, th, and script-supporting elements."] => some { base := .only ["td", "th"] true }
  | ["Flow content, but with no header or footer element descendants."] =>
      some { base := .flow, minusTags := ["footer", "header"] }
  | ["Flow content, but with no header, footer, sectioning content, or heading content descendants."] =>
      some { base := .flow, minusTags := ["footer", "header"], minusCats := ["sectioning", "heading"] }
  | ["Flow content, but with no heading content descendants, no sectioning content descendants, and no header, footer, or address element descendants."] =>
      some { base := .flow, minusTags := ["address", "footer", "header"], minusCats := ["sectioning", "heading"] }
  | ["Flow content, but with no form element descendants."] => some { base := .flow, minusTags := ["form"] }
  | ["Flow content, but with no descendant table elements."] => some { base := .flow, minusTags := ["table"] }
  | ["Phrasing content, but there must be no dfn element descendants."] => some { base := .phrasing, minusTags := ["dfn"] }
  | ["Phrasing content, but there must be no progress element descendants."] => some { base := .phrasing, minusTags := ["progress"] }
  | ["Phrasing content, but there must be no meter element descendants."] => some { base := .phrasing, minusTags := ["meter"] }
  | ["Phrasing content, optionally intermixed with heading content."] => some { base := .phrasing, plusCats := ["heading"] }
  | _ => none


/-- A transparent element: what it excludes from its context. -/
structure Transparent where
  name : String
  minusTags : List String := []
  minusCats : List String := []
  deriving Repr, Inhabited

/-- The transparent elements and their exclusions, from their sentences. -/
def transparents : List Transparent :=
  [{ name := "a", minusTags := ["a"], minusCats := ["interactive"] },
   { name := "ins" }, { name := "del" }, { name := "object" }, { name := "slot" },
   { name := "map" },
   { name := "canvas", minusCats := ["interactive"] },
   { name := "audio", minusCats := ["media"] },
   { name := "video", minusCats := ["media"] },
   { name := "noscript", minusTags := ["noscript"] }]


/-- An authored child-level reading of a sentence, pinned to the digest of
the block it reads. -/
structure Reading where
  name : String
  digest : String
  model : Model
  note : String
  deriving Repr, Inhabited

def readings : List Reading :=
  [{ name := "html", digest := "d750901ea4cfb34e89bd18c4329ef5ca1a68a631913a4a507035aa1120fa9d70",
     model := { base := .only ["head", "body"] false }, note := "\"A head element followed by a body element.\": the two, order not enforced" },
   { name := "head", digest := "faa39dd2013b03e002218eb818f5e348249adb7d2229a5cab975f20618222a6a",
     model := { base := .metadata }, note := "metadata content; the one-title and at-most-one-base bounds are not enforced" },
   { name := "hgroup", digest := "7aa278b8f2ea0c9db066537a70b1696bf73217f0f5065d509bcca35cb958716d",
     model := { base := .only ["p", "h1", "h2", "h3", "h4", "h5", "h6"] true }, note := "\"Zero or more p elements, followed by one h1..h6 element, followed by zero or more p elements\": membership, order not enforced" },
   { name := "dl", digest := "4038905c1cfb9c4fdedabd2fba6820cc7b121efc5d27a249d82ea2bacd85154c", model := { base := .only ["dt", "dd", "div"] true }, note := "dt/dd groups or div wrappers: membership, grouping not enforced" },
   { name := "figure", digest := "623700751d997a7e952558f4c71397c41d4fe50b71c7770cabc01c4b623ddae6", model := { base := .flow, plusTags := ["figcaption"] }, note := "flow content with one figcaption first or last: the count and position are not enforced" },
   { name := "div", digest := "4ab24ed390f90916468b62af3182f12e331da180b1803af35e66bd70546096c2", model := { base := .flow }, note := "flow content; the dt/dd case of a div inside dl is not admitted (the stricter side)" },
   { name := "ruby", digest := "38a3b8701b38542d393c27fa9a73dc46e5e697b4553ab41ee461164fef93a3e6", model := { base := .phrasing, plusTags := ["rt", "rp"] }, note := "\"See prose.\": phrasing with rt and rp annotations, order not enforced" },
   { name := "time", digest := "cb8a2f7a8cf252a847c6f611d9bd4e31f842e23a8796ce7557330f5f438ecb03", model := { base := .phrasing }, note := "phrasing content when datetime is present; the attribute is not seen" },
   { name := "picture", digest := "b2ba70e3ad690bf0dd72fe109abf4e97d3105e0b00b561ad80d6bae8b7ff5022", model := { base := .only ["source", "img"] true }, note := "sources then one img: membership, the count and order are not enforced" },
   { name := "table", digest := "7281e376185588441f7c35a87b2c817c2c681688caa31a6aaf288c590e50390c", model := { base := .only ["caption", "colgroup", "thead", "tbody", "tfoot", "tr"] true }, note := "\"In this order: ...\": membership, order and the tbody-or-tr choice not enforced" },
   { name := "colgroup", digest := "c529973ec5d53cfa7e031bda87dc827c56f32863f97904046905775c308b107d", model := { base := .only ["col", "template"] false }, note := "col and template when span is absent; the attribute is not seen" },
   { name := "label", digest := "b2f05b54776d0ee82a52278d7e4dab759112cdea6f238d4cf2ac650aa3999087", model := { base := .phrasing, minusTags := ["label"] }, note := "phrasing with no label descendants; the labelable-descendant rule is not seen" },
   { name := "button", digest := "aac62eb3d4ff82ce8800119cd9dae55e93365ce280f03d37fac892055cf7e9d6", model := { base := .phrasing, minusCats := ["interactive"] }, note := "phrasing with no interactive content descendant; tabindex is not seen" },
   { name := "select", digest := "fe337946a811fc79b1fed2bf90064f2ee72052cd216a46ac180a2c10f64df393", model := { base := .only ["button", "option", "optgroup", "hr", "noscript"] true }, note := "the customizable-select model: membership, the one-button bound not enforced" },
   { name := "datalist", digest := "424561578425cce06aed8ab0becc70e1a2a4d492e8dda5f337c8b37dc54ecb10", model := { base := .phrasing, plusTags := ["option"] }, note := "\"Either: phrasing content. Or: Zero or more option and script-supporting elements.\": the union" },
   { name := "optgroup", digest := "e3977cee5a08b732a7178474cee97d9941ce99a2c1f83ae5688187ed5a19c738", model := { base := .only ["legend", "option", "noscript", "div"] true }, note := "the customizable-select model: membership" },
   { name := "option", digest := "1375746e60ce3c9e85146c7ab0f95a0c0a1582a4f7acaa1e62dcee2ab5ba1263", model := { base := .text }, note := "text; the label/value cases and the customizable-select div case are not admitted (the stricter side)" },
   { name := "fieldset", digest := "65e8d175a18f7adb66e20cdfca9d158b73a235f662bb38cf4202e1a6a66be5ac", model := { base := .flow, plusTags := ["legend"] }, note := "\"Optionally, a legend element, followed by flow content.\": position not enforced" },
   { name := "legend", digest := "96b445d4e81c4530b9ba5e5fc341d803d62361e806955356b2d9bf04ca0b6c0d", model := { base := .phrasing, plusCats := ["heading"] }, note := "\"Phrasing content, optionally intermixed with heading content.\" outside an optgroup" },
   { name := "details", digest := "dae4636d68540e86cc746b5f565213e110a4cfa1299e50a4acdb21c4e853b9a9", model := { base := .flow, plusTags := ["summary"] }, note := "\"One summary element followed by flow content.\": the count and position are not enforced" },
   { name := "script", digest := "564635dd098ee1924180c4a7cedebb715fe0b4ecb5766522869e11ee7364047c", model := { base := .text }, note := "script content restrictions are prose; text" },
   { name := "template", digest := "66a1966da3e921dcc46fe23ff1b42c9b63ce8f32c47aa630ee06b4356f9fb622", model := { base := .flow }, note := "the DOM children are \"Nothing\" and the template contents are a fragment the HTML syntax writes inside the element; the authoring reading is flow content" },
   { name := "canvas", digest := "d57b26e741d2789236bd9b8e02967d8f2974b1c13dcbb5417639cd44afc2ce1e", model := { base := .flow, minusCats := ["interactive"] }, note := "transparent, with no interactive content descendants; the exceptions for a, img with usemap, button and some inputs are not seen; own set in flow context" },
   { name := "a", digest := "47fe774c5f4df179114fc71a733cdecab8e037191196918924eed477d89cb40e", model := { base := .flow, minusTags := ["a"], minusCats := ["interactive"] }, note := "transparent, with no interactive content or a descendants; own set in flow context" },
   { name := "video", digest := "aebbd45003249b39a1f4fd1a5eb1832215cee9ba7b0609c5b96feb6ce4b32858", model := { base := .flow, minusCats := ["media"] }, note := "transparent with no media element descendants; source and track are labelled direct children; own set in flow context" },
   { name := "audio", digest := "9170b66d7cb774c8a033e021bdbd1edd28383365e6290ae4230273ade3a694ff", model := { base := .flow, minusCats := ["media"] }, note := "as video" },
   { name := "noscript", digest := "8dbcd80015740fb7da22de141aa329b53180e5bd3f17295ba08e3194ac7bf36d", model := { base := .flow, minusTags := ["noscript"] }, note := "transparent with no noscript descendants outside head; in head, link, style and meta (a payload override); own set in flow context" },
   { name := "ins", digest := "59ba25f87f03aeda50ba77b50110d02fa4cd90a4a95193154d8ba7747f3ce5e8", model := { base := .flow }, note := "transparent; own set in flow context" },
   { name := "del", digest := "957c3085f9a164a6e4aebeb7a3c58463552ecdcda02f17475f00c90b50577ca2", model := { base := .flow }, note := "transparent; own set in flow context" },
   { name := "object", digest := "5a60e4935a0bd0bf2c39e78e3bf668d9538c9f11a87c64d292ff8fc06e132875", model := { base := .flow }, note := "transparent; own set in flow context" },
   { name := "slot", digest := "762ea10fa3fcac173bd0a1204ba1538c97f89ee0741a45cb58ac358147bc1899", model := { base := .flow }, note := "transparent; own set in flow context" },
   { name := "map", digest := "ce48cdbf08102b1d3a8a0fef92a8c61dcd574406f27e7755c6180b64830cb165", model := { base := .flow, plusTags := ["area"] }, note := "transparent; area is admitted under a map; own set in flow context" }]


/-! ## Sequences: the ordered models -/

/-- A regular expression over child tags. `base except` is one child the
element's base admits, other than the named tags; text counts as the tag
`pcdata`. -/
inductive Seq where
  | eps
  | tag (name : String)
  | base (except : List String)
  | seq (a b : Seq)
  | alt (a b : Seq)
  | star (a : Seq)
  | opt (a : Seq)
  | plus (a : Seq)
  deriving BEq, Repr, Inhabited

/-- An ordered reading of a sentence, pinned to its block digest: the
sequence the children must follow, and whether the script-supporting
elements may be intermixed anywhere. -/
structure Sequence where
  name : String
  digest : String
  seq : Seq
  interleave : Bool
  note : String
  deriving Repr, Inhabited

open _root_.Whatwg.Html.Schema.Readings.Seq in
/-- The ordered models, read as sequences over the child tags. Where a
sentence says "optionally intermixed with script-supporting elements", the
sequence is matched with those elements removed. -/
def sequences : List Sequence :=
  [{ name := "html", digest := "d750901ea4cfb34e89bd18c4329ef5ca1a68a631913a4a507035aa1120fa9d70",
     seq := seq (tag "head") (tag "body"), interleave := false,
     note := "\"A head element followed by a body element.\"" },
   { name := "head", digest := "faa39dd2013b03e002218eb818f5e348249adb7d2229a5cab975f20618222a6a",
     seq := seq (star (base ["title"])) (seq (tag "title") (star (base ["title"]))), interleave := false,
     note := "metadata content with exactly one title; the at-most-one base bound is not enforced, and the iframe srcdoc case (no title) is not read" },
   { name := "hgroup", digest := "7aa278b8f2ea0c9db066537a70b1696bf73217f0f5065d509bcca35cb958716d",
     seq := seq (star (tag "p")) (seq (alt (tag "h1") (alt (tag "h2") (alt (tag "h3") (alt (tag "h4") (alt (tag "h5") (tag "h6")))))) (star (tag "p"))),
     interleave := true, note := "\"Zero or more p elements, followed by one h1..h6 element, followed by zero or more p elements, optionally intermixed with script-supporting elements.\"" },
   { name := "dl", digest := "4038905c1cfb9c4fdedabd2fba6820cc7b121efc5d27a249d82ea2bacd85154c", seq := alt (star (seq (plus (tag "dt")) (plus (tag "dd")))) (plus (tag "div")), interleave := true,
     note := "groups of one or more dt then one or more dd, or one or more div, optionally intermixed with script-supporting elements" },
   { name := "figure", digest := "623700751d997a7e952558f4c71397c41d4fe50b71c7770cabc01c4b623ddae6", seq := alt (seq (tag "figcaption") (star (base ["figcaption"]))) (alt (seq (star (base ["figcaption"])) (tag "figcaption")) (star (base ["figcaption"]))),
     interleave := false, note := "\"Either: one figcaption element followed by flow content. Or: flow content followed by one figcaption element. Or: flow content.\"" },
   { name := "picture", digest := "b2ba70e3ad690bf0dd72fe109abf4e97d3105e0b00b561ad80d6bae8b7ff5022", seq := seq (star (tag "source")) (tag "img"), interleave := true,
     note := "\"Zero or more source elements, followed by one img element, optionally intermixed with script-supporting elements.\"" },
   { name := "table", digest := "7281e376185588441f7c35a87b2c817c2c681688caa31a6aaf288c590e50390c", seq := seq (opt (tag "caption")) (seq (star (tag "colgroup")) (seq (opt (tag "thead")) (seq (alt (star (tag "tbody")) (plus (tag "tr"))) (opt (tag "tfoot"))))),
     interleave := true, note := "\"In this order: optionally a caption element, followed by zero or more colgroup elements, followed optionally by a thead element, followed by either zero or more tbody elements or one or more tr elements, followed optionally by a tfoot element, optionally intermixed with one or more script-supporting elements.\"" },
   { name := "fieldset", digest := "65e8d175a18f7adb66e20cdfca9d158b73a235f662bb38cf4202e1a6a66be5ac", seq := seq (opt (tag "legend")) (star (base ["legend"])), interleave := false,
     note := "\"Optionally, a legend element, followed by flow content.\"" },
   { name := "details", digest := "dae4636d68540e86cc746b5f565213e110a4cfa1299e50a4acdb21c4e853b9a9", seq := seq (tag "summary") (star (base ["summary"])), interleave := false,
     note := "\"One summary element followed by flow content.\"" },
   { name := "select", digest := "fe337946a811fc79b1fed2bf90064f2ee72052cd216a46ac180a2c10f64df393", seq := seq (opt (tag "button")) (star (alt (tag "option") (alt (tag "optgroup") (alt (tag "hr") (tag "noscript"))))),
     interleave := true, note := "zero or one button, then option, optgroup, hr and noscript elements, optionally intermixed with script-supporting elements" },
   { name := "optgroup", digest := "e3977cee5a08b732a7178474cee97d9941ce99a2c1f83ae5688187ed5a19c738", seq := seq (opt (tag "legend")) (star (alt (tag "option") (alt (tag "noscript") (tag "div")))),
     interleave := true, note := "zero or one legend, then option, noscript and div elements, optionally intermixed with script-supporting elements" },
   { name := "audio", digest := "9170b66d7cb774c8a033e021bdbd1edd28383365e6290ae4230273ade3a694ff", seq := seq (star (tag "source")) (seq (star (tag "track")) (star (base ["source", "track"]))), interleave := false,
     note := "source elements, then track elements, then transparent content; the src-attribute case (no source elements) is the same sequence with none" },
   { name := "video", digest := "aebbd45003249b39a1f4fd1a5eb1832215cee9ba7b0609c5b96feb6ce4b32858", seq := seq (star (tag "source")) (seq (star (tag "track")) (star (base ["source", "track"]))), interleave := false,
     note := "as audio" }]

/-- The direct children a sentence admits first and outside any base:
the parent and the child. -/
def labelled : List (String × String) :=
  [("audio", "source"), ("audio", "track"), ("video", "source"), ("video", "track"), ("map", "area")]

/-- A transparent element whose base in one context is not the context's:
the context base name, the element, the base it takes. -/
def baseOverrides : List (String × String × BaseKind) :=
  [("metadata", "noscript", .only ["link", "style", "meta"] false)]

/-- Attributes the standard defines outside its index, admitted on every
element: the markup name, the kind (`prefix` or `text`), the note. -/
def extraAttrs : List (String × String × String) :=
  [("data-", "prefix", "custom data attribute prefix (`data-*`), on every element"),
   ("role", "text", "ARIA role, defined in ARIA in HTML, on every element"),
   ("aria-", "prefix", "ARIA state and property prefix (`aria-*`), on every element")]

end Whatwg.Html.Schema.Readings
