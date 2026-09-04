import Whatwg.Html.Schema.Tags
import Whatwg.Html.Schema.Attributes
import Whatwg.Html.Schema.Families
import Whatwg.Html.Schema.ContentModel
import Whatwg.Html.Schema.Standard

/-!
# Whatwg.Html.Schema

The generated schema (slice H6.1 of `docs/HTML-PACKAGE-PLAN.md`, ruling
HP-12): the element-tag universe of the HTML Standard at the pin, its
categories, every content set as a constructor-dispatch membership
function with the transparent payload table and the derivation parents,
one row per element with its reading and span digest, and the standard's
element definitions as text (`Standard`). `Tags`, `Families` and
`ContentModel` are written by `lake exe htmlstandard --write` and checked
for byte drift by `lake exe htmlstandard`; `Attributes` is written from
TyXML by `lake exe tyxmlschema --write` until H6.1b derives the attribute
universe from the standard. Nothing in them is a proof. Declaration records
for their constants inherit from the schema rows (ruling HP-10).
-/
