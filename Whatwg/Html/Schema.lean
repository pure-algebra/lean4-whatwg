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
the attribute universe of the standard's attribute and event-handler
indexes with each row's value kind and one attribute set per element, one
row per element with its reading and span digest, and the standard's
element definitions and index rows as text (`Standard`). All five modules
are written by `lake exe htmlstandard --write` and checked for byte drift
by `lake exe htmlstandard`. Nothing in them is a proof. Declaration records
for their constants inherit from the schema rows (ruling HP-10).
-/
