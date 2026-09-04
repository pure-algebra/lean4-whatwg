import Whatwg.Html.Schema.Readings
import Whatwg.Html.Schema.Exclusions
import Whatwg.Html.Schema.Condition
import Whatwg.Html.Schema.Tags
import Whatwg.Html.Schema.Sequence
import Whatwg.Html.Schema.Attributes
import Whatwg.Html.Schema.Families
import Whatwg.Html.Schema.ContentModel
import Whatwg.Html.Schema.Standard

/-!
# Whatwg.Html.Schema

The schema (slices H6.1 and H7 of `docs/HTML-PACKAGE-PLAN.md`, rulings
HP-12 and HP-13): the authored readings of the standard's prose
(`Readings`) and the exclusion record (`Exclusions`), and the generated
modules: the element-tag universe of the HTML Standard at the pin with its
markup names both ways, the void and transparent sets; the categories,
bases, each element's own base and descendant exclusions, the base
overrides and the labelled children (`Families`); the attribute universe
with each index row's value kind, one attribute set per element and one
helper row per attribute (`Attributes`); one row per element with its
reading and span digest (`ContentModel`); and the standard's element
definitions and index rows as text (`Standard`). The generated modules are
written by `lake exe htmlstandard --write` and checked for byte drift by
`lake exe htmlstandard`. Nothing in them is a proof.
-/
