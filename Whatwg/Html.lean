import Whatwg.Html.Schema
import Whatwg.Html.Content.Admission
import Whatwg.Html.Content.Transparent
import Whatwg.Html.Content.Lattice
import Whatwg.Html.Content.Divergence
import Whatwg.Html.Node.Raw
import Whatwg.Html.Node.Typed
import Whatwg.Html.Node.Erasure
import Whatwg.Html.Node.Admit
import Whatwg.Html.Node.Evidence
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Print.Escape
import Whatwg.Html.Print.Render
import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Bridge.Tyxml
import Whatwg.Html.Svg
import Whatwg.Html.Audit.Receipts

/-!
# Whatwg.Html

The HTML content model as a typed document algebra: a finite tag universe,
content sets closed under the transparent exclusions, a decidable
child-admission relation, tag-indexed trees whose admission obligations are
discharged at construction, a markup elaborator, and a serializer. The
schema is generated from the HTML Standard's own element definitions
(ruling HP-12 of `docs/HTML-PACKAGE-PLAN.md`); OCaml TyXML, whose
polymorphic-variant row types encode the same content model, is the
reference for the shape of the library and a cross-check, and nothing here
is a theorem about it.

Authority pins (`SPEC-MANIFEST.md`, `docs/PROVENANCE.md`):

- The HTML Standard, `whatwg/html` commit
  `746f2ede8a56bc01204e0f9cc23da33b37c6fbab` ("Review Draft Publication:
  July 2026"), `source` sealed under `vendor/whatwg-html-746f2ede/`: the
  semantic owner and the source of the schema. The projection
  `generated/html-standard-elements.tsv` and the generated modules under
  `Whatwg.Html.Schema` are regenerated and checked by `lake exe htmlstandard`;
  the readings of the standard's prose sentences are authored in
  `Gates/HtmlStandardEmit.lean`, each pinned to the span digest it reads.
- TyXML 4.6.0, `ocsigen/tyxml` commit
  `d2916535536f2134bad7793a598ba5b7327cae41`, sealed under
  `vendor/tyxml-d2916535/`: the reference. Its projection
  `generated/tyxml-html-schema.tsv` (`lake exe tyxmlschema`) is a
  cross-check, and its attribute universe stands in for the standard's
  until H6.1b.

`Whatwg.Html.Schema` holds the generated data (tags, content sets, element
rows with their readings and digests, and the interim attributes) behind
the drift gates,
`Whatwg.Html.Content` holds the lattice, transparent coherence and the
admission relation, `Whatwg.Html.Node` holds the raw tree, the tag-indexed
tree, the `admits` tactic that discharges its obligations by compiled
evaluation and a kernel-checked `Eq.refl`, its generated combinators and
erasure, and H4 adds
`Whatwg.Html.Print` with the escaper, the serializer, and the decoder that
inverts the serializer on the sublanguage its own output determines.
H5 adds `Whatwg.Html.Syntax`, the `html!` markup elaborator, with
`Whatwg.Html.Node.Evidence`, the erased evidence it attaches to a raw
literal. `Whatwg.Html.Bridge`, `Whatwg.Html.Svg` and `Whatwg.Html.Audit`
are still a docstring and nothing else. Every semantic declaration after
this arrives behind a frozen contract packet.
-/
