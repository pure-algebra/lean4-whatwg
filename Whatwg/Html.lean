import Whatwg.Html.Schema
import Whatwg.Html.Content.Admission
import Whatwg.Html.Content.Context
import Whatwg.Html.Content.Valid
import Whatwg.Html.Content.Explain
import Whatwg.Html.Content.Values
import Whatwg.Html.Content.Lattice
import Whatwg.Html.Node.Raw
import Whatwg.Html.Node.Walk
import Whatwg.Html.Node.Typed
import Whatwg.Html.Node.Svg
import Whatwg.Html.Node.SvgRead
import Whatwg.Html.Node.SvgKeys
import Whatwg.Html.Node.SvgValid
import Whatwg.Html.Node.Erasure
import Whatwg.Html.Node.Admit
import Whatwg.Html.Node.Evidence
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Print.Escape
import Whatwg.Html.Print.Render
import Whatwg.Html.Print.Xml
import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Svg
import Whatwg.Html.Audit.Receipts

/-!
# Whatwg.Html

The HTML content model as one decidable checker over raw trees and a typed
front end proven sound against it. A position is a context: a base, the
descendant exclusions inherited from every ancestor, and the labelled
direct children its parent admits; `Whatwg.Html.Content.validIn` decides
whether a raw tree may stand at a position, and `Whatwg.Html.Content.Doc`
is the trees it accepts. The typed tree of `Whatwg.Html.Node` carries the
proofs that make its erasure valid (`Element.valid`), the combinators and
the `html!` elaborator build it with diagnostics at the token, and the
serializer prints it. The schema is generated from the HTML Standard's
own element definitions and attribute indexes with an authored reading of
its prose sentences (`Whatwg.Html.Schema.Readings`); OCaml TyXML is the
reference for the shape of the library and a cross-check, and nothing here
is a theorem about it (rulings HP-12 and HP-13).

Authority pins (`SPEC-MANIFEST.md`, `docs/PROVENANCE.md`):

- The HTML Standard, `whatwg/html` commit
  `746f2ede8a56bc01204e0f9cc23da33b37c6fbab` ("Review Draft Publication:
  July 2026"), `source` sealed under `vendor/whatwg-html-746f2ede/`: the
  semantic owner and the source of the schema. The projection
  `generated/html-standard-elements.tsv`, the attribute projection
  `generated/html-standard-attributes.tsv` and the generated modules under
  `Whatwg.Html.Schema` are regenerated and checked by `lake exe whatwg_htmlstandard`;
  the readings of the standard's prose sentences are authored in
  `WhatwgGates/HtmlStandardEmit.lean`, each pinned to the span digest it reads.
- TyXML 4.6.0, `ocsigen/tyxml` commit
  `d2916535536f2134bad7793a598ba5b7327cae41`, sealed under
  `vendor/tyxml-d2916535/`: the reference. Its projection
  `generated/tyxml-html-schema.tsv` (`lake exe tyxmlschema`) is a
  cross-check; nothing under `Whatwg/` reads it.

`Whatwg.Html.Schema` holds the generated data (tags, content sets, the
attribute universe with its value kinds and per-element sets, element rows
with their readings and digests) behind the drift gate,
`Whatwg.Html.Content` holds the categories and bases, the contexts, the
admission relation and the checker, `Whatwg.Html.Node` holds the raw tree,
the context-indexed typed tree with its soundness theorem, the `admits`
tactic that discharges its obligations by compiled evaluation and a
kernel-checked `Eq.refl`, its generated combinators and erasure, and
`Whatwg.Html.Print` holds the escaper and the serializer on the standard's
fragment serialization algorithm, and the decoder that inverts the
serializer on the sublanguage its own output determines.
H5 adds `Whatwg.Html.Syntax`, the `html!` markup elaborator, with
`Whatwg.Html.Node.Evidence`, the erased evidence it attaches to a raw
literal. `Whatwg.Html.Svg` is the seam that admits an `svg` subtree
(`docs/SVG-PACKAGE-PLAN.md`), `Whatwg.Html.Content.Values` judges the
values of its attributes, and `Whatwg.Html.Node.Svg` is the typed SVG node:
an SVG subtree whose attribute values are right by their types, with the
reader `Whatwg.Html.Node.SvgRead` from a raw tree. `Whatwg.Html.Node.SvgValid`
judges the structure of a typed tree by its tags and its keys
(`Whatwg.Html.Node.SvgKeys`), with the law that this is the checker's verdict
on the raw tree, and `Child.ofSvg` places a typed tree in the typed HTML tree.
`Whatwg.Html.Print.Xml` writes the XML serialization of a tree, which a file that holds one
picture needs, on the algorithm of DOM Parsing and Serialization.
`Whatwg.Html.Audit` is still a docstring and nothing else.
-/
