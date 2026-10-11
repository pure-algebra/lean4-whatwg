import Whatwg.Svg.Data.Universe
import Whatwg.Svg.Data.Mask
import Whatwg.Svg.Data.NameTable
import Whatwg.Svg.Schema.Tags
import Whatwg.Svg.Schema.Categories
import Whatwg.Svg.Schema.Attributes
import Whatwg.Svg.Schema.ContentModel
import Whatwg.Svg.Schema.Readings
import Whatwg.Svg.Schema.Universe
import Whatwg.Svg.Content.Context

/-!
# Whatwg.Svg

SVG 2 for inline use: the elements, categories, content models and attributes of the W3C
standard, as the schema an HTML tree's SVG subtree is checked against. The plan is
`docs/SVG-PACKAGE-PLAN.md`. The authority is SVG 2 at the pin `vendor/w3c-svgwg-47e645ef/`
(`SPEC-MANIFEST.md`).

At slice S3a the library has three layers:

- `Whatwg.Svg.Data` names no schema: a finite universe, a set as a mask over it, and a name
  table with its two laws;
- `Whatwg.Svg.Schema.Tags`, `Categories`, `Attributes` and `ContentModel` are generated from
  the pin's definitions files by `lake exe whatwg_svgdefinitions`, which fails on a byte of
  drift. `Readings` is authored: it reads the four content models that the definitions state
  as a sentence. `Universe` is authored: it says what the generated data is an instance of;
- `Whatwg.Svg.Content.Context` is the position in an SVG subtree, its transition, and the
  judgments of one node.

The library imports no module of `Whatwg.Html` (ruling SV-6). The seam that admits `svg` in an
HTML tree is in `Whatwg.Html` and opens at slice S3b; the attribute value grammars open at S4.
`generated/svg-dangling.tsv` lists the names the definitions cite and never declare.
-/
