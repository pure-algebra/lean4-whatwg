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
import Whatwg.Svg.Value.Grammar
import Whatwg.Svg.Value.Number
import Whatwg.Svg.Value.Cohort
import Whatwg.Svg.Value.Path
import Whatwg.Svg.Value.Points
import Whatwg.Svg.Value.ViewBox
import Whatwg.Svg.Value.Transform
import Whatwg.Svg.Value.Attribute

/-!
# Whatwg.Svg

SVG 2 for inline use: the elements, categories, content models and attributes of the W3C
standard, as the schema an HTML tree's SVG subtree is checked against. The plan is
`docs/SVG-PACKAGE-PLAN.md`. The authority is SVG 2 at the pin `vendor/w3c-svgwg-47e645ef/`
(`SPEC-MANIFEST.md`).

The library has four layers:

- `Whatwg.Svg.Data` names no schema: a finite universe, a set as a mask over it, and a name
  table with its two laws;
- `Whatwg.Svg.Schema.Tags`, `Categories`, `Attributes` and `ContentModel` are generated from
  the pin's definitions files by `lake exe whatwg_svgdefinitions`, which fails on a byte of
  drift. `Readings` is authored: it reads the four content models that the definitions state
  as a sentence. `Universe` is authored: it says what the generated data is an instance of;
- `Whatwg.Svg.Content.Context` is the position in an SVG subtree, its transition, and the
  judgments of one node;
- `Whatwg.Svg.Value.Grammar` is the one description that reads and prints an attribute value,
  with its retraction and the soundness of its reader proved once (slice S4a). Each grammar is
  one value of it: `Number` (the number and the separators), `Path`, `Points`, `ViewBox` and
  `Transform` (slices S4b and S4c). `Cohort` holds the law of a number's canonical value, and
  `Attribute` says which grammar judges which attribute.

The library imports no module of `Whatwg.Html` (ruling SV-6). The seam that admits `svg` in an
HTML tree is in `Whatwg.Html`, and so is the judgment of the values of a tree.
`generated/svg-dangling.tsv` lists the names the definitions cite and never declare.
-/
