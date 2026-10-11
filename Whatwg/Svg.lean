import Whatwg.Svg.Schema.Tags
import Whatwg.Svg.Schema.Categories
import Whatwg.Svg.Schema.Attributes
import Whatwg.Svg.Schema.ContentModel
import Whatwg.Svg.Schema.Readings

/-!
# Whatwg.Svg

SVG 2 for inline use: the elements, categories, content models and attributes of the W3C
standard, as the schema an HTML tree's SVG subtree is checked against. The plan is
`docs/SVG-PACKAGE-PLAN.md`. The authority is SVG 2 at the pin `vendor/w3c-svgwg-47e645ef/`
(`SPEC-MANIFEST.md`).

At slice S2 the library is its schema, and the schema is data:

- `Whatwg.Svg.Schema.Tags`, `Categories`, `Attributes` and `ContentModel` are generated from
  the pin's definitions files by `lake exe whatwg_svgdefinitions`, which fails on a byte of
  drift;
- `Whatwg.Svg.Schema.Readings` is authored: it reads the four content models that the
  definitions state as a sentence.

The library imports no module of `Whatwg.Html` (ruling SV-6). The seam that admits `svg` in an
HTML tree is in `Whatwg.Html` and opens at slice S3; the attribute value grammars open at S4.
This slice states no law: the schema says what the definitions say, and
`generated/svg-dangling.tsv` lists the names they cite and never declare.
-/
