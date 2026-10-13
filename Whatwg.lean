import Whatwg.Infra
import Whatwg.Ecma262
import Whatwg.WebIdl
import Whatwg.Streams
import Whatwg.Html
import Whatwg.Svg
import Whatwg.Css
import Whatwg.Auto
import Whatwg.Url
import Whatwg.Signatures

/-!
# Whatwg

WHATWG standards reified in Lean 4, one library per standard. `Whatwg.Infra`
is the Infra Standard's value universe, including the byte and text helpers;
`Whatwg.Ecma262` is ECMA-262's promise objects and job queue and
`Whatwg.WebIdl` the Web IDL promise and exception vocabulary over them, the
two libraries beneath every Stratum S standard (ruling DB-11; their
declarations landed with the promise slices Q3 and Q3b, graph
`PROMISE-PG-FIRST`);
`Whatwg.Streams` is the Streams Standard;
`Whatwg.Html` is the HTML content model ported from TyXML under the HTML
Standard's authority (scaffolded at H1 of `docs/HTML-PACKAGE-PLAN.md`);
`Whatwg.Svg` is W3C SVG 2 for inline use beside it, a schema generated from the
standard's own definitions (`docs/SVG-PACKAGE-PLAN.md`);
`Whatwg.Url` is the URL Standard, whose percent-encoding packet (slice U3,
graph `URL-PG-PERCENT`) is its first set of declarations
(`docs/URL-PACKAGE-PLAN.md`);
`Whatwg.Signatures` is not a standard but the `Effects.Signature` faces of the
stateful layers, of which the ECMAScript agent's is the first (promise slice
Q5, graph `PROMISE-PG-AGENT`), and the one library that imports `effects`. A
consumer imports a standard's root, or this module for all of them.
-/
