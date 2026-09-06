import Whatwg.Infra
import Whatwg.Streams
import Whatwg.Html
import Whatwg.Url

/-!
# Whatwg

WHATWG standards reified in Lean 4, one library per standard. `Whatwg.Infra`
is the Infra Standard's value universe, including the byte and text helpers;
`Whatwg.Streams` is the Streams Standard;
`Whatwg.Html` is the HTML content model ported from TyXML under the HTML
Standard's authority (scaffolded at H1 of `docs/HTML-PACKAGE-PLAN.md`);
`Whatwg.Url` is the URL Standard's declaration-free bootstrap
(`docs/URL-PACKAGE-PLAN.md`). A
consumer imports a standard's root, or this module for all of them.
-/
