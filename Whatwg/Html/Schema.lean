import Whatwg.Html.Schema.Tags
import Whatwg.Html.Schema.Attributes
import Whatwg.Html.Schema.Families
import Whatwg.Html.Schema.ContentModel

/-!
# Whatwg.Html.Schema

The schema of the HTML content model (slice H2 of
`docs/HTML-PACKAGE-PLAN.md`): the element-tag and attribute-tag universes,
every named content set and attribute set as a constructor-dispatch
membership function, and one row per element and attribute constructor.
The four modules below were first transcribed from TyXML 4.6.0 at H2 and
are authored source since 2026-09-06, when the TyXML pin, its projection and
the drift gate were retired (ruling HP-10 as amended); the HTML Standard is
the sole authority. Nothing in them is a proof.
-/
