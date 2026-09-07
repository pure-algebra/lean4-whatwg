import Whatwg.Url.PercentEncoding
import Whatwg.Url.Host
import Whatwg.Url.Record
import Whatwg.Url.Parser
import Whatwg.Url.Serializer
import Whatwg.Url.Origin
import Whatwg.Url.Rendering
import Whatwg.Url.FormUrlEncoded
import Whatwg.Url.Api.Url
import Whatwg.Url.Api.UrlSearchParams
import Whatwg.Url.Boundary

/-!
# Whatwg.Url

The WHATWG URL Standard: percent encoding, hosts, URL records, parsing and serialization,
origins, rendering, form encoding, and the URL and URLSearchParams APIs.

Authority: `whatwg/url` commit `55d6699373ba68a16ec182f34222a74ed8bc3dac`, source `url.bs`,
sealed under `vendor/whatwg-url-55d66993/`. `SPEC-MANIFEST.md` owns the pin and dispositions;
`docs/PROVENANCE.md` owns the fetch and digest cross-check. The WPT `url/` corpus is evidence
at the existing WPT pin, not the semantic owner.

This root and every imported URL module are declaration-free bootstrap stubs. The URL census,
public declaration records, frozen breaker packets, and proofs follow `docs/URL-PACKAGE-PLAN.md`.
-/
