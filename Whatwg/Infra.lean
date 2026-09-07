import Whatwg.Infra.Bytes.Byte
import Whatwg.Infra.Bytes.Sequence
import Whatwg.Infra.Primitive.Integer
import Whatwg.Infra.Primitive.Singleton
import Whatwg.Infra.Text.CodePoint
import Whatwg.Infra.Text.String
import Whatwg.Infra.Text.Scalar
import Whatwg.Infra.Text.Codec
import Whatwg.Infra.Text.Case
import Whatwg.Infra.Text.Order
import Whatwg.Infra.Text.Substring
import Whatwg.Infra.Text.Whitespace
import Whatwg.Infra.Text.Scan
import Whatwg.Infra.Namespaces

/-!
# Whatwg.Infra

The WHATWG Infra Standard: byte sequences, code points, scalar-value strings,
lists, ordered maps, structs, and JSON values, the value universe every other
standard's operations take and return (Stratum V of
`docs/REIFICATION-STRATEGY.md`).

Authority pin: `whatwg/infra` commit `3f984adcd24a6d5c53cc26b3e737701808003f3e`
(2026-07-17, "Review Draft Publication: July 2026"), source `infra.bs`, sealed
under `vendor/whatwg-infra-3f984adc/` by `generated/vendor-manifest.tsv`;
`SPEC-MANIFEST.md` owns the pin and `docs/PROVENANCE.md` its fetch record.

This root is declaration-free (slice W5 of `docs/WHATWG-PACKAGE-PLAN.md`). Its
census, breadth scaffold, and first packet follow the P1–P3 order the Streams
library took, under their own contracts.
-/
