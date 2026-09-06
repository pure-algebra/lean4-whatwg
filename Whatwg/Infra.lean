import Whatwg.Infra.Bytes.Byte
import Whatwg.Infra.Bytes.Sequence
import Whatwg.Infra.Namespaces
import Whatwg.Infra.Primitive.Integer
import Whatwg.Infra.Primitive.Singleton
import Whatwg.Infra.Text.Case
import Whatwg.Infra.Text.CodePoint
import Whatwg.Infra.Text.Codec
import Whatwg.Infra.Text.Order
import Whatwg.Infra.Text.Scalar
import Whatwg.Infra.Text.Scan
import Whatwg.Infra.Text.String
import Whatwg.Infra.Text.Substring
import Whatwg.Infra.Text.Whitespace

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

The declaration-free W5 root (`docs/WHATWG-PACKAGE-PLAN.md`) now imports the
byte and text helpers added at `c610a5e`, so the common audit reaches them.
`docs/INFRA-PROOF-PLAN.md` records their intended obligations; import reachability
and elaboration do not close the remaining Infra assurance work.
-/
