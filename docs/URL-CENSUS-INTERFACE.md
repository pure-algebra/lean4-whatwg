# URL semantic census join interface (U2b)

Status: declaration record frozen before the separate breaker packet,
2026-09-05. This tooling belongs to `Gates.UrlCensus` and contributes to the
open `URL-PG-CENSUS` graph in `docs/URL-CENSUS-DAG.md`. The fixed source pin
remains owned by `SPEC-MANIFEST.md`. This record owns the join interface and
its acceptance conditions, not semantic dispositions or coverage states.

## Public declarations and existing-type relationships

All records and operations below are tooling. `SourceRow` is an adapter
around the existing canonical `Gates.Census.Row`, adding authored disposition,
parent, dependency and origin metadata. It neither replaces that carrier nor
defines a URL runtime value. `Explanation` is an authored source region with
a justification for remaining outside semantic rows. `Assignment` is a
derived view of one `Gates.UrlInventory.Entry`; it has no independent source
identity. All private helpers and generated constructors, projections and
instances inherit this ownership and assurance scope.

```lean
namespace Gates.UrlCensus
structure SourceRow where
  row : Gates.Census.Row
  disposition : Gates.Census.Disposition
  parent : Option String := none
  dependencies : Array String := #[]
  origins : Array Nat
  deriving Inhabited
structure Explanation where
  b : Nat
  e : Nat
  reason : String
  deriving Repr, BEq, DecidableEq, Inhabited
structure Assignment where
  candidate : Gates.UrlInventory.Entry
  owner : Option String
  reason : String
  deriving Repr, BEq, DecidableEq, Inhabited
def assign (bs : ByteArray) (rows : Array SourceRow)
    (explanations : Array Explanation) (externalIds : Array String) :
    Except String (Array Assignment)
end Gates.UrlCensus
```

## Frozen acceptance conditions

`assign` obtains its candidates by running `Gates.UrlInventory.scan` on the
input bytes; callers cannot supply a truncated candidate list. All offsets
are UTF-8 byte offsets, `[b,e)`. No URL denominator or coverage state is
returned by this function. A failure is `Except.error`; diagnostics are not
part of the frozen surface.

Every source row must have a unique nonempty ID of the form
`<row.kind.name>.<nonempty-name>`. Its source span is nonempty, within the
input and valid UTF-8. The anchor starts at `spanB`, has positive length,
ends no later than `spanE`, is valid UTF-8, and occurs exactly once in the
whole input. The row's `anchorB` must equal `spanB`. A duplicate ID or an
invalid, repeated, or misplaced anchor is an error.

`origins` is a nonempty array of one-based candidate ordinals at this pin.
Every ordinal must exist, be unique within its row and across all rows, and
refer to a candidate wholly contained by that row's source span. These are
the reviewed source entities that motivate the row. They are not inferred
from spelling. Multiple aliases or a shared algorithm body can be origins
of one row; they must not create duplicate canonical rows for one span.

Rows form an explicitly declared interval forest. Two spans must be disjoint
or one must strictly contain the other; crossing spans and identical spans
are errors. A contained row's `parent` must name its immediate enclosing row;
a root row must have `parent = none`. Missing parents, incorrect parents,
cycles and self-parent references are errors. A parent pointer alone cannot
invent containment.

Every dependency must resolve either to another row ID or to a declared
external ID. Row IDs and external IDs are disjoint, and the external list
contains unique nonempty names. Dependencies have no duplicates and cannot
reference the same row itself. Every declared external ID must be used;
unused external declarations are errors. Mutual dependencies between rows
are permitted: a dependency relation is not the parent forest. This join
checks identity only; the owning packet must separately establish the
dependency's semantics, pin, API and assurance route.

Explanatory regions have nonempty valid UTF-8 spans within the input and a
non-whitespace reason. Here whitespace means the same five ASCII characters
as the URL lexical reader: tab, LF, form feed, CR and space. No Unicode
normalization is applied. Regions may contain semantic rows, but can only account
for candidates that belong to no semantic row. Two regions must be disjoint;
overlapping or identical explanatory regions are rejected. Every region
must account for at least one candidate; an unused region is an error.
There is no implicit catch-all explanation or default disposition.

For each candidate, select the smallest semantic row span that wholly
contains it. Its assignment has `owner = some row.id` and `reason = ""`.
If no semantic row contains a heading, retain it as `owner = none` and
`reason = "structural heading"`. Every other candidate with no semantic
owner must be wholly contained in exactly one explanatory region; retain
`owner = none` and that region's reason verbatim. A candidate that has no
such assignment is an error. Output order and candidate data are exactly
those returned by `scan`. Each declared origin must ultimately be assigned
to the row that declares it, not a nested child or another row.

This is a strict join over reviewed authored input. A successful join proves
neither that an explanation is semantically justified nor that the chosen
spans contain all normative meaning. Independent source review remains
required before census cutover. The initial data packet must retain parser
state bodies and parent links, shared host/hostname behavior, alias and
parameter roles, out-of-wrapper hooks, slot initial values, and trailing
grammar clauses identified in `docs/URL-SOURCE-REVIEW.md`.

The finite breaker command is `lake build WhatwgTest.Url.CensusContract`.
Its red packet must be committed before implementation. The source pin,
fully classified authored census, deterministic projection, generated
assurance joins and numerator/report integration are separate remaining U2
obligations; the pure join's finite probes cannot close them by themselves.
