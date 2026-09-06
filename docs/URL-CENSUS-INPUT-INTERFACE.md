# URL authored census input and projection interface (U2c)

Status: frozen before the independent breaker, 2026-09-05, base `9c8cb49`.
This tooling contributes to `URL-PG-CENSUS`; source pins and dispositions
remain owned by `SPEC-MANIFEST.md`. U2b's strict assignment behavior remains
owned by `docs/URL-CENSUS-INTERFACE.md` and is not weakened here.

## Declarations and canonical relationships

The owner is `Gates.UrlCensusInput`. `Inputs` is a raw authored-file view,
not a semantic carrier. Returned rows and assignments reuse the canonical
`Gates.UrlCensus.SourceRow` and `Assignment`; no second row type is added.
Constructors, instances and private helpers inherit this tooling role and
the census graph. No declaration below models URL execution or grants a
specification coverage state.

```lean
namespace Gates.UrlCensusInput
structure Inputs where
  spans : String
  explanations : String
  dispositions : String
  overrides : String
  dependencies : String
  externals : String
  deriving Inhabited

def build (bs : ByteArray) (inputs : Inputs) :
    Except String (Array Gates.UrlCensus.SourceRow × Array Gates.UrlCensus.Assignment)
def project (bs : ByteArray) (inputs : Inputs) : Except String (String × String)
def cli (args : List String) : IO UInt32
end Gates.UrlCensusInput
```

## Authored text formats

LF separates lines; one terminal CR per line is removed, allowing CRLF.
Blank lines and whole-line comments are ignored after trimming the five
ASCII whitespace characters (tab, LF, form feed, CR, space). A comment's
first non-whitespace character is `#`. There are no inline comments.
Other fields are retained verbatim, with no general field trimming.
Fields are tab-separated; extra or missing fields are errors.

An identity token is nonempty and contains only ASCII letters, digits,
dot, underscore or hyphen. A natural-number token uses canonical ASCII
decimal digits: `0` or a nonzero digit followed by digits. Signs, whitespace,
Unicode digits and redundant leading zeros are rejected.

- `spans`: five fields `id`, `byte-start`, `byte-end`, `origins`, `parent`.
  The ID's prefix before the first dot must be a `Gates.Census.Kind.name`
  with a nonempty suffix. Origins are a nonempty comma-separated list of
  natural numbers; their positive/existence/uniqueness checks are U2b's.
  Parent is an identity token or `-` for none. Duplicate IDs fail.
- `explanations`: three fields `byte-start`, `byte-end`, `reason`. Reasons
  retain their exact text. Valid spans and nonblank justification are U2b's.
- `dispositions`: the existing three-field `Gates.Census.parseDispositions`
  format: `section-id`, `kind-or-*`, `disposition`. Section IDs are nonempty
  strings without ASCII whitespace; heading IDs may contain punctuation
  beyond the row identity-token vocabulary. Kind and disposition use
  the existing canonical vocabularies. Duplicate section/kind pairs fail.
- `overrides`: the existing three-field `Gates.Census.parseOverrides`
  format: `row-id`, `disposition`, `reason`. IDs are identity tokens and
  reasons contain a character beyond the five ASCII whitespace characters.
  Duplicate IDs fail. The reason is retained in the authored input digest.
- `dependencies`: two fields `row-id`, `dependencies`. Every source row
  requires exactly one entry, even when it has no dependencies (`-`). A
  nonempty list is comma-separated identity tokens. Missing, duplicate and
  unused row entries fail. Dependency existence, duplicates, self-reference
  and external-use checks remain U2b's; cycles between distinct rows are
  permitted.
- `externals`: one identity token per data line. Every external ID must
  begin with `ext.` and have a nonempty suffix. They are dependency identities;
  their pins, semantics and assurance remain separately reviewed obligations.
  Duplicate, colliding and unused identities fail under U2b.

`build` scans the source with `Gates.UrlInventory.scan`. Each row's section
is the last heading candidate whose start is at or before that row's span
start (or the empty section when none exists). A row-specific override wins;
otherwise a rule for that section and exact kind wins over its wildcard.
There is no ancestor-section fallback or inferred default. Reuse the existing
disposition parser/resolver and record which rule/override each row uses.
Unresolved rows and unused rules/overrides are errors.

Generate anchors only from a row's own prefix. Try the existing
`Gates.Census.anchorLadder` lengths in order, restricted to lengths below
the row length, then the full row length. Each attempted end advances to
a UTF-8 boundary without passing the row end. Choose the first prefix that
occurs exactly once in the entire input (overlapping matches count).
For a short span this can be its entire contents. If no such prefix exists,
fail; do not borrow later source text to make it unique. Empty, invalid,
out-of-input or non-UTF-8 row spans fail before anchor generation.

Run `Gates.UrlCensus.assign` on the resulting rows, explanations and external
identities. Any rejection remains a build error. Return source rows sorted
by `Gates.Census.Row.sortKey` and the full assignments in scanner order.
No caller-supplied candidate list or precomputed anchor is accepted.

## Deterministic projections

`project` first calls `build`; it cannot render unchecked authored data.
It returns census TSV, then assignment TSV. Both use LF and a final LF,
with the following first two lines (braces denote computed values and
`\t` denotes one literal tab):

```text
#url-census format=1 generator=Gates.UrlCensusInput input-sha256={source SHA-256} rows={row count}
#kind\tid\tbyte-start\tbyte-end\tspan-sha256\tanchor-end\tanchor-sha256\tparent\torigins\tdisposition\tdependencies
```

```text
#url-source-assignments format=1 generator=Gates.UrlCensusInput input-sha256={source SHA-256} candidates={candidate count}
#ordinal\tkind\tbyte-start\tbyte-end\tspan-sha256\tlabel\tsection\towner\treason
```

Immediately after those two lines, each projection has six comment lines
`#input {name}-sha256={digest}` in the fixed order `spans`, `explanations`,
`dispositions`, `overrides`, `dependencies`, `externals`. Hash the exact
UTF-8 bytes of each supplied string, including comments and line endings.
Use the existing `Gates.Sha256.hexDigest` for every source/input/span/anchor
digest. No source summary is substituted for a span hash.

Census data follows the sorted rows. Parent and empty dependencies use `-`;
origins and dependencies preserve their authored list order with commas.
Assignment data follows scanner order, with one-based ordinals. Candidate
kinds use the spellings in the existing inventory TSV; an absent owner uses
`-`. Preserve candidate fields and reason exactly, escaping backslash as
`\\`, tab as `\t`, LF as `\n` and CR as `\r` in textual fields.
Dispositions retain `Gates.Census.Disposition.name` spellings.

The CLI accepts no arguments (check) or `--write` (regenerate); any other
arguments return 2 and usage. It finds the project root through
`Gates.Common.projectRoot`, verifies the existing pinned URL source digest,
then reads the six correspondingly named TSV files under `census/url/`
as strictly valid UTF-8. It calls `project` before any write.
The outputs are `generated/url-census.tsv` and
`generated/url-source-assignments.tsv`. Check mode rejects missing files or
any byte of drift in either output and reports every differing line.
Write mode writes both exact outputs and names both files. Successful check
or write returns 0 with a scoped PASS line; input/projection errors return 1
with FAIL. No generated declaration/numerator file is written by this packet.

## Assurance boundary

The breaker freezes syntax, join, anchor and projection fixtures before
implementation. The narrow command is
`lake build WhatwgTest.Url.CensusInputContract`. Default build, actual axiom
receipts, source-data review and repository gates follow. Tooling may still
reach choice through existing String/scanner dependencies; no URL semantic
proof is granted that dependency by this reader. Dependency identities do
not prove external implementations, and these source projections establish
no URL coverage report without the later declaration/numerator joins.
