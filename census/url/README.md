# URL census authored inputs

The URL census is still being assembled under U2. These are authored source
decisions, not generated output. No file here establishes a denominator or
coverage state until the full join and reporting gates are admitted.

`spans.tsv` records authored identities and containing source spans for the
explicit algorithm blocks, parser-state clauses, unwrapped computational
hooks, IDL declarations, validation conditions, carriers, slots, grammar
predicates, cross-cutting laws and prose requirements. Fields
are tab-separated: `id`, `byte-start`, `byte-end`, `origin-ordinals`, `parent`.
Origin ordinals refer to `generated/url-source-inventory.tsv` at the fixed
URL pin; multiple origins are comma-separated. A dash means no parent.
The row kind is its ID prefix, using the `Gates.Census.Kind` vocabulary.

`explanations.tsv` records `byte-start`, `byte-end` and the verbatim reason
for explanatory source regions. Notes that state a law, constraint or
audience-specific requirement retain a source row. Explanations of examples
name their related source rows so the examples remain available as witnesses.

`dispositions.tsv` classifies the nearest source section and row kind;
`overrides.tsv` records any justified row-specific exception. Every rule
must be used, and each row must resolve without an inferred default.
`dependencies.tsv` gives exactly one explicit dependency list per row;
`externals.tsv` names the external identities used by those lists.
`docs/URL-DEPENDENCIES.md` defines their meanings and open obligations.

These offsets and origin choices are authored decisions. `lake exe urlcensus`
reads all six files, checks the pinned source and strict joins, and compares
`generated/url-census.tsv` and `generated/url-source-assignments.tsv` against
a fresh Lean regeneration. `lake exe urlcensus --write` writes both outputs.
The census contains each span and unique in-span prefix anchor's digest;
both outputs hash the exact bytes of all six authored inputs. The format
and reader are frozen in `docs/URL-CENSUS-INPUT-INTERFACE.md`.

Canonical-owner records, external semantic assurance, declaration snapshots
and the numerator/report still require their separate joins. Missing
source assignments are errors under `docs/URL-CENSUS-INTERFACE.md`, not
implicit exclusions. `docs/URL-SOURCE-REVIEW.md` retains the source-reading
obligations and review evidence. An interval assignment is not evidence that
the rows' laws hold. Independent review of the dispositions and dependency
meanings remains distinct from the mechanical identity checks.

Host and hostname parser cases share one clause span and have two origins.
The basic parser is their parent, as it is for the other state clauses.
The opaque-path clause retains the legacy source ID through its origin;
the census name follows the current algorithm meaning. IDL header spans
retain the extended attributes; member rows are individual source statements,
whose context/dependency on their interface must be recorded separately.
