# Specification coverage

> Scope: the report below is Streams-specific. Infra has a definition census
> and an all-absent generated row list, checked by `lake exe census --standard
> infra`; it has no authored theorem numerator or coverage report yet. The two
> standards never share a denominator.

> URL bootstrap: `Whatwg.Url` has its own pinned source and declaration-free
> scaffold (`docs/URL-PACKAGE-PLAN.md`). URL has no census, numerator, or
> coverage report yet and contributes no rows to the Streams report. U2
> establishes its separate denominator and checked reporting path.

> Promise lane: `Whatwg.WebIdl` and `Whatwg.Ecma262` have pinned sources and
> declaration-free roots (`docs/PROMISE-PACKAGE-PLAN.md`). Neither has a
> census, a numerator, or a coverage report yet, and neither contributes rows
> to any other standard's report. Slice Q2 establishes their two separate
> denominators; the placeholder blocks below record their shape until then.
> Five standards will then hold five denominators that never mix.

This document owns the definition, vocabulary, and reporting format of the
specification coverage metric. Numbers live in generated and emitted facts,
never here. Read this before quoting, changing, or extending coverage.

## What the metric measures

Coverage is the share of pinned specification *rows* that have a Lean
witness. A row is an abstract operation, an internal slot, an IDL member, or
a stated requirement of `index.bs` at the pin, anchored to its text by span
digest. It is not an implementation checklist and not a conformance claim.

Three artefacts carry it once P1 lands:

| Artefact | Role | Owner |
| --- | --- | --- |
| `generated/spec-algorithm-census.tsv` | the denominator: one row per specification row, anchored to the pinned bytes with a span digest | the P1 census generator under `Gates/` |
| `WhatwgTest/Audit/SpecCoverage.lean` | the numerator: the frozen row list with disposition, coverage state, witnesses, receipts, and exact witness statements | authored, test-side |
| a Lean census gate | byte drift of the census and the join between census and Lean rows | CI step |

The pinned source is `vendor/whatwg-streams-b9ba9f49/index.bs`; the
generator refuses any other bytes.

## Vocabulary

**Row kinds** (`kind` column, fixed): `op` (an abstract operation or
algorithm block), `slot` (an internal slot), `idl` (an IDL attribute,
method, or constructor), `requirement` (a stated requirement, as in piping),
`rule` (a cross-cutting rule the text states in prose), `type` (a carrier
definition in a definition-keyed standard such as Infra). A row id is
`<kind>.<kebab-name>` and is stable for the life of the census.

Seven further kinds exist for ECMA-262 and are used by no other standard
(ruling R-P2, 2026-09-06). They exist because the disposition of an ECMAScript
clause is decided by which of these it is, and collapsing them onto `op` and
`slot` would erase the distinction that decides `owned` against
`foreignBoundary` against `hostOnly`:

| Kind | What the row is | Effect on the denominator |
| --- | --- | --- |
| `builtin` | a built-in function object of the `Promise` constructor or prototype | in, unless its disposition excludes it; a `hostOnly` accessor is in and may stay `absent` |
| `hook` | a host-defined abstract operation, a host layering point | in; a `foreignBoundary` hook can never go `green`, which is the point of counting it |
| `property` | a clause whose content is a property descriptor or an initial value | in, and `hostOnly` in every case at the current pin |
| `record` | a specification record type together with its field table | in |
| `field` | one row of a record's field table | in; each field is counted separately from its record so a boundary field does not taint an owned record |
| `term` | a `<dfn>` that names neither a record nor an operation | in |
| `clause` | a structural clause with no operation, record or property of its own | in, unless it is `evidenceOnly`, which is the usual case for a bare heading |

No kind removes a row from the denominator. Only the disposition does that,
and only `evidenceOnly`, `refused` and `targetOnly` do it. A kind that is
usually paired with an excluded disposition, such as `clause`, is still
counted whenever the row's own disposition counts. `builtin` and `hook` in
particular put rows in the denominator that this repository may never make
`green`; that is the honest record, not a defect.

**Source shapes.** A census reads one of two markup dialects, and the shape is
a property of the standard, not of the metric.

| Shape | Sources | Row-bearing constructs |
| --- | --- | --- |
| Bikeshed | Streams `index.bs`, Infra `infra.bs`, URL `url.bs`, Web IDL `index.bs` | `<div>` blocks carrying an `algorithm` attribute, `<dfn>` definitions with their Bikeshed dfn type and `for`, `<xmp class="idl">` and `<pre class=idl>` blocks, `<h2>`–`<h5>` headings for the disposition walk, and authored `rule` locators |
| ecmarkup | ECMA-262 `spec.html` | `<emu-clause>` with its `id` and `type`, the structured `<h1>` that carries the operation name and signature, `<emu-alg>` bodies whose steps are indentation-nested `1. ` lines rather than HTML lists, `<emu-table>` field and slot rows, `<dfn>` terms, and normative `<li>` requirement bullets |

The two dialects differ in more than tag names. In ecmarkup an operation's
name lives only in its `<h1>`, section numbers are generated at build time and
so are never read from the source or printed in a row, and clause ids are not
confined to the `[a-z0-9-]` alphabet the Bikeshed sources use. A row id
derived from an ecmarkup clause id therefore preserves `.`, `%` and case
through a documented injective escaping (ruling R-P3).

**Disposition** is the `SPEC-MANIFEST.md` vocabulary and answers who owns the
row's carrier. `evidenceOnly`, `refused`, and `targetOnly` rows are outside
the denominator and may carry no witness. Every other disposition counts.
`owned` and `requirement` rows must carry at least one witness before they
leave `absent`.

**Coverage state** answers what has been proved about the row today:

| State | Meaning | Rule |
| --- | --- | --- |
| `absent` | no witness | the only state allowed with an empty witness list |
| `partial` | at least one witness, but some step or clause of the row has no theorem | must list what is missing in the row's comment |
| `green` | every step or clause of the row is a named theorem over the Lean model, with an axiom receipt inside the ceiling (`propext`, `Quot.sound`, `Classical.choice` since ruling R-11), under a named observation mask where the family has one (an equational family whose contract states no mask records that instead, per row) | never declared to make a number move |

The green criterion is step-by-step against the algorithm text. A finite
probe, a compile, a WPT pass, or a theorem about the Lean model's own
invariants does not turn a step green. When in doubt the state is `partial`.

**Witness**: a Lean `theorem` (never a `def`, never a Prop-typed def) whose
exact statement is frozen in the module's `StatementSnapshot` section by
`#check (@name : proposition)` ascription, and whose kernel receipt is
inside the ceiling: any subset of `propext`, `Quot.sound`, `Classical.choice`
(ruling R-11).

**Assertion steps discharged by typing (ruled at the P3 coverage landing,
2026-09-02).** A step of the form "Assert: X has internal slots A and B"
whose negation the carrier cannot represent (the argument type carries the
fields) has no theorem to witness it and counts as discharged. The numerator
records this mechanically (`Justification.byTyping`) so the rule can be
overturned in one place; overturning it would move four queue-operation rows
from `green` to `partial` and nothing else. Every other step is judged
strictly: a step left to a foreign-boundary row forces `partial`, and the
module fails the build on a `green` row with such a step.

## The report format

The only sanctioned way to state coverage is the block printed by the
coverage report gate, which runs the Lean emit and prints:

```text
WHATWG Streams (b9ba9f49) coverage: denominator <D>; owned-with-green <O>/<D>;
green <G>, partial <P>, absent <A>; census <total> rows, <E> excluded
partial: <ids>
```

The block is three lines, broken exactly as shown: after
`owned-with-green <O>/<D>;` and after `<E> excluded`. When no row is
`partial` the third line is `partial:` with nothing after it.

Quote that block verbatim, with the commit it was produced at. Do not compute
a percentage by hand, do not round, and do not describe a row as covered in
prose unless it is `green` in the module. A handoff, plan row, or pull
request that mentions coverage links the gate run and pastes the block. It
never restates numbers from memory or from an earlier session.

### Blocks not yet emitted

The promise lane's two standards have no census and no numerator, so
`lake exe census --standard webidl --report` and
`--standard ecma262 --report` do not exist yet and the executable refuses a
report for a standard without a numerator. The blocks below record the shape
those reports will take, with the label each standard's `Gates.Census.Standard`
record supplies. Every field is a placeholder: **no number below has been
computed, and neither block may be quoted as coverage.**

```text
WHATWG Web IDL (a652053f) coverage: denominator <D>; owned-with-green <O>/<D>;
green <G>, partial <P>, absent <A>; census <total> rows, <E> excluded
partial: <ids>
```

```text
ECMAScript ES2026 (0248456c) coverage: denominator <D>; owned-with-green <O>/<D>;
green <G>, partial <P>, absent <A>; census <total> rows, <E> excluded
partial: <ids>
```

Slice Q2 of `docs/PROMISE-PACKAGE-PLAN.md` replaces the placeholders with the
Lean emit's own bytes, at which point both blocks read all-`absent` until the
Q3 packet lands its first witness. Infra is the precedent for the intermediate
state: a checked census, a generated all-`absent` row list, and no report.

## Ownership of the three facts (ruled at P1 landing, 2026-09-02)

- The generated census owns row ids, order, anchors, spans, digests, and
  counts. Its row format carries no disposition column.
- The authored files under `census/` own dispositions: a section map and
  per-row overrides. A row that no entry reaches fails generation; an entry
  that reaches no row also fails generation.
- `WhatwgTest/Audit/SpecCoverage.lean` owns coverage states and
  witnesses, and checks ids and order against the census in both directions
  and that every authored override reached its row. Its frozen row list is
  generated into `SpecCoverageRows.lean` by the same `--write` and covered
  by the same drift gate; the authored freeze is the pair of expected totals
  and the checks.
- Since the P3 coverage landing (2026-09-02) the report is printed from the
  numerator's checked emit: `bin/Census.lean` imports
  `WhatwgTest/Audit/SpecCoverage.lean`, so building the census
  executable elaborates the numerator's gate, and `Gates.Census.verifyEmit`
  re-derives every census-owned column from a fresh regeneration and enforces
  the witness rules before `lake exe census --report` prints. There is no
  generated coverage file; a red numerator fails the build instead of
  printing a number.

`typedef`, `enum`, and `includes` statements are `idl` rows; an `includes`
statement, which declares no name, is identified by the pair it relates
(landed at P1.1).

## How the number moves

**Adding a witness** happens in the coverage module only: add the theorem
name and its receipt to the row's witnesses; add the exact statement as a
`#check (@…` ascription and append the name to the snapshot list in the same
order; change the row's state only if the green criterion is met; keep the
totals true; run the census gate.

**Adding or re-pinning a census row** happens in the generator only. A row is
`kind|id|anchor|offset-start|offset-end|expected-span-sha256|summary`, where
the anchor occurs exactly once in `index.bs`. A digest that drifts because
upstream changed is a deliberate re-pin: the whole pin moves together, never
one row.

## Path to full coverage

Coverage rises by building models, not by relabelling rows. The families and
the phase that closes each: queue-with-sizes and strategies (P3); readable
default path (P4); writable (P5); transform (P6); piping requirements (P7);
promise-job configuration and mask M2 rows (P8); byte streams (P9).

Take exact row counts from the census, never from this document.
