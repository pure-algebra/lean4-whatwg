# Census authored inputs

This directory is authored input to the P1 specification-algorithm census, not
generated output. `Gates/Census.lean` reads it; `generated/` receives what the
generator writes. Nothing here may be produced by a tool.

`SPEC-MANIFEST.md` owns the disposition vocabulary and the section table these
files are seeded from. `docs/SPEC-COVERAGE.md` owns the row kinds, the row
format, and what a disposition does to the denominator. Neither is restated
here; this file records only the format of the inputs and the places where a
line departs from a literal reading of the manifest table.

The files in this directory are the Streams census's inputs. Each further
standard has its own subdirectory with the same discipline: `census/infra/`
(which adds `types.tsv`), `census/url/` (whose six inputs have their own
README), and, from the promise lane, `census/webidl/` and `census/ecma262/`,
described at the end of this file. No two standards share a file, a
denominator, or a row id space.

## Files

| File | Fields | Role |
| --- | --- | --- |
| `dispositions.tsv` | `<section id>` `<kind or *>` `<disposition>` | the disposition of every row in a section |
| `overrides.tsv` | `<row id>` `<disposition>` `<reason>` | the disposition of one row whose section does not describe it |
| `rules.tsv` | `<kebab name>` `<locator>` | authored `rule` rows; empty at P1 |

Fields are tab-separated. A line whose first non-space character is `#`, and a
blank line, are ignored.

## How a row gets its disposition

1. An override in `overrides.tsv` whose row id matches, if there is one.
2. Otherwise the row's heading ancestry is walked from the innermost `<h4>`
   outward through the `<h3>` to the `<h2>`. At each section a line for the
   row's own kind wins over that section's `*` line, and the first section
   with either line decides.
3. A row that neither reaches fails generation. The generator has no default
   and invents no disposition.

Both directions are checked. An entry in `dispositions.tsv` or
`overrides.tsv` that no row uses also fails generation, so an entry cannot
outlive the rows it was written for.

## Where these files depart from a literal reading of the manifest table

The manifest table is keyed by `<h2>` and `<h3>` section. Five groups of rows
need a finer key, and each departure is derived from a rule the manifest or the
root `AGENTS.md` already states rather than from a new policy.

- **Transfer sub-sections.** `rs-transfer`, `ws-transfer` and `ts-transfer` are
  `<h4>` sections inside the otherwise `owned` stream classes, and they state
  the transferable-streams protocol. The manifest refuses transferable streams
  and the root `AGENTS.md` representation rules refuse them with a refusal
  theorem, so these three sections are `refused`.
- **The underlying source, sink and transformer APIs.** The manifest names the
  `UnderlyingSource`, `UnderlyingSink` and `Transformer` dictionaries and their
  members `foreignBoundary` in its own prose, below the table. Those
  dictionaries and their callbacks are the whole content of the
  `underlying-sink-api` and `transformer-api` sections. The
  `underlying-source-api` section also carries two Web IDL type declarations
  that belong to no dictionary — the `ReadableStreamController` union typedef
  and the `ReadableStreamType` enum — and `overrides.tsv` returns those two to
  the `hostOnly` the manifest rules for a `typedef` or an `enum`.
- **The piping requirements.** The requirement bullets are stated inside the
  `ReadableStreamPipeTo` algorithm block, which sits under the `owned`
  `rs-all-abstract-ops`. The manifest dispositions the piping requirements and
  that reference algorithm `requirement`, so the `requirement` rows of
  `rs-abstract-ops` and the `op.readable-stream-pipe-to` row carry it.
- **Foreign internal slots.** Twelve `slot` rows name ECMAScript internals
  rather than streams state: the `ArrayBuffer` and `ArrayBufferView` slots
  the byte-stream algorithms read, and the promise and completion-record
  fields the algorithms branch on. The manifest names ArrayBuffer detachment
  `foreignBoundary`, and the root `AGENTS.md` representation rules put host
  runtime objects outside stored content, so the nine `ArrayBuffer` and
  `ArrayBufferView` rows are `foreignBoundary`. The three promise and
  completion-record rows were the weakest of the twelve and were flagged for
  ratification. Ruling R-P5 (2026-09-06) ratified them as they stood and
  recorded the cross-reference: the same named slots are `owned` in the
  ECMA-262 census, and the Streams rows become references into
  `Whatwg.Ecma262` when P8 opens, at slice Q4 of
  `docs/PROMISE-PACKAGE-PLAN.md`. Slice Q4 is that point.
  `slot.promise-state` and `slot.promise-is-handled` are now `owned`: since
  slice Q3 they are modelled by `Whatwg.Ecma262.Promise.State` and the
  `handled` field of its `Cell`, and the Streams algorithms reach them
  through `Writable.promiseTable` and `Readable.readTable`. They stay inside
  the denominator and stay `absent` until a witness is named. The third row,
  `slot.value`, stays `foreignBoundary`: it is a completion-record field read
  off a host abrupt completion, it has no counterpart row in the ECMA-262
  census, and gap `G-10` of `docs/PROMISE-EXTRACTION-INVENTORY.md` records
  that no Completion carrier exists in `Whatwg.Ecma262` at this pin.
- **The transfer-only slot.** `ReadableStream`'s `[[Detached]]` is defined in
  the `rs-internal-slots` section, which is `owned`, but nothing outside the
  refused `*-transfer` sub-sections reads or writes it. The manifest refuses
  it with them, so it is an override rather than a section default.

## The promise lane's two directories

`census/webidl/` and `census/ecma262/` are the authored inputs of the two
promise censuses opened 2026-09-06. They do not exist until slice Q1 of
`docs/PROMISE-PACKAGE-PLAN.md` lands; this section records the format they are
written to, so that the breaker's frozen input interface and the authored files
agree from the first commit. The rules above still hold: nothing here is
generated, every entry must reach a row, and every row must resolve without a
default.

| File | Fields | Role |
| --- | --- | --- |
| `sections.tsv` | `<heading or clause id>` | the frozen section scope; a row outside it is not emitted |
| `dispositions.tsv` | `<section id>` `<kind or *>` `<disposition>` | as for Streams and Infra |
| `overrides.tsv` | `<row id>` `<disposition>` `<reason>` | as for Streams and Infra |
| `rules.tsv` | `<kebab name>` `<locator>` `[<end locator>]` | authored `rule` rows, with the optional third field described below |
| `dependencies.tsv` | one line per row id, naming the identities that row consumes | as `census/url/dependencies.tsv` |
| `externals.tsv` | the external identities those lines name | as `census/url/externals.tsv` |

`census/ecma262/` additionally has no `types.tsv`: `type` is an Infra kind, and
ECMA-262 carrier definitions are `record` and `term` rows instead.

**The section scope is data, not code.** Ruling R-P1 gives the generator
profile a `sectionScope` switch; the plan resolves that switch against an
authored `sections.tsv` rather than a list in Lean, so that widening or
narrowing the scope is a data review with the same both-directions check as
every other input. An id in `sections.tsv` that matches no heading fails
generation, and an authored entry that reaches only rows the scope excludes
fails generation too. Both existing censuses have whole-document scope and no
`sections.tsv`; an absent file means "the whole document".

**The optional end locator (ruling R-P4).** `rules.tsv` gains a third,
optional field: a byte string that must occur exactly once after the locator
and that ends the row's span, replacing the next-blank-line rule for that row.
Web IDL's six `idl-DOMException-derived-interfaces` bullets need it, because
they sit in one blank-line-delimited paragraph and would otherwise receive six
nested spans all ending at the same offset. The field is optional and absent
from `census/rules.tsv` and `census/infra/rules.tsv`, both of which are empty
of rows, so the change is byte-neutral for the two existing censuses.

**Dependency and external rows (ruling R-P6).** Each of the two censuses
carries exactly one dependency list per row, in the format the URL lane
established, and one externals file naming every identity those lists use.
The split is fixed by the ruling:

- Web IDL's escapes go to the `Whatwg.Ecma262` boundary — five ECMA-262
  operations and three intrinsics, which is the exact P8 surface — to Infra
  dependency rows by existing Infra row id, to out-of-scope sections of the
  same pinned Web IDL source recorded as `hostOnly` dependency rows naming
  their heading id, and to externals for HTML, DOM and realm machinery.
- ECMA-262's escapes go to a named ECMA-262 core boundary carrying Completion
  Records, Abstract Closures and the object-model operations, and to externals
  for agents, realms and execution contexts.

The Infra dependency rows are the first real cross-census join in this
repository: they name a row id in `generated/infra-census.tsv` rather than a
new external identity, and an id that no Infra row carries fails generation.

**No `slot` rows for Web IDL (ruling R-P4).** The slot scanner is off for that
standard. Every slot it would have produced anchors at an incidental use site
rather than at a definition, and the four that matter —
`[[PromiseIsHandled]]`, `[[Promise]]`, `[[Resolve]]`, `[[Reject]]` — are
`Whatwg.Ecma262` dependency rows instead, which is where DB-11 puts them.

## Counting note

The manifest's P0 survey records 66 distinct internal slot names. Four of those
are Bikeshed bibliography citations rather than internal slots, so the census
carries 62 `slot` rows. `Gates/Census.lean` documents the mechanical rule that
separates the two.
