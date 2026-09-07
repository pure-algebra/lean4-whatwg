# Web IDL census inputs

Authored input to `lake exe census --standard webidl`, seeded from the Web IDL
section-disposition table of `SPEC-MANIFEST.md` as amended by rulings R-P1,
R-P4, R-P6, R-P10 and R-P16 in `COORDINATION.md`. The frozen packet is
`test/contracts/webidl-census.contract.md` as amended by
`test/contracts/webidl-census-q2.contract.md`; between them they own every
count below and this directory owns none of them.

Nothing here is coverage. A census row is a byte span of
`vendor/whatwg-webidl-a652053f/index.bs` with a joined disposition, and every
row of this standard is `absent` until `Whatwg.WebIdl` has a declaration.
Offsets in this file are 0-based byte offsets into that sealed source, ends
exclusive.

| File | Role |
| --- | --- |
| `sections.tsv` | the five heading ids that fix the scope |
| `dispositions.tsv` | `<heading id>` TAB `<kind or *>` TAB `<disposition>`, resolved from the row's innermost `<h5>` outward to its `<h2>` |
| `overrides.tsv` | per-row exceptions with a reason; present and entry-free at Q1 |
| `rules.tsv` | the nine authored `rule` rows — the six bullets of `idl-DOMException-derived-interfaces` and the three the Q2 addendum adds — each with the optional end locator R-P4 adds |
| `dependencies.tsv` | one line per row, naming the identities that row's own span reaches |
| `externals.tsv` | the external identities those lines name, in four namespaces |

`census/README.md` owns the formats these files share with the Streams, Infra
and ECMA-262 inputs, and the both-directions rule that an entry no row uses and
a row no entry reaches each fail generation. What follows is only what is
particular to this standard.

## The section scope

`sections.tsv` carries five line-opening heading ids: `idl-exceptions`,
`idl-promise`, `js-promise`, `js-exceptions` and `idl-DOMException`. With their
subsections they are 54,343 bytes, 7.81 % of the 695,845-byte pinned file. A
listed id that is not a line-opening heading with that exact id fails
generation; a listed section that governs no row fails generation; and a row
that lands outside every listed section fails generation.

The scope is data rather than a list in Lean (R-P1's `sectionScope` switch,
resolved by `docs/PROMISE-PACKAGE-PLAN.md` against this file) so that widening
it is a data review. Widening it is also a contract change: section 2 of the
frozen packet freezes these five ids, their spans and their digests. Scope
filtering is a predicate the scanners consult before the disposition join and
before the duplicate check, which is what keeps the ten out-of-scope
`<pre class="idl">` blocks of this source from parsing at all.

## The nine `rule` rows and their end locators

`idl-DOMException-derived-interfaces` (211138–213283) states six `must` and
`should` constraints on deriving an interface from `DOMException`, with no
algorithm. Their disposition is `requirement`, realized by
`QuotaExceededError`.

The six bullets sit in one blank-line-delimited paragraph, so the
next-blank-line rule would give all six the same span end. R-P4 adds an
optional third field to `rules.tsv`: a byte string that must occur exactly once
in the pinned file and strictly after the start locator, and that ends the
row's span. Each bullet's end locator is the opening text of the next bullet,
and the last bullet's is the note that follows the list, which yields six
disjoint spans:

| Row | Span |
| --- | --- |
| `rule.domexception-derived-identifier` | 211607–211774 |
| `rule.domexception-derived-constructor-name` | 211775–211921 |
| `rule.domexception-derived-constructor-message` | 211922–212161 |
| `rule.domexception-derived-constructor-options` | 212162–212318 |
| `rule.domexception-derived-attributes` | 212319–212507 |
| `rule.domexception-derived-serializable` | 212508–212653 |

Slice Q2 adds three more, frozen by
`test/contracts/webidl-census-q2.contract.md` and answering review debts D3 and
D5 of `COORDINATION.md`. They use the same mechanism for the same reason: the
text states them as prose that no scanner keys on.

| Row | Span | Disposition |
| --- | --- | --- |
| `rule.domexception-serialization-steps` | 676192–676691 | `owned` |
| `rule.domexception-deserialization-steps` | 676693–677111 | `owned` |
| `rule.promise-to-js` | 347211–347495 | `hostOnly` |

The first two are `DOMException`'s own serialization and deserialization steps,
written as plain `<ol>` lists in running prose: no `<div>` carries an
`algorithm` attribute over them, no `<dfn>` opens inside them, and they are not
IDL. The same two operations of the derived `QuotaExceededError` are rows only
because that section writes them inside `<div algorithm="…">`, and a census in
which the derived interface's steps are rows and the base interface's are not
is wrong about the source. Their start locators need the `<var>value</var>`
tail: the shorter `Their [=serialization steps=], given` occurs twice, at
216531 and 676192, because `QuotaExceededError` states the same sentence with
the Bikeshed variable spelling `|value|`, and a two-occurrence locator is
refused. The serialization row's end locator is the deserialization row's start
locator, which puts the boundary at the blank line after `</ol>` and keeps the
two spans disjoint.

The third is `convert an IDL promise to a JavaScript value`, a bare
`<p id="promise-to-js">` paragraph whose mirror image `op.js-to-promise`
(346692–347209) is a row only because it is written as
`<div id="js-to-promise" algorithm="…">`. Carrying one direction of the pair
and not the other silently asserts that only one direction is specified. Its id
mirrors the element's own `id`, and its disposition comes from the unchanged
`js-promise * hostOnly` line, because the innermost heading containing byte
347211 is `js-promise`: `js-promise-manipulation` opens at 347497.

The third field is absent from `census/rules.tsv` and `census/infra/rules.tsv`,
both of which are empty of rows, so the change is byte-neutral for the two
existing censuses.

## The ownership split

The landed census is 124 rows: 61 `owned`, 49 `hostOnly`, 8 `evidenceOnly`, 6
`requirement`; denominator 116 with 8 excluded. It was 121 rows with
denominator 112 at the Q1 landing; slice Q2 added the three `rule` rows above
and moved one row between two dispositions. Two rulings decide where the line
falls, and both move it away from where the survey put it.

**R-P4 puts the type in the binding layer and the verbs in the library.** The
eleven operations of `js-promise-manipulation` are `owned` — they are the verbs
DB-11 places in `Whatwg.WebIdl`, and the pinned Streams source invokes them 197
times — while `idl-promise` (the `Promise` type itself, 2 rows) and the
`js-promise` conversion are `hostOnly`. `mark a promise as handled` is `owned`
with the rest although Streams invokes it zero times at this pin: it is a
promise verb DB-11 names, and an uncovered denominator row is the honest record
of that. The same ruling turns `scanSlots` off for this standard, so the
promise internals the operations write — `[[Promise]]`, `[[Resolve]]`,
`[[Reject]]`, `[[PromiseIsHandled]]` — are external identities of
`externals.tsv` rather than rows anchored at incidental use sites.

**R-P10 fixes the exception half.** The base `DOMException` error names are one
`owned` definition row per name — 32 `type` rows, plus the names table
`op.dfn-error-names-table` (198659–198938) that introduces them — and not one
enumeration row: the closed universe is the data `Whatwg.WebIdl.Exceptions`
carries. `idl-DOMException-derived-predefineds` is `hostOnly` for the whole
section rather than `evidenceOnly` for its worked instance. With the three
heading-borne definitions R-P4 admits (`Promise` on `idl-promise`, "exception
objects" on `js-exception-objects`, and the `DOMException` interface on
`idl-DOMException`), the expected total moved from the survey's 118 to 121,
which is what the Q1 breaker recomputed and froze, and the Q2 addendum's three
authored `rule` rows take it to 124.

**The two Q2 disposition moves (review debt D4).**
`js-handling-exceptions` is `hostOnly`, not the Q1 `evidenceOnly`: its one row
`op.an-exception-was-thrown` (669437–669665) is an exported normative `<dfn>`
under a sentence that requires propagation, which is a host obligation and not
an example, and `evidenceOnly` put it outside the denominator where no witness
is ever owed and no host-profile refusal is ever recorded against it. The move
is authored on the section's own line and not in `overrides.tsv`, because
`Gates.Census.finishBuild` credits an overridden row to the override alone and
the section's line would then match no row. The mirror move in the ES2026
census promotes `clause.promise-objects` from `evidenceOnly` to `owned` for the
same reason and by the same mechanism.

`idl-DOMException` is the one section whose lines are keyed by kind rather than
by `*`, and it is worth reading once. Its 35 rows are
`type.idl-dom-exception` (673398–673477) and 30 `idl` rows — the interface
statement, the constructor and the three attributes (673588–673888) and the 25
legacy `const` members (673892–675042) — all `hostOnly`; and two `op` rows,
`op.dom-exception-name` and `op.dom-exception-message`, both anchored at
675214–675370, which are `owned` because the associated name and message are
first-order content. The constructor steps and the three getter steps carry no
row of their own: their `constructor` and `attribute` dfns fold into the
IDL-block rows under R-P2, and those rows are `hostOnly`. The serialization and
deserialization steps (675370–677113) produced no row at all until slice Q2;
review debt D3 of `COORDINATION.md` opened the choice between authored `rule`
rows and a recorded exclusion, and the Q2 addendum took the first. They are the
section's two `rule` rows and its fourth disposition line,
`idl-DOMException rule owned`: they are steps of the interface over the same
associated name and message the two `op` rows already carry, so they take the
owned side of this cell's line, and they are neither `idl` rows nor the
interface type.

## The externals rule

Every row carries exactly one line in `dependencies.tsv`, derived from the
`[=…=]`, `[$…$]`, `{{…}}` and `[[…]]` references inside that row's own byte
span, with whitespace normalised inside an autolink because Bikeshed wraps them
across lines. Recording a dependency is not a proof edge: it says the row's
text reaches that identity, and nothing about its meaning.

Each identity must resolve to a row of this census, to a row of
`generated/infra-census.tsv` — the first cross-census join in this repository —
or to an identity declared in `externals.tsv`. R-P6 fixes the four external
namespaces: `ext.ecma262.*` is the `Whatwg.Ecma262` boundary and the exact P8
surface; `ext.webidl.*` names out-of-scope headings of this same pinned file,
each `hostOnly` at the boundary, because promoting them to rows would open the
whole 695 KB file; `ext.html.*` is realm, task and structured-serialization
machinery, of which `ext.html.queue-a-microtask` is the one carrying an
ordering obligation, since it is a step of `wait for all`; and `ext.dom.*` is
reached only by the descriptive prose of the error-names table.

The rule is symmetric and strict in both directions: a dependency naming an
undeclared identity fails generation, and a declared identity that no
dependency line uses fails generation too. That is why three ECMA-262 escapes
the packet's section 7 lists are absent from `externals.tsv`.
`{{%Error.prototype%}}`, `[=PromiseCapability=]` and
`[=ECMAScript/error objects=]` occur four times between them, at 504381,
663945, 346660 and 194765, and no row's span covers any of the four, so no
dependency line can name them. R-P17 ratifies the omission and the header of
`externals.tsv` records it, with the offsets, so that it reads as a consequence
of the row set rather than as an oversight.
