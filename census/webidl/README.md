# Web IDL census inputs

Authored input to `lake exe census --standard webidl`, seeded from the Web IDL
section-disposition table of `SPEC-MANIFEST.md` as amended by rulings R-P1,
R-P4, R-P6, R-P10 and R-P16 in `COORDINATION.md`. The frozen packet is
`test/contracts/webidl-census.contract.md`; it owns every count below and this
directory owns none of them.

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
| `rules.tsv` | the six authored `rule` rows of `idl-DOMException-derived-interfaces`, each with the optional end locator R-P4 adds |
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

## The six `rule` rows and their end locators

`idl-DOMException-derived-interfaces` (211138–213283) states six `must` and
`should` constraints on deriving an interface from `DOMException`, with no
algorithm. They are the only authored rows of this census, and their
disposition is `requirement`, realized by `QuotaExceededError`.

The six bullets sit in one blank-line-delimited paragraph, so the
next-blank-line rule would give all six the same span end. R-P4 adds an
optional third field to `rules.tsv`: a byte string that must occur exactly once
at or after the start locator and that ends the row's span. Each bullet's end
locator is the opening text of the next bullet, and the last bullet's is the
note that follows the list, which yields six disjoint spans:

| Row | Span |
| --- | --- |
| `rule.domexception-derived-identifier` | 211607–211774 |
| `rule.domexception-derived-constructor-name` | 211775–211921 |
| `rule.domexception-derived-constructor-message` | 211922–212161 |
| `rule.domexception-derived-constructor-options` | 212162–212318 |
| `rule.domexception-derived-attributes` | 212319–212507 |
| `rule.domexception-derived-serializable` | 212508–212653 |

The third field is absent from `census/rules.tsv` and `census/infra/rules.tsv`,
both of which are empty of rows, so the change is byte-neutral for the two
existing censuses.

## The ownership split

The landed census is 121 rows: 59 `owned`, 47 `hostOnly`, 9 `evidenceOnly`, 6
`requirement`; denominator 112 with 9 excluded. Two rulings decide where the
line falls, and both move it away from where the survey put it.

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
which is what the breaker recomputed and froze.

`idl-DOMException` is the one section whose lines are keyed by kind rather than
by `*`, and it is worth reading once. Its 33 rows are
`type.idl-dom-exception` (673398–673477) and 30 `idl` rows — the interface
statement, the constructor and the three attributes (673588–673888) and the 25
legacy `const` members (673892–675042) — all `hostOnly`; and two `op` rows,
`op.dom-exception-name` and `op.dom-exception-message`, both anchored at
675214–675370, which are `owned` because the associated name and message are
first-order content. The constructor steps and the three getter steps carry no
row of their own: their `constructor` and `attribute` dfns fold into the
IDL-block rows under R-P2, and those rows are `hostOnly`. The serialization and
deserialization steps (675370–677113) are `<ol>` lists rather than algorithm
blocks and produce no row at all; review debt D3 of `COORDINATION.md` records
that Q2 decides between authored `rule` rows and a recorded exclusion.

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
