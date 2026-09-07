# Specification manifest

This file owns the authority pins, the authority order, and the
section-by-section dispositions of the WHATWG Streams Standard for this
repository, and, since slice W5 of `docs/WHATWG-PACKAGE-PLAN.md`, the
authority pins of the Infra, HTML, and URL Standards, and, since the promise
lane opened 2026-09-06, those of the Web IDL Standard and ECMA-262 with their
section dispositions. The original disposition
tables and coverage report are Streams-scoped; the URL bootstrap survey below
is separate. Its reviewed source census is projected by `lake exe urlcensus`;
the declaration/numerator join and URL coverage denominator remain unadmitted.
`docs/PROVENANCE.md` owns the fetch record and cross-check of
every digest quoted here; `generated/vendor-manifest.tsv` owns the per-file
digests of the vendored bytes.

Status: P0 pins frozen, 2026-09-01. Dispositions below are the P0 survey;
from P1 the generated census owns every row and this table becomes its
authored input.

## Authority pins

| Authority | Exact pin | Role |
| --- | --- | --- |
| WHATWG URL Standard source | `whatwg/url` commit `55d6699373ba68a16ec182f34222a74ed8bc3dac`, 2026-08-18, "Review Draft Publication: August 2026"; `url.bs` SHA-256 `a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`, 162,680 bytes; CC-BY 4.0 with BSD-3-Clause for source-code portions | semantic owner for `Whatwg.Url`; URL section survey below and U2c source census in `docs/URL-PACKAGE-PLAN.md`; no semantic declarations or admitted coverage denominator yet |
| Web Platform Tests `url/` | existing `web-platform-tests/wpt` commit `480fdfcd85d043c23875665f464c35c0043dff52`; 49 files, retained with the existing root `LICENSE.md` | URL host test corpus; fetched only, no host run or theorem evidence |
| WHATWG Streams Standard source | `whatwg/streams` commit `b9ba9f49d95b4280be0dc2372377a006c3a91c18`, 2026-08-18, "Review Draft Publication: August 2026"; `index.bs` SHA-256 `24360b4f8446e6c80e185c5021fcca9b67a7e0bb62490a00109080ebc04c6440`, 417,076 bytes | **semantic owner** |
| WHATWG Infra Standard source | `whatwg/infra` commit `3f984adcd24a6d5c53cc26b3e737701808003f3e`, 2026-07-17, "Review Draft Publication: July 2026"; `infra.bs` SHA-256 `7c38e6e25ef21f536142cfc6d94954c41bc9889cd0b6fd67ab34571215acd8eb`; CC-BY 4.0 | semantic authority for `Whatwg.Infra`, the value universe (Stratum V); pinned at W5, no dispositions yet |
| WHATWG HTML Standard source | `whatwg/html` commit `746f2ede8a56bc01204e0f9cc23da33b37c6fbab`, 2026-07-17, "Review Draft Publication: July 2026"; `source` SHA-256 `c985a14d1871fe862de386f5af92b5da84068267c6095ef0379c069ae85f9cde`, 7,891,297 bytes; CC-BY 4.0 | semantic owner of the HTML content model for `Whatwg.Html`; pinned at H0 of `docs/HTML-PACKAGE-PLAN.md`, no dispositions yet |
| TyXML 4.6.0 | `ocsigen/tyxml` commit `d2916535536f2134bad7793a598ba5b7327cae41` (tag `4.6.0`, 2023-09-27); `lib/**`, `syntax/reflect/**`, licenses; LGPL-2.1 with linking exception; `html_types.mli` SHA-256 `0031c56d5bcc048b11ba47fd4d840235bfc52ced9722269510818c14004b3df3`, `html_sigs.mli` `5cf48b32cc19f4c9b400f388a749b1a8c0f4e5b058ae88e21ca568a899622f9b` | retired 2026-09-06: the transcription source from which the `Whatwg.Html.Schema` modules were first generated at H2; the pin, projection and drift gate are removed and the schema is authored source under the HTML Standard alone (ruling HP-1, HP-10 as amended) |
| Web IDL Standard source | `whatwg/webidl` commit `a652053f1e74e4aaf647528deb174012ed6c909f`, 2026-03-16, "Review Draft Publication: March 2026"; `index.bs` SHA-256 `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`, 695,845 bytes; CC-BY 4.0 | semantic owner of the specification-level promise operations every WHATWG algorithm uses ("a new promise", "resolve", "reject", "react", "wait for all", "mark as handled") and of the exception kinds and conversions the `hostOnly` boundary names; library root `Whatwg.WebIdl` (ruling DB-11); pinned 2026-09-06 for P8; the section dispositions below seed `census/webidl/`, and `docs/PROMISE-PACKAGE-PLAN.md` owns the lane's slices, fences and commands; no census is generated and no coverage denominator is admitted yet |
| ECMAScript Language Specification, ES2026 | `tc39/ecma262` commit `0248456c758431e4bb8e5d26333ff1865123c9cd` (tag `es2026`, 2026-03-31); `spec.html` SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0`, 2,978,793 bytes; Ecma license in `LICENSE.md` | semantic owner of Promise objects, their internal slots, PromiseReaction and PromiseCapability records, `NewPromiseReactionJob`, `HostEnqueuePromiseJob` and the job abstraction that DB-03 models as deterministic FIFO state; not a WHATWG standard, the language beneath the platform; library root `Whatwg.Ecma262` (ruling DB-11); pinned 2026-09-06 for P8; the clause dispositions below seed `census/ecma262/`, and `docs/PROMISE-PACKAGE-PLAN.md` owns the lane's slices, fences and commands; no census is generated and no coverage denominator is admitted yet |
| Streams reference implementation | same commit, `reference-implementation/`; dual CC0 / MIT | second-tier evidence: candidate realizer and reading aid |
| Web Platform Tests `streams/` | `web-platform-tests/wpt` commit `480fdfcd85d043c23875665f464c35c0043dff52`, 2026-09-02; BSD-3-Clause | host conformance corpus |
| Node | v22.23.2 on Windows 11 x86-64 | local host profile via `node:stream/web` |
| Bun | 1.4.0 on Windows 11 x86-64 | local host profile |
| reference implementation under Node | the pinned tree above | local host profile, closest to the text |
| Lean | `leanprover/lean4:v4.33.1`; `lean-toolchain` SHA-256 `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`; three dependencies by exact commit: `hash` (lean4-hash) at `0168306b7068b97758e3f2d4307eeb97aa31a104`, `effects` (lean4-effects, tag `v0.5.0`) at `c28833b3c14431ba2886a0fb66bcc688c86c2589`, and `typescript` (lean4-typescript, tag `v0.2.0`) at `fcbc05a40e52f9bbe8a8e3ee0f4a746ebd4e9554` | kernel, elaborator, compiler, standard library; exact package dependencies for the hash gates, effect algebra, and TypeScript target |
| EffHOL | arXiv:2506.09458v1, 2025-06-11; PDF SHA-256 `a493e698895878136a71e9ffdaaf9ece786cdd30864f853149cd69cec774ad0c` | logic-layer design basis |
| FIPS 180-4 | NIST, August 2015; PDF SHA-256 `0455b406d89648d20cbde375561e19c245b9815e894164c2670772e3d54deb82` | transcription source for the SHA-256 specification, owned by lean4-hash since the swap; pin moved to lean4-hash in slice W3b of `docs/WHATWG-PACKAGE-PLAN.md`; formerly the S1 SHA-256 specification |
| Process precedent | `pure-algebra/lean4-effect4` commit `e9075e192bb3065e3900ccabe7c0c2a6df1ddffc`; `mepuka/foldlab` commit `8d36195970b83a1439ec705b9a504617554b8062` (`formal/fips202`) | breaker/builder discipline and the SHA3 refinement precedent; not semantic pins |

The vendored trees are byte-identical to upstream at those commits. Nothing
under `vendor/` is edited; re-pinning moves a whole tree together.

## Authority order

1. Each standard's source at its pin (`index.bs` for Streams, `url.bs` for
   URL). Where it states an algorithm, the model is that
   algorithm. Where it states requirements, the model is that specification,
   and any algorithm is a candidate realizer.
2. A separately identified implementation, where pinned. Evidence, never
   authority. No URL implementation is admitted by the bootstrap.
3. WPT. Host conformance, never authority.
4. Local host profiles, then published browser results by run identifier.

## Disposition vocabulary

Every census row receives exactly one disposition.

| Disposition | Meaning |
| --- | --- |
| `owned` | modelled in Lean; must carry at least one witness before its coverage row can leave `absent` |
| `requirement` | stated as constraints rather than an algorithm (piping); modelled as a specification φ, realized by a named algorithm |
| `foreignBoundary` | a host-supplied body or host object whose behaviour enters only as typed decisions with a profile: underlying source, sink, and transformer methods; ArrayBuffer detachment; `AbortSignal` |
| `hostOnly` | Web IDL conversions, brand checks, and constructor overload resolution; enforced by the host's IDL layer, recorded as refusals at the boundary |
| `refused` | transferable streams and their `MessagePort` protocol; a refusal theorem states they are outside the model |
| `evidenceOnly` | examples, introductions, and the "other specifications" section; never counted in the denominator |
| `targetOnly` | rows that exist only for the P11 TypeScript profile |

### Row kinds the two promise censuses use

`docs/SPEC-COVERAGE.md` owns the row-kind vocabulary and what a kind does to
the denominator. What belongs here is the mapping from each pinned source's
own constructs to a kind, the way the P1.1 ruling below maps `typedef`, `enum`
and `includes` statements onto `idl` rows.

The Web IDL census uses the existing kinds only. Its `<div>` algorithm blocks
are `op`; its `<pre class=idl>` statements are `idl`; a standalone `<dfn>`
becomes `idl`, `type` or `op` by its Bikeshed dfn type (`attribute`, `const`
and `constructor` fold into the IDL-block rows, `exception` is a `type`, the
rest are `op`); the six derived-interface bullets are authored `rule` rows
carrying disposition `requirement`; no `slot` rows are emitted (ruling R-P4).

The ECMA-262 census adds seven kinds, used by no other standard, because the
distinction between an abstract operation, a host hook and a built-in function
object is the distinction that decides the disposition (ruling R-P2):

| Kind | The construct it names in `spec.html` |
| --- | --- |
| `builtin` | an `<emu-clause type="built-in function">`: a function object of the `Promise` constructor or prototype |
| `hook` | an `<emu-clause type="host-defined abstract operation">`: a host layering point |
| `property` | a clause whose whole content is a property descriptor or an initial value |
| `record` | a clause defining a specification record type and its field table |
| `field` | one `<tr>` of a record's field table |
| `term` | a `<dfn>` that names neither a record nor an operation |
| `clause` | a structural clause with no operation, record or property of its own |

`op`, `slot` and `requirement` keep their existing meanings there: `op` is an
`<emu-clause type="abstract operation">`, `slot` is one `<tr>` of the promise
instances' internal-slot table, and `requirement` is a normative `<li>` that
constrains a host rather than stating an algorithm.

## Section dispositions (P0 survey of `index.bs`)

The survey counted 248 algorithm-block openers beginning `<div algorithm`,
of which 229 are the bare `<div algorithm>` and 19 carry attributes, and
about 8,400 lines (the earlier figure of 7,041 was a non-blank line count).
The survey's "66 distinct internal slot names" was an overcount of four:
`[[FETCH]]`, `[[COMPRESSION]]`, `[[ENCODING]]`, and `[[WEBSOCKETS]]` are
Bikeshed bibliography citations that never occur in the escaped or
autolinked slot spelling (verified by the coordinator at P1 landing); the
census carries 62 `slot` rows. The P1 census keys on the `<div algorithm`
prefix, not the closing bracket, which is what keeps those 19 blocks. From
P1 the generated census owns every count. After P1.1: 248 `op`, 133 `idl`
across 20 IDL blocks (including six `typedef`, `enum`, and `includes`
statements), 62 `slot`, 7 `requirement`, denominator 410 with 40 excluded.
Do not quote these as coverage.

| Section id | Title | Disposition | Phase |
| --- | --- | --- | --- |
| `intro`, `model`, `conventions` | introduction, model, conventions | `evidenceOnly` (the model section is a reading aid for masks and backpressure) | — |
| `rs-class` | `ReadableStream` class | `owned`; IDL members `hostOnly` at the boundary | P4 |
| `generic-reader-mixin`, `default-reader-class` | reader mixin, default reader | `owned` | P4 |
| `byob-reader-class`, `rbs-controller-class`, `rs-byob-request-class` | BYOB reader, byte controller, BYOB request | `owned`, separate calculus; ArrayBuffer detach `foreignBoundary` | P9 |
| `rs-default-controller-class` | default controller | `owned` | P4 |
| `rs-all-abstract-ops` | readable abstract operations | `owned`; tee is P4-late; byte ops P9 | P4 / P9 |
| `ws-class`, `default-writer-class`, `ws-default-controller-class`, `ws-all-abstract-ops` | writable stream, writer, controller, abstract operations | `owned` | P5 |
| `ts-class`, `ts-default-controller-class`, `ts-all-abstract-ops` | transform stream, controller, abstract operations | `owned` | P6 |
| `pipe-chains` (model) and `ReadableStreamPipeTo` | piping requirements and the reference algorithm | `requirement` realized by the reference algorithm | P7 |
| `qs-api`, `blqs-class`, `cqs-class`, `qs-abstract-ops` | queuing strategies | `owned` | P3 |
| `queue-with-sizes` | queue-with-sizes | `owned` | P3 |
| `transferrable-streams` | transferable streams | `refused` | — |
| `misc-abstract-ops` | miscellaneous abstract operations | `owned` where used; `hostOnly` for IDL helpers | P3–P7 as consumed |
| `other-specs` | using streams in other specifications | `evidenceOnly` | — |
| `creating-examples`, `acks` | examples, acknowledgments | `evidenceOnly` | — |

Underlying source, sink, and transformer dictionaries (`UnderlyingSource`,
`UnderlyingSink`, `Transformer`) are `foreignBoundary`: their `start`,
`pull`, `cancel`, `write`, `close`, `abort`, `transform`, and `flush` members
are named operations whose invocations are decisions, with the spec's
"if it throws" and "wait for the promise" clauses modelled as answer kinds.

## URL section dispositions (U0 bootstrap survey of `url.bs`)

This survey routes future packets; it is not a generated census or a coverage
claim. U2 of `docs/URL-PACKAGE-PLAN.md` must inventory definitions, algorithms,
parser states, record components, IDL members, validation errors, and prose
requirements by byte span before semantic implementation. Each row then gets
one disposition, including explicit dependency and boundary decisions.

| Section id | Bootstrap disposition and boundary | Planned slice |
| --- | --- | --- |
| `goals` | goals requiring named laws in future packets; explanatory text `evidenceOnly` | U2 |
| `infrastructure`, `writing`, `parsers`, `percent-encoded-bytes` | URL-owned helpers and validation-error behavior `owned`; Infra carriers retain their canonical owner; Encoding calls need dependency records | U3 |
| `security-considerations` | security recommendations inventoried separately from executable algorithms; normative constraints `requirement` | U2 |
| `hosts-(domains-and-ip-addresses)`, `host-representation`, `host-miscellaneous`, `host-writing`, `host-parsing`, `host-serializing`, `host-equivalence` | `owned`; domain processing links to the IDNA dependency below | U4 |
| `idna` | URL's invocation parameters and error handling `owned`; Unicode UTS #46 processing and tables need their own exact pin and assurance route | U4 |
| `urls`, `url-representation`, `url-miscellaneous`, `url-writing`, `url-parsing`, `url-serializing`, `url-equivalence` | `owned`; record and parser-state contracts distinguish validation errors from failure, and null from empty components | U5 |
| `origin` | URL algorithm `owned`; HTML origin values and File API blob URL entries require named dependency/boundary records | U6 |
| `url-rendering`, `url-rendering-simplification`, `url-rendering-elision`, `url-rendering-i18n` | `requirement` where the text constrains presentation; explanatory examples `evidenceOnly`; keep separate from serialization | U6 |
| `application/x-www-form-urlencoded`, `urlencoded-parsing`, `urlencoded-serializing`, `urlencoded-hooks` | `owned`; Encoding dependency must account for UTF-8 and any supported legacy encoder | U7 |
| `api`, `url-class`, `interface-urlsearchparams` | URL and URLSearchParams algorithms, mutation and association `owned`; Web IDL conversions and host identity need explicit boundary records | U8 |
| `url-apis-elsewhere` | cross-standard requirements inventoried at U2; dependency obligations follow their named owner | U8 |
| `acknowledgments` | `evidenceOnly` | — |

The host miscellaneous algorithms also reference Public Suffix List data;
URL-writing requirements reference the IANA URI Schemes registry, and
rendering references Unicode bidi behavior. Their external authority and
data/version boundaries require explicit U2 rows as well.

No missing dependency is silently replaced by a host call. U2 must decide
and record whether each imported algorithm is a proved dependency, a URL-owned
adapter, or an explicit profiled boundary. Such a boundary limits the eventual
claim and cannot count as a proof of that external standard.

## Web IDL section dispositions (survey of `index.bs` at `a652053f`, 2026-09-06)

Scope is five sections, 54,343 bytes, 7.81 % of the pinned file, and the scope
itself is frozen input: `census/webidl/sections.tsv` carries the heading ids
and widening it is a contract change, not a convenience
(`docs/PROMISE-PACKAGE-PLAN.md`, slice Q1). Offsets are 0-based byte offsets
into `vendor/whatwg-webidl-a652053f/index.bs`, ends exclusive. The row counts
are the survey's proposal; the generated census owns every count once it
exists, and none of these numbers is coverage.

| Section id | Span | Rows in scope | Disposition |
| --- | --- | --- | --- |
| `idl-exceptions` (lead) | 193957–198581 | 9 definitions: `exception`, `simple exception`, the five simple exception types, `create`, `throw` | `owned`: the first-order exception universe `Whatwg.WebIdl.Exceptions` is reserved for |
| `idl-DOMException-error-names` | 198581–211138 | 32 error-name definitions; 22 legacy `const` members | names `owned` (the closed universe every WHATWG algorithm draws from); the `idl` const rows `hostOnly` |
| `idl-DOMException-derived-interfaces` | 211138–213283 | 6 authored `rule` rows, bullets at 211607, 211775, 211922, 212162, 212319, 212508 | `requirement`: `must`/`should` constraints with no algorithm, realized by `QuotaExceededError` |
| `idl-DOMException-derived-predefineds` | 213283–217551 | 3 algorithm blocks, 5 definitions, the `QuotaExceededError` IDL block | `hostOnly`; no Streams algorithm reaches the name. Flagged: `evidenceOnly` is arguable since it is the worked instance of the six requirements above it |
| `idl-promise` | 252146–252819 | the heading-borne `Promise` interface-type definition and `dfn-promise-type` | `hostOnly` (ruling R-P4), overriding the survey's recommendation of `owned`: it is a type-system entry, and the binding layer is `hostOnly` |
| `js-promise` (lead) | 346519–347497 | `js-to-promise` (346692–347209) and the reverse conversion | `hostOnly`: binding-layer conversions |
| `js-promise-manipulation` | 347497–356716 | the 11 promise operations | `owned`: the verbs DB-11 places in `Whatwg.WebIdl`; Streams invokes them 197 times |
| `js-promise-examples` | 356716–364590 | 7 example algorithm blocks and 1 definition, all inside `<div class="example">` | `evidenceOnly` |
| `js-exceptions` (lead) | 663547–663610 | none | no row source; 63 bytes of heading |
| `js-DOMException-specialness` | 663610–664320 | none | `hostOnly`: what the JavaScript binding does to the `DOMException` prototype |
| `js-exception-objects` | 664320–664612 | 1 heading-borne definition | `hostOnly`: which host object represents each exception kind |
| `js-creating-throwing-exceptions` | 664612–669093 | 4 algorithm blocks | `owned`: what gives `create` and `throw` their meaning |
| `js-handling-exceptions` | 669093–671837 | 1 definition plus a JavaScript example | `evidenceOnly`: the propagation rule is ECMA-262's |
| `idl-DOMException` | 673398–677113 | the heading-borne interface definition, 30 IDL statements, 6 definitions | `idl` rows `hostOnly`; the associated `name` and `message` and the constructor and getter steps `owned` |

`mark a promise as handled` is `owned` although the pinned Streams source
invokes it zero times (ruling R-P4): it is a promise verb DB-11 names, and an
uncovered denominator row is the honest record of that. `wait for all` is
`owned` for the same structural reason, reached from Streams only through
`get a promise to wait for all`, once, in the pipe-to shutdown path.

No `slot` rows are emitted for this standard (ruling R-P4). The promise
internals the operations write — `[[PromiseIsHandled]]`, `[[Promise]]`,
`[[Resolve]]`, `[[Reject]]` — are `Whatwg.Ecma262` dependency rows, where
DB-11 puts them, rather than rows anchored at incidental use sites.

## ECMA-262 clause dispositions (survey of `spec.html` at `0248456c`, 2026-09-06)

Scope is two clause subtrees, 49 clauses, 72,286 bytes, 2.43 % of the pinned
file: `sec-jobs` (624525–636548) and `sec-promise-objects`
(2686444–2746707). `sec-host-promise-rejection-tracker` is inside the second,
not a third root. Section numbers are derived from the clause forest, not read
from the source, and the census row format carries no section-number column.
Offsets are 0-based byte offsets into `vendor/ecma262-0248456c/spec.html`,
ends exclusive.

| Clause id | § | Rows | Disposition |
| --- | --- | --- | --- |
| `sec-jobs` | 9.5 | `clause.jobs` and its four requirement bullets (625769, 626257, 626357, 626486) | `requirement`: constraints on any host scheduler, realized by the FIFO queue in `Whatwg.Ecma262.Jobs` under DB-03 |
| `sec-jobcallback-records` | 9.5.1 | `record.job-callback-record`, 2 fields | the record and `[[HostDefined]]` `foreignBoundary`; `[[Callback]]` `owned` |
| `sec-hostmakejobcallback`, `sec-hostcalljobcallback` | 9.5.2–3 | 2 hooks, 1 requirement bullet each | `foreignBoundary`: host state and re-entry into user code |
| `sec-hostenqueuegenericjob`, `sec-hostenqueuetimeoutjob` | 9.5.4, 9.5.6 | 2 hooks | `foreignBoundary`: no in-scope caller, and wall-clock scheduling is not FIFO state |
| `sec-hostenqueuepromisejob` | 9.5.5 | 1 hook, 3 requirement bullets | the hook and the ordering bullet (634739–634841) `requirement`, realized by the FIFO queue (ruling R-P5); the realm-preparation and active-script bullets `foreignBoundary` |
| `sec-promise-objects`, `sec-promise-abstract-operations`, `sec-promise-jobs` | 27.2, 27.2.1, 27.2.2 | 3 structural clauses | `evidenceOnly`: the settled/resolved vocabulary and two headings |
| `sec-promisecapability-records`, `sec-promisereaction-records` | 27.2.1.1–2 | 2 records, 6 fields | `owned`: DB-11 puts both records in `Whatwg.Ecma262` |
| `sec-ifabruptrejectpromise` | 27.2.1.1.1 | 1 op | `owned`: a shorthand whose six-step expansion is the theorem |
| `sec-createresolvingfunctions`, `sec-fulfillpromise`, `sec-newpromisecapability`, `sec-ispromise`, `sec-rejectpromise`, `sec-triggerpromisereactions` | 27.2.1.3–8 | 6 ops | `owned`: first-order state transitions over the promise slots |
| `sec-host-promise-rejection-tracker` | 27.2.1.9 | 1 hook | `foreignBoundary`: host bookkeeping with no stated observable effect |
| `sec-newpromisereactionjob`, `sec-newpromiseresolvethenablejob` | 27.2.2.1–2 | 2 ops | `owned`; the thenable `then` call of the second is a boundary step inside an owned row |
| `sec-promise-constructor`, `sec-properties-of-the-promise-constructor`, `sec-properties-of-the-promise-prototype-object` | 27.2.3, 27.2.4, 27.2.5 | 3 structural clauses | `hostOnly`: global-object and prototype plumbing |
| `sec-promise-executor` | 27.2.3.1 | `builtin.promise` | `owned`, with its `NewTarget` and `OrdinaryCreateFromConstructor` steps left to the host object model |
| `sec-promise.all`, `.allsettled`, `.any`, `.race`, `.reject`, `.resolve`, `.try`, `.withResolvers` | 27.2.4.1–9 | 8 built-ins | `owned`: the combinator semantics, with the iterator protocol as a named boundary |
| `sec-getpromiseresolve`, `sec-performpromiseall`, `sec-performpromiseallsettled`, `sec-performpromiseany`, `sec-performpromiserace`, `sec-promise-resolve` | 27.2.4.1.1–27.2.4.7.1 | 6 ops | `owned` |
| `sec-promise.prototype`, `sec-promise.prototype.constructor`, `sec-promise.prototype-%symbol.tostringtag%` | 27.2.4.4, 27.2.5.2, 27.2.5.5 | 3 properties | `hostOnly`: property descriptors |
| `sec-get-promise-%symbol.species%` | 27.2.4.10 | 1 built-in | `hostOnly`: subclass species dispatch enforced by the host object model |
| `sec-promise.prototype.catch`, `.finally`, `.then` | 27.2.5.1, 27.2.5.3–4 | 3 built-ins | `owned`; `finally` depends on `SpeciesConstructor`, which is out of scope and enters as a dependency row |
| `sec-performpromisethen` | 27.2.5.4.1 | 1 op | `owned`: the entry point every WHATWG "react to" call reaches |
| `sec-properties-of-promise-instances` | 27.2.6 | 1 clause, 5 slots | `owned`: the promise carrier itself |
| terms | — | `term.job` | `owned` |
| terms | — | `term.job-activescriptormodule`, `term.job-preparedtoevaluatecode` | `foreignBoundary`: defined over the execution context stack |
| terms | — | `term.promise-intrinsic`, `term.promise-prototype-object`, `term.promise-prototype-intrinsic` | `hostOnly`: intrinsic identities supplied by the host's realm |

The ruled totals are the survey's: 77 rows, 3 `evidenceOnly` and therefore
outside the denominator, and of the remaining 74, 44 `owned`, 13
`foreignBoundary`, 10 `hostOnly` and 7 `requirement` (ruling R-P5). Nothing is
`refused` and nothing is `targetOnly`. The 20 `emu-note` blocks are not rows at
all. These are proposals seeded into `census/ecma262/`; do not quote them as
coverage.

The promise instance slots are `owned` here while the Streams census keeps
`[[PromiseState]]`, `[[PromiseIsHandled]]` and `[[Value]]` `foreignBoundary`.
The two censuses answer two ownership questions about two libraries; the
Streams rows become references into `Whatwg.Ecma262` when P8 opens, and until
then they stay exactly as P1 landed them.

## Promise and job model (Streams)

The specification is written over ECMAScript promises. Promise-job order is
deterministic under ECMAScript's FIFO job queue, so the job queue is state in
the configuration, not a decision kind. The only decisions are consumer calls,
foreign-boundary answers with their settlement timing, and abort signals. This
is a P0 ruling recorded in `docs/DESIGN-BASIS.md`; P8 tests it against WPT
ordering cases under mask M2.

## Rulings made at P1 landing (2026-09-02)

- ECMAScript promise and completion-record internals (`[[PromiseState]]`,
  `[[PromiseIsHandled]]`, `[[Value]]`) are `foreignBoundary`: they are host
  runtime objects the representation rules exclude from stored content; the
  job queue that settles them is state (DB-03).
- ArrayBuffer and ArrayBufferView internals read by the byte-stream
  algorithms are `foreignBoundary`, consistent with ArrayBuffer detachment.
- The `*-transfer` subsections of the three stream classes are `refused`
  with their two slots; `[[Detached]]` on `ReadableStream`, which exists
  only for that protocol, is `refused` too, by authored override (landed at
  P1.1).
- The three underlying-source, underlying-sink, and transformer dictionaries
  and their members are `foreignBoundary`; every other IDL member is
  `hostOnly` at the boundary.
- `ReadableStreamPipeTo` itself carries disposition `requirement` as the
  reference realizer of the seven piping requirements.
- `typedef`, `enum`, and `includes` statements in the IDL blocks (six at the
  pin) receive `idl` rows with disposition `hostOnly` (landed at P1.1). Two
  of them, the `ReadableStreamController` union typedef and the
  `ReadableStreamType` enum, sit inside the `underlying-source-api` IDL
  block whose section is `foreignBoundary`; they are Web IDL type
  declarations, not dictionary members with host-supplied bodies, so they
  are `hostOnly` by authored override. Ratified by the coordinator at the
  P2 landing, 2026-09-02.

## Rulings made at the promise lane opening (2026-09-06)

Seven rulings answer the open decisions of the two promise census surveys.
`docs/PROMISE-PACKAGE-PLAN.md` owns the slices that carry them out and records
which survey decision each one answers.

- **R-P1, generator shape.** `Gates.Census.Standard.definitionKeyed` becomes a
  source profile: a Bikeshed profile with per-scanner switches
  (`algorithmRows`, `definitionRows`, `idlRows`, `slotRows`,
  `requirementMarker`, `sectionScope`, heading levels) and an ecmarkup profile
  served by a new `Gates/Ecmarkup.lean` scanner. The command line keeps its
  shape, `lake exe census --standard <key>`. The Streams and Infra projections
  and rows modules must be byte-identical across the refactor, and the breaker
  freezes that identity.
- **R-P2, kinds.** `Gates.Census.Kind` gains `builtin`, `hook`, `property`,
  `record`, `field`, `term` and `clause` for ECMA-262. Web IDL uses the
  existing kinds, with definition rows disambiguated by Bikeshed dfn type and
  `for`. Existing kinds and their spellings are unchanged.
- **R-P3, ids.** ECMA-262 row ids derive from clause ids with `.`, `%` and
  case preserved through an injective, documented escaping, not through
  `kebab`, which collides `sec-promise.resolve` with `sec-promise-resolve`.
  Requirement bullets that carry no id are positional within their clause and
  guarded by the span digest.
- **R-P4, Web IDL scope.** `idl-promise`, the promise type, is `hostOnly`. The
  promise operations in `js-promise` are `owned`, including `mark as handled`,
  which is unused by Streams at this pin and stays an honest uncovered
  denominator row. The binding layer stays `hostOnly`. `scanSlots` is off for
  Web IDL; the promise internals it mentions are `Whatwg.Ecma262` dependency
  rows. Heading-borne definitions (`<h3 id=… interface>` and the bare `dfn`
  attribute) are definition rows. `rules.tsv` gains an optional end locator so
  the six derived-interface bullets get disjoint spans.
- **R-P5, ECMA-262 dispositions.** The survey's proposal stands — 44 `owned`,
  13 `foreignBoundary`, 10 `hostOnly`, 7 `requirement` — with
  `HostEnqueuePromiseJob` and its ordering bullet ruled `requirement`,
  realized by the FIFO queue in `Whatwg.Ecma262.Jobs` under DB-03, the same
  specification-and-realizer pattern this manifest already applies to
  `ReadableStreamPipeTo`. `HostEnqueueTimeoutJob` and `HostEnqueueGenericJob`
  are `foreignBoundary`. The promise instance slots are `owned` in this census
  while the Streams census keeps them `foreignBoundary`: the two censuses
  describe two libraries, and the Streams rows become references into
  `Whatwg.Ecma262` when P8 opens.
- **R-P6, escaping references.** Each census carries `dependencies.tsv` and
  `externals.tsv` in the URL lane's format. Web IDL's escapes split into the
  `Whatwg.Ecma262` boundary (the exact P8 surface), Infra dependency rows,
  out-of-scope Web IDL sections as `hostOnly`, and HTML and DOM realm
  machinery as externals. ECMA-262's escapes split into Completion Records,
  Abstract Closures and the object-model operations as a named ECMA-262 core
  boundary, and agents, realms and execution contexts as externals.
- **R-P7, sequencing.** Breaker first, with both contracts frozen red in one
  packet; then the Web IDL builder lands the profile refactor and the Web IDL
  standard; then the ECMA-262 builder lands the ecmarkup scanner, developed in
  parallel as a pure scanner with its own battery, and the `ecma262` standard
  on top of it; then independent review; then the coordinator lands with all
  gates. Two CI steps are added, one per standard.

## Open rows

- `ReadableStreamTee` and the async-iteration protocol are `owned` but are
  scheduled after the P4 representative closes.
- `AbortSignal` interaction in piping is `foreignBoundary` with a profile
  fixed at P7.
