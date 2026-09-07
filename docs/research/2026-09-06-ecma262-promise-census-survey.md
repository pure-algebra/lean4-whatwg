# ECMA-262 promise and job census survey

Read-only source survey of the ECMAScript clauses that the `Whatwg.Ecma262`
lane will census, taken 2026-09-06 against the sealed pin. Nothing here is a
coverage claim, a disposition ruling, or a Lean declaration. It is the exact
byte-level input a census generator and its breaker contract will be built
from, plus the decisions the coordinator must take before either is written.

## 0. Pin, method, and what was measured

| Fact | Value |
| --- | --- |
| Source | `vendor/ecma262-0248456c/spec.html` |
| Upstream | `tc39/ecma262` commit `0248456c758431e4bb8e5d26333ff1865123c9cd`, tag `es2026`, 2026-03-31 |
| Size | 2,978,793 bytes |
| SHA-256 | `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0` |
| Line endings | LF only: 53,844 LF, 0 CR, in the whole file |
| Sectioning elements in the whole file | 2,189 `<emu-clause>`, 73 `<emu-annex>`, 1 `<emu-intro>`; every open tag has a matching close and the nesting is balanced |
| Other whole-file counts | 2,239 `<emu-alg>`, 1,507 `<emu-grammar>`, 998 `<emu-xref>`, 95 `<emu-table>`, 89 `<emu-eqn>`, 711 `<emu-note>`, 3 `<emu-import>` |
| Non-ASCII bytes in the whole file | 8,887 |

The file digest was re-checked with `Get-FileHash -Algorithm SHA256` and agrees
with the pin recorded in `SPEC-MANIFEST.md`. The three `<emu-import href=…>`
elements, at byte offsets 2071774, 2071857 and 2071937, pull the Unicode
property tables from sibling HTML files that are **not** vendored; they are far
outside the clauses surveyed here and are noted only so that a future
whole-file scanner does not assume `spec.html` is self-contained.

Method: the file was read as raw bytes and decoded with ISO-8859-1 so that one
character equals one byte and every offset below is a true 0-based byte offset.
The clause forest was built by a stack machine over the merged `<emu-clause` /
`</emu-clause>`, `<emu-annex` / `</emu-annex>`, `<emu-intro` / `</emu-intro>`
event stream; an open tag counts only when the character after the element name
is whitespace or `>`. Span digests were computed over `bytes[start, end)` with
`System.Security.Cryptography.SHA256` and four of them were re-checked
independently by extracting the span to a file and running `Get-FileHash`
(`sec-jobs`, `sec-promise-objects`, `sec-fulfillpromise`,
`sec-properties-of-promise-instances`); all four agree.

Section numbers are **not printed in the source**. ecmarkup generates them at
build time. The numbers in this document are derived from the clause forest by
the rule: the single `<emu-intro>` is unnumbered; top-level `<emu-clause>`
elements are numbered 1…29 in document order; top-level `<emu-annex>` elements
are lettered A…H in document order; a child's number is its parent's number, a
dot, and its 1-based index among that parent's sectioning children. The rule
reproduces the published numbering at the two anchors that can be checked
against the pinned text without a build: `sec-jobs` is 9.5 inside
`sec-executable-code-and-execution-contexts` (clause 9) and `sec-promise-objects`
is 27.2 inside `sec-control-abstraction-objects` (clause 27).

## 1. The clause tree in scope

Two subtrees are in scope: `sec-jobs` (7 clauses, bytes 624525..636548, 12,023
bytes) and `sec-promise-objects` (42 clauses, bytes 2686444..2746707, 60,263
bytes). `sec-host-promise-rejection-tracker` is **not** a third root: it sits at
27.2.1.9 inside `sec-promise-abstract-operations` and is already covered by the
second subtree. Total: **49 clauses, 72,286 bytes, 2.43 % of the file, 2.24 % of
its 2,189 `<emu-clause>` elements.**

`aoid` occurs exactly **once** in the whole in-scope region, on
`sec-ifabruptrejectpromise`. Every other operation name is carried only by the
structured-header `<h1>`; ecmarkup derives the aoid from that header at build
time. A census generator that keys on `aoid=` will find 1 of 22 operations.

The `type` attribute occurs 34 times, with exactly four distinct values in
scope: `abstract operation` (15), `built-in function` (13),
`host-defined abstract operation` (6), and absent (15).

The title column below is the raw `<h1>` inner text with runs of whitespace
collapsed to one space; ecmarkup's structured headers are multi-line, so the
raw bytes contain newlines the table cannot show. `end` is the offset just past
the matching `</emu-clause>`.

| § | id | aoid | type | `<h1>` title (whitespace-normalised) | start | end | SHA-256 of `[start, end)` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 9.5 | `sec-jobs` | — | — | Jobs and Host Operations to Enqueue Jobs | 624525 | 636548 | `871310fa2bcc46a2c06c2b0cc2e590632270246801336d7188185f0b4b3573bf` |
| 9.5.1 | `sec-jobcallback-records` | — | — | JobCallback Records | 628436 | 630247 | `0fdda86da2a80f733a34298da2bec97f7a3c3da2cb173e0270813d63a9e85a1d` |
| 9.5.2 | `sec-hostmakejobcallback` | — | host-defined abstract operation | HostMakeJobCallback ( _callback_: a function object, ): a JobCallback Record | 630253 | 631441 | `f8ccca3399819ba3253b0dbec63f9663ed4fc3737ae74cc708e00e1235c46e4a` |
| 9.5.3 | `sec-hostcalljobcallback` | — | host-defined abstract operation | HostCallJobCallback ( _jobCallback_: a JobCallback Record, _V_: an ECMAScript language value, _argumentsList_: a List of ECMAScript language values, ): either a normal completion containing an ECMAScript language value or a throw completion | 631447 | 632699 | `8c71cf59d88d1e5d189be02e8a179a59d57dd35c0978b0419fcc02ea34d34267` |
| 9.5.4 | `sec-hostenqueuegenericjob` | — | host-defined abstract operation | HostEnqueueGenericJob ( _job_: a Job Abstract Closure, _realm_: a Realm Record, ): ~unused~ | 632705 | 633441 | `3c4716a0db0dc18a9eb400f975a12026aa81cfdae6924d2b51e79348fd621b51` |
| 9.5.5 | `sec-hostenqueuepromisejob` | — | host-defined abstract operation | HostEnqueuePromiseJob ( _job_: a Job Abstract Closure, _realm_: a Realm Record or *null*, ): ~unused~ | 633447 | 635836 | `2dd7ba925b7ef8424773a60bdef524789cf044e2a97d7f1796fa74acec613b93` |
| 9.5.6 | `sec-hostenqueuetimeoutjob` | — | host-defined abstract operation | HostEnqueueTimeoutJob ( _timeoutJob_: a Job Abstract Closure, _realm_: a Realm Record, _milliseconds_: a non-negative finite Number, ): ~unused~ | 635842 | 636532 | `ee98ff2feb4f02946c4508ed8d47e5c1df82714138d1644cee02b912d6345870` |
| 27.2 | `sec-promise-objects` | — | — | Promise Objects | 2686444 | 2746707 | `21deb38546b2e5e928888349f91a40a16074a8cfa7f91469a0aec56c5bc7e9e0` |
| 27.2.1 | `sec-promise-abstract-operations` | — | — | Promise Abstract Operations | 2687651 | 2702809 | `fa30b3b37aa9cfd702de3d7a9b8d1408ec959bd95381ef7dd7653f5c2675436f` |
| 27.2.1.1 | `sec-promisecapability-records` | — | — | PromiseCapability Records | 2687751 | 2690437 | `08c37430874eb8f162eb3e84825cfecf3aae49700ec1a28e9728864e79fe83ab` |
| 27.2.1.1.1 | `sec-ifabruptrejectpromise` | `IfAbruptRejectPromise` | — | IfAbruptRejectPromise ( _value_, _capability_ ) | 2689617 | 2690417 | `7453862884877f7d2186444ab91e950c928cb0a711074025577311073a810ba9` |
| 27.2.1.2 | `sec-promisereaction-records` | — | — | PromiseReaction Records | 2690445 | 2692671 | `d66fc8081d7a889ffbdd77b8a4828c5ad87095a72fa04b257f808dbea8816743` |
| 27.2.1.3 | `sec-createresolvingfunctions` | — | abstract operation | CreateResolvingFunctions ( _toResolve_: a Promise, ): a Record with fields [[Resolve]] (a function object) and [[Reject]] (a function object) | 2692679 | 2695411 | `8227712c5eaa66d17942e1b7c13a8d6f7c29f24a03a591df81ce9868a90c8944` |
| 27.2.1.4 | `sec-fulfillpromise` | — | abstract operation | FulfillPromise ( _promise_: a Promise, _value_: an ECMAScript language value, ): ~unused~ | 2695419 | 2696230 | `f0efa1ffede8b5b861cdb87a36f340ddbab87b2cdcd83abd7172d68e41a1c67e` |
| 27.2.1.5 | `sec-newpromisecapability` | — | abstract operation | NewPromiseCapability ( _C_: an ECMAScript language value, ): either a normal completion containing a PromiseCapability Record or a throw completion | 2696238 | 2698770 | `9d0157b63bd72c38fb0951e4d0030b46997508ca43b46c5402eb901bb4f5c1d9` |
| 27.2.1.6 | `sec-ispromise` | — | abstract operation | IsPromise ( _x_: an ECMAScript language value, ): a Boolean | 2698778 | 2699315 | `4762e66357e6408fde8f751a3008cda25dd492e99c5061b291f99c8514a121cf` |
| 27.2.1.7 | `sec-rejectpromise` | — | abstract operation | RejectPromise ( _promise_: a Promise, _reason_: an ECMAScript language value, ): ~unused~ | 2699323 | 2700252 | `1006df0c95f76cd0a9edadadb8f68bf85446b0e8778485cfd8b913fb169fc056` |
| 27.2.1.8 | `sec-triggerpromisereactions` | — | abstract operation | TriggerPromiseReactions ( _reactions_: a List of PromiseReaction Records, _argument_: an ECMAScript language value, ): ~unused~ | 2700260 | 2701212 | `ba03acae7a5640e794655f0fcb6e085859ce91eb4a8f899472ff01dc122c1839` |
| 27.2.1.9 | `sec-host-promise-rejection-tracker` | — | host-defined abstract operation | HostPromiseRejectionTracker ( _promise_: a Promise, _operation_: *"reject"* or *"handle"*, ): ~unused~ | 2701220 | 2702791 | `8b44c32c206fff92fefb2dbf3208efb4b53226fb18bd8cd42dfe1f72182fde07` |
| 27.2.2 | `sec-promise-jobs` | — | — | Promise Jobs | 2702815 | 2707559 | `9ee19fb76c828986e3aff598ace336dfbacab6a69c51bcedc46c007ba1f1b7cb` |
| 27.2.2.1 | `sec-newpromisereactionjob` | — | abstract operation | NewPromiseReactionJob ( _reaction_: a PromiseReaction Record, _argument_: an ECMAScript language value, ): a Record with fields [[Job]] (a Job Abstract Closure) and [[Realm]] (a Realm Record or *null*) | 2702885 | 2705591 | `3225cb2f3907ae48b448c01a862587e80cd5e8b795b8ad5d610df68b5f291a7b` |
| 27.2.2.2 | `sec-newpromiseresolvethenablejob` | — | abstract operation | NewPromiseResolveThenableJob ( _promiseToResolve_: a Promise, _thenable_: an Object, _then_: a JobCallback Record, ): a Record with fields [[Job]] (a Job Abstract Closure) and [[Realm]] (a Realm Record) | 2705599 | 2707541 | `cde161e71ffde5bfde25825afa6b4e7c879c31d8056ab6c26f2d27c461f92e13` |
| 27.2.3 | `sec-promise-constructor` | — | — | The Promise Constructor | 2707565 | 2711513 | `b7bb9e4831d34a8a4e091ccd90506e9cce8ad25ef7a1b66cccec25149c5fa1d1` |
| 27.2.3.1 | `sec-promise-executor` | — | built-in function | Promise ( _executor_ ) | 2708413 | 2711495 | `765932794c01fd8b82164d88f54a765a96ed390f011de69396470e48f2575ea5` |
| 27.2.4 | `sec-properties-of-the-promise-constructor` | — | — | Properties of the Promise Constructor | 2711519 | 2736555 | `31a227af9032fdbb0e501b8419acf570bbee74959df62259fc4d57c4f6655b1a` |
| 27.2.4.1 | `sec-promise.all` | — | built-in function | Promise.all ( _iterable_ ) | 2711835 | 2717026 | `86c966b7f88d69f50dda8100c3b3e1bc1af352fdc6d0e47a3fc7687fb9e65a90` |
| 27.2.4.1.1 | `sec-getpromiseresolve` | — | abstract operation | GetPromiseResolve ( _promiseConstructor_: a constructor, ): either a normal completion containing a function object or a throw completion | 2713285 | 2713877 | `e3d4435301645c214ed0df54ef70ba2b71216c1c447f36c2e274c183125bf85b` |
| 27.2.4.1.2 | `sec-performpromiseall` | — | abstract operation | PerformPromiseAll ( _iteratorRecord_: an Iterator Record, _constructor_: a constructor, _resultCapability_: a PromiseCapability Record, _promiseResolve_: a function object, ): either a normal completion containing an ECMAScript language value or a throw completion | 2713887 | 2717006 | `a1c1fd99668df4f6b18316ccf4cfee9cd40d7137fb93e50da05c8abd5be5bfca` |
| 27.2.4.2 | `sec-promise.allsettled` | — | built-in function | Promise.allSettled ( _iterable_ ) | 2717034 | 2723460 | `083105d5a28c05d0f92325aef4b388e12d420abfc379d2c93551522b1d52e108` |
| 27.2.4.2.1 | `sec-performpromiseallsettled` | — | abstract operation | PerformPromiseAllSettled ( _iteratorRecord_: an Iterator Record, _constructor_: a constructor, _resultCapability_: a PromiseCapability Record, _promiseResolve_: a function object, ): either a normal completion containing an ECMAScript language value or a throw completion | 2718509 | 2723440 | `a9a3a64032ae6ac8500aa76e05a2ebd5751d2d0ef53fe9f4f23d714392ad9caa` |
| 27.2.4.3 | `sec-promise.any` | — | built-in function | Promise.any ( _iterable_ ) | 2723468 | 2728545 | `10016318f59b61ad2f3e3e153be3dcc23881ce3a0c5611f9cd9fb6cf3dda4ed4` |
| 27.2.4.3.1 | `sec-performpromiseany` | — | abstract operation | PerformPromiseAny ( _iteratorRecord_: an Iterator Record, _constructor_: a constructor, _resultCapability_: a PromiseCapability Record, _promiseResolve_: a function object, ): either a normal completion containing an ECMAScript language value or a throw completion | 2724939 | 2728525 | `820398cb01553fc0bfe57e34aa9e430372e3639acee832fa85abb916ff98483d` |
| 27.2.4.4 | `sec-promise.prototype` | — | — | Promise.prototype | 2728553 | 2728863 | `bdce2e364c2e0104a38b05bea65aa79f5c7262473ed8c83fafb37a756eaac56c` |
| 27.2.4.5 | `sec-promise.race` | — | built-in function | Promise.race ( _iterable_ ) | 2728871 | 2731537 | `68eabc5289e154aa5cf28ea5f159eb83daff9f1cff470c012f4f5882b5b61865` |
| 27.2.4.5.1 | `sec-performpromiserace` | — | abstract operation | PerformPromiseRace ( _iteratorRecord_: an Iterator Record, _constructor_: a constructor, _resultCapability_: a PromiseCapability Record, _promiseResolve_: a function object, ): either a normal completion containing an ECMAScript language value or a throw completion | 2730549 | 2731517 | `1061c0d5656d6fe17c945f326aac79e2938ef121d2d454f722e93a7b4edde680` |
| 27.2.4.6 | `sec-promise.reject` | — | built-in function | Promise.reject ( _r_ ) | 2731545 | 2732230 | `7b918a7dc1f44d633f07ded2e87864b7d841d669d50b5631e4c96475d8bf3ba5` |
| 27.2.4.7 | `sec-promise.resolve` | — | built-in function | Promise.resolve ( _x_ ) | 2732238 | 2733852 | `e38d9843379c55dc41c53b77e053048e86c125c752a9e999ed2a1ff1ef77cc7c` |
| 27.2.4.7.1 | `sec-promise-resolve` | — | abstract operation | PromiseResolve ( _C_: an Object, _x_: an ECMAScript language value, ): either a normal completion containing an ECMAScript language value or a throw completion | 2732914 | 2733832 | `9bfa14eade2e7991ee59dcdfdba99458d54bf48a8640dc0727e85df00ce649e6` |
| 27.2.4.8 | `sec-promise.try` | — | built-in function | Promise.try ( _callback_, ..._args_ ) | 2733860 | 2734885 | `498e54e44b5ef0d5b7faaa243a5b4f9c8505d90f820c9c3a01b33858f18b6535` |
| 27.2.4.9 | `sec-promise.withResolvers` | — | built-in function | Promise.withResolvers ( ) | 2734893 | 2735729 | `35bfc8591d8a2046a0d07a2943e44c5891f7a5a22bb93fd99148a419ddc99a45` |
| 27.2.4.10 | `sec-get-promise-%symbol.species%` | — | built-in function | get Promise [ %Symbol.species% ] | 2735737 | 2736537 | `b019e293eb4a7b2349f33ab6e48abc9c20427063aa3f0acdbc3e233dac58a20a` |
| 27.2.5 | `sec-properties-of-the-promise-prototype-object` | — | — | Properties of the Promise Prototype Object | 2736561 | 2744129 | `f1599e711c81aceabca5ef33d796867271015536b12200fc2e04b12a14c212d4` |
| 27.2.5.1 | `sec-promise.prototype.catch` | — | built-in function | Promise.prototype.catch ( _onRejected_ ) | 2737067 | 2737453 | `5fa520b7bc4b9fdb9599ae193385ee21dbb2188ee37f036a02d34903f6174f25` |
| 27.2.5.2 | `sec-promise.prototype.constructor` | — | — | Promise.prototype.constructor | 2737461 | 2737661 | `8176eb3689ce275615a724264dbf4b369621a8fe40f3db39e1bb2f81bf495a07` |
| 27.2.5.3 | `sec-promise.prototype.finally` | — | built-in function | Promise.prototype.finally ( _onFinally_ ) | 2737669 | 2740006 | `8900f09e03c588c6f990f5a511d98a0e8b90b65bd067a6d7d276b657deddbed6` |
| 27.2.5.4 | `sec-promise.prototype.then` | — | built-in function | Promise.prototype.then ( _onFulfilled_, _onRejected_ ) | 2740014 | 2743689 | `97a409281b34879a52da89b63be07cc15a9dfd70443035debcb4b38636dbd588` |
| 27.2.5.4.1 | `sec-performpromisethen` | — | abstract operation | PerformPromiseThen ( _promise_: a Promise, _onFulfilled_: an ECMAScript language value, _onRejected_: an ECMAScript language value, optional _resultCapability_: a PromiseCapability Record, ): an ECMAScript language value | 2740635 | 2743669 | `ff69ee65628ebe06e4fe2717feb6013c3d3089b3fa2b034fd90c085c3fa7e2ce` |
| 27.2.5.5 | `sec-promise.prototype-%symbol.tostringtag%` | — | — | Promise.prototype [ %Symbol.toStringTag% ] | 2743697 | 2744111 | `dbe55bc57a9ab199033ca8ad2742c44d565f74431e43aa49e1c2b03ff8300eb3` |
| 27.2.6 | `sec-properties-of-promise-instances` | — | — | Properties of Promise Instances | 2744135 | 2746691 | `f3c8e70543376d039c9138e95afd153a99dd914f87398ba9208d8b76bd00aa0d` |

### 1.1 Per-clause content matrix

`own bytes` is the clause span minus the spans of its sectioning children.
`algs` and `steps` count only the clause's own `<emu-alg>` blocks; `steps`
counts every `1. ` line, at every nesting level.

| § | id | algs | steps | `dl.header` | `<dt>description</dt>` | `emu-table` | `emu-note` | `dfn` | `<ul>` | `<p>` | own bytes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 9.5 | `sec-jobs` | 0 | 0 | 0 | 0 | 0 | 2 | 3 | 3 | 7 | 3957 |
| 9.5.1 | `sec-jobcallback-records` | 0 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | 3 | 1811 |
| 9.5.2 | `sec-hostmakejobcallback` | 1 | 1 | 1 | 0 | 0 | 1 | 0 | 1 | 4 | 1188 |
| 9.5.3 | `sec-hostcalljobcallback` | 1 | 2 | 1 | 0 | 0 | 1 | 0 | 1 | 4 | 1252 |
| 9.5.4 | `sec-hostenqueuegenericjob` | 0 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 1 | 736 |
| 9.5.5 | `sec-hostenqueuepromisejob` | 0 | 0 | 1 | 1 | 0 | 1 | 0 | 1 | 2 | 2389 |
| 9.5.6 | `sec-hostenqueuetimeoutjob` | 0 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 1 | 690 |
| 27.2 | `sec-promise-objects` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 4 | 1253 |
| 27.2.1 | `sec-promise-abstract-operations` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 182 |
| 27.2.1.1 | `sec-promisecapability-records` | 0 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | 2 | 1886 |
| 27.2.1.1.1 | `sec-ifabruptrejectpromise` | 2 | 6 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 800 |
| 27.2.1.2 | `sec-promisereaction-records` | 0 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | 2 | 2226 |
| 27.2.1.3 | `sec-createresolvingfunctions` | 1 | 33 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2732 |
| 27.2.1.4 | `sec-fulfillpromise` | 1 | 8 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 811 |
| 27.2.1.5 | `sec-newpromisecapability` | 1 | 14 | 1 | 1 | 0 | 1 | 0 | 0 | 1 | 2532 |
| 27.2.1.6 | `sec-ispromise` | 1 | 3 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 537 |
| 27.2.1.7 | `sec-rejectpromise` | 1 | 9 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 929 |
| 27.2.1.8 | `sec-triggerpromisereactions` | 1 | 4 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 952 |
| 27.2.1.9 | `sec-host-promise-rejection-tracker` | 0 | 0 | 1 | 1 | 0 | 2 | 0 | 1 | 4 | 1571 |
| 27.2.2 | `sec-promise-jobs` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 96 |
| 27.2.2.1 | `sec-newpromisereactionjob` | 1 | 26 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 2706 |
| 27.2.2.2 | `sec-newpromiseresolvethenablejob` | 1 | 11 | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 1942 |
| 27.2.3 | `sec-promise-constructor` | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 1 | 866 |
| 27.2.3.1 | `sec-promise-executor` | 1 | 13 | 0 | 0 | 0 | 1 | 0 | 0 | 5 | 3082 |
| 27.2.4 | `sec-properties-of-the-promise-constructor` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 406 |
| 27.2.4.1 | `sec-promise.all` | 1 | 11 | 0 | 0 | 0 | 1 | 0 | 0 | 2 | 1480 |
| 27.2.4.1.1 | `sec-getpromiseresolve` | 1 | 3 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 592 |
| 27.2.4.1.2 | `sec-performpromiseall` | 1 | 31 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 3119 |
| 27.2.4.2 | `sec-promise.allsettled` | 1 | 11 | 0 | 0 | 0 | 1 | 0 | 0 | 2 | 1495 |
| 27.2.4.2.1 | `sec-performpromiseallsettled` | 1 | 52 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 4931 |
| 27.2.4.3 | `sec-promise.any` | 1 | 11 | 0 | 0 | 0 | 1 | 0 | 0 | 2 | 1491 |
| 27.2.4.3.1 | `sec-performpromiseany` | 1 | 33 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 3586 |
| 27.2.4.4 | `sec-promise.prototype` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 310 |
| 27.2.4.5 | `sec-promise.race` | 1 | 11 | 0 | 0 | 0 | 2 | 0 | 0 | 3 | 1698 |
| 27.2.4.5.1 | `sec-performpromiserace` | 1 | 6 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 968 |
| 27.2.4.6 | `sec-promise.reject` | 1 | 4 | 0 | 0 | 0 | 1 | 0 | 0 | 2 | 685 |
| 27.2.4.7 | `sec-promise.resolve` | 1 | 3 | 0 | 0 | 0 | 1 | 0 | 0 | 2 | 696 |
| 27.2.4.7.1 | `sec-promise-resolve` | 1 | 6 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 918 |
| 27.2.4.8 | `sec-promise.try` | 1 | 9 | 0 | 0 | 0 | 1 | 0 | 0 | 2 | 1025 |
| 27.2.4.9 | `sec-promise.withResolvers` | 1 | 7 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 836 |
| 27.2.4.10 | `sec-get-promise-%symbol.species%` | 1 | 1 | 0 | 0 | 0 | 1 | 0 | 0 | 3 | 800 |
| 27.2.5 | `sec-properties-of-the-promise-prototype-object` | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 1 | 1 | 556 |
| 27.2.5.1 | `sec-promise.prototype.catch` | 1 | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 386 |
| 27.2.5.2 | `sec-promise.prototype.constructor` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 200 |
| 27.2.5.3 | `sec-promise.prototype.finally` | 1 | 25 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 2337 |
| 27.2.5.4 | `sec-promise.prototype.then` | 1 | 5 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 641 |
| 27.2.5.4.1 | `sec-performpromisethen` | 1 | 29 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 3034 |
| 27.2.5.5 | `sec-promise.prototype-%symbol.tostringtag%` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 414 |
| 27.2.6 | `sec-properties-of-promise-instances` | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 1 | 2556 |
| **total** | | **32** | **390** | **21** | **10** | **4** | **20** | **9** | **11** | **74** | **72286** |

### 1.2 Sub-clause anchors that a census will need

Four `<emu-table>` blocks carry the record and slot rows. Each `<tr>` span
below runs from `<tr>` to just past `</tr>`.

| Table id | span | table SHA-256 | body rows |
| --- | --- | --- | --- |
| `table-jobcallback-records` | 629317..630229 (912 B) | `f46212297d0b0bebdc6035fb67ffe038e67083fd668c6201376efe4a6bda10df` | 2 |
| `table-promisecapability-record-fields` | 2688316..2689607 (1291 B) | `c7d4ca513064a4786052794ad5ae689a4512dc429a5d2d3faec607f3c489360b` | 3 |
| `table-promisereaction-record-fields` | 2691046..2692651 (1605 B) | `18ccd2f700a78567f5e9d148733a4165b8819f8d1d73401068a49b9f7f72bab7` | 3 |
| `table-internal-slots-of-promise-instances` | 2744540..2746673 (2133 B) | `4534e5a8c30c8d3840e7f79e0ba46867d1e9201282c6fc6209baf43d8fa5bd87` | 5 |

| Field / slot | value column | `<tr>` span | SHA-256 |
| --- | --- | --- | --- |
| `[[Callback]]` | a function object | 629684..629930 | `0aa3d4ac28a7163324040babf2ffc96e492bf530e71b7c29e1222596bb86ab57` |
| `[[HostDefined]]` | anything (default value is ~empty~) | 629941..630193 | `9edf19e8961f9d0341683b05f33c634d920df9b2f48412b1d1c623cda62a4446` |
| `[[Promise]]` | an Object | 2688749..2688997 | `59942a56a0e02b4fcc325226c71897937d87e435526b06ec2166a0e8c882cf64` |
| `[[Resolve]]` | a function object | 2689010..2689283 | `c1b547ccba62ad0a5b2b5222643a00a19ee63336b5d9821ba27cb3501542f57c` |
| `[[Reject]]` | a function object | 2689296..2689567 | `0d38dbfc1eeaa69490e9efc8b8e68e16603c20f82f9cd20f4793fb65d70b9371` |
| `[[Capability]]` | a PromiseCapability Record or *undefined* | 2691475..2691802 | `67b47fd1bc6773cb099432f10db3b5b427d445cd1a10077db3ec90ec381d6a77` |
| `[[Type]]` | ~fulfill~ or ~reject~ | 2691815..2692138 | `9d8bbc74e5fa8aca1901755de043e11705ab76ee6dbaa10339cfc408f71fa8d2` |
| `[[Handler]]` | a JobCallback Record or ~empty~ | 2692151..2692611 | `79e2058b8d3cfcbff3ace42ff8e52406429d38ea5252ebb18bd4b0fa56fa25ca` |
| `[[PromiseState]]` | ~pending~, ~fulfilled~, or ~rejected~ | 2744957..2745252 | `b752fb3cead6b7d3063935ef7a5867b1af9f1f298b688dbe9d015540012f33fb` |
| `[[PromiseResult]]` | an ECMAScript language value or ~empty~ | 2745263..2745619 | `c0c3b1b3c19902cdec5971211ec6f5cce01d5a5696f5728c480c61013cbb9a2f` |
| `[[PromiseFulfillReactions]]` | a List of PromiseReaction Records | 2745630..2745966 | `f13205764479117eddbc24d537a2981738b8e758dd5bd4f0d2042ce382fba3e0` |
| `[[PromiseRejectReactions]]` | a List of PromiseReaction Records | 2745977..2746311 | `d4c90d6b411a4b0359bfc0e9e75c1f9c25be373fb12d3a5bdbea60339a020f81` |
| `[[PromiseIsHandled]]` | a Boolean | 2746322..2746637 | `c5e0730a73986eb475cb399584433d21e4aadecc069e3b2d61517937d39ed652` |

Nine normative `<li>` bullets state host requirements rather than algorithms.
Four are the general job-scheduling requirements inside `sec-jobs`, three are
the extra `sec-hostenqueuepromisejob` requirements, and one each belongs to
`sec-hostmakejobcallback` and `sec-hostcalljobcallback`.

| Owner clause | `<li>` span | SHA-256 | lead-in |
| --- | --- | --- | --- |
| `sec-jobs` | 625769..626250 | `c1afc33fed819c64bf74bbdfda723687b449fc135daaa0bb9dd9b73d0f5954e2` | At some future point in time, when there is no running context … (contains the nested `<ol>` of three host steps) |
| `sec-jobs` | 626257..626350 | `dec0ab05daf30a7def2efe98018bbdf58750e2f762313b2b50d8184b00720ec5` | Only one Job may be actively undergoing evaluation … |
| `sec-jobs` | 626357..626479 | `3cee57a0e02ed9d66b34bdaa1398995eebf32ac008eb9d493e15647bb9235378` | Once evaluation of a Job starts, it must run to completion … |
| `sec-jobs` | 626486..626589 | `22934fdf600a46d75443c562c8de0fdd4f441e8f67c4816d25ac4ec03aca194b` | The Abstract Closure must return a normal completion … |
| `sec-hostmakejobcallback` | 630615..630699 | `398f9ac14e8275f65bf58957f19f8f0cceda1440f931d2b7293e78dd002aed01` | It must return a JobCallback Record whose [[Callback]] field is _callback_. |
| `sec-hostcalljobcallback` | 631993..632098 | `1e479d75efd60b7e7342f9d2113a4237de99cfba08a1a29c1dc25a9a268bce96` | It must perform and return the result of Call(…). |
| `sec-hostenqueuepromisejob` | 634193..634410 | `7a33838fa1b5acbfb44c7f685abffc7c489667fdb590f30a80f8273c5a2f2e89` | If _realm_ is not *null*, … prepared to evaluate ECMAScript code … |
| `sec-hostenqueuepromisejob` | 634419..634730 | `4041960ebfe66a4dc729e9f67acf868e6dc7049835b24a08552ffc3d4da696d6` | Let _scriptOrModule_ be GetActiveScriptOrModule() … active script or module … |
| `sec-hostenqueuepromisejob` | 634739..634841 | `6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65` | Jobs must run in the same order as the HostEnqueuePromiseJob invocations that scheduled them. |

The last of those is the exact text DB-03 rests on. It is a requirement on host
implementations, not an algorithm, and the deterministic FIFO queue is its
candidate realizer in the DB-05 sense.

Nine `<dfn>` elements occur in scope.

| `<dfn>` span | SHA-256 | source |
| --- | --- | --- |
| 624685..624724 | `9be48048e1c5bbdd279753b6e574c4c1c10fe0b30daf54b1bbf468ee353a9fa5` | `<dfn id="job" variants="Jobs">Job</dfn>` |
| 627006..627070 | `189a5af3e9e04656c8e4196392fefc25a9cc1990eaf2792b0eb79fb2b5539ade` | `<dfn id="job-activescriptormodule">active script or module</dfn>` |
| 627505..627584 | `516906e43a51acff6bea69b650808674600154eadcaebbdfb147e455c32f01ec` | `<dfn id="job-preparedtoevaluatecode">prepared to evaluate ECMAScript code</dfn>` |
| 628524..628584 | `54ef5417e65871cce61e2e0a1efb666ba47c7dead643705ca264fc056a27b2c8` | `<dfn variants="JobCallback Records">JobCallback Record</dfn>` |
| 2687855..2687927 | `6c39f9bfd6d3abed12955522f762626a1425b0674b339544d88809b34c89f096` | `<dfn variants="PromiseCapability Records">PromiseCapability Record</dfn>` |
| 2690545..2690613 | `826e8932401d93428b48c960486d7e00497f7f491f156bbf8a9494779af91faa` | `<dfn variants="PromiseReaction Records">PromiseReaction Record</dfn>` |
| 2707710..2707730 | `bab66ccb5d0f0e98396dd6d48bb696c5f831210ac5edba920d191654b5003425` | `<dfn>%Promise%</dfn>` |
| 2736697..2736732 | `362a4b141200ade425ce88a78c944ae6cd994fc2cfb7f1ab754a83d1c3a4b5cf` | `<dfn>Promise prototype object</dfn>` |
| 2736764..2736794 | `302fe81fc6fd80019abc332c6a47ba9dedd0e029fa784d49a7a328142294695e` | `<dfn>%Promise.prototype%</dfn>` |

Only three of the nine carry an `id`, and six carry no `id` at all. Any id
scheme keyed on `<dfn id=…>`, as the Infra definition-keyed census profile is,
will miss two thirds of them.

## 2. The ecmarkup subset actually present

### 2.1 Elements

Every element occurring anywhere inside the two in-scope byte ranges, with open
and close tag counts. There are 22 distinct element names; every one is
explicitly closed (open count equals close count for all 22), and there are no
void or self-closing tags, no comments (0 `<!--` inside the ranges), and no
malformed tags (a tag scanner that respects quoted attribute values found 0
unterminated or unnamed tags).

| Element | open | close | Role |
| --- | --- | --- | --- |
| `emu-clause` | 49 | 49 | sectioning; the row spine |
| `h1` | 49 | 49 | title, and for 34 clauses the structured header that carries the operation name, parameter list and return type |
| `p` | 74 | 74 | prose, some of it normative (property attributes, default host behaviour) |
| `emu-alg` | 32 | 32 | algorithm bodies; **their contents are markdown-ish `1. ` lines, not `<ol>/<li>`** |
| `dl` | 21 | 21 | always `class="header"`; the structured-header block |
| `dt` | 10 | 10 | always the literal text `description`; no `for` or `effects` `<dt>` occurs in scope |
| `dd` | 10 | 10 | the description text |
| `emu-note` | 20 | 20 | non-normative notes |
| `ul` | 11 | 11 | requirement bullets and object-description bullets |
| `li` | 32 | 32 | list items in `<ul>` and in the one `<ol>` |
| `ol` | 1 | 1 | the three host preparation/invoke/cleanup steps nested inside the first `sec-jobs` requirement bullet, at 625964 |
| `dfn` | 9 | 9 | term definitions |
| `emu-table` | 4 | 4 | record-field and internal-slot tables |
| `table` | 4 | 4 | inside every `emu-table` |
| `thead` | 4 | 4 | header row wrapper |
| `tr` | 17 | 17 | 4 header rows + 13 body rows |
| `th` | 12 | 12 | 3 per table |
| `td` | 39 | 39 | 3 per body row |
| `emu-xref` | 8 | 8 | cross references, all with empty content |
| `em` | 6 | 6 | emphasis in the 27.2 state-vocabulary prose |
| `a` | 3 | 3 | three external links, all to `https://html.spec.whatwg.org/` |
| `emu-not-ref` | 1 | 1 | suppresses autolinking of the word `Invoke` at 626046 |

Elements that the wider document uses but that **do not occur** in scope:
`emu-grammar`, `emu-eqn`, `emu-import`, `emu-figure`, `emu-normative-optional`,
`ins`, `del`, `var`, `code`, `emu-val`, `emu-const`, `emu-nt`, `pre`, `br`,
`h2`, `figure`, `caption` (as an element; `caption` occurs only as an attribute
of `emu-table`).

### 2.2 Attributes

Eight distinct attribute names occur, on five distinct elements.

| Attribute | count | on |
| --- | --- | --- |
| `id` | 56 | `emu-clause` (49), `emu-table` (4), `dfn` (3) |
| `type` | 34 | `emu-clause` only |
| `class` | 21 | `dl` only, always the value `header` |
| `oldids` | 14 | `emu-clause` (11), `emu-table` (3) |
| `href` | 11 | `emu-xref` (8), `a` (3) |
| `variants` | 4 | `dfn` only |
| `caption` | 4 | `emu-table` only |
| `aoid` | 1 | `emu-clause` only (`sec-ifabruptrejectpromise`) |

Every attribute value in scope is double-quoted; no unquoted or
single-quoted attribute value occurs, and there is no bare valueless
attribute (unlike the Infra source, where `<dfn ignore>` occurs).

**Attribute order is not fixed.** Eleven in-scope `<emu-clause>` tags carry
`oldids`, and two of them write it *before* `id`:

- `<emu-clause oldids="sec-get-promise-@@species" id="sec-get-promise-%symbol.species%" type="built-in function">` at 2735737
- `<emu-clause oldids="sec-promise.prototype-@@tostringtag" id="sec-promise.prototype-%symbol.tostringtag%">` at 2743697

The remaining nine write `id` first, and three of those interleave `oldids`
between `id` and `type` (`sec-performpromiseall` at 2713887,
`sec-performpromiseallsettled` at 2718509, `sec-performpromiseany` at 2724939).
A scanner must read named attributes, never positional ones. The existing
`Gates.Census.attrValue?` rule — the attribute name must be preceded by
whitespace — is sufficient to keep `id=` from being read out of `oldids=`, and
was checked against all 49 tags.

### 2.3 Which of the subset carries semantic content

| Construct | Semantic? | What it carries |
| --- | --- | --- |
| `<emu-clause id type>` | yes | the row identity, the row kind (through `type`), and the span |
| `<h1>` of a typed clause | yes | the operation name, the ordered parameter list with each parameter's type phrase, `optional` markers, and the return-type phrase. This is the only place the operation name exists; `aoid` is absent 33 times out of 34 |
| `<h1>` of an untyped clause | mixed | a plain section title for 11 clauses; a property name (`Promise.prototype`, `Promise.prototype.constructor`, `Promise.prototype [ %Symbol.toStringTag% ]`) for 3; the operation name for `sec-ifabruptrejectpromise` |
| `<dl class="header">` | yes when non-empty | 21 occurrences; 11 are empty (`<dl class="header">` immediately followed by `</dl>`) and 10 carry exactly one `<dt>description</dt>` / `<dd>…</dd>` pair. No `For:` and no `Effects:` `<dt>` occurs in scope, so a parser must not require them but must accept them if the pin moves |
| `<emu-alg>` body | yes | 32 blocks, 390 steps. Contents are **not** HTML lists |
| `<emu-table>` + `<table><thead><tr><th>` + `<tr><td>` | yes | 4 tables, 13 body rows: 8 record fields and 5 internal slots. Column 1 is the field or slot name, column 2 the type phrase, column 3 the meaning |
| `<emu-note>` | no | 20 blocks; `evidenceOnly` by construction |
| `<emu-xref href="#…">` | reference | 8, all with empty content; 4 point at in-scope tables, 3 at `#sec-jobs`, 1 at `#sec-promise-executor` |
| `<dfn>` | yes | 9 term definitions; see 1.2 |
| `<ul>`/`<li>` | mixed | 11 lists, 32 `<li>`. Nine `<li>` are host requirements (1.2); four in `sec-jobs` are the two definitional condition lists; the rest describe the constructor object and prototype object and are property facts |
| `<ol>` | yes | 1 block, 3 `<li>`, nested inside the first `sec-jobs` requirement bullet |
| `<em>`, `<a>`, `<emu-not-ref>` | no | typography and links |
| `<var>`, `<code>`, `emu-grammar`, `emu-eqn`, `ins`, `del` | absent | none occur in scope |

### 2.4 The `<emu-alg>` micro-syntax

This is the part a hand-written byte parser will spend its time on, and it is
not HTML.

- 32 blocks, all opened by the bare tag `<emu-alg>` — no `example`, no
  `replaces-step`, no `type` attribute anywhere in scope.
- 390 step lines. Every non-blank line inside an `<emu-alg>` matches
  `^ *1\. ` — there are **zero** continuation lines, zero blank-line-separated
  paragraphs, and zero `[id="step-…"]` step annotations in scope.
- 175 of the 390 steps are top-level; nesting is expressed only by leading
  spaces, two per level, and the maximum depth below top level is 3 (four
  levels total, reached in `sec-newpromisereactionjob`, `sec-performpromiseall`,
  `sec-performpromiseallsettled`, `sec-performpromiseany`, and
  `sec-promise.prototype.finally`).
- The base indent of a block is 8, 10 or 12 spaces depending on how deeply the
  clause is nested, so a parser must derive nesting from indentation *relative
  to the block's own minimum*, never from an absolute column. The observed
  absolute indents are 8 (3 lines), 10 (131), 12 (100), 14 (87), 16 (53) and
  18 (16).
- Every step number is written as the literal `1.`; ecmarkup renumbers at build
  time. A parser must not read the digit as an ordinal.
- Inline markup inside a step is ecmarkup shorthand, not HTML: `_variable_`,
  `*literal*` (including `*"string"*` and `*null*`, `*undefined*`, `*true*`,
  `*false*`), `~spec-enum~`, `[[InternalSlot]]`, `%Intrinsic%`, backtick code,
  and the completion prefixes `? ` (53 occurrences) and `! ` (9 occurrences).
- List literals are written `« … »` with U+00AB and U+00BB.

### 2.5 Encoding and byte-level hazards

- **No character entity reference occurs anywhere in scope.** A regex for
  `&[#0-9A-Za-z]+;` over both ranges returns zero matches, and the byte `&`
  occurs zero times. Entities *do* occur elsewhere in the file (for example
  `+&infin;` in the `sec-createbuiltinfunction` header), so a whole-file
  scanner still needs them; a scanner restricted to these two spans does not.
- Exactly **188 non-ASCII bytes** occur in scope, forming four distinct code
  points: U+00AB `«` (44), U+00BB `»` (44), U+201C (2) and U+201D (2), the last
  two inside the 27.2 prose about a promise being "locked in". The bytes
  observed are 0xC2 (88), 0xAB (44), 0xBB (44), 0xE2 (4), 0x80 (4), 0x9C (2),
  0x9D (2). Every structural byte a scanner tests is below 0x80, so the
  ASCII-first classification rule of `Gates.Census` transfers unchanged; the
  only requirement is that anchor and excerpt boundaries be aligned forward to
  a UTF-8 character boundary, exactly as `alignForward` already does.
- Line endings are LF only, and there are **zero tab characters** in scope.
  Indentation is spaces, which is what makes the two-space nesting rule sound.
- Nesting a byte parser must handle: `emu-clause` inside `emu-clause` four
  levels below a top-level clause. Eight in-scope clauses are that deep — the
  ones with five-component section numbers: `sec-ifabruptrejectpromise`,
  `sec-getpromiseresolve`, `sec-performpromiseall`,
  `sec-performpromiseallsettled`, `sec-performpromiseany`,
  `sec-performpromiserace`, `sec-promise-resolve` and `sec-performpromisethen`.
  Also: `table` inside
  `emu-table`; `tr` inside `thead` inside `table`; `li` inside `ol` inside `li`
  inside `ul` (the `sec-jobs` requirement list). `<p>` is always explicitly
  closed in scope, so the implicit-close rule of HTML is not exercised. No
  element in scope may contain itself except `li`.
- Two clause ids contain a literal `%`: `sec-get-promise-%symbol.species%` and
  `sec-promise.prototype-%symbol.tostringtag%`. Fifteen clause ids contain a
  `.`, and one (`sec-promise.withResolvers`) contains an upper-case letter. Ids
  are therefore **not** in the `[a-z0-9-]` alphabet the Streams census assumes.

### 2.6 The `kebab` collision

Running the existing `Gates.Census.kebab` over the 49 in-scope ids produces
exactly one collision:

```
sec-promise-resolve  <-  sec-promise.resolve  (27.2.4.7, built-in function)
                     <-  sec-promise-resolve  (27.2.4.7.1, abstract operation)
```

`kebab` maps every non-alphanumeric byte to one separator, so the `.` in
`Promise.resolve` and the `-` in `PromiseResolve`'s clause id become the same
character. `sec-promise.withResolvers` also changes shape, to
`sec-promise-with-resolvers`, because `kebab` inserts a separator before an
upper-case letter that follows a lower-case one. No other pair collides. The
id scheme in section 3 avoids the collision by prefixing with the row kind and
by deriving built-in ids from the `<h1>` name rather than from the clause id.

## 3. Proposed row taxonomy

### 3.1 Row format

Unchanged from `docs/SPEC-COVERAGE.md` and `Gates.Census.renderRow`:

```
kind|id|prefix|start|end|sha256|excerpt
```

with `Gates.Census.escapeField` escaping over `\`, `|`, LF, CR and tab, and the
header line in `Gates.Census.censusHeader` shape:

```
#census format=1 generator=Gates.Census input=vendor/ecma262-0248456c/spec.html input-sha256=ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0 rows=<N> regenerate=lake exe census --standard ecma262 --write
```

This is a third `Gates.Census.Standard` record with
`key := "ecma262"`, `label := "ECMAScript ES2026 (0248456c)"`,
`inputRelativePath := "vendor/ecma262-0248456c/spec.html"`,
`censusRelativePath := "generated/ecma262-census.tsv"`, and
`authoredDir := "census/ecma262"`. The existing `definitionKeyed : Bool`
discriminator is not expressive enough for a third source shape — see open
decision 2.

**`prefix`** is the anchor: the shortest UTF-8-aligned prefix of the row's own
span that occurs exactly once in the pinned bytes, chosen from the existing
`anchorLadder` with a final fallback to the whole span. This was computed for
all 77 proposed rows and **every one is anchorable within its own span**:

| anchor length | rows | which |
| --- | --- | --- |
| 20 | 1 | `term.promise-intrinsic` (`<dfn>%Promise%</dfn>`, whose span is 20 bytes) |
| 24 | 19 | 5 clauses, 9 requirement bullets, 5 terms |
| 32 | 26 | clauses only |
| 48 | 29 | 18 clauses, 11 field and slot rows |
| 64 | 1 | `field.promise-capability-record.promise` |
| 252 | 1 | `field.job-callback-record.host-defined` |

Two of those are worth flagging to a breaker. `field.job-callback-record.host-defined`
(span 629941..630193) is unique only at its **full 252-byte span**: every ladder
rung from 24 to 192 collides with another `<tr>` elsewhere in the file, because
the row opens with the same indented `<tr>\n<td>\n[[Host…` shape that dozens of
other record tables use. `Gates.Census.chooseAnchorLength` already appends
`remaining` after the ladder, so it resolves, but only just, and the fallback
path is currently exercised by no Streams or Infra row. Second,
`field.promise-capability-record.promise` (2688749..2688997) is the only row in
the lane that needs the 64-byte rung. Both should be frozen as assertions.

**`excerpt`** is the first `summaryLimit` bytes of the span, UTF-8-aligned and
whitespace-normalised, exactly as `Gates.Census.renderRow` does today. For a
structured-header clause the first 200 bytes cover the open tag and most of the
`<h1>` signature, which is the most useful 200 bytes the clause has. No change
to `summaryLimit` is needed or proposed.

### 3.2 Kinds and counts

The repository's fixed kind vocabulary is `idl | op | requirement | rule |
slot | type`. It does not fit ECMA-262: there is no IDL, and the distinction
between an abstract operation, a host hook and a built-in function object is
the distinction that decides the disposition. The proposal is to extend
`Gates.Census.Kind` with seven constructors — `builtin`, `hook`, `record`,
`field`, `property`, `clause` and `term` — used **only** by the `ecma262`
standard, leaving every existing Streams and Infra row spelling untouched. The
existing `op`, `slot` and `requirement` are reused unchanged; `idl`, `rule` and
`type` are unused by this standard. See open decision 1 for the minimal-change
alternative.

One **primary** row per clause, so that the 49 clause spans partition exactly
into 49 primary rows; plus **sub-rows** for the table bodies, the requirement
bullets and the terms.

| kind | rows | source | id scheme | `prefix` holds | `excerpt` holds |
| --- | --- | --- | --- | --- | --- |
| `op` | **16** | 15 clauses with `type="abstract operation"` plus `sec-ifabruptrejectpromise` (`aoid`) | `op.<kebab of the h1 operation name>`, e.g. `op.perform-promise-then`, `op.if-abrupt-reject-promise` | the clause open tag prefix | the open tag and the signature |
| `hook` | **6** | the 6 clauses with `type="host-defined abstract operation"` | `hook.<kebab of the h1 name>`, e.g. `hook.host-enqueue-promise-job` | same | same |
| `builtin` | **13** | the 13 clauses with `type="built-in function"` | `builtin.` then the h1 property path lower-cased with its dots kept, e.g. `builtin.promise.all`, `builtin.promise.prototype.then`, `builtin.promise`, `builtin.get-promise-symbol-species` | same | same |
| `property` | **3** | `sec-promise.prototype`, `sec-promise.prototype.constructor`, `sec-promise.prototype-%symbol.tostringtag%` | `property.` then the h1 property path, e.g. `property.promise.prototype` | same | the open tag and the "initial value" sentence |
| `record` | **3** | `sec-jobcallback-records`, `sec-promisecapability-records`, `sec-promisereaction-records` | `record.` then the kebab of the record name taken from the clause's first `dfn`, e.g. `record.promise-capability-record` | same | same |
| `clause` | **8** | the remaining structural clauses: `sec-jobs`, `sec-promise-objects`, `sec-promise-abstract-operations`, `sec-promise-jobs`, `sec-promise-constructor`, `sec-properties-of-the-promise-constructor`, `sec-properties-of-the-promise-prototype-object`, `sec-properties-of-promise-instances` | `clause.` then the clause id with its leading `sec-` stripped | same | the open tag and the `<h1>` |
| **primary subtotal** | **49** | | | | |
| `field` | **8** | the `<tr>` body rows of the three record tables | `field.<record kebab>.<slot kebab>`, e.g. `field.promise-reaction-record.handler` | the `<tr>` prefix | the row's three cells, normalised |
| `slot` | **5** | the `<tr>` body rows of `table-internal-slots-of-promise-instances` | `slot.<kebab of the slot name>`, e.g. `slot.promise-state` | same | same |
| `requirement` | **9** | the nine normative `<li>` of 1.2 | `requirement.<owner clause id stripped>.<1-based index>`, e.g. `requirement.jobs.3`, `requirement.hostenqueuepromisejob.3` | the `<li>` prefix | the bullet text, normalised |
| `term` | **6** | the six `<dfn>` that are not a record name | `term.<kebab of the dfn id, else of its text>`, e.g. `term.job`, `term.job-activescriptormodule`, `term.promise-intrinsic` | the `<dfn>` prefix | the definition sentence |
| **total** | **77** | | | | |

Rationale for the two boundary calls in that table:

- The `record` rows take the whole *clause* span, not the table span, because
  the clause is what a re-pin moves and because `sec-promisecapability-records`
  also contains `sec-ifabruptrejectpromise` as a child (whose span is excluded
  from the `record` row only if the generator subtracts child clauses; it does
  not today, and should not, because `Gates.Census` rows may nest — a Streams
  `op` row's span already contains its `requirement` rows).
- The three `<dfn>` that name a record are **not** `term` rows, because the
  `record` row already owns that name. This is the only place the survey
  removes a candidate row, and it is the reason `term` is 6 rather than 9.

### 3.3 Id determinism

Every id above is derived from bytes that occur in the source, in this order of
preference, so the scheme is deterministic and re-derivable:

1. For a typed clause, the leading identifier of the `<h1>`, up to the first
   `(` or the end of the first line, whitespace-normalised. This is exactly
   what ecmarkup itself uses to synthesise the aoid, so the census id and the
   specification's own operation name never diverge.
2. For an untyped clause with an `aoid`, that attribute.
3. For a record, the text of the clause's first `<dfn>`.
4. For a table row, the `[[Name]]` in the first `<td>`.
5. For a requirement bullet, the owner clause's id and the bullet's index in
   its list, both of which are positional and therefore stable only while the
   list is stable. This is the weakest id in the scheme; open decision 4.
6. For a structural clause, the clause id itself with the `sec-` prefix
   removed.

`kebab` is applied to (1)–(4) and to (6), except that for `builtin` and
`property` the `.` separators of the ECMAScript property path are preserved,
since `Promise.prototype.then` and `PromiseResolve` are different names and
flattening the dots is what creates the collision in 2.6.

## 4. Proposed dispositions

Vocabulary is `SPEC-MANIFEST.md`'s seven: `owned`, `requirement`,
`foreignBoundary`, `hostOnly`, `refused`, `evidenceOnly`, `targetOnly`. A ✱
marks a row the coordinator must ratify before generation.

### 4.1 The five rulings this section applies

- **DB-11**: promise objects, reaction and capability records, and the job
  queue live in `Whatwg.Ecma262`. Under this census they are therefore
  **`owned`**, even though the *same* internal slots are `foreignBoundary` in
  the Streams census by the P1 landing ruling. Two censuses now give the same
  named slot two dispositions. That is consistent — the Streams census records
  that Streams does not own them and ECMA-262 does — but it is exactly the sort
  of thing `AGENTS.md` tells us to stop and repair if it is accidental. It is
  not accidental here, and it should be written down. ✱
- **DB-03**: the job queue is deterministic FIFO **state**, not a decision
  kind. The nine host requirement bullets are therefore `requirement` rows in
  the DB-05 sense: constraints realized by the FIFO queue model.
- **Host bookkeeping is a foreign boundary** (the standing rule): the JobCallback
  `[[HostDefined]]` field, `HostMakeJobCallback`, `HostCallJobCallback` and
  `HostPromiseRejectionTracker` are `foreignBoundary`.
- **Representation rules**: host closures and runtime objects are not stored
  content. The 13 Abstract Closures created inside in-scope algorithms and the
  11 `CreateBuiltinFunction` wrappings are not Lean functions; the built-in
  function *objects* they produce are `hostOnly` plumbing over an `owned`
  closure descriptor.
- **`evidenceOnly` is outside the denominator**, so it must not be used to hide
  work. Only 20 `emu-note` blocks and 3 purely structural headings get it.

### 4.2 Primary rows

| id | kind | disposition | reason |
| --- | --- | --- | --- |
| `clause.jobs` | clause | `requirement` ✱ | Its own text is the four host job-scheduling requirements; DB-03's FIFO queue is the realizer. Ratify because the alternative is `owned` with the bullets carrying the requirement. |
| `record.job-callback-record` | record | `foreignBoundary` ✱ | Exists solely to carry a host-defined value across a job boundary; its `[[Callback]]` field is `owned` and `[[HostDefined]]` is not. Ratify the split. |
| `hook.host-make-job-callback` | hook | `foreignBoundary` | A host hook whose whole purpose is attaching host state; the default is the identity wrapping and the model takes the answer as a decision. |
| `hook.host-call-job-callback` | hook | `foreignBoundary` | Same; it re-enters user code, which is a foreign boundary by DB-02. |
| `hook.host-enqueue-generic-job` | hook | `foreignBoundary` | Not called by any in-scope algorithm; out of the promise lane and never modelled. |
| `hook.host-enqueue-promise-job` | hook | `requirement` ✱ | DB-03 says the queue is deterministic FIFO state; that makes this hook a specification realized by the queue, exactly the DB-05 shape, not a boundary. Ratify: the alternative reading is `foreignBoundary` with the FIFO order recovered only from the three bullets. |
| `hook.host-enqueue-timeout-job` | hook | `foreignBoundary` | Wall-clock scheduling; nothing in the promise lane calls it and its "at least _milliseconds_ milliseconds" is not FIFO state. |
| `clause.promise-objects` | clause | `evidenceOnly` ✱ | Its four paragraphs are the fulfilled/rejected/pending/settled/resolved vocabulary. Ratify: this vocabulary is load-bearing for mask M1 and M2 statements, so `owned` is arguable. |
| `clause.promise-abstract-operations` | clause | `evidenceOnly` | 182 own bytes: a heading and nothing else. |
| `record.promise-capability-record` | record | `owned` | DB-11 puts the capability record in `Whatwg.Ecma262`; every field is first-order. |
| `op.if-abrupt-reject-promise` | op | `owned` | A shorthand with an explicit six-step expansion; the expansion is the theorem. |
| `record.promise-reaction-record` | record | `owned` | DB-11; the reaction lists are the promise's own state. |
| `op.create-resolving-functions` | op | `owned` | 33 steps, all first-order over `[[AlreadyCalled]]` and the promise slots. The two Abstract Closures it builds are closure descriptors, not Lean functions. |
| `op.fulfill-promise` | op | `owned` | 8 steps, pure state transition. |
| `op.new-promise-capability` | op | `owned` | 14 steps; the `Construct(_C_, …)` call to a subclass constructor is a foreign-boundary answer, which forces `partial`, never `foreignBoundary` on the row. |
| `op.is-promise` | op | `owned` | 3 steps, a slot brand check. |
| `op.reject-promise` | op | `owned` | 9 steps; its `HostPromiseRejectionTracker` call is the one step left to a boundary. |
| `op.trigger-promise-reactions` | op | `owned` | 4 steps; the core of the FIFO enqueue. |
| `hook.host-promise-rejection-tracker` | hook | `foreignBoundary` | Pure host bookkeeping; the default implementation returns `~unused~` and the specification states no observable effect. |
| `clause.promise-jobs` | clause | `evidenceOnly` | 96 own bytes: a heading. |
| `op.new-promise-reaction-job` | op | `owned` | 26 steps; the settlement order theorem under mask M2 lives here. |
| `op.new-promise-resolve-thenable-job` | op | `owned` ✱ | 11 steps, but its whole content is calling a thenable's `then`, which is a foreign boundary. Ratify: `owned` with a boundary step, or `foreignBoundary` outright. The `Whatwg.Ecma262/Promise.lean` stub already calls thenables a foreign boundary. |
| `clause.promise-constructor` | clause | `hostOnly` | Its own text states that `%Promise%` is the initial value of the global `Promise` property, has `%Function.prototype%` as `[[Prototype]]`, and may be `extends`-ed. Global-object plumbing, enforced by the host. |
| `builtin.promise` | builtin | `owned` ✱ | 13 steps; the constructor is where a promise is created and where `CreateResolvingFunctions` is called. Its `NewTarget` and `OrdinaryCreateFromConstructor` steps are host object-model steps. Ratify the split between the `owned` initialisation and the `hostOnly` allocation. |
| `clause.properties-of-the-promise-constructor` | clause | `hostOnly` | Two bullets about `[[Prototype]]` and property presence. |
| `builtin.promise.all` … `builtin.promise.any` (3 rows) | builtin | `owned` | 11 steps each; the combinator prize the R0 survey named. Their iterator steps are a named boundary (section 5, group D), which forces `partial`, not a different disposition. |
| `op.get-promise-resolve` | op | `owned` | 3 steps. |
| `op.perform-promise-all`, `op.perform-promise-all-settled`, `op.perform-promise-any`, `op.perform-promise-race` (4 rows) | op | `owned` | 31, 52, 33 and 6 steps; these carry the whole combinator semantics. |
| `property.promise.prototype` | property | `hostOnly` | A property descriptor: `{ [[Writable]]: false, [[Enumerable]]: false, [[Configurable]]: false }`. |
| `builtin.promise.race` | builtin | `owned` | 11 steps. |
| `builtin.promise.reject`, `builtin.promise.resolve` | builtin | `owned` | 4 and 3 steps. |
| `op.promise-resolve` | op | `owned` | 6 steps; the `x is a Promise with constructor C` fast path is a named theorem. |
| `builtin.promise.try` | builtin | `owned` | 9 steps; new in ES2026 and untested by any Streams path. |
| `builtin.promise.with-resolvers` | builtin | `owned` | 7 steps; it is the exact shape Web IDL's "a new promise" wants, so DB-11 makes it worth owning. |
| `builtin.get-promise-symbol-species` | builtin | `hostOnly` ✱ | A one-step accessor whose only purpose is subclass species dispatch. Ratify: `hostOnly` says the host's object model enforces it; `refused` would say the model does not support subclassing at all. |
| `clause.properties-of-the-promise-prototype-object` | clause | `hostOnly` | Four bullets about `[[Prototype]]` and slot absence. |
| `builtin.promise.prototype.catch` | builtin | `owned` | 2 steps, a delegation to `then`. |
| `property.promise.prototype.constructor` | property | `hostOnly` | The initial value is `%Promise%`; a property fact. |
| `builtin.promise.prototype.finally` | builtin | `owned` ✱ | 25 steps and four Abstract Closures. Ratify because it is the only in-scope built-in whose semantics depend on `SpeciesConstructor`, which is out of scope. |
| `builtin.promise.prototype.then` | builtin | `owned` | 5 steps; the entry point every WHATWG "react to" call reaches. |
| `op.perform-promise-then` | op | `owned` | 29 steps, 14 of them top-level. The single most important row in the lane. |
| `property.promise.prototype.symbol-to-string-tag` | property | `hostOnly` | A property descriptor. |
| `clause.properties-of-promise-instances` | clause | `owned` | Its content is the internal-slot table, which is the promise carrier itself. |

### 4.3 Sub-rows

| id group | rows | disposition | reason |
| --- | --- | --- | --- |
| `field.job-callback-record.callback` | 1 | `owned` | A plain function-object reference; first-order as a handle. |
| `field.job-callback-record.host-defined` | 1 | `foreignBoundary` | "Field reserved for use by hosts"; the standing host-bookkeeping rule. |
| `field.promise-capability-record.*` | 3 | `owned` | DB-11. |
| `field.promise-reaction-record.*` | 3 | `owned` | DB-11; `[[Type]]` (`~fulfill~`/`~reject~`) and `[[Handler]]` (`a JobCallback Record or ~empty~`) are the two-constructor shape DB-02 asks for. |
| `slot.promise-state`, `slot.promise-result`, `slot.promise-fulfill-reactions`, `slot.promise-reject-reactions`, `slot.promise-is-handled` | 5 | `owned` ✱ | DB-11 makes these `Whatwg.Ecma262`'s carrier. Three of them (`[[PromiseState]]`, `[[PromiseIsHandled]]`, and the Streams census's `[[Value]]`) are `foreignBoundary` in the Streams census by the P1 landing ruling; ratify the two-census reading described in 4.1. |
| `requirement.jobs.1` … `.4` | 4 | `requirement` | DB-03: constraints on any host scheduler, realized by the FIFO queue. |
| `requirement.hostmakejobcallback.1`, `requirement.hostcalljobcallback.1` | 2 | `foreignBoundary` ✱ | They constrain a hook the model treats as a boundary; a requirement row whose realizer is a boundary cannot ever go green. Ratify: `foreignBoundary` (honest) or `requirement` (uniform). |
| `requirement.hostenqueuepromisejob.1`, `.2` | 2 | `foreignBoundary` | Realm preparation and active-script propagation are host bookkeeping the model never observes. |
| `requirement.hostenqueuepromisejob.3` | 1 | `requirement` | "Jobs must run in the same order as the HostEnqueuePromiseJob invocations that scheduled them" — the exact FIFO sentence DB-03 rests on, and the P8 flagship. |
| `term.job` | 1 | `owned` | The Job carrier. |
| `term.job-activescriptormodule`, `term.job-preparedtoevaluatecode` | 2 | `foreignBoundary` | Both are defined over the execution context stack, which is out of scope and never modelled. |
| `term.promise-intrinsic`, `term.promise-prototype-object`, `term.promise-prototype-intrinsic` | 3 | `hostOnly` | Intrinsic identities; the host's realm supplies them. |

### 4.4 Denominator effect

Under this proposal, `evidenceOnly` covers 3 rows (`clause.promise-objects`,
`clause.promise-abstract-operations`, `clause.promise-jobs`), nothing is
`refused`, and nothing is `targetOnly`. **Denominator 74 of 77 rows, 3
excluded.** The 20 `emu-note` blocks are not rows at all, so they never reach
the denominator; that is a deliberate difference from a naive "every block is a
row" reading and is worth stating in `census/ecma262/README.md` when it is
written.

Of the 74, **44 are `owned`, 13 `foreignBoundary`, 10 `hostOnly` and 7
`requirement`**. Split by primary and sub-row: the 49 primary rows are 31
`owned`, 7 `hostOnly`, 6 `foreignBoundary`, 2 `requirement`, 3 `evidenceOnly`;
the 28 sub-rows are 13 `owned`, 7 `foreignBoundary`, 5 `requirement`, 3
`hostOnly`. Eight rows in 4.2 and two row groups in 4.3 carry ✱, and every one
of them moves at least one of these counts, so none of the counts should be
quoted before ratification.

## 5. References that escape the scope

Twenty of the 42 distinct operation call sites in scope resolve to in-scope
clauses. The remaining 22, plus the records, intrinsics and conventions the
algorithms lean on, escape. They are grouped below by how they should be
recorded. "Dependency row" means a row in `census/ecma262/dependencies.tsv` in
the shape `census/url/dependencies.tsv` established: one line per row id naming
the external identity it consumes. "External" means an entry in an externals
table with a pin and no obligation to model. "Named boundary" means a profiled
foreign boundary in the DB-02 sense, with declared answer kinds.

### Group A — Completion Records and the abrupt/normal discipline

| Concept | Defining clause | § | span |
| --- | --- | --- | --- |
| The Completion Record Specification Type | `sec-completion-record-specification-type` | 6.2.4 | 247107..252413 |
| `NormalCompletion` | `sec-normalcompletion` | 6.2.4.1 | 250353..250829 |
| `ThrowCompletion` | `sec-throwcompletion` | 6.2.4.2 | 250837..251239 |
| `Completion ( _completionRecord_ )` | `sec-completion-ao` | 5.2.4.1 | 91403..91983 |
| the `?` and `!` shorthands | `sec-shorthands-for-unwrapping-completion-records` | 5.2.4.3 | — |
| implicit normal completion | `sec-implicit-normal-completion` | 5.2.4.4 | — |

Call-site counts in scope: `Completion(` 23, `NormalCompletion(` 3,
`ThrowCompletion(` 2, `? ` 53, `! ` 9. `[[Value]]` is read 55 times and
`[[Type]]` 8 times.

**Recommendation: dependency rows, and `Whatwg.Ecma262` must own a Completion
carrier.** This is not a boundary. Every one of the 390 steps is written in the
completion discipline, and 53 `? ` prefixes are early returns a Lean model must
reproduce exactly. A boundary here would make every row `partial` forever. The
carrier is small — normal/throw/return with a value — and it must be admitted
before the first `op` row can go green.

### Group B — Abstract Closures and function creation

| Concept | Defining clause | § | span |
| --- | --- | --- | --- |
| The Abstract Closure Specification Type | `sec-abstract-closure` | 6.2.8 | 271039..272533 |
| `CreateBuiltinFunction` | `sec-createbuiltinfunction` | 10.3.4 | 737655..740191 |
| Built-in Function Objects | `sec-built-in-function-objects` | 10.3 | 731152..740207 |
| `SetFunctionName`, `SetFunctionLength` | `sec-setfunctionname`, `sec-setfunctionlength` | 10.2.9, 10.2.10 | 716518..718111, 718117..718822 |

Thirteen Abstract Closures are created inside in-scope algorithms (`resolveSteps`
at 2693157, `rejectSteps` at 2694759, `executorClosure` at 2697314, the
`NewPromiseReactionJob` job at 2703575, the `NewPromiseResolveThenableJob` job
at 2706061, `fulfilledSteps` at 2715572 and 2720346, `rejectedSteps` at 2721755
and 2726859, `thenFinallyClosure` at 2738365, `returnValue` at 2738665,
`catchFinallyClosure` at 2739123, `throwReason` at 2739425). Eleven of them are
then wrapped by `CreateBuiltinFunction`; the two Job closures are not.

**Recommendation: a named boundary, "closure descriptors".** The representation
rules forbid storing Lean functions. Each of the 13 closures becomes a
first-order descriptor: a tag naming which closure it is, plus its captured
values (the source states the capture list explicitly in every case — "captures
_values_, _resultCapability_, and _remainingElementsCount_"). Application is a
total function on descriptors, so the closures stay `owned`; only
`CreateBuiltinFunction`'s object allocation and the `*""*` name/length
bookkeeping are `hostOnly`.

### Group C — the object model

| Operation | Clause | § | span |
| --- | --- | --- | --- |
| `Call` | `sec-call` | 7.3.13 | 348462..349552 |
| `Construct` | `sec-construct` | 7.3.14 | 349558..350749 |
| `Get` | `sec-get-o-p` | 7.3.2 | 339304..339842 |
| `Invoke` | `sec-invoke` | 7.3.20 | 356390..357357 |
| `IsCallable` | `sec-iscallable` | 7.2.3 | 321992..322544 |
| `IsConstructor` | `sec-isconstructor` | 7.2.4 | 322550..323116 |
| `CreateDataPropertyOrThrow` | `sec-createdatapropertyorthrow` | 7.3.6 | 342484..343666 |
| `DefinePropertyOrThrow` | `sec-definepropertyorthrow` | 7.3.8 | 344868..345691 |
| `OrdinaryObjectCreate` | `sec-ordinaryobjectcreate` | 10.1.12 | 686012..687577 |
| `OrdinaryCreateFromConstructor` | `sec-ordinarycreatefromconstructor` | 10.1.13 | 687583..689003 |
| `SameValue` | `sec-samevalue` | 7.2.9 | 326198..327025 |
| `SpeciesConstructor` | `sec-speciesconstructor` | 7.3.22 | 358544..359599 |
| `GetFunctionRealm` | `sec-getfunctionrealm` | 7.3.24 | 360971..362187 |
| `CreateArrayFromList` | `sec-createarrayfromlist` | 7.3.17 | 353435..354109 |

**Recommendation: externals with a profile, recorded as `foreignBoundary`
dependency rows.** These reach arbitrary user code (`Call`, `Construct`,
`Get` on a Proxy, `Invoke`), which is exactly the decision-kind treatment
`AGENTS.md` already mandates for underlying source, sink and transformer
methods. Their answers enter the tape as returned value, synchronous throw, or
promise settlement, with no modelled body. `SameValue` is the one exception and
can be a proved dependency on the value carrier.

### Group D — the iterator protocol

| Operation / type | Clause | § | span |
| --- | --- | --- | --- |
| Iterator Records | `sec-iterator-records` | 7.4.1 | 375082..376654 |
| `GetIterator` | `sec-getiterator` | 7.4.4 | 377783..378836 |
| `IteratorStepValue` | `sec-iteratorstepvalue` | 7.4.10 | 382802..383797 |
| `IteratorClose` | `sec-iteratorclose` | 7.4.11 | 383803..385025 |
| Iteration (the containing clause) | `sec-iteration` | 27.1 | 2628956..2686440 |

Used only by the four combinators, 4 call sites each for `GetIterator`,
`IteratorStepValue` and `IteratorClose`. `[[Done]]` is read 4 times.

**Recommendation: a named boundary, "iterator tape".** The combinators consume
a sequence of iterator answers — next value, done, throw — that is structurally
identical to a Streams foreign-boundary answer tape. This keeps the combinator
semantics `owned` while making explicit that no iterator implementation is
proved. It also bounds the P8 combinator work: without this boundary the lane
inherits all of §27.1.

### Group E — execution contexts, realms, agents

| Concept | Clause | § | span |
| --- | --- | --- | --- |
| Execution Contexts | `sec-execution-contexts` | 9.4 | 613273..624521 |
| `GetActiveScriptOrModule` | `sec-getactivescriptormodule` | 9.4.1 | 620281..620971 |
| Realms | `sec-code-realms` | 9.3 | 604679..613269 |
| Agents | `sec-agents` | 9.6 | 636552..643297 |
| `AgentSignifier` | `sec-agentsignifier` | 9.6.1 | — |
| Script Records | `sec-script-records` | 16.1.4 | 1363201..1365220 |
| Abstract Module Records | `sec-abstract-module-records` | 16.2.1.5 | 1388952..1398415 |

"Realm Record" occurs 11 times in scope, "execution context stack" 6,
`[[AgentSignifier]]` twice, `[[Realm]]` 9 times, "the current Realm Record"
twice.

**Recommendation: a named boundary, "host agent profile".** DB-03 makes the
*queue* state; it does not make the realm and active-script bookkeeping state.
Nothing in mask M1 or M2 observes a realm. The boundary records that
`[[Realm]]` is carried opaquely through a job and never inspected, which is
true of every in-scope algorithm.

### Group F — intrinsics and well-known symbols

| Concept | Clause | § | span |
| --- | --- | --- | --- |
| Well-Known Intrinsic Objects | `sec-well-known-intrinsic-objects` | 6.1.7.4 | 216017..239957 |
| Well-Known Symbols | `sec-well-known-symbols` | 6.1.5.1 | 120583..127678 |

Six distinct intrinsics are named in scope: `%Promise%` (4), `%Promise.prototype%`
(3, plus one as the string `*"%Promise.prototype%"*`), `%Object.prototype%` (4),
`%Function.prototype%` (1), `%Symbol.species%` (3 as `%Symbol.species%`, 1 as the
lower-cased spelling inside the clause id), `%Symbol.toStringTag%` (2 plus the
clause id).

**Recommendation: externals.** An opaque enumeration of intrinsic names with an
identity relation and no behaviour. `%Promise%` and `%Promise.prototype%` also
get `term` rows in scope (section 3.2) because the source `<dfn>`s them here.

### Group G — error objects

| Concept | Clause | § | span |
| --- | --- | --- | --- |
| TypeError | `sec-native-error-types-used-in-this-standard-typeerror` | 20.5.5.5 | 1685938..1686293 |
| AggregateError | `sec-aggregate-error-objects` | 20.5.7 | 1692351..1697088 |
| Error Objects | `sec-error-objects` | 20.5 | — |

Nine in-scope steps throw a `*TypeError*`; two create an `*AggregateError*`
(`PerformPromiseAny` at 2726246 and 2727534), one of them setting an `*"errors"*`
property.

**Recommendation: externals with a profile.** The model carries a throw
completion tagged with an error kind and a reason value; it never constructs an
Error object. This matches the `hostOnly` treatment `SPEC-MANIFEST.md` gives
Web IDL exception kinds and keeps the AggregateError `*"errors"*` array as a
first-order list.

### Group H — specification-wide conventions

| Concept | Clause | § | span |
| --- | --- | --- | --- |
| The List and Record Specification Types | `sec-list-and-record-specification-type` | 6.2.2 | 241422..244684 |
| implementation-defined | `sec-terms-and-definitions-implementation-defined` | 4.4.2 | 43325..43570 |
| Host Layering Points | `sec-host-layering-points` | D | 2952850..2955648 |
| Host Hooks (summary) | `sec-host-hooks-summary` | D.1 | 2953028..2953887 |
| Running Jobs (summary) | `sec-host-running-jobs` | D.4 | 2954830..2955052 |

Also in this group: the `« … »` List literal notation (44 pairs in scope), the
nine `~enum~` spellings observed (`~done~`, `~empty~`, `~fulfill~`,
`~fulfilled~`, `~pending~`, `~reject~`, `~rejected~`, `~sync~`, `~unused~`), and
the `_var_` / `*literal*` / `%intrinsic%` inline conventions of 2.4.

**Recommendation: a conventions record plus dependency rows.** The nine enum
spellings and the List type must be admitted as carriers before the first row is
written; annex D is `evidenceOnly` and should be recorded as an external so that
a future reader can see the host hooks were enumerated and checked against the
six in-scope `hook` rows. D.4 contains no requirement of its own — it is a
pointer back to `sec-jobs`.

### Group I — in-family hooks named but not called

| Concept | Clause | § | span |
| --- | --- | --- | --- |
| `HostEnqueueFinalizationRegistryCleanupJob` | `sec-host-cleanup-finalization-registry` | 9.9.4.1 | 657392..658392 |
| `EnqueueResolveInAgentJob` | `sec-enqueueresolveinagentjob` | 25.4.3.13 | — |

The first is named in the `sec-jobs` prose at 624875 but defined outside scope
and never called by an in-scope algorithm. The second is an out-of-scope
*consumer* of `PromiseCapability Record`, discovered while indexing; it matters
because a future `Atomics.waitAsync` lane would enter this library from above.

**Recommendation: dependency rows marked out-of-lane**, so that a later reader
can see they were found and deliberately excluded rather than missed.

## 6. Risks for a Lean byte-level parser, and how to bound them

**R1 — the file is one 2,978,793-byte blob and the rows live in 2.43 % of it.**
`Gates.Census.occurrences` scans the whole file for each pattern with a cap of
4096 hits. On this file `<emu-clause` occurs 2,189 times, `<emu-alg` 2,239 and
`<emu-xref` 998, all under the cap, but `<p>`, `<li>` and `<td>` will not be.
*Bound*: restrict every scan to the two in-scope byte windows, resolved once
from the two root clause ids, and refuse if either root is not found exactly
once. Do not raise the 4096 cap; a cap hit must be an error, never a silent
truncation. The R0 measurements (229 span digests over 374,064 bytes at 7.98 ms
compiled) say the digest pass over 72,286 bytes is free; the risk is the scan,
not the hash.

**R2 — `<emu-alg>` is not HTML.** A generator that reuses the Streams IDL or
requirement line scanners will read algorithm bodies as prose. *Bound*: a
dedicated step lexer with three refusal conditions — a non-blank line inside an
`<emu-alg>` that does not match `^ *1\. `, an indent that is not a multiple of
two relative to the block minimum, and an indent that jumps by more than one
level. All three are vacuous at this pin (0, 0 and 0 violations across 390
steps), which makes them cheap, permanent regression assertions for the breaker
battery.

**R3 — attribute order and non-`[a-z0-9-]` ids.** Two clauses put `oldids`
before `id`; two ids contain `%`; fifteen contain `.`; one contains an
upper-case letter. *Bound*: read attributes by name with the
whitespace-before-name rule already in `attrValue?`, never positionally; and do
not run `kebab` over a raw clause id. Section 2.6 shows the one collision
`kebab` produces; the breaker battery should assert that
`sec-promise.resolve` and `sec-promise-resolve` receive different row ids.

**R4 — fuel.** Every scan must stay fuel-bounded structural recursion with fuel
taken from a size the data carries, as `Gates.Census` does. The clause stack
machine needs a depth bound: the deepest in-scope clause nests 4 levels from
the document root and the deepest anywhere in the file should be measured
before the bound is fixed. *Bound*: fuel `= opens.size + closes.size + 1` for
the matcher, as `matchCloseAux` already uses, and an explicit refusal on stack
underflow or on a close tag whose name does not match the open on top.

**R5 — ASCII-first classification.** Only 188 bytes in scope are non-ASCII, in
four code points, and none is a structural byte. *Bound*: classify only bytes
below 0x80; copy every other byte; align every anchor and excerpt boundary
forward past continuation bytes with the existing `alignForward`. Add a
regression assertion that the four in-scope code points survive a round trip
through the excerpt normaliser, since `«` and `»` are inside `<emu-alg>` steps
that the excerpt of a short clause will reach.

**R6 — refusing unhandled shapes rather than skipping them.** The Streams IDL
scanner counts unrecognised statements and reports the count, which is zero at
its pin. That is the right pattern but the wrong default for a new lane, where
a shape appearing for the first time means the survey was wrong. *Bound*: every
scanner returns `.error` on an unrecognised shape. Concretely: an `<emu-clause>`
with a `type` value outside the four observed; a `<dl class="header">` with a
`<dt>` other than `description`; an `<emu-table>` whose `<thead>` does not have
exactly three `<th>`; a `<tr>` body row without exactly three `<td>`; a `<dfn>`
with neither `id` nor text; an `<emu-alg>` with a `replaces-step` or `example`
attribute. Each of these is a one-line check whose failure at the current pin
would be a real finding.

**R7 — the entity-free assumption.** Zero entity references occur in scope but
they occur elsewhere in the file. *Bound*: refuse on `&` inside a row span
rather than decoding it, so a re-pin that introduces one is a visible failure.

**R8 — the excerpt normaliser and the `|` separator.** `escapeField` already
escapes `|`, backslash and the three whitespace characters. In-scope text
contains 0 tab and 0 CR, so only LF and `|` can occur; `|` does not occur in
scope at all. *Bound*: keep `escapeField` unchanged and assert round-tripping
through `splitRow` for all 77 rows.

**R9 — a second census reading the same standard.** `Gates.Census.Standard` has
a single `definitionKeyed : Bool` discriminator. Adding ECMA-262 as a third
shape with that flag would force one of the two existing profiles onto it.
*Bound*: replace the flag with an explicit profile constructor before the
ecma262 standard is added, so the change is visible in one place and the
Streams and Infra profiles keep their exact current behaviour. See open
decision 2.

**R10 — section numbers are derived, not read.** Nothing in the source states
that `sec-promise-objects` is 27.2. If the census prints a section number it is
printing a computed fact that a re-pin can silently change. *Bound*: the census
row format has no section-number column and should not gain one; section
numbers belong in prose like this document, where they are labelled as derived.

## 7. Open decisions for the coordinator

1. **Extend the kind vocabulary, or reuse the existing six?** The proposal in
   section 3.2 adds `builtin`, `hook`, `record`, `field`, `property`, `clause`
   and `term` to `Gates.Census.Kind`, used only by the `ecma262` standard. The
   minimal-change alternative maps ECMA-262 onto the existing six as
   `op` (16 + 6 hooks + 13 built-ins = 35), `slot` (8 fields + 5 slots = 13),
   `requirement` (9), `type` (3 records + 6 terms = 9) and `rule` (the 11
   structural clauses, authored in `rules.tsv`) — 77 rows either way, but the
   disposition join loses the distinction between an abstract operation, a host
   hook and a built-in function object, which is the distinction that decides
   `owned` versus `foreignBoundary` versus `hostOnly`. Recommendation: extend.
2. **How does `Gates.Census.Standard` grow to a third source shape?** The
   `definitionKeyed : Bool` flag is already at its limit. Replacing it with a
   `profile : Profile` sum touches the two existing standards' records but not
   their behaviour, and `lake exe census` and `lake exe census --standard infra`
   must produce byte-identical projections after the change. This must be
   settled before any ECMA-262 scanner is written, because a breaker contract
   frozen against the current record shape would have to be re-frozen.
3. **Does DB-11 make the promise internal slots `owned` here while they stay
   `foreignBoundary` in the Streams census?** Section 4.1 argues yes, and that
   the two censuses are describing two different ownership questions. The
   coordinator must say so explicitly, and `census/README.md`'s "Foreign
   internal slots" paragraph — which already flags the three promise and
   completion-record rows as "the weakest of the twelve" — should record the
   cross-reference. Eight ✱ rows in section 4.2 and two ✱ row groups in 4.3
   hang on this and on decisions 4, 5 and 6.
4. **Is `HostEnqueuePromiseJob` a `requirement` realized by the FIFO queue, or a
   `foreignBoundary`?** DB-03 already rules the queue is deterministic state,
   which points at `requirement` and puts the P8 flagship theorem on the bullet
   at 634739..634841. Choosing `foreignBoundary` instead would leave DB-03 with
   no row to attach to. The same question decides
   `requirement.hostmakejobcallback.1` and `requirement.hostcalljobcallback.1`,
   which are requirements on hooks the model treats as boundaries and therefore
   can never go green.
5. **How are the nine requirement bullets identified?** The scheme in 3.3 uses
   the owner clause id plus a 1-based positional index, which is the only thing
   the source offers: none of the nine carries an `id`, unlike the Streams
   piping bullets, which the Streams census keys on their own `<dfn id=…>`. A
   positional id is stable only while the list is stable, and upstream reorders
   requirement bullets between editions. The alternative is a content-derived
   id (a kebab of the bullet's first clause), which is stable under reordering
   but changes on any editorial rewording.
6. **Is `sec-promise-objects`' state vocabulary `evidenceOnly` or `owned`?** The
   four paragraphs at 2686444 define *fulfilled*, *rejected*, *pending*,
   *settled*, *resolved* and *unresolved*, and every mask M1/M2 statement about
   promise settlement will use those words. `evidenceOnly` removes it from the
   denominator; `owned` puts a prose paragraph in the numerator with no
   algorithm to witness it.
7. **Which of the four escaping-reference treatments applies to Group C?**
   Section 5 recommends `foreignBoundary` externals for the 14 object-model
   operations, but `SameValue` and `CreateArrayFromList` are total functions on
   first-order data and could be proved dependencies. Splitting group C costs a
   second externals category; keeping it whole costs two rows that could have
   been green.
8. **Does this lane open with a census, or with a contract for the census
   scanner?** The URL lane's U2a receipt shows the cost of discovering five
   lexical defects after the scanner landed. The shapes in section 6's R6 list
   are all cheap to assert and all vacuous at this pin, which makes a
   breaker-first battery unusually cheap here.

## 8. What this survey did not do

- No `lake`, `lean` or build command was run; nothing in this document is a
  Lean receipt.
- The anchor ladder was checked for all 77 proposed spans, but by a PowerShell
  re-implementation of `chooseAnchorLength`, not by `Gates.Census` itself. The
  re-implementation clamps a ladder rung to the span length; `Gates.Census`
  does not, and would try a 256-byte probe that runs past the end of
  `field.job-callback-record.host-defined`'s `<tr>` before falling back to
  `remaining`. Whether that changes the chosen anchor for that one row must be
  checked against the real generator.
- Step-level rows were considered and rejected: 390 steps is a plausible
  granularity for a numerator, but `docs/SPEC-COVERAGE.md` already judges steps
  inside the coverage *state* of a row rather than as rows, and the Streams
  census does the same.
- The Web IDL side of DB-11 (`Whatwg.WebIdl`, pin
  `a652053f1e74e4aaf647528deb174012ed6c909f`) was not surveyed. The join
  between Web IDL's "a new promise" / "react" vocabulary and the ECMA-262 rows
  above is a separate pass and is what will decide whether Streams' existing
  `Readable.PromiseState` and `Writable.UnitPromise` become views with
  conversion receipts, as DB-11 requires.
- `docs/research/README.md` has not been updated with a row for this document,
  because this pass was fenced to writing exactly one file. That row is owed.
