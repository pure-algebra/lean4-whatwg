# W10 design: retarget P11 and P12; one shared gate package

Status: research record of the W10 design seat of review lane W, 2026-10-01,
branch `review/w10-retarget-design` from `97a8715`, under rulings R-W0 and
R-W1(f). It recommends; it makes no Model Claim, closes no graph edge,
changes no disposition, and edits no plan, router, contract or code. The
retarget is proposed text for `PLAN.md` (appendix A); the shared gate package
is a plan in the manner of `docs/HASH-PACKAGE-PLAN.md`. Creating a repository
or changing another one is the operator's decision.

| Subject | Pin |
| --- | --- |
| this repository | `97a871522ce18f792449f51300c9d93288abb398` |
| lean4-effect4 | `refactor/phase1-phase3` at `efcf1ae2f4d4ef7b599e5038572c66a977fe35b2` |
| `typescript` | `6afc9b841603796c16b266c0b8b92ded37a9445c` (`.lake/packages/typescript`) |
| `effects` | `a4ee7a14248ee5976039b73039319efa87834986` (v0.8.0) |
| `hash` | `c906b15dc3e94ebac0c10056270fbb345a1d2b6e` |
| toolchain | `leanprover/lean4:v4.33.1`, Windows 11 |

Evidence labels follow `docs/research/2026-09-30-implementation-review.md`:
`[C]` measured or read by this seat, with the command or path; `[S]` read in
source by a read-only helper of this seat and not re-read here; `[H]` a
hypothesis not tried.

## 1. Recommendation

Part A. P11 consumes lean4-typescript's syntax and renderer and builds here
only what this repository owns: the closed combinator alphabet as
first-order data, a lowering to `TypeScript.Module` that emits the host's own
WHATWG Streams API, an admitted-fragment predicate, and a host harness. It
loses its typing and simulation proofs, which no pinned artifact can carry:
the compiler's acceptance and the host runs become host observations, and
the theorems are totality, decoding and fragment admission. P12 drops the
Effect Channel embedding, whose target does not exist at `efcf1ae2` (no
Channel, Sink or Pull module; Flow archived), and becomes the
`Effects.Signature` face of the Streams calculi beside W9's agent face, plus
the Node bridge it already names.

Part B. D56 is real at the base: a module that removes the gate's linters in
an initializer and replaces its command builds green with no pass run. The
repair is a gate executable over the built `.olean` files. The prototype
imports them with `importModules (loadExts := false)`, so no audited
initializer, parser or elaborator runs, and reproduces the in-tree gate's
counts exactly (16,723 declarations; 84, 122 and 176 reaching
`Classical.choice`) in 4.3 s. Its own axiom traversal
agrees with `Lean.collectAxioms` on every declaration; registrations,
attribute reads and the token table from raw entries equal the loaded ones;
it reads all 222 sources. It also sees what the in-tree command cannot:
whether each `.olean` is current (Lake's trace hash) and the options each
module was compiled with (`-DwarningAsError=true` on all 216), closing D51
for every option Lake traces.

First step, in this repository alone and useful if no package ever ships:
`whatwg_trustgate` under a breaker addendum V2d, the passes factored into a
`WhatwgGates/Trust/` library both gates call, the three lists in a data
module `WhatwgGates/TrustConfig.lean`. The executable is decisive in CI; the
in-tree command stays for one lane, then the coordinator rules on retiring
it. Then the operator extracts `lean4-trustgate` (library and namespace
`TrustGate`) with history on the hash precedent, each consumer's cutover
proved by identical counts and identical self-test lines.

Order: (1) rule appendix A; (2) V2d breaker, factor builder, executable
builder, review; (3) breakers freeze representatives 8 and 9; (4) operator:
the shared repository, then each consumer.

## 2. Evidence

### 2.1 This repository at the base

- `[C]` `lake build` after warming the cache from the main checkout: "Build
  completed successfully (386 jobs)", 2.5 s, and the gate line "checked 222
  source files and 16723 declarations; Classical.choice is reached by 84 of
  12766 declarations in Whatwg, 122 of 2360 in WhatwgTest and 176 of 1597 in
  WhatwgGates; strict ceiling propext and Quot.sound over 5 module prefix(es)
  with 0 exact exception(s); 0 source-token exemption(s)".
- `[C]` The in-tree gate's narrow run, `lake env lean WhatwgTest.lean`
  (imports plus every pass): 7.6 s wall, the same summary line.
- `[C]` `WhatwgTest/Audit/AxiomGate.lean` is 1,542 lines; its declarations
  are `private` in `WhatwgTest.Audit`, and no battery ascribes any of them
  (`Select-String` over `Whatwg`, `WhatwgTest`, `WhatwgGates` for
  `AxiomGate` and `TrustSelfTest`: docstring mentions only).
- `[C]` Debt D53's size: 432 lines under `WhatwgTest/` name a `Gates.`
  declaration, 114 of them `#check` lines, in 19 files, four of them the
  generated `SpecCoverageRows` modules whose digests
  `WhatwgTest/Audit/CensusProfileIdentity.lean` pins.
- `[C]` The P2 stubs this retarget touches, all declaration-free:
  `Whatwg/Streams/Alphabet/Combinators.lean`,
  `Whatwg/Streams/Target/TypeScript/{Ir,Lower,Render,Decode,Simulation}.lean`,
  `Whatwg/Streams/Bridge/{EffectChannel,NodeStreams}.lean`. `Ir.lean`'s
  docstring promises "the typed TypeScript intermediate representation ...
  with its typing judgment"; `EffectChannel.lean` promises "the embedding
  between this calculus and the Effect Channel calculus".
- `[C]` `lakefile.toml` already says of the `typescript` require "P11 lowers
  through it instead of declaring a second intermediate representation"; no
  module under `Whatwg/` imports `Effects` or `TypeScript`.

### 2.2 lean4-effect4 at `efcf1ae2`: the review's sentences re-verified

The review's "Fit with lean4-effect4" read `0f16828a`. Between the two
commits 2,100 files differ, mostly research evidence trees; the lakefile,
manifest, toolchain and `src/Effect4/Program/Stream.lean` are unchanged
`[S]`. Each sentence of "Demand" and "Shared substrate":

| Sentence (review) | At `efcf1ae2` | Evidence |
| --- | --- | --- |
| lean4-effect4 built an unproved ECMAScript promise host (`OCaml5/Runtime/Promise.lean`) and archived it in `ab9f464b` | true with two corrections: the path was `src/OCaml5/Runtime/Promise.lean`, and `ab9f464b` removed it from `main` (the file survives in history, at `14e6835`); `src/OCaml5/` now holds only `Eff`, `Lcnf`, `Ml`, `Tools`; nothing models ECMAScript promise jobs, and "promise" there means Effect's `Deferred` | `[C]` `git show --stat ab9f464b`; `git ls-tree efcf1ae2 src/OCaml5/`; `[S]` 0 theorems, 13 `#guard`s in the removed file |
| `Whatwg.Ecma262` is the proved counterpart | still true: no ECMAScript job queue exists there | `[S]` |
| Its `DeferredStore` relates to `Promise.Table` by a projection under M1 | unverified: `DeferredStore` exists (used in `src/Effect4/Laws/Machine/Arena.lean`); no theorem in either repository states the projection | `[C]` `git grep DeferredStore`; the relation stays `[H]` |
| Its stream kernel is three external rows, open, pull and close, with answer `Option (List α)` | true, file unchanged; rows `openRow`, `pullRow`, `closeRow`, all `.async` and `.external`; no theorem about streams; ruled by DI-11 ("streams add zero new `Eff` constructors") | `[C]` `git diff 0f16828a efcf1ae2 -- src/Effect4/Program/Stream.lean` is empty; `[C]` DI-11 row of `docs/DESIGN-ISSUES.md` |
| It has no Channel calculus, so P12's "Effect Channel embedding" has no target | true: no `Channel`, `Sink` or `Pull` file under `src/`; `docs/core/language-cut.md` rules `Stream`, `Channel`, `Sink` "design only ... nothing landed"; DI-89 names Stream and Channel as a later packet | `[C]` `git ls-tree -r efcf1ae2 -- src`, `git grep Channel -- docs/core/language-cut.md` |
| and it retired the Flow route that section 5 lowers through | true: DB-02 "superseded by `Eff`", the route on branch `archive/flow-route`, and `AGENTS.md` says "do not re-import it"; the `effects` package at v0.8.0 still ships a generic `Effects/Flow/*` with checked admission and no lowering | `[C]` DB-02 of its `docs/DESIGN-BASIS.md`, its `AGENTS.md` section "What the tree is"; `git ls-tree` of `.lake/packages/effects` |
| RS-3 says each stateful standard is an `Effects.Signature` with one `Handler`; nothing under `Whatwg/` imports `Effects` | true | `[C]` no `import Effects` under `Whatwg/` |
| The calculi are bespoke step functions, so lean4-effect4 cannot sum a provider signature with its own | true, and narrower than stated: since `7a12f485` lean4-effect4's core root `Effect4` reaches no `Effects` module; `Signature.sum` is used only on its proof side (`Laws/Program/Sched.lean`, `RSig = StoreSig ⊕ₛ FiberSig`) | `[S]` |
| `Effects.Trace.Mask.m1` keeps operations, answers and the outcome, and `m2` keeps every event | understated: `m1` sets `ops`, `answers`, `outcome` and `frontier`, so it keeps the frontier and, through answers, failures; lean4-effect4 uses neither mask nor any trace mask of its own (its observation is `Effect4.Machine.obs`, fiber exits and stores) | `[C]` `Effects/Trace.lean` at v0.8.0, `def m1`; `[S]` no reference in lean4-effect4 |
| DB-04 uses the same two names; the names agree and the meanings differ | true | `[C]` |
| At v0.8.0 `Effects.Morphism` and `Effects.Transport` moved under `Effects.Experimental`, with no contract; a bridge built on signature morphisms would rest on that | true; lean4-effect4 imports no `Effects.Experimental` module, and its DI-20 records that the morphism kit has no Effect4 consumer | `[S]` |

What an embedding of `Whatwg.Streams` could target in lean4-effect4 today
`[S]`: external rows (`Row` with `.external` registration, the precedent of
`Program/Stream.lean` and `Program/Packages.lean`), the parked host
specification (`HostSpec`, `LawfulHostSpec` in `Program/Profile.lean`), and
on its proof side `Signature.sum`. There is no public signature or handler
extension point in its core library, and no lowering of any program to
Effect `Stream`, `Channel` or `Sink`: its printer `Effect4.Program.print`
has syntactic laws (`read_print`, `readModule_printModule`), and its design
basis lists typed lowering and simulation as pending. The vendored Effect
rc.112 sources it pins do carry `Stream.fromReadableStream` and
`Stream.toReadableStream` over the host API `[C]`
(`git grep "export const fromReadableStream"` in
`vendor/effect-4.0.0-rc.112/src/Stream.ts`).

### 2.3 lean4-typescript at `6afc9b8`

- `[C]` The pinned copy is detached at `6afc9b8`, reachable from
  `origin/codex/typed-source-carrier` only. `[S]` `git ls-remote`: upstream
  heads `main` at `71bad12` and `codex/typed-source-carrier` at `6afc9b8`;
  tags `v0.1.0` to `v0.4.3` and `v0.5.0` at `71bad12`; no tag equals or
  contains `6afc9b8`, and there is no `v0.6.0`. Debt D52 stands.
- `[C]` The local checkout `C:\Users\kokok\Dev\lean4-typescript` does not
  contain `6afc9b8` (`git cat-file` fails). `[S]` It sits on branch
  `v0.5.0-generator-cond` at `6a70b88`, whose two "v0.5.0" commits diverge
  from upstream after `18220f7`; upstream re-authored them as `71bad12`.
- `[S]` Contents: package `typescript`, version 0.6.0, MIT, no
  dependencies, libraries `TypeScript` and `TypeScriptTest`, no executable.
  `TypeScript.Syntax` (`Expr`, `Stmt`, `Decl`, `Module`, `Import`),
  `TypeScript.TypeRef` (structural types, with `LawfulBEq` and
  `DecidableEq`), `TypeScript.Render` (`Render.module : Style → Module →
  String`, total, structural), `TypeScript.Identifier`, `TypeScript.HostPin`
  (data; "the checks themselves run outside Lean"), `TypeScript.Structure`
  (block graph to structured control flow, unproved). Eight theorems, all
  `TypeRef` equality reflection. No typing judgment, no parser, no render
  determinism or injectivity theorem, no compiler harness, no axiom gate;
  its tests use `native_decide`.
- `[S]` Scope: the README says the package "knows nothing about effects",
  but the fragment is shaped for Effect generators (`Stmt.constYield`,
  `scopedGen`, `ProgDecl` printing `Effect.gen`), with no Stream or Channel
  nodes and no operators, `new`, loops over iterables, `try`, `async` or
  `await`. A Streams lowering would add constructors upstream or use
  `.call` and `.method` over identifiers.
- `[S]` lean4-effect4 imports it from seven `src/Effect4/Codegen/` modules
  and keeps its own compiler harness outside the package
  (`harness/schema-host/package.json` pins `typescript` 7.0.2,
  `@effect/tsgo` 0.38.0, `effect` 4.0.0-rc.112).

### 2.4 The four gates

Read by a helper seat `[S]`; this repository's gate was read here `[C]`, and
the others' `warningAsError` settings, CI kernel replays and lean4-hash's
scanned directories were spot-checked `[C]`. Rows are checks; cells name the
implementing declaration.

| Check | this repository: `WhatwgTest/Audit/AxiomGate.lean` | lean4-effect4: `Test/Audit/AxiomGate.lean` | lean4-hash: `HashTest/Audit/AxiomGate.lean` | lean4-effects: `EffectsTest/Audit/AxiomGate.lean` |
| --- | --- | --- | --- | --- |
| environment pass | `auditedDeclarations` (per-module `constNames`), `environmentFindings`: unsafe, partial, axiom, native auxiliary, `@[extern]`, `@[implemented_by]`, bodyless `opaque` | inline loop over `environment.constants.toList`; same six refusals; the root's own constants escape | inline; unsafe and partial only | inline; unsafe, partial, bodyless `opaque` |
| axiom ceilings | `repositoryCeiling` (R-11) and `strictCeiling`; `forbiddenAxioms`; `isNativeAuxiliaryAxiom` | one choice-free ceiling; choice admitted by module or declaration | one ceiling with choice; native shape | as lean4-effect4 |
| strict prefixes and exceptions | `strictCeilingPrefixes`, exact and private exceptions, five need checks | inverted: `choiceImplementationModules`, `choiceImplementationDeclarations`, inheritance through `admissionAncestors`, stale checks, reasons in comments | none | as lean4-effect4, lists nearly empty |
| token pass and word list | `foldCodeTokens`, `scanSource`; 25 refused words plus `unsafe`, `partial`; exemptions with five checks | none (retired 2026-09-19) | `unsafe`, `partial` only; `hashbin/` not scanned | 8 words by raw text, so `«sorry»` passes; no exemptions |
| metaprogramming-module rule | `metaprogrammingModules` (10), 44 keywords, `registrationsOf` over parser entries, 18 keyed attributes and the init attributes | none | none | none |
| token-table hygiene | `nonBaseTokens`, `inertFailures` | none | none | none |
| configuration shape | `configShapeFindings` | none | none | none |
| root rule and linters | `rootFindings`, `checkRootGateCommand`, `checkRootCommands` | none | none | none |
| reverse closure | `closureFindings` | forward closure and a library-layering check (`moduleImportClosure`) | forward only | forward only |
| self-test | `WhatwgGates/TrustSelfTest.lean` (`whatwg_trustselftest`): 75 plants, narrow runs, 81 checks, in CI | `scripts/test-trust-boundaries.sh` over the private lists; its fixture names constants deleted since (`[S]`, likely stale) | `HashGates/TrustSelfTest.lean` (`hash_trustselftest`), 9 plants | `scripts/test-trust-gate.sh` and `scripts/test-source-trust-tokenizer.sh`: 7 plants, 10 tokenizer cases |
| kernel replay | `lake env leanchecker Whatwg WhatwgTest WhatwgGates` in CI | none | `leanchecker --fresh Hash.Verified` | none |
| reporting | every finding, summary only when clean | first error | first error | first error |
| `warningAsError` | package `leanOptions` | `-DwarningAsError=true` in every library's `moreLeanArgs` | package `leanOptions` | none anywhere |

The superset on refusals is this repository's gate: every refusal of the
other three is in it, and it adds the 25-word token pass, rules 1 to 5 of
addendum V2c, collect-all reporting, entry-point scanning and a kernel
replay. It is not a strict superset of lean4-effect4's: it lacks that gate's
library-layering check (`Effect4` never reaches `Effect4.Laws`), its
choice-free default ceiling (a policy difference R-11 chose), and its fresh
root elaboration when the source inventory changes. lean4-hash pins its
per-family audits with `#guard_msgs` and floors (`minimumDeclarations`),
which guard against a vacuous audit; lean4-effects keeps a signature and
axiom parity receipt. Roughly 75 lines of this repository's gate descend
from lean4-effect4's (`moduleOf?`, `isGeneratedSafeRecursor`,
`synthesizedOpaqueBodies` are identical) `[S]`.

What each would gain or lose by adopting this repository's gate:

| Repository | Gains | Loses unless the package adds it |
| --- | --- | --- |
| lean4-effect4 | the token pass it retired, rules 1 to 5, the root's constants audited, collect-all reporting, a kernel replay | layering rules; admission inheritance, so auxiliaries need exact entries; a long metaprogramming list (its `Laws.Auto.*` and tactic modules) |
| lean4-hash | environment refusals for axiom, `@[extern]`, `@[implemented_by]`, bodyless `opaque`; the full word list; `hashbin/` scanned | nothing; its family audits and `leanchecker --fresh` stay its own |
| lean4-effects | environment refusals; escaped and qualified spellings; rules 1 to 5 | nothing, but the options check refuses its tree until it builds with `warningAsError` |

### 2.5 The executable prototype

The prototype is `W10Proto.lean` with a temporary `[[lean_exe]]` entry
(`supportInterpreter = true`, needed only by the comparison mode), built by
`lake build w10_proto` and run from the worktree root; appendix B lists it.
Both files were removed before the final commit. Every number is `[C]`.

| Measurement | Command | Result |
| --- | --- | --- |
| axiom pass, extensions not loaded | `lake exe w10_proto` | PASS; 16,723 declarations of 2,564 environment modules; choice reached by 84 of 12,766 in Whatwg, 122 of 2,360 in WhatwgTest, 176 of 1,597 in WhatwgGates: the in-tree gate's numbers; 28,147 constants traversed |
| time | the same, three runs | import 1.2 s, axiom traversal 1.3 to 1.4 s, token scan 1.0 s; 4.3 s wall including `lake exe` and the attribute reads below (5.7 s on the first, cold run) |
| agreement with `Lean.collectAxioms` | `lake exe w10_proto --compare` | 0 of 16,723 declarations differ |
| the table route | an earlier revision's `--tables` mode, `importModules (loadExts := true)` and `Lean.collectAxioms` | 1.6 s, but it requires `enableInitializersExecution`, which is `unsafe`, and runs the imported modules' initializers in the interpreter: without `supportInterpreter` it stopped on an interpreted call to `IO.getRandomBytes` |
| registrations from raw entries | `lake exe w10_proto`, `--compare` | 8 token, 8 parser, 8 command-elaborator and 2 initializer entries in audited modules; the same with extensions loaded |
| environment-pass reads | `lake exe w10_proto`, `--compare` | over every constant of the environment, Lean's included: 963 `@[extern]`, 324 `@[implemented_by]`, 15 axioms, 3,622 `unsafe` or `partial`; the same with extensions loaded, since a parametric attribute answers for an imported declaration from raw module entries |
| token table | `--compare` | rebuilt from the builtin table and raw `.token` entries: 511 tokens; `Parser.getTokenTable` with extensions loaded: 511; no token in one and not the other |
| source scan | `lake exe w10_proto` | 222 sources, 415,600 tokens of code, 0 tokenization failures; 416 `#guard`, 35 `config`, 2 `run_cmd`: the contract's counts (V2c.4, V2c.7) |
| freshness | the same | 216 of 216 audited modules match the source hash their Lake `.trace` records; after appending a comment to `Whatwg.lean` without rebuilding, 215 and `stale [Whatwg]` |
| recorded options | the same | `-DwarningAsError=true`, `-DautoImplicit=false`, `-DrelaxedAutoImplicit=false` on all 216 |
| extension inventory | `lake exe w10_proto --extensions` | 51 environment extensions hold entries from audited modules, read from `ModuleData.entries` by name with no extension registered |
| the residual of V2c.7 | a temporary module `WhatwgTest/W10Plant.lean`, imported first by `WhatwgTest.lean`: an `initialize` that filters `rootGateCommandCheck` out of `lintersRef` and `rootCommandsCheck` out of `moduleLintersRef`, and a `macro_rules` that expands the gate command to `#check 1`; then `lake build` and `lake exe w10_proto --extensions`; both files removed and the tree rebuilt | `lake build` exit 0, 387 jobs, the root printing `1 : Nat` and no gate line: the gate replaced and its post-command check removed, accepted. The executable's raw reads recorded the plant: initializer entries 2 to 4, one `Lean.Elab.macroAttribute` entry (52 extensions), 223 sources scanned. The prototype does not run rule 1 as a refusal, so this is the input a ported pass refuses, not its verdict |

## 3. Part A: retarget P11 and P12

### 3.1 What the P11 row presumes that no longer holds

P11 reads "closed combinator alphabet, typed TypeScript IR, lowering,
render, host harness", exit "typing and simulation proofs; deterministic
bytes; exact coverage". Three presumptions fail.

1. A typed TypeScript IR built here. The lakefile already chose to lower
   through the `typescript` package instead, and that package supplies the
   syntax and a renderer, not a typing judgment (2.3). Building a second IR
   here would duplicate it and violate the choice the lakefile records.
2. Typing and simulation proofs. A typing proof needs a TypeScript typing
   judgment; a simulation proof needs a semantics of the emitted fragment
   and of the host's Streams API. No pinned artifact has either, and
   lean4-effect4's own design basis lists typed lowering and simulation as
   pending. What can be a theorem here is about the lowering as data.
3. Section 5 of `docs/REIFICATION-STRATEGY.md`, that Stratum S "lowers
   through the checked Flow to Effect v4 `Stream`/`Channel`/`Sink`
   programs". lean4-effect4 archived Flow, has no Stream or Channel, and
   rules that streams add no `Eff` constructors (2.2).

### 3.2 P11 candidates

| Candidate | Deliverable | Exit gate | Cost |
| --- | --- | --- | --- |
| P11-a, host-native target, consumed syntax | the alphabet as first-order data; `lower : Program → TypeScript.Module` emitting the host's own `ReadableStream`, `TransformStream`, `pipeThrough` and `pipeTo`; an admitted-fragment predicate over `TypeScript.Module`; `TypeScript.Render.module` to UTF-8 bytes; a harness with a pinned compiler and the DB-08 host profiles | lowering total on admitted programs and decoded back to its program (theorems); every rendered module admitted (theorem) and byte-identical on regeneration (drift gate); compiler acceptance and M1 agreement with the model on a frozen corpus (host observations) | small upstream additions or `.call` and `.method` spellings; no theorem relates host execution to the model |
| P11-b, own typed IR and semantics | the stubs' plan: an IR here with a typing judgment and a fragment semantics, and simulation proofs | as written today | a second IR beside the consumed one; a TypeScript and Streams-API semantics authored here with nothing to check it against but the hosts; large |
| P11-c, through lean4-effect4 | lower to `Eff` and print Effect TypeScript | lean4-effect4's printer laws | no target: `Eff` has no stream constructors by DI-11 and only three external rows |

Recommendation: P11-a. It keeps the semantic owner first-order data here,
lowers to the API the standard itself defines (RS-5's host realizer with a
generated adapter), and puts every claim it cannot prove where DB-08 already
puts host evidence. The tradeoff is explicit: a green P11 says the lowering
is total, injective by decoding and lands in an admitted fragment, and that
pinned hosts agree with the model on a corpus under M1; it does not say the
emitted program behaves as the model on every input. A simulation theorem
becomes a later row if a fragment semantics is ever pinned.

### 3.3 What the P12 row presumes that no longer holds

P12 reads "Node legacy streams calculus, Effect Channel embedding
(cross-repository)", exit "each bridge names its loss and its mask". The
Node half stands. The Effect half presumes a Channel calculus in
lean4-effect4 (none, 2.2) and, through RS-3, that the bridge is a signature
morphism, which would rest on the uncontracted `Effects.Experimental` root.

### 3.4 P12 candidates

| Candidate | Deliverable | Exit gate | Cost |
| --- | --- | --- | --- |
| P12-a, face plus Node | the `Effects.Signature` face of the Streams calculi in W9's `WhatwgEffects` library, beside the agent face, with its embedding in the calculus; the Node legacy calculus related through `Readable.toWeb` and `Readable.fromWeb` | the face's handler run equals the calculus run under a DB-04 mask (theorem); each Node direction names its loss under M1, with the Node profile's observations as host evidence | the face uses only `Signature`, `Program`, `Handler` and `Signature.sum`, never `Effects.Experimental`; W9 lands first |
| P12-b, Node only | the Node calculus and bridge | as today, Node half | lean4-effect4 gets nothing to sum; RS-3 stays unrealised |
| P12-c, hold the Effect half | Node now; the Channel embedding waits on lean4-effect4's Stream and Channel packet | as today | an open row with no owner and no date |

Recommendation: P12-a. The face is the one thing lean4-effect4 can consume
today (it already sums signatures on its proof side), it is built and
proved here, and it is the bridge RS-3 asked for. The tradeoff: Effect TS
interop at the program level stays host evidence (Effect rc.112's
`Stream.fromReadableStream` and `toReadableStream`, observed in the P11
harness under a named loss) until lean4-effect4 has a Stream calculus to
embed into; the P12 row says so rather than carrying an unbuildable
deliverable.

### 3.5 Representatives 8 and 9

- 8, target: one program of the closed alphabet (a default readable piped
  through one map transform) lowered to an admitted `TypeScript.Module`,
  rendered to bytes that regenerate identically, accepted by the pinned
  TypeScript compiler, and run on the Node profile with an M1 observation
  equal to the model's on one input.
- 9, bridge: one Node legacy `Readable` related to a WHATWG `ReadableStream`
  in both directions with its loss named under M1, and one operation of the
  readable default path through the `Effects.Signature` face whose handler
  run equals the calculus step under M1.

Neither is frozen today (`test/contracts/` holds no logic, target or bridge
contract `[C]`), and AGENTS.md's breadth rule asks for a frozen
representative in every group before depth. Freezing 8 and 9 is breadth work
a breaker can do as soon as the retarget is ruled.

### 3.6 Cross-repository parts and the first in-repository step

Cross-repository, each the operator's: a tag upstream for the `typescript`
pin (D52), or a pin moved to a tag; constructors added upstream if the
lowering needs Stream-shaped syntax (otherwise `.call` and `.method`
suffice); whether the harness shares lean4-effect4's compiler pins
(`typescript` 7.0.2, `@effect/tsgo` 0.38.0) or carries its own; and
lean4-effect4's choice to sum the face. Everything else is here. The first
in-repository step is the coordinator's ruling on appendix A, then a breaker
packet freezing representative 8 (the alphabet's first constructor, the
fragment predicate's statement, the corpus case and the compiler pin) and
representative 9 (the face's one operation and the Node case), red. The stub
docstrings of `Target/TypeScript/Ir.lean` and `Bridge/EffectChannel.lean`
change in those packets: `Ir.lean` becomes the admitted-fragment predicate
over the consumed syntax, and `EffectChannel.lean` is removed in favour of a
face module under W9's library. `docs/ARCHITECTURE.md`'s two rows change at
the same landing.

### 3.7 What section 5 of `docs/REIFICATION-STRATEGY.md` must change

Three sentences are false at `efcf1ae2`: Stratum S lowering "through the
checked Flow to Effect v4 `Stream`/`Channel`/`Sink` programs"; that this is
"Effect4's own ledger"; and the vocabulary "program lowering is
`required-open`", which lean4-effect4 no longer uses (its design basis says
"pending"). The host-native half ("or to the host's native WHATWG Streams
under RS-5 with a generated adapter") becomes the route. Appendix A gives
the replacement paragraph; section 9 of that document gains one sentence
that the Flow route it cited is archived.

### 3.8 Relation to W9

W9 proposes `Whatwg.Effects.*` in its own library `WhatwgEffects`, under the
strict ceiling, with the agent face first. The retargeted P12 is the second
module of that library: a Streams face whose operations are the algebraic
ones RS-3 names (`enqueue`, `read`, `write`, `close`, `error`,
`desiredSize`), whose promise settlements go through W9's agent face, and
whose handler is the calculus step. Two constraints follow from 2.2: the
face theorems name DB-04's M1 and M2, never `Effects.Trace.Mask.m1` (the
names collide and the meanings differ), and nothing under the strict prefix
imports `Effects.Experimental`. R-W1(a) applies: before the face lands, the
constants it cites from `effects` are measured for `Classical.choice`.

## 4. Part B: one shared gate package

### 4.1 The architecture decision of D56

The gate is a command inside the tree it audits, so code that runs during
that tree's elaboration can replace it or remove its linters (D56, contract
V2c.7). The repair is a gate that runs in its own process over the built
`.olean` files, the way `leanchecker` does, and that loads nothing it would
have to trust.

Mechanism, measured in 2.5:

1. `Lean.importModules imports {} (loadExts := false)`. No environment
   extension's import hook runs, so no parser descriptor is evaluated and
   no `initialize` of an audited module runs; the call needs neither
   `unsafe` nor the interpreter. The constant map, the module headers and
   every extension's raw module entries are available.
2. Declarations are enumerated per module from `ModuleData.constNames`,
   attributed by `getModuleIdxFor?`, as the in-tree gate does.
3. Axioms are collected by an own memoised traversal of each constant's
   kernel type and value, in `Lean.CollectAxioms.collect`'s order, rather
   than from the per-module tables `exportedAxiomsExt` wrote when each
   audited module was elaborated. The traversal is total (an explicit stack
   bounded by fuel; exhaustion is an error).
4. Registrations are read from the parser extension's, the keyed
   attributes' and the init attributes' raw module entries, exactly the
   readers `registrationsOf` uses; and, beyond them, every extension with
   entries in an audited module is read by name from `ModuleData.entries`.
5. The final token table is rebuilt from `Parser.builtinTokenTable` and the
   raw `.token` entries, and every audited source is tokenized with the
   in-tree gate's `foldCodeTokens`; the source passes port unchanged.
6. Each module's Lake `.trace` gives the source hash its `.olean` was built
   from and the `-D` options it was compiled with.

The executable's own code is the gate library, Lean, Lake's trace hashing,
and this repository's config module. The config module is the one audited
module linked into it; its one definition is data and it imports only the
library's `Config` module, so no other audited code runs in its process.

### 4.2 What the executable sees, and what it cannot

| Channel | In-tree command | Executable |
| --- | --- | --- |
| gate replaced by a `macro_rules` or `@[command_elab]` | caught by the V2c.5 linters, which an initializer can remove | not applicable: nothing audited elaborates or runs in its process; the registration is still refused by rule 1 from raw entries |
| linters removed by an initializer | accepted by `lake build` (measured, 2.5), caught only by the self-test (V2c.7) | not applicable; the `initialize` and the macro are in the raw entries the executable reads (measured), and rule 1 refuses them |
| root with extra commands or constants | root rule and `map₂` check | root rule ported as a lexical check of `WhatwgTest.lean`; the root module's constants audited like any module's when its `.olean` is current |
| registration channels outside the six kinds (`unif_hint`, simprocs by attribute, code actions) | not refused (D56) | refusable by an allowlist of extensions by name: 51 today, each with a reason; an unknown extension with an audited entry is refused |
| options set in `lakefile.toml` (`leanOptions`, `moreLeanArgs`) | invisible (section 13, V2c.7) | visible in each module's trace; the gate can require `-DwarningAsError=true` and refuse a `debug.*` option on every audited module (D51's lakefile half). `weakLeanArgs` stay invisible: Lake keeps them out of the trace by design, so a `-Ddebug.skipKernelTC=true` passed that way is caught only by `leanchecker`, unless the gate also refuses a non-empty `weakLeanArgs` in `lakefile.toml` |
| a stale verdict replayed from cache (D49) | possible: the gate reads files Lake does not track | not possible: it reads at run time and refuses an `.olean` whose trace hash differs from its source |
| a declaration added with the kernel check off (D55) | not caught | not caught; `leanchecker` stays a separate CI step (79 s, R-V6) |
| `example`, `#guard`, `set_option`, any token | the token passes | the same token passes: no trace of these reaches an `.olean`, so this part stays lexical |
| options set by a metaprogram (`withOptions`), names built by metaprogramming | invisible | invisible: they leave no trace in a trace file or a constant except through what the axiom pass and `leanchecker` see |
| a dependency's syntax or the toolchain's base tokens | trusted through the pins | the same |

So the executable closes D56's first item (replacement and linter removal)
structurally, its registration-channel item by an allowlist, and D49 for
this gate; D55 stays with `leanchecker`; the lexical limits of sections 13,
V2b.6 and V2c.7 stay as they are, because the source scan is the same code.

One consequence for the import set. If the in-tree command still runs and
refuses, Lake does not write the root's `.olean`, so an executable that
imports the root would read a stale root and stop on freshness. The
executable therefore imports every module that an audited source names,
the root excepted, and checks the root lexically; when the root's `.olean`
is current it also audits the root's constants. This keeps the two gates
independent in the self-test. The prototype imports the root itself, which
declares no constant, so its counts are the same either way.

### 4.3 The in-tree command: keep, slim, retire

| Option | What `lake build` decides | Cost |
| --- | --- | --- |
| keep both, one library | every pass, as today; the executable is decisive in CI | two entry points over one library; the V2c.5 linters remain |
| retire the command after one lane | nothing about trust; `lake exe whatwg_trustgate` after `lake build` decides | the root `AGENTS.md` "Gates" table changes; a local `lake build` no longer refuses a trust token |
| command only | as today | D56 stays |

Recommendation: keep both through one lane, with both calling the same
`WhatwgGates/Trust/` library so no pass is written twice; then the
coordinator decides retirement on the evidence that the executable refused
every row the command refused. The command costs about 7.6 s per root
re-elaboration; the executable 4.3 s per run.

### 4.4 Lake, CI and D49

- Target: a plain `[[lean_exe]] whatwg_trustgate` with root
  `whatwgbin.TrustGate`, beside the other gate executables. Lake 5.0.0 also
  accepts a `lintDriver` naming an executable, in this package or as
  `<package>/<name>` in a dependency (`lake lint`); that is an alias worth
  adding, not a substitute, because building a driver builds its own
  imports, not the audited libraries. `testDriver` (`lake test`), which
  lean4-hash points at its `HashVerified` library, fits a library of
  checks better than a gate over the built tree.
- Freshness: the executable cannot make Lake build the audited libraries
  first `[H]` (not checked whether `lake exe` can be made to); it refuses a
  missing or stale `.olean` instead, so a forgotten `lake build` fails
  closed.
- CI: after "Test root and the elaboration-time axiom gate", a step `lake
  exe whatwg_trustgate`; the self-test and `leanchecker` steps stay.
- D49: the executable reads every input at run time and compares source
  hashes, so its verdict is never a cached replay. D49 stays open for the
  census batteries and `SpecCoverage.lean`; W6's and W7's executables move
  their gates the same way.

### 4.5 The shared package: name, libraries, namespaces

- Repository `pure-algebra/lean4-trustgate`, beside lean4-hash,
  lean4-effects and lean4-typescript; Lake package `trustgate`; MIT; zero
  dependencies; Lean 4.33.1.
- Library `TrustGate` (modules `TrustGate.*`), its own test library
  `TrustGateTest`, executable roots `trustgatebin.*`, executables
  `trustgate_*` (`trustgate_selftest`), following `docs/AGENT-ROUTING.md`,
  "Packages cloned from this skeleton".
- Declaration namespaces equal module prefixes: `TrustGate.*`. That
  resolves D53 for the code that crosses repositories. For the rest of this
  repository's tooling, recommend resolving D53 by rule rather than rename:
  `Gates.*` is repository-private, no audited module imports another
  package's tooling modules (a layering rule the package can check), and
  the rename (114 `#check` lines in 19 files, four generated modules and
  their digest pins) waits for a consumer that needs it.

### 4.6 API: library code and per-repository data

Library code is every pass, the word lists' defaults, the loader, the
traversal, the tokenizer, the reports and the self-test harness. Per-
repository data is one Lean value of type `TrustGate.Config` in a module of
the consumer that imports only the library's `Config` module. Lean, not a
data file: it is typed and elaborated, the gate audits it, the self-test's
anchors stay Lean source lines, and no TOML or JSON parser joins the trusted
code. The cost is one executable per consumer, a one-line root.

Elaborated in the prototype (appendix B), in namespace `TrustGate`:

```lean
structure Ceiling where
  label : String
  axioms : List Name
structure StrictException where
  declaration : Name
  reason : String
structure Config where
  roots : Array Name
  trees : List Name
  ceiling : Ceiling
  strictCeiling : Ceiling
  strictPrefixes : List Name
  strictExceptions : List StrictException
  forbiddenAxioms : List Name
structure AuditedDeclaration where
  name : Name
  moduleName : Name
  tree : Name
def auditedDeclarations (config : Config) (environment : Environment) :
    Except String (Array AuditedDeclaration)
def dependencies (info : ConstantInfo) : Array Name
abbrev AxiomMemo := Std.HashMap Name (Array Name)
def axiomsOf (environment : Environment) (fuel : Nat) (memo : AxiomMemo)
    (root : Name) : Except String (Array Name × AxiomMemo)
def strictPrefixOf? (config : Config) (moduleName : Name) : Option Name
def axiomPass (config : Config) (declarations : Array AuditedDeclaration)
    (axiomsOfDecl : AuditedDeclaration → Array Name) : AxiomReport
def tokenTableFromEntries (environment : Environment) : IO Parser.TokenTable
def foldCodeTokens {σ : Type} (environment : Environment)
    (tokenTable : Parser.TokenTable) (fileName input : String) (init : σ)
    (step : σ → Syntax → Position → σ) : σ × Option String
def traceOf (buildRoot sourceRoot : System.FilePath) (moduleName : Name) :
    IO (Bool × Array String)
```

Proposed beyond the prototype `[H]` (not elaborated):

| Field of `Config` | Holds | Today |
| --- | --- | --- |
| `label : String` | the word every diagnostic and the summary line start with, so this repository's frozen fragments ("Whatwg trust gate: …") stay byte-identical | spelled in the gate's strings |
| `trees`, `sources` | audited prefixes; module source directories, root files, entry-point directories, the test root | `auditedTrees`, `auditedSources` |
| `ceiling`, `rules : List CeilingRule` | the repository ceiling and rules by tree, prefix or exact module, longest scope wins; lean4-effect4's admitted modules are exact-module rules | `repositoryCeiling`, `strictCeilingPrefixes` |
| `exceptions`, `privateExceptions` | exact admissions, each with a reason | the two exception lists |
| `sourceTokenExemptions`, `metaprogrammingModules` | exact module entries with reasons | the two lists |
| `extraRefusedWords` | additions only; the 25 words and the 44 keywords are library defaults | `refusedWords`, `metaprogrammingKeywords` |
| `extensionAllowlist` | additions to the library's allowlist of extensions, with reasons | none |
| `requiredOptions` | options every audited module's trace must record, default `-DwarningAsError=true` | none |
| `layers : List LayerRule` | "module prefix A never reaches prefix B", lean4-effect4's layering check | none here |
| `minimumDeclarations` | per-tree floors against a vacuous audit, lean4-hash's idea | none |
| `summary` | the summary line's shape; this repository's is the frozen template of contract section 7 | `runGate`'s `logInfo` |

with `def run (config : Config) (args : List String) : IO UInt32` as the
executable body and the in-tree command calling the same passes.

Declaration record for these names: owner `WhatwgGates/Trust/` here, the
`TrustGate` package after extraction; disposition tooling, with no
specification anchor; reuse mode move (R-P12), since each replaces a
`private` declaration of `WhatwgTest/Audit/AxiomGate.lean` and nothing is
duplicated; assurance route the contract and the trust self-test, as for
the gate in lane V, with no proof graph.

In this repository the data would be `WhatwgGates/TrustConfig.lean`
(`Gates.TrustConfig.config`), holding the three lists below their frozen
anchor comments, and the entry point `whatwgbin/TrustGate.lean`, one line.
The gate checks that the config module imports only `TrustGate.Config`.

### 4.7 The self-test and the contract

The harness mechanism (`Placement`, `Edit`, `withEdits`, `checkPlant`,
`templateMatches`, `expectNarrowRun`) is generic and moves to the package as
`TrustGate.SelfTest` `[H]`. The plant tables, the fixtures and the anchors
stay with each consumer, because they name its files and its data. The
anchors move with the lists to the config module, so the nine after-anchor
rows (V2-S3 to V2-S6, V2-X1, V2-X2, V2c-L1 to V2c-L3) change their target
file and nothing else.

`test/contracts/trust-gate-hardening.contract.md` stays here as this
repository's contract: its fragments, rows and claim scope are about this
tree. The package gets its own contract, frozen by a breaker in that
repository, stating each pass with `<label>` in place of `Whatwg`, seeded
from sections 4, 6, V2b.3 and V2c.2 to V2c.6. A word-list change then lands
upstream; this repository's V2-T and V2b-T rows are what stop a pin bump
that would drop a word. Breaker ownership of this repository's packet does
not move.

### 4.8 Extraction order

| Step | Where | Act | Cutover proof | Operator |
| --- | --- | --- | --- | --- |
| 0 | here | breaker addendum V2d: the executable's contract, the moved anchors, the executable column of every row, executable-only plants | red rows exactly as declared | no |
| 1 | here | factor the passes into `WhatwgGates/Trust/*.lean`, the lists into `WhatwgGates/TrustConfig.lean`; the in-tree command calls the library | all 81 self-test lines identical; the Whatwg count of the summary line identical; WhatwgTest and WhatwgGates counts move by exactly the moved constants; every constant outside the moved modules unchanged by fingerprint (WP-7's method) | no |
| 2 | here | `whatwg_trustgate`, its CI step, the self-test's executable column | the executable's counts equal the in-tree summary on the unmodified tree; every V2d row green | no |
| 3 | new repository | create lean4-trustgate from `WhatwgGates/Trust/**` with history (`git filter-repo`, HP-3's precedent); namespace `TrustGate`; label-generic messages; its own contract, self-test, CI and `leanchecker`; tag `v0.1.0` | its gate green on itself; a fixture consumer reproduces this repository's fragments | yes: create, push, tag |
| 4 | here | `[[require]] trustgate` at the tag's commit under the dependency policy's probe; delete `WhatwgGates/Trust/**` | every self-test line identical; the executable's report identical; Whatwg count identical; WhatwgGates count lower by exactly the moved constants | the push of step 3 |
| 5 | lean4-hash | adopt with its data | its gate's declaration and choice counts identical; its 9 plants pass; every new refusal measured zero on its tree or listed | yes |
| 6 | lean4-effects | adopt; `warningAsError` decided | counts identical; its parity receipt unchanged | yes |
| 7 | lean4-effect4 | adopt with layering rules and exact admission lists | counts and the layering verdict identical | yes |

The acceptance probe at step 4 follows `PLAN.md`'s dependency policy: exact
pin, builds on 4.33.1, MIT, zero transitive packages; nothing under
`Whatwg/` imports it, so the library's representation cannot narrow. Steps 1
and 2 are the first step usable if the package never ships. lean4-hash and
lean4-effects state a zero-dependency rule; whether a gate dependency counts
is the operator's (decision O3).

### 4.9 Relation to W6 and W7

W6's `whatwg_declsnapshot` and W7's `whatwg_ledger` both load the built
environment in an executable. They should share the loader with this one:
one module (`WhatwgGates/Trust/Load.lean` here, `TrustGate.Load` after
extraction) owning `initSearchPath`, `importModules (loadExts := false)`,
per-module declaration enumeration and the trace freshness check. Measured
for them: a persistent extension's entries, such as W6's freeze registry,
are readable from `ModuleData.entries` by extension name with nothing
loaded, so neither needs `loadExts` or an initializer. Whichever slice lands
first owns the module; the others import it. W7's reference checks (does a
named theorem exist, in which module) are `environment.find?` and
`getModuleIdxFor?` on the same environment.

## 5. Effect on frozen surfaces and on the trust gate

- Frozen statements and batteries: no `#check` ascription changes; no
  battery ascribes a gate declaration (2.1). Ruling R-W1(b) is met with
  zero altered ascriptions.
- The contract: addendum V2d, appended by a breaker. It changes section 10
  and V2c.2's anchor location from `WhatwgTest/Audit/AxiomGate.lean` to
  `WhatwgGates/TrustConfig.lean` (anchor text unchanged), the selector
  `auditSource` of section 1, the judge of every row (an executable column),
  and V2c.7's claim scope (the items 4.2 closes). Sections 3, 7 and every
  fragment are unchanged.
- Self-test rows: the nine after-anchor rows retarget their file; every row
  gains an executable expectation (the same fragment, a named executable
  fragment, or fail-closed on a stale `.olean` where Lean itself refused the
  planted module); new `V2d-` rows: a module that both replaces the gate
  command and removes the linters with an initializer (accepted by `lake
  build`, the V2c.7 hole; refused by the executable), `unif_hint` in an
  unlisted module (if the allowlist is adopted), a source edited after the
  build (stale), and a library compiled with `-DwarningAsError=false`
  through `moreLeanArgs` (slow: it rebuilds a library in the probe; a review
  clause if the breaker measures it too slow).
- The metaprogramming list: unchanged at V2d. `WhatwgGates/Trust/*` declares
  no syntax and runs nothing at elaboration, and `whatwgbin/TrustGate.lean`
  cannot be listed. `WhatwgTest.Audit.AxiomGate` stays listed while the
  command exists and leaves the list if it is retired.
- Summary line: template unchanged; at step 1 its WhatwgTest and
  WhatwgGates counts move by the moved constants, which the landing states.
- Ceilings: `WhatwgGates` stays under R-11; no strict prefix changes.
- Owners: the breaker owns V2d, its fixtures, rows, selectors and the
  harness mechanism; the builder owns `WhatwgGates/Trust/**`,
  `WhatwgGates/TrustConfig.lean`, `whatwgbin/TrustGate.lean`, the wrapper in
  `WhatwgTest/Audit/AxiomGate.lean`, the `lakefile.toml` entry, the CI step
  and the two tree routers; the coordinator owns the root `AGENTS.md` gate
  table, `PLAN.md` and `COORDINATION.md`.

## 6. Slices

In-repository first step, W10-G, after the coordinator's ruling:

1. Breaker (own process): addendum V2d of
   `test/contracts/trust-gate-hardening.contract.md`; fixtures
   `test/fixtures/trust-gate/v2d-*.lean.txt`; rows `V2d-*`; the executable
   judge in `WhatwgGates/TrustSelfTest.lean` (mechanism only); selectors for
   the config module. Red: every executable column "could not run" and the
   nine after-anchor rows "could not plant"; `known-red.txt` unchanged.
2. Builder B1, factor: fence `WhatwgTest/Audit/AxiomGate.lean`,
   `WhatwgGates/Trust/*.lean` (new), `WhatwgGates/TrustConfig.lean` (new),
   `WhatwgGates.lean`, `WhatwgGates/AGENTS.md`, `WhatwgTest/AGENTS.md`.
   Exit: step 1's cutover proof, the nine retargeted rows green again; the
   executable columns stay red.
3. Builder B2, executable: fence `whatwgbin/TrustGate.lean` (new),
   `WhatwgGates/Trust/{Load,Main}.lean`, `lakefile.toml` (one
   `[[lean_exe]]`), `.github/workflows/ci.yml`. Exit: every V2d row green;
   the executable's report equals the summary line on the unmodified tree.
4. Independent reviewer checks: the executable imports with `loadExts :=
   false` and never calls `enableInitializersExecution` or `evalConst`; it
   declares nothing `unsafe` or `partial`; its root's import closure holds
   no audited module but the config; the counts and the per-declaration
   axiom sets agree with `Lean.collectAxioms` (rerun appendix B's
   comparison); the rebuilt token table equals the loaded one; freshness
   and options checks fail closed; V2d's claim scope says what stays
   lexical, what stays with `leanchecker` and what stays trusted.

Part A's slices are the two breaker packets of 3.6, after the ruling, each
followed by its builder; the P11 builder depends on D52's resolution only
for the pin's durability, not for the code.

Dependencies on W6 to W9: W6 and W7 share the loader (4.9) and add their own
executables beside this one; whichever lands first owns `Load`. W9's
`WhatwgEffects` library is audited automatically under the `Whatwg` tree and
adds a strict prefix through the config module's list. W8 has no gate
dependency.

## 7. Decisions

For the coordinator:

1. P11 row. Options: P11-a, P11-b, P11-c (3.2). Recommend P11-a. Cost of a:
   no simulation theorem, host evidence instead; of b: a second IR and an
   authored TypeScript semantics; of c: no target exists.
2. P12 row. Options: P12-a, P12-b, P12-c (3.4). Recommend P12-a. Cost of a:
   W9 must land first; of b: nothing for lean4-effect4 to sum; of c: an
   ownerless open row.
3. The executable gate as the first in-repository step (W10-G, addendum
   V2d). Options: now; after W6 and W7 land their loaders; not at all.
   Recommend now. Cost: one breaker and two builder slices; not doing it
   leaves D56's first item to the self-test alone.
4. The in-tree command. Options: keep both on one library; retire after one
   lane; command only (4.3). Recommend keep both, then rule retirement on
   evidence. Cost: the V2c.5 linters stay for a lane.
5. Registration rule by extension allowlist in the executable. Options:
   adopt (51 named extensions with reasons; a toolchain bump reviews the
   list); keep the six-kind denylist. Recommend adopt. Cost: list
   maintenance per toolchain.
6. Required options from Lake traces (`-DwarningAsError=true` on every
   audited module, no `debug.*` option) and no `weakLeanArgs` in
   `lakefile.toml`, which Lake keeps out of traces. Options: adopt; record
   only. Recommend adopt; it closes D51 for every option Lake traces. Cost:
   none measured.
7. D53. Options: resolve by rule (4.5); rename `Gates.*` to `WhatwgGates.*`
   now. Recommend by rule. Cost of renaming: 114 `#check` lines, four
   generated modules and their digest pins under a ruling naming the change.
8. Where the lists live. Options: a data module `WhatwgGates/TrustConfig.lean`
   (nine rows retarget their file); keep them in
   `WhatwgTest/Audit/AxiomGate.lean` (the executable would then link a
   metaprogramming module). Recommend the data module.
9. The shared loader of W6, W7 and W10. Options: one module owned by the
   first to land; one per executable. Recommend one module.

For the operator:

1. Create `pure-algebra/lean4-trustgate` (name: package `trustgate`, library
   `TrustGate`). Options: create after step 2 lands here; never (each
   repository keeps its gate; this one carries the executable). Recommend
   after step 2. Cost: one repository, its CI and a tag; not creating it
   leaves four drifting copies.
2. History. Options: `git filter-repo` of `WhatwgGates/Trust/**` and the
   gate's history (HP-3's precedent); a fresh copy with a provenance pin.
   Recommend filter-repo. Cost: one operation, then a push.
3. Dependency shape for zero-dependency packages (lean4-hash,
   lean4-effects). Options: `[[require]] trustgate` (every downstream clones
   one small package; Lake builds it only where imported; pins move in
   step); the gate run in CI from a pinned checkout with a data-file config
   (a parser joins the trusted code, pins leave the manifest); those two
   keep their own gates. Recommend the require, ruled as a test-only
   dependency in their routers. Cost as listed.
4. Order of consumers after this repository. Recommend lean4-hash (gains
   most, loses nothing), lean4-effects (`warningAsError` first), then
   lean4-effect4 (layering rules and exact admission lists).
5. The `typescript` pin (D52). Options: tag `6afc9b8` upstream as `v0.6.0`;
   move every consumer to a tagged commit; keep the branch pin. Recommend
   the tag. Also: the local checkout of lean4-typescript is on a diverged
   branch and lacks the pinned commit, so a local build of the pin needs a
   fetch.
6. The compiler pin of the P11 harness. Options: share lean4-effect4's
   `harness/schema-host` pins; own pins under `harness/`. Recommend own pins
   recorded in `docs/PROVENANCE.md`, equal to lean4-effect4's at first.

This seat pushed nothing and wrote nothing outside its worktree; every push
and every change to another repository above is the operator's.

## 8. Not checked

- No WPT run, no TypeScript compiler run, no Node or Bun run; Part A's host
  claims are design, not observation.
- The prototype runs the axiom pass and the tokenizer, and measures the
  inputs of the other passes: the attribute reads of the environment pass,
  registrations by count, the token table, freshness, options and the
  extension inventory. It does not run the environment refusals, rule 1's
  per-module attribution, hygiene, the configuration shape, the root rule or
  the closures as passes; those are the in-tree code over inputs 2.5 shows
  identical, and no planted violation was put to the prototype.
- Of the executable-only plants of section 5, only the V2c.7 residual was
  built (against `lake build` and the prototype's raw reads); the others
  were not planted.
- lean4-effect4, lean4-hash and lean4-effects were read, not built; the
  matrix rests on a helper's reading (`[S]`) spot-checked on their lakefiles,
  CI files and lean4-effect4's design documents.
- Whether a `-D` option in `weakLeanArgs` is overridden by a traced one
  (Lake passes weak arguments first); the gate design refuses them instead.
- Whether `lake exe` or a driver can be made to build the audited libraries
  first; whether Lake resolves one `trustgate` version when two required
  packages pin different commits.
- The cost of the executable column in the self-test (about 81 extra runs of
  4 s each, `[H]`).
- `git ls-remote` against lean4-typescript was run by a helper; no tag was
  created anywhere.

## Appendix A: proposed text

### `PLAN.md`, phase table rows P11 and P12

```text
| P11 — targets | the closed combinator alphabet as first-order data; a lowering to `TypeScript.Module` of the pinned `typescript` package that emits the host's own WHATWG Streams API; an admitted-fragment predicate over that syntax; rendering through `TypeScript.Render.module` to UTF-8 bytes; a host harness that checks each rendered module with a pinned TypeScript compiler and runs it under the local host profiles | the lowering is total on admitted programs and decodes back to its program, and every rendered module is admitted (theorems); rendered bytes regenerate identically (drift gate); the pinned compiler accepts every rendered module and each host run's M1 observation equals the model's on the frozen corpus (host observations under named profiles); every alphabet constructor has a lowering case and a corpus case |
| P12 — bridges | the `Effects.Signature` face of the Streams calculi in the `WhatwgEffects` library beside the agent face, with its embedding in the calculus; the Node legacy streams calculus and its relation to the WHATWG calculus through `Readable.toWeb` and `Readable.fromWeb` | the face's handler run equals the calculus run under a named DB-04 mask (theorem); each Node direction names its loss under M1, with the Node profile's observations as host evidence; an embedding into an Effect Stream or Channel calculus opens only when lean4-effect4 lands one |
```

### `PLAN.md`, "Broad-before-deep representatives", items 8 and 9

```text
8. target: one program of the closed alphabet lowered to an admitted
   `TypeScript.Module`, rendered to bytes that regenerate identically,
   accepted by the pinned TypeScript compiler, and run on the Node profile
   with an M1 observation equal to the model's on one input;
9. bridge: one Node legacy stream related in both directions with its loss
   named, and one readable operation through the `Effects.Signature` face
   whose handler run equals the calculus step under M1.
```

### `docs/REIFICATION-STRATEGY.md`, section 5, replacement paragraph

```text
Stratum A lowers to TypeScript functions over Schema-typed values, or to a
pinned host body under RS-5. Stratum S lowers in this repository, from the
closed combinator alphabet, to the `typescript` package's first-order
syntax, emitting the host's own WHATWG Streams API (RS-5's host realizer with
a generated adapter); the TypeScript compiler at a pinned version and the
host profiles of DB-08 check what is emitted, as host observations under a
named mask. lean4-effect4 is not a lowering target: its `Eff` adds no stream
constructors (its DI-11), its Flow route is archived, and it has no Stream
or Channel calculus at `efcf1ae2`. Effect programs meet these streams
through Effect's own `Stream.fromReadableStream` and `toReadableStream` on
the host, observed in the same harness, and through the `Effects.Signature`
face (P12), which lean4-effect4 may sum with its own signatures. Stratum V
lowers as Schema where a consumer asks. lean4-effect4's design basis lists
typed lowering and simulation as pending; every Stratum S deliverable
inherits that until a fragment semantics is pinned.
```

## Appendix B: prototype source

`W10Proto.lean`, built with this temporary `lakefile.toml` entry and removed
afterwards. `lake exe w10_proto` prints every measurement of 2.5 except the
comparison, which `--compare` adds, and the extension names, which
`--extensions` adds. The table route's 1.6 s was measured by an earlier
revision with a `--tables` mode whose comparison `--compare` now makes.

```toml
[[lean_exe]]
name = "w10_proto"
root = "W10Proto"
supportInterpreter = true
```

```lean
import Lean
import Lake.Build.Trace

/-!
# W10 prototype: the trust gate as an executable over `.olean` files

Uncommitted prototype of the W10 design seat (review lane W). It imports the
built `.olean` files with `Lean.importModules (loadExts := false)`: no
environment-extension import hook and no initializer of the audited code
runs, and no parser descriptor is evaluated. It enumerates every constant by
the module `getModuleIdxFor?` records and runs the axiom pass with both
ceilings and the strict prefixes, collecting axioms by its own memoised
traversal rather than the per-module tables an audited module's own
elaboration wrote. Further modes rebuild the token table from raw parser
entries and tokenize every audited source, check each module's `.olean`
against the source hash and options Lake recorded, and list every
environment-extension entry an audited module records. `--compare` loads the
extensions a second time, which is `unsafe` and needs `supportInterpreter`,
only to compare its own results with `Lean.collectAxioms` and the loaded
token table; the default route needs neither.
-/

open Lean

namespace TrustGate

/-- A ceiling: the axioms a declaration may reach. -/
structure Ceiling where
  label : String
  axioms : List Name

/-- An exact admission of one declaration past the strict ceiling. -/
structure StrictException where
  declaration : Name
  reason : String

/-- Per-repository data the shared library reads; nothing here is code. -/
structure Config where
  /-- Modules imported to build the audited environment. -/
  roots : Array Name
  /-- Audited module trees, disjoint under `Name.isPrefixOf`. -/
  trees : List Name
  /-- The ceiling every audited tree is under. -/
  ceiling : Ceiling
  /-- The narrower ceiling under `strictPrefixes`. -/
  strictCeiling : Ceiling
  strictPrefixes : List Name
  strictExceptions : List StrictException
  /-- Axioms no audited constant may reach. -/
  forbiddenAxioms : List Name

/-- One constant of an audited module. -/
structure AuditedDeclaration where
  name : Name
  moduleName : Name
  tree : Name

def treeOf? (config : Config) (moduleName : Name) : Option Name :=
  config.trees.find? (·.isPrefixOf moduleName)

/-- Every constant of every audited module, attributed to the module
`getModuleIdxFor?` records, exactly as the in-tree gate reads them. -/
def auditedDeclarations (config : Config) (environment : Environment) :
    Except String (Array AuditedDeclaration) := do
  let header := environment.header
  if header.moduleNames.size != header.moduleData.size then
    throw s!"trust gate: {header.moduleNames.size} module names, \
      {header.moduleData.size} module data entries"
  let mut found : Array AuditedDeclaration := #[]
  for index in [0:header.moduleNames.size] do
    let some moduleName := header.moduleNames[index]?
      | throw s!"trust gate: module index {index} has no name"
    let some tree := treeOf? config moduleName | continue
    let some data := header.moduleData[index]?
      | throw s!"trust gate: module {moduleName} has no data"
    for name in data.constNames do
      if (environment.getModuleIdxFor? name).map (·.toNat) == some index then
        found := found.push { name, moduleName, tree }
  return found

/-- The constants a constant's kernel declaration mentions, in the order
`Lean.CollectAxioms.collect` visits them at v4.33.1. -/
def dependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- One frame of the traversal: a constant, the dependencies still to visit,
and the axioms found so far. -/
structure Frame where
  name : Name
  pending : List Name
  found : NameSet

/-- Every constant whose closure is finished, with its sorted axioms. A
constant on the stack holds the sentinel `#[]`, as in `Lean.CollectAxioms`. -/
abbrev AxiomMemo := Std.HashMap Name (Array Name)

def mergeInto (set : NameSet) (axioms : Array Name) : NameSet :=
  axioms.foldl (init := set) fun acc name => acc.insert name

/-- Axioms `root` reaches, extending `memo`. An explicit stack bounded by
`fuel` steps replaces recursion, so the function is total; exhausted fuel is
an error, never a silent answer. -/
def axiomsOf (environment : Environment) (fuel : Nat) (memo : AxiomMemo)
    (root : Name) : Except String (Array Name × AxiomMemo) := Id.run do
  if let some known := memo[root]? then
    return .ok (known, memo)
  let start (memo : AxiomMemo) (name : Name) : Option Frame × AxiomMemo :=
    match environment.find? name with
    | none => (none, memo.insert name #[])
    | some info =>
        let found : NameSet :=
          if info matches .axiomInfo _ then ({} : NameSet).insert name else {}
        (some { name, pending := (dependencies info).toList, found },
          memo.insert name #[])
  let (first?, memo0) := start memo root
  let some first := first? | return .ok (#[], memo0)
  let mut memo := memo0
  let mut stack : Array Frame := #[first]
  for _ in [0:fuel] do
    let some top := stack.back? | break
    match top.pending with
    | [] =>
        let result := top.found.toArray.qsort Name.lt
        memo := memo.insert top.name result
        stack := stack.pop
        match stack.back? with
        | none => return .ok (result, memo)
        | some parent =>
            stack := stack.pop.push
              { parent with found := mergeInto parent.found result }
    | next :: rest =>
        stack := stack.pop.push { top with pending := rest }
        match memo[next]? with
        | some known =>
            let some current := stack.back? | return .error "trust gate: empty stack"
            stack := stack.pop.push
              { current with found := mergeInto current.found known }
        | none =>
            let (frame?, memo') := start memo next
            memo := memo'
            if let some frame := frame? then
              stack := stack.push frame
  return .error s!"trust gate: axiom traversal of {root} exhausted {fuel} steps"

/-- The longest strict prefix a module is under. -/
def strictPrefixOf? (config : Config) (moduleName : Name) : Option Name :=
  config.strictPrefixes.foldl (init := none) fun best candidate =>
    if candidate.isPrefixOf moduleName then
      match best with
      | some current =>
          if current.getNumParts < candidate.getNumParts then some candidate else best
      | none => some candidate
    else best

/-- The verdict of the axiom pass. -/
structure AxiomReport where
  findings : Array String := #[]
  /-- Per tree: declarations reaching an axiom the strict ceiling drops, and
  declarations. -/
  perTree : List (Name × Nat × Nat) := []
  declarations : Nat := 0

/-- The axiom pass over audited declarations, given each one's axioms. -/
def axiomPass (config : Config) (declarations : Array AuditedDeclaration)
    (axiomsOfDecl : AuditedDeclaration → Array Name) : AxiomReport := Id.run do
  let dropped := config.ceiling.axioms.filter (!config.strictCeiling.axioms.contains ·)
  let excepted := config.strictExceptions.map (·.declaration)
  let mut findings : Array String := #[]
  let mut perTree : Std.HashMap Name (Nat × Nat) := {}
  for declaration in declarations do
    let axioms := axiomsOfDecl declaration
    let (reached, total) := perTree.getD declaration.tree (0, 0)
    let reaches := dropped.any axioms.contains
    perTree := perTree.insert declaration.tree
      (if reaches then reached + 1 else reached, total + 1)
    for axiomName in axioms do
      let name := declaration.name
      if axiomName.anyS (· == "_native") then
        findings := findings.push
          s!"declaration {name} reaches forbidden axiom {axiomName} (native_decide auxiliary)"
      else if config.forbiddenAxioms.contains axiomName then
        findings := findings.push s!"declaration {name} reaches forbidden axiom {axiomName}"
      else if !config.ceiling.axioms.contains axiomName then
        findings := findings.push s!"declaration {name} reaches unexpected axiom {axiomName}"
      else if !config.strictCeiling.axioms.contains axiomName then
        if let some strictPrefix := strictPrefixOf? config declaration.moduleName then
          if !excepted.contains name then
            findings := findings.push
              s!"declaration {name} reaches {axiomName} under the strict ceiling of \
                {strictPrefix}, and no exact exception names it"
  let perTreeList := config.trees.map fun tree => (tree, perTree.getD tree (0, 0))
  return { findings, perTree := perTreeList, declarations := declarations.size }

/-- The final token table, rebuilt from the `lean` binary's builtin table and
every module's raw global `.token` parser entries, with no parser evaluated
and no extension loaded. -/
def tokenTableFromEntries (environment : Environment) : IO Parser.TokenTable := do
  let mut table ← Parser.builtinTokenTable.get
  for index in [0:environment.header.moduleNames.size] do
    for entry in Parser.parserExtension.ext.getModuleEntries environment index do
      match entry with
      | .global (.token token) => table := table.insert token token
      | _ => pure ()
  return Parser.Module.updateTokens table

/-- One-based position of a token. -/
structure Position where
  line : Nat
  column : Nat

/-- Lean's tokenizer over one source, folding `step` over every token of code;
the rounds and parsers of the in-tree gate's `foldCodeTokens`. -/
def foldCodeTokens {σ : Type} (environment : Environment) (tokenTable : Parser.TokenTable)
    (fileName input : String) (init : σ) (step : σ → Syntax → Position → σ) :
    σ × Option String := Id.run do
  let inputContext := Parser.mkInputContext input fileName
  let parserContext : Parser.ParserModuleContext := { env := environment, options := {} }
  let fail (pos : String.Pos.Raw) (reason : String) : String :=
    let position := inputContext.fileMap.toPosition pos
    s!"tokenization failed in {fileName}:{position.line}:{position.column + 1}: {reason}"
  let mut folded := init
  let mut state := Parser.mkParserState input
  let mut projectionEnd : Option String.Pos.Raw := none
  let rounds := input.utf8ByteSize + 1
  for _ in [0:rounds] do
    let skipped := Parser.whitespace.run inputContext parserContext tokenTable state
    if let some error := skipped.errorMsg then
      return (folded, some (fail state.pos (toString error)))
    state := skipped
    if inputContext.atEnd state.pos then
      return (folded, none)
    let start := state.pos
    let docComment := Parser.Command.docComment.fn.run inputContext parserContext tokenTable state
    if docComment.errorMsg.isNone then
      state := docComment.popSyntax
      projectionEnd := none
    else
      let moduleDoc := Parser.Command.moduleDoc.fn.run inputContext parserContext tokenTable state
      if moduleDoc.errorMsg.isNone then
        state := moduleDoc.popSyntax
        projectionEnd := none
      else
        let tokenParser :=
          if projectionEnd == some state.pos && (inputContext.get state.pos).isDigit then
            Parser.fieldIdxFn
          else
            Parser.tokenFn []
        let next := tokenParser.run inputContext parserContext tokenTable state
        if let some error := next.errorMsg then
          return (folded, some (fail state.pos (toString error)))
        let token := next.stxStack.back
        let position := inputContext.fileMap.toPosition start
        folded := step folded token { line := position.line, column := position.column + 1 }
        projectionEnd :=
          if token.isToken "." || token.isToken "|>." then token.getTailPos? else none
        state := next.popSyntax
    unless start.byteIdx < state.pos.byteIdx do
      return (folded, some (fail start "the tokenizer consumed nothing"))
  return (folded, some (fail state.pos s!"the scan did not end within {rounds} rounds"))

/-- Freshness and options of one module, read from the `.trace` Lake wrote:
whether the source's hash, computed as Lake computes it, is the one recorded,
and the `-D` options recorded. -/
def traceOf (buildRoot sourceRoot : System.FilePath) (moduleName : Name) :
    IO (Bool × Array String) := do
  let source := Lean.modToFilePath sourceRoot moduleName "lean"
  let trace := Lean.modToFilePath buildRoot moduleName "trace"
  let hash ← Lake.computeTextFileHash source
  let text ← IO.FS.readFile trace
  let fresh := (text.splitOn s!"\"{hash.toString}\"").length > 1
  let mut options : Array String := #[]
  for line in text.splitOn "\n" do
    if (line.splitOn "\"-D").length > 1 then
      options := options.push
        ("-D" ++ (((line.splitOn "\"-D").getD 1 "").splitOn "\"").headD "")
  return (fresh, options)

/-- `MonadEnv` over a plain state, for `Lean.collectAxioms` in comparison mode. -/
abbrev EnvM := StateM Environment

instance : MonadEnv EnvM where
  getEnv := get
  modifyEnv := modify

end TrustGate

open TrustGate

/-- This repository's data, as `WhatwgTest/Audit/AxiomGate.lean` holds it at
`97a8715`. -/
def whatwgConfig : Config where
  roots := #[`WhatwgTest]
  trees := [`Whatwg, `WhatwgTest, `WhatwgGates]
  ceiling := ⟨"R-11", [``propext, ``Quot.sound, ``Classical.choice]⟩
  strictCeiling := ⟨"R-V1", [``propext, ``Quot.sound]⟩
  strictPrefixes :=
    [`Whatwg.Ecma262, `Whatwg.WebIdl, `Whatwg.Url, `Whatwg.Infra.Text.Utf8, `Whatwg.Streams]
  strictExceptions := []
  forbiddenAxioms := [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- Token, parser, command-elaborator and initializer entries that audited
modules record, read from raw module entries. -/
def registrationCounts (config : Config) (environment : Environment) :
    Nat × Nat × Nat × Nat := Id.run do
  let mut tokens := 0
  let mut parsers := 0
  let mut commandElaborators := 0
  let mut initializers := 0
  for index in [0:environment.header.moduleNames.size] do
    let some moduleName := environment.header.moduleNames[index]? | continue
    if (treeOf? config moduleName).isNone then continue
    for entry in Parser.parserExtension.ext.getModuleEntries environment index do
      match entry with
      | .global (.token _) | .scoped _ (.token _) => tokens := tokens + 1
      | .global (.parser ..) | .scoped _ (.parser ..) => parsers := parsers + 1
      | _ => pure ()
    commandElaborators := commandElaborators +
      (Elab.Command.commandElabAttribute.ext.ext.getModuleEntries environment index).size
    initializers := initializers +
      (regularInitAttr.ext.getModuleEntries environment index).size +
      (regularInitAttr.ext.getModuleIREntries environment index).size
  return (tokens, parsers, commandElaborators, initializers)

/-- The environment pass's attribute reads over every constant of the
environment (Lean's own included): `@[extern]`, `@[implemented_by]`, declared
axioms, and `unsafe` or `partial` constants. Parametric attributes answer
for an imported declaration from its module's raw entries, so the counts
must not depend on whether extensions were loaded. -/
def environmentCounts (environment : Environment) : Nat × Nat × Nat × Nat := Id.run do
  let mut externs := 0
  let mut implemented := 0
  let mut axioms := 0
  let mut unsafeOrPartial := 0
  for (name, info) in environment.constants.map₁.toList do
    if isExtern environment name then externs := externs + 1
    if (Compiler.getImplementedBy? environment name).isSome then implemented := implemented + 1
    if info matches .axiomInfo _ then axioms := axioms + 1
    if info.isUnsafe || info.isPartial then unsafeOrPartial := unsafeOrPartial + 1
  return (externs, implemented, axioms, unsafeOrPartial)
/-- Measurement only: load the extensions, which runs the imported modules'
initializers, and compare with `Lean.collectAxioms` and the loaded token table. -/
unsafe def compareWithLoadedExtensions (config : Config) (imports : Array Import)
    (declarations : Array AuditedDeclaration) (own : Std.HashMap Name (Array Name))
    (rebuilt : Parser.TokenTable) : IO Unit := do
  enableInitializersExecution
  let loaded ← importModules imports {} (loadExts := true)
  let mut mismatches : Nat := 0
  for declaration in declarations do
    let fromTables := (collectAxioms declaration.name : EnvM (Array Name)).run' loaded
    if fromTables.qsort Name.lt != own.getD declaration.name #[] then
      mismatches := mismatches + 1
  IO.println s!"compare: {mismatches} of {declarations.size} declarations differ \
    between the own traversal and Lean.collectAxioms over the loaded module tables"
  let loadedTable := Parser.Module.updateTokens (Parser.getTokenTable loaded)
  let rebuiltSet : Std.HashSet String := rebuilt.values.foldl (·.insert ·) {}
  let loadedSet : Std.HashSet String := loadedTable.values.foldl (·.insert ·) {}
  let onlyRebuilt := rebuiltSet.toArray.filter (!loadedSet.contains ·)
  let onlyLoaded := loadedSet.toArray.filter (!rebuiltSet.contains ·)
  IO.println s!"compare: token table rebuilt from raw entries {rebuiltSet.size} tokens, \
    loaded {loadedSet.size}; only rebuilt {onlyRebuilt.size}, only loaded {onlyLoaded.size}"
  let (externs, implemented, axioms, unsafeOrPartial) := environmentCounts loaded
  IO.println s!"compare: with extensions loaded, over every constant: {externs} extern, \
    {implemented} implemented_by, {axioms} axioms, {unsafeOrPartial} unsafe or partial"
  let (tokens, parsers, commandElaborators, initializers) := registrationCounts config loaded
  IO.println s!"compare: with extensions loaded, {tokens} token, {parsers} parser, \
    {commandElaborators} command-elaborator, {initializers} initializer entries"

unsafe def main (args : List String) : IO UInt32 := do
  let started ← IO.monoMsNow
  initSearchPath (← findSysroot)
  let config := whatwgConfig
  let imports := config.roots.map fun module => ({ module } : Import)
  let environment ← importModules imports {} (loadExts := false)
  let loaded ← IO.monoMsNow
  let declarations ← match auditedDeclarations config environment with
    | .ok found => pure found
    | .error message => IO.eprintln message; return 2
  let mut memo : AxiomMemo := {}
  let mut axiomTable : Std.HashMap Name (Array Name) := {}
  for declaration in declarations do
    match axiomsOf environment 100000000 memo declaration.name with
    | .ok (axioms, memo') =>
        memo := memo'
        axiomTable := axiomTable.insert declaration.name axioms
    | .error message => IO.eprintln message; return 2
  let collected ← IO.monoMsNow
  let table := axiomTable
  let report := axiomPass config declarations fun d => table.getD d.name #[]
  for finding in report.findings do
    IO.eprintln s!"FAIL {finding}"
  let trees := ", ".intercalate (report.perTree.map fun (tree, reached, total) =>
    s!"{reached} of {total} in {tree}")
  IO.println s!"{if report.findings.isEmpty then "PASS" else "FAIL"} axiom pass: \
    {report.declarations} declarations of {environment.header.moduleNames.size} \
    environment modules ({memo.size} constants traversed); Classical.choice is reached \
    by {trees}; {config.strictPrefixes.length} strict prefix(es); \
    {report.findings.size} finding(s)"
  IO.println s!"timing ms: import {loaded - started}, axioms {collected - loaded}"
  let root ← IO.currentDir
  let audited := environment.header.moduleNames.filter (treeOf? config · |>.isSome)
  -- Raw registrations of audited modules, no extension loaded.
  let (tokens, parsers, commandElaborators, initializers) :=
    registrationCounts config environment
  IO.println s!"raw registrations in audited modules: {tokens} token, {parsers} parser, \
    {commandElaborators} command-elaborator, {initializers} initializer entries"
  let (externs, implemented, axioms, unsafeOrPartial) := environmentCounts environment
  IO.println s!"environment reads, extensions not loaded, over every constant: {externs} \
    extern, {implemented} implemented_by, {axioms} axioms, {unsafeOrPartial} unsafe or partial"
  -- The source passes' input.
  let tokenTable ← tokenTableFromEntries environment
  let isLean (path : System.FilePath) : Bool :=
    path.extension.map (·.toLower) == some "lean"
  let mut sources : Array System.FilePath :=
    #[root / "Whatwg.lean", root / "WhatwgGates.lean", root / "WhatwgTest.lean"]
  for directory in ["Whatwg", "WhatwgTest", "WhatwgGates", "whatwgbin"] do
    sources := sources ++ ((← (root / directory).walkDir).filter isLean)
  let scanStarted ← IO.monoMsNow
  let mut counts : Nat × Nat × Nat × Nat := (0, 0, 0, 0)
  let mut failures : Array String := #[]
  for source in sources do
    let input ← IO.FS.readFile source
    let (found, failure?) :=
      foldCodeTokens environment tokenTable source.toString input counts
        fun (all, guards, configs, runCmds) token _ =>
          let guards := if token.isToken "#guard" then guards + 1 else guards
          let configs := match token with
            | .ident _ _ name _ => if name == `config then configs + 1 else configs
            | _ => configs
          let runCmds := if token.isToken "run_cmd" then runCmds + 1 else runCmds
          (all + 1, guards, configs, runCmds)
    counts := found
    if let some failure := failure? then failures := failures.push failure
  let scanEnded ← IO.monoMsNow
  let (all, guards, configs, runCmds) := counts
  IO.println s!"token scan: {sources.size} sources, {all} tokens of code, \
    {failures.size} tokenization failure(s); `#guard` {guards}, identifier `config` \
    {configs}, `run_cmd` {runCmds}; {scanEnded - scanStarted} ms"
  -- Freshness and recorded options.
  let buildRoot := root / ".lake" / "build" / "lib" / "lean"
  let mut fresh := 0
  let mut stale : Array Name := #[]
  let mut options : Std.HashMap String Nat := {}
  for moduleName in audited do
    let (isFresh, recorded) ← traceOf buildRoot root moduleName
    if isFresh then fresh := fresh + 1 else stale := stale.push moduleName
    for option in recorded do
      options := options.insert option (options.getD option 0 + 1)
  IO.println s!"freshness: {fresh} of {audited.size} audited modules match the source \
    hash their trace records; stale {stale.toList}; options {options.toList}"
  -- Every extension with entries in an audited module, by name, from `ModuleData`.
  let mut byExtension : Std.HashMap Name Nat := {}
  for index in [0:environment.header.moduleNames.size] do
    let some moduleName := environment.header.moduleNames[index]? | continue
    if (treeOf? config moduleName).isNone then continue
    let some data := environment.header.moduleData[index]? | continue
    for (extensionName, entries) in data.entries do
      if entries.size > 0 then
        byExtension := byExtension.insert extensionName
          (byExtension.getD extensionName 0 + entries.size)
  IO.println s!"extensions with entries in audited modules: {byExtension.size}"
  if args.contains "--extensions" then
    for (name, count) in byExtension.toArray.qsort (·.1.toString < ·.1.toString) do
      IO.println s!"  {name} {count}"
  if args.contains "--compare" then
    compareWithLoadedExtensions config imports declarations axiomTable tokenTable
  return if report.findings.isEmpty && failures.isEmpty && stale.isEmpty then 0 else 1
```

The plant of the V2c.7 measurement, `WhatwgTest/W10Plant.lean`, with the
line `import WhatwgTest.W10Plant` put first in `WhatwgTest.lean`; both were
removed and the tree rebuilt to the base's gate line afterwards:

```lean
-- W10 design seat, uncommitted measurement: the residual of contract V2c.7.
-- An initializer removes the gate module's two post-command linters, and a
-- macro replaces the gate command, so no pass runs.
import WhatwgTest.Audit.AxiomGate

open Lean Elab Command

initialize
  lintersRef.modify fun linters =>
    linters.filter (·.name != `WhatwgTest.Audit.rootGateCommandCheck)
  moduleLintersRef.modify fun linters =>
    linters.filter (·.name != `WhatwgTest.Audit.rootCommandsCheck)

macro_rules | `(#whatwg_streams_axiom_gate) => `(#check 1)
```