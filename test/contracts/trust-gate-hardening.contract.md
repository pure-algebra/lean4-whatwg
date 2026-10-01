# Trust-gate hardening contract (review lane V, slice V2)

Status: FROZEN / RED, V2 trust-gate breaker seat, 2026-09-30, on branch
`review/v2-gate-breaker`, based on
`325d5d5` (the commit that lands rulings R-V0 to R-V5).

Authority: rulings R-V1 (strict ceiling by module prefix) and R-V2 (gate
hardening, breaker first) at the end of `COORDINATION.md`. Evidence:
`docs/research/2026-09-30-implementation-review.md`, sections "A
`native_decide` inside an `example` is not rejected", "A narrow run of the
gate fails" and "The trust gate".

This packet freezes behaviour, not code. The subject is the command
`#whatwg_streams_axiom_gate` in `WhatwgTest/Audit/AxiomGate.lean`, run last by
the test root `WhatwgTest.lean`, together with the root search of
`WhatwgTest/Audit/SpecCoverage.lean`. The executable falsifiers are the plant
rows whose labels begin `V2-` in `Gates/TrustSelfTest.lean`, run by
`lake exe trustselftest`, and the fixtures they name under
`test/fixtures/trust-gate/`.

## 1. Files and fences

Breaker-owned and frozen by this packet:

- this file;
- the fixtures `test/fixtures/trust-gate/{env,token,strict,benign-trust}-*.lean.txt`
  listed in section 9;
- in `Gates/TrustSelfTest.lean`: the rows of `acceptancePlants` and
  `rejectionPlants` whose labels begin `V2-`, the selectors
  `toolingPlantModule`, `strictPlantModule`, `testPlantModule` and
  `binEntryPoint`, the anchors `strictExceptionAnchor` and
  `tokenExemptionAnchor`, `gateSummaryTemplate`, `narrowRuns`, and the
  mechanism they use (`Placement`, `Edit`, `withEdits`, `checkPlant`,
  `templateMatches`, `expectNarrowRun`).

The builder implements in its claimed fence (R-V2, `COORDINATION.md` claims
table): `WhatwgTest/Audit/AxiomGate.lean`, the root search of
`WhatwgTest/Audit/SpecCoverage.lean`, `.github/workflows/ci.yml`,
`Gates/AGENTS.md` and `WhatwgTest/AGENTS.md`. The builder edits none of the
files above. A row that cannot be satisfied as frozen is reported to the
coordinator, not repaired by the builder.

The plants are not registered in `test/counterexamples/REGISTER.md`. That
register's `README.md` keeps "negative fixtures and implementation mutants"
apart "because they attack gates rather than semantic statements", and no
existing trust-gate plant has a register row. The `V2-` labels are this
packet's stable identifiers; they are never reused.

## 2. Terms

- *Audited tree*: the modules whose name has `Whatwg`, `WhatwgTest` or `Gates`
  as a prefix under `Lean.Name.isPrefixOf`, which compares whole components:
  `Whatwg` is a prefix of `Whatwg.Url` and of `Whatwg` itself, and not of
  `WhatwgTest.Url`.
- *Audited source*: every `.lean` file under `Whatwg/`, `WhatwgTest/`, `Gates/`
  and `bin/`, and the three roots `Whatwg.lean`, `Gates.lean`,
  `WhatwgTest.lean`.
- *Environment pass*: the loop over every constant of an audited module.
- *Axiom pass*: the loop that calls `Lean.collectAxioms` on those constants and
  applies a ceiling.
- *Modifier pass*: the existing token check for the `unsafe` and `partial`
  keywords.
- *Trust-token pass*: the token check this packet adds (section 4).
- *Code*: every token of an audited source except comments, documentation
  comments, module documentation, and literals (string in every form, raw
  string, interpolated string, character, numeric, and name literals such as
  `` `Lean.ofReduceBool `` and ``` ``Lean.ofReduceBool ```).
- A diagnostic template below writes `<d>` for a declaration name, `<m>` for a
  module name, `<p>` for a strict prefix, `<path>` for a source path, `<word>`
  for a refused word and `<n>` for a decimal numeral. Names are printed as
  Lean prints a `Name` in a message.

## 3. Gate order

Every check of R-V1 and R-V2 is an elaboration-time check of the same command.
The observable requirement is the plant table of section 9: each plant's
fragment appears in the failing build's output. Two existing plants fix the
order for a gate that stops at its first finding:

- `native-decide.lean.txt` (unchanged) is a `theorem` proved by
  `native_decide`. It contains the token `native_decide` and also leaves the
  auxiliary axiom `…._native.native_decide.ax_1_1` in the environment. It must
  still print `(native_decide auxiliary)`.
- `partial.lean.txt` and `unsafe.lean.txt` (unchanged) must still print the
  modifier pass's message, ahead of the environment pass's
  "declaration … is partial".

Plants V2-E2 and V2-E5 likewise carry a refused token (`axiom`,
`«implemented_by»`) and must print the environment pass's message. A gate that
stops at its first finding therefore runs, in this order:

1. module closure (unchanged; `bin/` excluded, section 5);
2. the modifier pass (unchanged);
3. the environment pass (section 4.1);
4. the axiom pass with both ceilings, and the strict-exception checks
   (section 6);
5. the trust-token pass and the exemption checks (sections 4.2 and 4.3);
6. the summary line (section 7).

A gate that collects every finding and reports them together satisfies the
rows in any order.

## 4. Refusals of R-V2

### 4.1 Environment pass, in every audited tree

For every constant of an audited module, other than a generated safe
recursor (the existing `isGeneratedSafeRecursor` exception):

| Condition | Diagnostic template (verbatim) |
| --- | --- |
| it is an axiom (`ConstantInfo.axiomInfo`) and its name has a component `_native` | must contain `(native_decide auxiliary)`, for example `Whatwg trust gate: declaration <d> is a native-evaluation axiom (native_decide auxiliary)` |
| it is any other axiom | `Whatwg trust gate: declaration <d> is an axiom; no audited tree declares one` |
| `Lean.isExtern` holds for it | ``Whatwg trust gate: declaration <d> is `@[extern]`; host code replaces its checked body`` |
| `Lean.Compiler.getImplementedBy?` returns a value for it | ``Whatwg trust gate: declaration <d> is `@[implemented_by]`; another declaration replaces its checked body in compiled code`` |
| it is an `opaque` whose value, after stripping leading `fun` binders, has head constant `Inhabited.default` or `Classical.ofNonempty` | ``Whatwg trust gate: declaration <d> is an `opaque` with no authored body; Lean synthesised its value, so it denotes an inhabitant nobody chose`` |

The first row exists because Lean 4.33.1 records a `native_decide` proof of a
named declaration as a declared auxiliary axiom (measured at the base:
`theorem t : (2 : Nat) + 2 = 4 := by native_decide` leaves the axiom
`t._native.native_decide.ax_1_1`, and `#print axioms t` names it; the current
gate's comment says `bv_decide` does the same), and the existing plant's
fragment is unchanged (section 8). An `opaque` with an authored body is
admitted (plant V2-A2); an authored body that is literally `default` is
refused with the bodyless ones, by design.

### 4.2 Trust-token pass, in every audited source

The pass refuses a token of code that carries a refused word. A token carries
word `w` when it is

- an atom (a keyword) whose text is `w`; or
- an identifier whose `Name`, with `«»` escapes removed, equals `w`; or, for
  the three forbidden axioms only, an identifier whose `Name`'s last component
  is the short name.

| Refused word, printed as | Spellings refused | Channel |
| --- | --- | --- |
| `native_decide` | `native_decide` | compiler evaluation; no constant inside an `example` |
| `bv_decide` | `bv_decide` | the same, through an LRAT check |
| `bv_decide?` | `bv_decide?` | runs `bv_decide` (breaker addition: same channel) |
| `bv_check` | `bv_check` | replays an LRAT certificate the same way (breaker addition) |
| `native` | the identifier `native` in any position: `decide +native`, `decide (native := true)`, `{ native := true }`, `-native` | the native configuration flag in all its spellings |
| `sorry` | `sorry`, `«sorry»` | an admitted goal; inside an `example` with `warningAsError` off, nothing records it |
| `axiom` | `axiom`, `«axiom»` | an assumption |
| `implemented_by` | `implemented_by`, `«implemented_by»` | replaces a checked body |
| `extern` | `extern`, `«extern»` | replaces a checked body with host code |
| `debug.skipKernelTC` | `debug.skipKernelTC`, `«debug».skipKernelTC` and every other escaping | a declaration the kernel never checks |
| `Lean.ofReduceBool` | `ofReduceBool` (short, under `open Lean`), `Lean.ofReduceBool`, `_root_.Lean.ofReduceBool`, and any identifier ending in the component `ofReduceBool` | a forbidden axiom |
| `Lean.ofReduceNat` | the same shapes for `ofReduceNat` | a forbidden axiom |
| `Lean.trustCompiler` | the same shapes for `trustCompiler` | a forbidden axiom |

Decisions frozen here:

- The short and qualified spellings of the three axiom names are refused
  alike, because both elaborate to the same constant; a longer name that merely
  ends in the component (`Foo.ofReduceBool`) is refused as well, at no cost to
  the tree.
- Every other word is refused only as a whole name: `Foo.native_decide`,
  `Foo.extern`, `Foo.native` and `Foo.debug.skipKernelTC` are names (plant
  V2-A1), because only the whole spelling resolves to the tactic, attribute,
  flag or option.
- An identifier that contains a refused word is a name: `axioms` (the
  `#print axioms` receipts), `externals`, `my_native_decide_note`,
  `partialSum` (plant V2-A1).
- `unsafe` and `partial` stay with the modifier pass, keyword-only, with its
  existing message; `«unsafe»` and `«partial»` remain names (`benign.lean.txt`,
  unchanged).

Diagnostic template (verbatim; nothing may stand between `<path>` and
` contains`, and text may follow `trust token`, such as a position):

```text
Whatwg source trust gate: <path> contains an authored `<word>` trust token
```

`<path>` is the audited source's path; the plants check its last component
(`Whatwg.lean`, `TrustSelfTestPlant.lean`, `TrustSelfTestToolingPlant.lean`,
`Citations.lean`). The pass may stop at the first refused token or report
every one.

### 4.3 Source-token exemption by exact module name

A module that must name a refused word in code is admitted to the trust-token
pass, and to no other check, by an exact entry in a list held as data in
`WhatwgTest/Audit/AxiomGate.lean`. An entry is the module's full `Name` and a
reason (section 10 fixes its source form). The modifier pass, the environment
pass and the axiom pass never exempt anything, and no file under `bin/` can be
exempted.

| Condition | Diagnostic template (verbatim) |
| --- | --- |
| an entry names a module with no audited source | `Whatwg source trust gate: source-token exemption names missing module <m>` |
| an entry names a module whose source carries no refused word in code | `Whatwg source trust gate: stale source-token exemption for <m>; its source contains no refused token` |

At this commit the list needs no entry (section 5). The gate source should
spell its word lists as string literals and its axiom names as name literals,
as it does today, so that it needs none.

## 5. `bin/` and the current tree

`bin/` joins the source passes, the modifier pass and the trust-token pass, and
nothing else. Its files are executable roots that no audit root imports: the
module-closure check does not apply to them, and the environment and axiom
passes cannot see their constants (section 13).

Measurement at the base, with the gate's own tokenizer, the gate's token table
and the rules of section 4.2, over the 222 audited sources including the six
under `bin/`:

| Finding | Where | Handling |
| --- | --- | --- |
| no refused word in code anywhere | all 222 files | the unmodified tree must be accepted as it is; no exemption entry is needed |
| identifier `axioms` (1,041 times, from `#print axioms`; twice as a local in `WhatwgTest/Audit/SpecCoverage.lean`) | test tree | a name, not `axiom`: accepted |
| keyword `run_cmd` | `WhatwgTest/Infra/IntegerConstructiveContract.lean`, `WhatwgTest/Infra/ScalarConstructiveContract.lean` | not refused by R-V2 |
| name literals ``` ``sorryAx ```, ``` ``Lean.ofReduceBool ```, ``` ``Lean.ofReduceNat ```, ``` ``Lean.trustCompiler ``` | the gate's `forbiddenAxioms` | literals: exempt |
| refused words inside strings | the gate, `Gates/TrustSelfTest.lean`, census batteries | literals: exempt |
| axiom, `opaque`, `@[extern]` or `@[implemented_by]` constants, authored or generated | none: measured over the compiled environment of `WhatwgTest.lean`, all 16,346 audited constants | the environment pass refuses nothing in the tree |

At the base the token table holds `sorry`, `axiom`, `unsafe` and `partial` as
keywords, and `native_decide`, `bv_decide`, `bv_decide?`, `bv_check`,
`extern`, `implemented_by` and `native` as identifiers; section 4.2 refuses
both shapes so that a change of grammar does not open a hole.

## 6. Strict ceiling of R-V1

- The strict list is data in `WhatwgTest/Audit/AxiomGate.lean`. At landing it
  contains `Whatwg.Ecma262`; the plants depend on that prefix. Which other
  prefixes join is the coordinator's measurement under R-V1.
- A declaration is under the strict ceiling when its module (from
  `Environment.getModuleIdxFor?`, not its name) has a strict prefix under
  `Name.isPrefixOf`. This covers authored, private, auxiliary and
  Lean-generated constants alike, and an equation lemma counts in the module
  that minted it.
- The strict ceiling admits `propext` and `Quot.sound`. A declaration under it
  that reaches `Classical.choice` is refused unless an exact exception names
  it. `WhatwgTest`, the tooling tree and every non-strict `Whatwg` module keep
  R-11 (`propext`, `Quot.sound`, `Classical.choice`). The forbidden axioms and
  the native auxiliaries are refused everywhere, as today.
- The former implementation ceiling, `auditImplementationModules` and their
  staleness check collapse into this structure (R-V1). No message of theirs is
  frozen.

| Condition | Diagnostic template (verbatim) |
| --- | --- |
| a strict declaration reaches `Classical.choice` and no exception names it | `Whatwg axiom gate: declaration <d> reaches Classical.choice under the strict ceiling of <p>, which admits propext and Quot.sound only, and no exact exception names it` |
| an exception names no declaration | `Whatwg axiom gate: strict-ceiling exception names missing declaration <d>` |
| an exception names a declaration whose module has no strict prefix | `Whatwg axiom gate: stale strict-ceiling exception for <d>; its module <m> is under no strict prefix` |
| an exception names a strict declaration that does not reach `Classical.choice` | `Whatwg axiom gate: stale strict-ceiling exception for <d>; it does not reach Classical.choice` |
| an exception's reason is empty after trimming ASCII whitespace | `Whatwg axiom gate: strict-ceiling exception for <d> carries no reason` |

`<p>` is the strict prefix that matched, the longest if several do. An entry
with a blank reason is reported by the last row: the gate does not instead
report its declaration by the first row (plant V2-S6). Exceptions are exact:
an excepted declaration's auxiliaries need entries of their own unless a later
ruling says otherwise. Private declarations may be excepted by owner module
and original name, as the current gate's private list does, under the same
four checks.

## 7. Summary line

A successful run logs exactly one line matching, with each `<n>` a decimal
numeral:

```text
Whatwg module and axiom gate: checked <n> source files and <n> declarations; Classical.choice is reached by <n> of <n> declarations in Whatwg, <n> of <n> in WhatwgTest and <n> of <n> in Gates; strict ceiling propext and Quot.sound over <n> module prefix(es) with <n> exact exception(s); <n> source-token exemption(s)
```

The fields, in order: audited sources (with `bin/` and the three roots);
audited declarations; for each audited tree, the declarations that reach
`Classical.choice` (by `Lean.collectAxioms`) and the declarations in it; the
length of the strict list; the exact exceptions (public and private); the
source-token exemptions. The message is one line: no interpolated list or
other value that Lean's formatter may break.

For information, measured at the freeze with `Lean.collectAxioms` over the
compiled environment: `Whatwg` 278 of 12,806, `WhatwgTest` 70 of 1,950,
`Gates` 175 of 1,590 (this packet's harness included); 16,346 in all. Under
`Whatwg.Ecma262`, `Whatwg.WebIdl` and `Whatwg.Url` six declarations reach
`Classical.choice`, the six theorems slice V1 repairs; `Whatwg.Ecma262.Jobs`
has none.

## 8. Unchanged behaviour

- The rows of `acceptancePlants` and `rejectionPlants` that predate this
  packet are unchanged (the only edit near them is the list separator after
  the last old row of each table), and so are their fixtures. Their fragments still
  pass: ``contains an authored `partial` declaration modifier``,
  ``contains an authored `unsafe` declaration modifier``,
  `reaches forbidden axiom sorryAx` or ``declaration uses `sorry` ``,
  `(native_decide auxiliary)`, any rejection for the four malformed-literal
  plants, `is not reachable from the WhatwgTest audit root`, and acceptance of
  `benign.lean.txt`.
- The harness behaves as before for those rows: `withEdits` with one appended
  fixture writes exactly what `withPlanted` wrote.

## 9. Plants

Placement: *append* adds the fixture after a newline; *new module* writes the
fixture as a new file and puts `import <Module>` first in `WhatwgTest.lean`;
*after anchor* inserts it after the anchor line of section 10. Every plant is
undone before the next. Fragments are checked as substrings of the build
output.

Acceptance plants (the build must succeed):

| ID | Fixture | Target, placement | State at the freeze |
| --- | --- | --- | --- |
| V2-A1 | `benign-trust-tokens.lean.txt` | `Whatwg.lean`, append | green |
| V2-A2 | `env-authored-opaque.lean.txt` | `Whatwg.lean`, append | green |
| V2-S2 | `strict-choice.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | green |

Rejection plants (the build must fail and print the fragment):

| ID | Fixture | Target, placement; further edit | Expected fragment |
| --- | --- | --- | --- |
| V2-E1 | `env-declared-axiom.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | `declaration plantedDeclaredAxiom is an axiom; no audited tree declares one` |
| V2-E2 | `env-production-axiom.lean.txt` | `Whatwg.lean`, append | `declaration plantedProductionAxiom is an axiom; no audited tree declares one` |
| V2-E3 | `env-extern.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | `` declaration plantedExternTarget is `@[extern]` `` |
| V2-E4 | `env-implemented-by.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | `` declaration plantedImplementedTarget is `@[implemented_by]` `` |
| V2-E5 | `env-escaped-implemented-by.lean.txt` | `Whatwg.lean`, append | `` declaration plantedEscapedTarget is `@[implemented_by]` `` |
| V2-E6 | `env-bodyless-opaque.lean.txt` | `Whatwg.lean`, append | ``declaration plantedBodylessOpaque is an `opaque` with no authored body`` |
| V2-E7 | `env-bodyless-opaque-parameterised.lean.txt` | `Gates/TrustSelfTestToolingPlant.lean`, new module | ``declaration plantedParameterisedOpaque is an `opaque` with no authored body`` |
| V2-T01 | `token-native-decide.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `native_decide` trust token`` |
| V2-T02 | `token-bv-decide.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``TrustSelfTestPlant.lean contains an authored `bv_decide` trust token`` |
| V2-T03 | `token-bv-decide-query.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``TrustSelfTestPlant.lean contains an authored `bv_decide?` trust token`` |
| V2-T04 | `token-bv-check.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``TrustSelfTestPlant.lean contains an authored `bv_check` trust token`` |
| V2-T05 | `token-native-flag.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `native` trust token`` |
| V2-T06 | `token-native-config.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `native` trust token`` |
| V2-T07 | `token-sorry.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `sorry` trust token`` |
| V2-T08 | `token-axiom.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `axiom` trust token`` |
| V2-T09 | `token-extern.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `extern` trust token`` |
| V2-T10 | `token-implemented-by.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `implemented_by` trust token`` |
| V2-T11 | `token-skip-kernel-tc.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `debug.skipKernelTC` trust token`` |
| V2-T12 | `token-skip-kernel-tc-escaped.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `debug.skipKernelTC` trust token`` |
| V2-T13 | `token-of-reduce-bool.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `Lean.ofReduceBool` trust token`` |
| V2-T14 | `token-of-reduce-nat.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `Lean.ofReduceNat` trust token`` |
| V2-T15 | `token-trust-compiler.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `Lean.trustCompiler` trust token`` |
| V2-T16 | `token-native-decide.lean.txt` | `Gates/TrustSelfTestToolingPlant.lean`, new module | ``TrustSelfTestToolingPlant.lean contains an authored `native_decide` trust token`` |
| V2-T17 | `token-native-decide.lean.txt` | `bin/Citations.lean`, append; a comment appended to `WhatwgTest.lean` | ``Citations.lean contains an authored `native_decide` trust token`` |
| V2-S1 | `strict-choice.lean.txt` | `Whatwg/Ecma262/TrustSelfTestPlant.lean`, new module | `declaration TrustSelfTestPlant.plantedChoice reaches Classical.choice under the strict ceiling of Whatwg.Ecma262` |
| V2-S3 | `strict-exception-missing.lean.txt` | `WhatwgTest/Audit/AxiomGate.lean`, after the strict anchor | `strict-ceiling exception names missing declaration TrustSelfTestPlant.plantedMissing` |
| V2-S4 | `strict-exception-stale.lean.txt` | the same; new module `Whatwg/Ecma262/TrustSelfTestPlant.lean` from `strict-choice-free.lean.txt` | `stale strict-ceiling exception for TrustSelfTestPlant.plantedChoiceFree; it does not reach Classical.choice` |
| V2-S5 | `strict-exception-nonstrict.lean.txt` | the same; new module `WhatwgTest/TrustSelfTestPlant.lean` from `strict-choice.lean.txt` | `stale strict-ceiling exception for TrustSelfTestPlant.plantedChoice; its module WhatwgTest.TrustSelfTestPlant is under no strict prefix` |
| V2-S6 | `strict-exception-unreasoned.lean.txt` | the same; new module `Whatwg/Ecma262/TrustSelfTestPlant.lean` from `strict-choice.lean.txt` | `strict-ceiling exception for TrustSelfTestPlant.plantedChoice carries no reason` |
| V2-X1 | `token-exemption-stale.lean.txt` | `WhatwgTest/Audit/AxiomGate.lean`, after the token anchor; new module `WhatwgTest/TrustSelfTestPlant.lean` from `strict-choice.lean.txt` | `stale source-token exemption for WhatwgTest.TrustSelfTestPlant; its source contains no refused token` |
| V2-X2 | `token-exemption-missing.lean.txt` | the same anchor | `source-token exemption names missing module WhatwgTest.TrustSelfTestPlantMissing` |

Why each plant is shaped as it is:

- Every token plant leaves no constant the environment and axiom passes would
  refuse: an `example`, a `#check`, a never-expanded macro quotation, or a
  theorem that reaches no axiom (V2-T11, V2-T12). Each compiles under the
  package options, so at the base the gate accepts it.
- V2-E1, V2-E3 and V2-E4 attach the axiom, `extern` and `implemented_by`
  through `Lean.addDecl` and the attribute API inside `run_cmd`, so no source
  token names them: they show the environment pass is independent of the token
  pass. They sit in a new test module because the gate module's own source
  may one day hold an exemption.
- V2-T07 switches `warningAsError` off for one command; with it on, Lean's own
  "declaration uses `sorry`" already fails the build, as the existing plant
  shows. V2-T13 to V2-T15 switch the deprecation linter off for one command,
  since Lean 4.33.1 deprecates the three axioms.
- V2-T03 and V2-T04 use quotations because `bv_decide?` writes an LRAT file
  beside the source when it runs.
- The strict plants use a new leaf module under `Whatwg.Ecma262` rather than
  `Whatwg/Ecma262/Jobs.lean`. The gate decides strictness by module, so the
  behaviour tested is the same; a plant in `Jobs.lean` would rebuild all of
  `Whatwg.Streams` twice per plant, because `Whatwg.Streams.Readable.State`
  imports `Whatwg.Ecma262.Promise`, which imports `Jobs`. V2-S1 and V2-S2
  plant the same text, so the declaration's name is identical and only its
  module differs.
- The tooling plants use a new module under `Gates/` because every census
  battery imports `Gates` and reads `vendor/` and `docs/` at elaboration time,
  and the probe copies neither.
- V2-T17 also appends a comment to `WhatwgTest.lean`: the gate reads `bin/` at
  elaboration time, Lake does not track that read (debt D49), and without the
  edit a cached verdict would be replayed.

## 10. Source anchors the gate carries

Two lines of `WhatwgTest/Audit/AxiomGate.lean` are frozen. Each occurs
exactly once; the harness matches the line after trimming ASCII whitespace:

```text
-- trust-selftest: strict-ceiling exception entries are inserted below this line
-- trust-selftest: source-token exemption entries are inserted below this line
```

Each stands on its own line immediately before the list expression that is
the body of its list (the public strict-exception list; the source-token
exemption list), so that inserting after it a line of the form

```lean
  ⟨`Some.Name, "reason"⟩ ::
```

yields that list with the entry prepended, whatever its other entries. The
element type of each list is therefore a structure or product whose anonymous
constructor takes exactly the full `Name` and the reason `String`, in that
order, and the name is a single-backtick literal, so an entry for a missing
declaration elaborates. For example:

```lean
private def strictCeilingExceptions : List StrictCeilingException :=
  -- trust-selftest: strict-ceiling exception entries are inserted below this line
  []
```

A plant that needs an anchor fails with "could not plant" while the anchor is
absent or repeated. The anchors are comments: the token passes ignore them and
they change nothing the gate decides.

## 11. Narrow runs

After the final green control, in the probe root:

| ID | Command | Required |
| --- | --- | --- |
| V2-N1 | `lake env lean WhatwgTest.lean` | exit code 0 and a line matching the summary template of section 7 |
| V2-N2 | `lake env lean WhatwgTest/Audit/SpecCoverage.lean` | exit code 0 and a line matching `Whatwg spec coverage gate: <n> frozen rows agree with ` |

The gate turns its own file name into an absolute path (joining it to the
working directory when it is relative) before searching upward for the root;
`SpecCoverage.lean`'s root search gets the same repair (R-V2). At the base,
V2-N1 fails with "Whatwg axiom gate: source file has no parent directory" and
V2-N2 with "spec coverage gate: could not locate the project root".

## 12. Review clauses (not planted)

These are part of the contract and are checked by the independent reviewer,
because planting them would need a seam in the gate, a red acceptance row, or
a measurement only the builder can make.

- R1. A well-formed strict exception admits its declaration: a choice-reaching
  declaration under a strict prefix, named by an entry with a non-blank
  reason, is accepted. Not planted, because an acceptance row that needs the
  anchor is red until the builder lands, and the red state of this packet is
  fixed to rejection rows and narrow runs. The failure it guards against is
  over-refusal, which the first real exception would expose at once.
- R2. An exempted module's refused token is accepted, and only in that module
  and only by the trust-token pass. Not planted for the same reason.
- R3. The summary counts are what section 7 says they are, and the three tree
  counts of declarations sum to the declaration count. The template checks
  shape only.
- R4. Private strict exceptions, if the builder adds them, are resolved to
  exactly one declaration each and pass the four checks of section 6.
- R5. The environment pass inspects every constant, including Lean-generated
  ones, and the unmodified tree is accepted with no exemption, exception or
  special case beyond the existing `isGeneratedSafeRecursor`. A generated
  constant that trips section 4.1 is reported to the coordinator with its name
  rather than silenced. One such shape is known and absent today: `deriving
  Repr, BEq` on a nested inductive (measured on
  `inductive Tree | leaf | node (children : List Tree)`) makes Lean generate
  `instReprTree.repr` and `instBEqTree.beq` as `opaque` constants whose value
  is `fun … => default`, with `isPartial` false. Section 4.1's opaque row
  refuses them, consistently with the tree's ban on `partial`: in the kernel
  they denote `default`, not the function their names advertise.
- R6. CI gains `lake exe trustselftest` and, if the builder measures it under
  fifteen minutes on this host and it passes on the unmodified tree, a
  `leanchecker` replay of the three libraries (R-V2); otherwise the measurement
  is recorded. `WhatwgTest/AGENTS.md` (which still says the gate module is the
  one module admitted to an implementation ceiling) and `Gates/AGENTS.md` (the
  trust self-test row) describe the landed gate.
- R7. The R-V3(c) renames are applied to this harness by the V3 seat, which
  owns `Gates/**` and `bin/**`: the selectors `toolingPlantModule` and
  `binEntryPoint`, the fragments of V2-T16 and V2-T17 and the tree name `Gates`
  in the summary template may change to the renamed spellings, with a dated
  note here; nothing else.

## 13. What a pass does not mean

A green `lake exe trustselftest` with this packet says that each plant above
is refused or accepted for its stated reason on this toolchain. It does not
say the following.

- The trust-token pass is lexical. It reads spellings, not meanings. It does
  not see a name built by metaprogramming (`Lean.mkIdent`, `Name.mkStr`,
  string concatenation), a name literal, an option set by `-D`, by
  `leanOptions` or `moreLeanArgs` in `lakefile.toml`, or by `withOptions` or
  `modifyScope` inside a metaprogram, or code inside the `{…}` holes of an
  interpolated string, which the tokenizer reads as string text.
- `debug.skipKernelTC` set any way other than its spelled option is caught
  only by a kernel replay (`leanchecker`): a `run_cmd` that adds a theorem with
  the option set in its `Options` leaves a theorem that reaches no axiom and
  that no pass of this gate refuses. R-V2 makes that replay conditional on the
  builder's measurement.
- A macro or tactic defined outside the audited trees (in a dependency or in
  core) that expands to `native_decide`, `sorry` or another channel inside an
  `example` is seen by neither pass: no token in our source, no constant in
  the environment.
- `bin/` is covered by the source passes only. Its constants are compiled into
  executables and never enter the audited environment.
- `set_option warningAsError false` is not refused. Its known abuse, a
  `sorry` inside an `example`, is caught by the `sorry` token.
- An exemption or exception admits by exact name; the gate checks that it is
  needed, not that its reason is true.
- The gate reports where trust enters; it says nothing about whether a
  statement models its specification text.
- Every gate verdict is an elaboration-time verdict that Lake may replay from
  cache when only an untracked file changed (debt D49).

## 14. Red state at the freeze

`lake build` is green on the unmodified tree (the packet adds fixtures and
harness code only). `lake exe trustselftest` fails, and fails exactly on the
31 `V2-` rejection rows and the two narrow runs; every older row and the three
`V2-` acceptance rows pass. The run is recorded in section 15.

| Row | At the freeze |
| --- | --- |
| V2-E1, V2-E2 | rejected for an unexpected reason: today's gate reports "reaches unexpected axiom" |
| V2-E3 to V2-E7, every V2-T row, V2-S1 | unexpectedly accepted |
| V2-S3 to V2-S6, V2-X1, V2-X2 | could not plant: the anchors do not exist yet |
| V2-N1, V2-N2 | non-zero exit, as section 11 says |

The builder turns every row green without editing a breaker-owned file. No
module is red, so `test/fixtures/trust-gate/known-red.txt` gains no entry: it
lists red modules only (R-V2).

## 15. Freeze run

Order matters: `lake build` first, then `lake exe trustselftest`. The probe
is seeded from the checkout's `.lake/build` and does not copy `vendor/` or
`docs/`; a module that the probe must re-elaborate and that reads them (every
census battery imports `Gates`) fails step 0 for a missing file. This was
observed once at this freeze, when `Gates/TrustSelfTest.lean` had been rebuilt
alone; after a full `lake build` step 0 passes.

Recorded on Windows 11, Lean 4.33.1, at the freeze tree: `lake build` exit 0,
396 jobs; `lake exe trustselftest` exit 1 in 5 min 19 s. Its result lines, in
the order the harness checks them (the harness's standard output is
block-buffered when redirected, so in a captured log these lines follow its
standard-error lines):

```text
PASS declared red set matches the observed red set (0 module(s))
PASS trust gate accepted the unmodified source tree (the step-0 build)
PASS trust gate accepted comments, strings, and numeric projections
PASS trust gate accepted V2-A1 refused trust words in comments, documentation, strings and name literals, and identifiers that only contain them
PASS trust gate accepted V2-A2 an opaque with an authored body in the production tree
PASS trust gate accepted V2-S2 a theorem reaching Classical.choice in a new module under WhatwgTest
PASS planted partial declaration rejected with the expected diagnostic: contains an authored `partial` declaration modifier
PASS planted unsafe declaration rejected with the expected diagnostic: contains an authored `unsafe` declaration modifier
PASS planted sorry in the production tree rejected with the expected diagnostic: declaration uses `sorry`
PASS planted native_decide in the production tree rejected with the expected diagnostic: (native_decide auxiliary)
PASS planted malformed string literal rejected
PASS planted malformed raw string literal rejected
PASS planted malformed decimal literal rejected
PASS planted unterminated comment rejected
FAIL trust gate rejected V2-E1 an axiom added through Lean.addDecl in a new test module for an unexpected reason; expected one of: [declaration plantedDeclaredAxiom is an axiom; no audited tree declares one]
FAIL trust gate rejected V2-E2 a declared axiom in the production tree for an unexpected reason; expected one of: [declaration plantedProductionAxiom is an axiom; no audited tree declares one]
FAIL trust gate unexpectedly accepted V2-E3 @[extern] attached through the attribute API in a new test module
FAIL trust gate unexpectedly accepted V2-E4 @[implemented_by] attached through the attribute API in a new test module
FAIL trust gate unexpectedly accepted V2-E5 @[implemented_by] under its escaped name in the production tree
FAIL trust gate unexpectedly accepted V2-E6 an opaque with no body in the production tree
FAIL trust gate unexpectedly accepted V2-E7 a parameterised opaque with no body in a new tooling module
FAIL trust gate unexpectedly accepted V2-T01 native_decide inside an example in the production tree
FAIL trust gate unexpectedly accepted V2-T02 bv_decide inside an example in a new test module
FAIL trust gate unexpectedly accepted V2-T03 bv_decide? inside a tactic quotation in a new test module
FAIL trust gate unexpectedly accepted V2-T04 bv_check inside a tactic quotation in a new test module
FAIL trust gate unexpectedly accepted V2-T05 decide +native inside an example in the production tree
FAIL trust gate unexpectedly accepted V2-T06 decide (native := true) inside an example in the production tree
FAIL trust gate unexpectedly accepted V2-T07 sorry inside an example with warningAsError switched off
FAIL trust gate unexpectedly accepted V2-T08 axiom inside a command quotation in the production tree
FAIL trust gate unexpectedly accepted V2-T09 extern inside a command quotation in the production tree
FAIL trust gate unexpectedly accepted V2-T10 implemented_by inside a command quotation in the production tree
FAIL trust gate unexpectedly accepted V2-T11 debug.skipKernelTC on a theorem in the production tree
FAIL trust gate unexpectedly accepted V2-T12 the escaped spelling of debug.skipKernelTC in the production tree
FAIL trust gate unexpectedly accepted V2-T13 the qualified spelling Lean.ofReduceBool in the production tree
FAIL trust gate unexpectedly accepted V2-T14 the short spelling ofReduceNat under open Lean in the production tree
FAIL trust gate unexpectedly accepted V2-T15 the spelling _root_.Lean.trustCompiler in the production tree
FAIL trust gate unexpectedly accepted V2-T16 native_decide inside an example in a new tooling module
FAIL trust gate unexpectedly accepted V2-T17 native_decide inside an example in an entry point under bin/
FAIL trust gate unexpectedly accepted V2-S1 a theorem reaching Classical.choice in a new module under Whatwg.Ecma262
FAIL could not plant V2-S3 a strict-ceiling exception naming no declaration: <probe>\WhatwgTest\Audit\AxiomGate.lean: the anchor line `-- trust-selftest: strict-ceiling exception entries are inserted below this line` occurs 0 time(s); exactly one is required
FAIL could not plant V2-S4 a strict-ceiling exception naming a declaration that reaches no Classical.choice: <probe>\WhatwgTest\Audit\AxiomGate.lean: the anchor line `-- trust-selftest: strict-ceiling exception entries are inserted below this line` occurs 0 time(s); exactly one is required
FAIL could not plant V2-S5 a strict-ceiling exception naming a declaration under no strict prefix: <probe>\WhatwgTest\Audit\AxiomGate.lean: the anchor line `-- trust-selftest: strict-ceiling exception entries are inserted below this line` occurs 0 time(s); exactly one is required
FAIL could not plant V2-S6 a strict-ceiling exception whose reason is blank: <probe>\WhatwgTest\Audit\AxiomGate.lean: the anchor line `-- trust-selftest: strict-ceiling exception entries are inserted below this line` occurs 0 time(s); exactly one is required
FAIL could not plant V2-X1 a source-token exemption for a module that names no refused token: <probe>\WhatwgTest\Audit\AxiomGate.lean: the anchor line `-- trust-selftest: source-token exemption entries are inserted below this line` occurs 0 time(s); exactly one is required
FAIL could not plant V2-X2 a source-token exemption naming no module: <probe>\WhatwgTest\Audit\AxiomGate.lean: the anchor line `-- trust-selftest: source-token exemption entries are inserted below this line` occurs 0 time(s); exactly one is required
PASS planted unreachable test module rejected with the expected diagnostic: is not reachable from the WhatwgTest audit root
PASS trust gate accepted the restored source tree
FAIL V2-N1 the axiom gate run narrowly as `lake env lean WhatwgTest.lean`: `lake env lean WhatwgTest.lean` exited with code 1
  WhatwgTest.lean:90:0: error: Whatwg axiom gate: source file has no parent directory
FAIL V2-N2 the spec coverage gate run narrowly by its relative file name: `lake env lean WhatwgTest/Audit/SpecCoverage.lean` exited with code 1
  WhatwgTest/Audit/SpecCoverage.lean:877:0: error: spec coverage gate: could not locate the project root
FAIL trust self-test
```

`<probe>` stands for the throwaway copy's path. The two "unexpected reason"
rows printed today's diagnostic,
`Whatwg axiom gate: declaration plantedDeclaredAxiom reaches unexpected axiom plantedDeclaredAxiom; allowed axioms are [propext, …]`
and the same for `plantedProductionAxiom`. `lake exe citations` and
`lake exe vendorseal` pass at the freeze.

## 16. Findings outside this packet

Recorded for the coordinator; none is in this packet's or the V2 builder's
fence.

- Six more elaboration-time batteries fail a narrow run by relative file name,
  through `Gates.Common.findProjectRoot`, which has the same relative-path
  defect: `WhatwgTest/Audit/CensusProfileIdentity.lean`,
  `WhatwgTest/Audit/WebIdl/CensusContract.lean`,
  `WhatwgTest/Audit/WebIdl/CensusQ2Contract.lean`,
  `WhatwgTest/Audit/Ecma262/CensusContract.lean`,
  `WhatwgTest/Audit/Ecma262/CensusQ2Contract.lean` and
  `WhatwgTest/Audit/Ecma262/EcmarkupScanner.lean` (each: `gate: could not
  locate the repository root`). Making `findProjectRoot`'s directory absolute
  first would repair all six; `Gates/**` is the V3 seat's after V2.
- That error message, `Gates.Common`'s module documentation and
  `Gates/AGENTS.md` say the root is found by `Whatwg.Streams.lean`; the code
  looks for `Whatwg.lean`.
- The probe's `copiedTrees` documentation says `vendor/` stays out because
  the probe never runs the census generator, but the census batteries read
  `vendor/` and `docs/` when they are re-elaborated, so a stale cache makes
  step 0 fail (section 15).

## Addendum V2b (2026-10-01)

Status: FROZEN / RED, V2b breaker seat, 2026-10-01, on branch
`review/v2b-token-breaker`, based on `863b596` (the commit that lands ruling
R-V6, which opens this addendum). The addendum is appended; no earlier sentence
of this file is changed. Where it and an earlier section differ, the addendum
governs, and V2b.5 names each place.

Authority: ruling R-V6 at the end of `COORDINATION.md`. The V2 builder found
that an `example` under `set_option warningAsError false` can admit a goal
through spellings the frozen word list does not carry (`sorryAx` by name,
`debug.byAsSorry`); a breaker freezes fixtures and plant rows for those and
for every other goal-admitting spelling it finds in the toolchain, and the
coordinator applies the word-list change.

### V2b.1 Method, and the fact that decides most rows

Each candidate was written as a small file in a scratch directory outside the
worktree, pinned to `leanprover/lean4:v4.33.1`, and elaborated with
`lake env lean -DwarningAsError=true <file>`, the package's own option. The
toolchain source under `src/lean/Init`, `src/lean/Lean` and `src/lean/Std` was
read for every `sorry`-like syntax, every option whose description mentions
`sorry` or skipping a check, and every caller of `Lean.Elab.admitGoal`,
`Lean.MVarId.admit`, `Lean.Meta.mkSorry` and `Lean.Meta.mkLabeledSorry`. Lean's
own semantic highlighter classes four keywords as sorry-like: `sorry`, `admit`,
`stop` and `#exit` (`keywordSemanticTokenMap` in
`Lean/Server/FileWorker/SemanticHighlighting.lean`). `Std` adds no admitting
syntax.

`Lean.warnIfUsesSorry` (`Lean/AddDecl.lean`) logs "declaration uses `sorry`"
for every declaration added to the environment, an `example` included, whose
value contains `sorryAx`, synthetic or not, unless the option `warn.sorry` is
false or the message log already holds an error. Under the package-wide
`warningAsError = true` that warning is an error: `example : (1 : Nat) = 2 :=
by admit` and `example : (1 : Nat) = 2 := sorryAx _ true` each fail the build.
An admitted goal inside an `example` therefore survives the build through one
of three source-level switches only:

1. `set_option warningAsError false`, for one command or for the rest of the
   file;
2. `set_option warn.sorry false`, which removes the warning itself, so that the
   `example` passes with no message even under `warningAsError = true`;
3. `#guard_msgs`, which removes the messages of the command it wraps, with
   `(drop all)`, `(drop error)`, or a docstring that expects the message.
   `(drop warning)` does not: under `warningAsError` the message is already an
   error.

A failing proof behaves the same way: the elaborator closes the goal with a
synthetic `sorry` and logs an error, which fails the build unless `#guard_msgs`
consumes it.

### V2b.2 Candidates

"Admits" means the file's `example` of the false goal `(1 : Nat) = 2`
elaborated with exit code 0 under the stated condition. "Today's gate" is the
gate at the base, whose passes see no constant and no refused word in such an
`example`.

| Candidate | Measured | Admits, or skips a check | Today's gate | Decision |
| --- | --- | --- | --- | --- |
| the term `sorryAx _ false`, also spelled `_root_.sorryAx` | exit 0 with `warningAsError` off; exit 0 and no message under `#guard_msgs (drop all)` | admits | accepts | refuse `sorryAx`, last-component shape (V2b-T01, V2b-T02) |
| the tactic `admit`, also `grind => admit` | the same | admits: core's `macro "admit" : tactic` expands to the `sorry` tactic | accepts | refuse `admit` (V2b-T03) |
| the tactic `stop tacs` | the same, and through a `macro` that expands to it | admits every goal: it expands to `repeat sorry` | accepts | not refused: legitimate identifier uses (V2b.4); Lean's warning catches it once the two switches are refused |
| the tactic `impossible by t` | the same | admits the goal its inner tactic has just refuted: core closes it "as if `sorry` was used" | accepts | refuse `impossible` (V2b-T04) |
| the tactic `apply?` | the same | admits: on partial suggestions it calls `admitGoal goal (synthetic := false)` | accepts | refuse `apply?` (V2b-T05) |
| the tactic `try?` | the same | admits: it runs its suggestion `impossible by decide` | accepts | refuse `try?` (V2b-T06) |
| the tactic `grind?` | the same | admits: `grind` with `useSorry` closes what it cannot solve and suggests `grind => sorry` | accepts | refuse `grind?` (V2b-T07) |
| `grind +trace`, `grind (trace := true)` | exit 0 with `warningAsError` off; exit 1 under `warn.sorry false` alone, through its own warning "generated tactic cannot close the goal" | admits, through the same `useSorry` | accepts | no word: `trace` is an ordinary configuration field; caught once `warningAsError` is refused (V2b-T11 uses it) |
| `set_option debug.byAsSorry true` | exit 0 with `warningAsError` off or under `#guard_msgs` | admits: every `by` block of propositional type becomes `sorry` | accepts | refuse `debug.byAsSorry` (V2b-T08) |
| `set_option debug.terminalTacticsAsSorry true` | the same, under `omega` and under `grind` | admits: `omega` and `grind` close their goal with `sorry` | accepts | refuse `debug.terminalTacticsAsSorry` (V2b-T09) |
| `set_option debug.proofAsSorry true` | an `example` is unaffected (`decide` runs and fails); a `theorem` reaches `sorryAx` | theorem bodies only | the axiom pass refuses the theorem | not added: no hole |
| `set_option warn.sorry false` | exit 0 and no message under `warningAsError = true`, with `admit`, with `stop`, and with an elaborator that builds `sorryAx` from a name literal | removes the one warning that catches every admission | accepts | refuse `warn.sorry` (V2b-T10) |
| `set_option warningAsError false` | every admitting row above passes with it | turns that warning back into a warning | accepts (section 13) | refuse `warningAsError` (V2b-T11); supersedes section 13 (V2b.5) |
| `#exit` | after a file-level `set_option warningAsError false`, exit 0 with every later command unelaborated; without it, exit 1 ("using 'exit' to interrupt Lean"); `set_option warningAsError false in #exit` does not end the file | skips every later command | accepts with the file-level switch | not added: once `warningAsError` is refused, its own warning fails the build (V2b.6) |
| `#guard_msgs (drop error) in`, `(drop all)`, or a docstring expecting the error | exit 0 for `example : (1 : Nat) = 2 := by decide`, a failing proof with no admitting word, and for every admitting spelling above | admits any `example` | accepts | not refused: legitimate uses (V2b.4); recorded in V2b.6 |
| `Lean.reduceBool c`, `Lean.reduceNat n` | `example : plantedNativeInput = true := (rfl : Lean.reduceBool plantedNativeInput = true)` exit 0; the same statement as a `theorem` reaches `Lean.trustCompiler` | skips a check: the kernel evaluates `c` with compiled code | accepts in an `example` | refuse both, last-component shape (V2b-T12, V2b-T13) |
| an elaborator or macro defined in an audited tree: `elab` calling `Lean.MVarId.admit`, `run_tac` calling `Lean.Elab.admitGoal`, `elab` assigning `sorryAx` built from a name literal, `macro` expanding to `stop` | each admits with `warningAsError` off; the name-literal one with no message under `warn.sorry false` | admits | accepts | no word: a name literal is not code and the Meta API names are ordinary; Lean's warning catches each once the two switches are refused |
| `Lean.Environment.addDeclCore … (doCheck := false)` inside `run_cmd` | adds `plantedUnchecked : False` with value `Nat.zero`; `#print axioms` reports no axiom; `example : False := plantedUnchecked` elaborates | skips the kernel check of a persistent theorem | accepts in every pass: a theorem that reaches no axiom | no word closes it; the class of section 13's second bullet (V2b.6) |
| `decide +kernel` | exit 1: the kernel rejects the false goal | no | — | not a hole |
| `lcProof`, `lcUnreachable`, `unsafeCast`, `ptrAddrUnsafe` | exit 1: "(kernel) invalid declaration, it uses unsafe declaration" | no | — | not a hole |
| the term `unsafe t` | carries the keyword `unsafe` | — | the modifier pass refuses it | unchanged |
| `exact?`, `exact?%`, `rw?` | exit 1: `exact?` and `exact?%` log an error when they cannot close the goal; `rw?` rewrites with its first suggestion and the goal then fails as unsolved | no: every step they take is a checked one | — | not added |
| `#check_failure t` | exit 0 with an information message | no: it adds no declaration | — | not a hole |
| `@[csimp]`, an `opaque` with a body, `omit`, `include` | `@[csimp]` needs a proved equation; an authored `opaque` body is kernel-checked; `omit` and `include` only manage section variables | no | — | not a hole |
| `native_decide`, `bv_decide`, `bv_decide?`, `bv_check`, `native`, `sorry`, `axiom`, `implemented_by`, `extern`, `debug.skipKernelTC`, the three forbidden axioms | section 4.2 | — | refused | unchanged |

The premise that a macro or elaborator defined in the audited trees must spell
`sorry` to admit a goal does not hold: a macro can expand to `stop`, and an
elaborator can close a goal through the Meta API, or through `sorryAx` built
from a name literal, without spelling any refused word (the elaborator row).

### V2b.3 Words added to section 4.2

The carried-by rule of section 4.2 keeps its two shapes. A whole-name word is
carried by an atom whose text is the word, or by an identifier whose `Name`,
with `«»` escapes removed, equals the word's `Name`. The last-component shape,
which section 4.2 gives the three forbidden axioms, extends to `sorryAx` and
the two kernel-evaluation hooks.

| Refused word, printed as | Shape | Spellings refused | Channel |
| --- | --- | --- | --- |
| `admit` | whole name | `admit`, `«admit»`, in tactic and in `grind` mode | core's second name for the `sorry` tactic |
| `impossible` | whole name | `impossible`, `«impossible»` | closes a goal its inner tactic refutes, as if by `sorry` |
| `apply?` | whole name | `apply?` | library search that closes the goal with `sorry` on partial results |
| `try?` | whole name | `try?` | runs its suggestions, `impossible` among them |
| `grind?` | whole name | `grind?` | closes with `sorry` what `grind` cannot solve |
| `debug.byAsSorry` | whole name | `debug.byAsSorry` and every escaping, any value | every `by` block of propositional type becomes `sorry` |
| `debug.terminalTacticsAsSorry` | whole name | the same shapes | `omega` and `grind` close their goal with `sorry` |
| `warn.sorry` | whole name | `warn.sorry`, `«warn».sorry`, `warn.«sorry»`, any value | removes "declaration uses `sorry`" |
| `warningAsError` | whole name | `warningAsError`, `«warningAsError»`, any value | makes the package's warnings, that one included, warnings again |
| `sorryAx` | last component | `sorryAx`, `_root_.sorryAx`, and any identifier ending in the component | the axiom behind `sorry`, by name |
| `Lean.reduceBool` | last component | `reduceBool` (short, under `open Lean`), `Lean.reduceBool`, `_root_.Lean.reduceBool`, and any identifier ending in the component | the kernel evaluates the argument with compiled code |
| `Lean.reduceNat` | last component | the same shapes for `reduceNat` | the same, for `Nat` |

Measured with the gate's tokenizer (`Parser.tokenFn` with the token table of an
environment that imports `Lean`): `admit`, `stop`, `impossible`, `apply?`,
`try?` and `grind?` are identifier tokens, because tactic names are not reserved
symbols (`LeadingIdentBehavior.both`); the option names are dotted
identifiers; `«warn».sorry` and `warn.«sorry»` read as the identifier
`warn.sorry`; `#exit` and `#guard_msgs` are atoms. Section 4.2 refuses both
shapes for every word, so a change of grammar opens no hole.

Diagnostic fragments, in the template of section 4.2, unchanged:

```text
Whatwg source trust gate: <path> contains an authored `admit` trust token
Whatwg source trust gate: <path> contains an authored `impossible` trust token
Whatwg source trust gate: <path> contains an authored `apply?` trust token
Whatwg source trust gate: <path> contains an authored `try?` trust token
Whatwg source trust gate: <path> contains an authored `grind?` trust token
Whatwg source trust gate: <path> contains an authored `debug.byAsSorry` trust token
Whatwg source trust gate: <path> contains an authored `debug.terminalTacticsAsSorry` trust token
Whatwg source trust gate: <path> contains an authored `warn.sorry` trust token
Whatwg source trust gate: <path> contains an authored `warningAsError` trust token
Whatwg source trust gate: <path> contains an authored `sorryAx` trust token
Whatwg source trust gate: <path> contains an authored `Lean.reduceBool` trust token
Whatwg source trust gate: <path> contains an authored `Lean.reduceNat` trust token
```

Decisions frozen here:

- `warningAsError` and `warn.sorry` are refused whatever value they are set to.
  Setting either to its default is never needed in source, and a rule on the
  value would need more than one token.
- `sorryAx`, `Lean.reduceBool` and `Lean.reduceNat` take the last-component
  shape, as the three forbidden axioms do: `_root_.sorryAx` names the same
  constant (V2b-T02), `reduceNat` under `open Lean` resolves to the hook
  (V2b-T13), and no identifier in the tree ends in any of the three components.
- Every other added word is refused only as a whole name.
  `plantedV2bVocabulary.admit`, `goal.admit`, `Lean.MVarId.admit`,
  `Lean.Elab.admitGoal`, `admitted` and `impossibleCase` are names; V2b-A1 pins
  the first, and the last two. `(← getMainGoal).admit` is refused: the
  tokenizer reads the atom `.` and then the identifier `admit`.

### V2b.4 Legitimate uses in the tree

Measured at the base by searching the audited sources, then confirmed with the
tokenizer rule: a scratch file outside the worktree that imports `WhatwgTest`,
takes the token table of that environment, and repeats the gate's scan
(`Parser.whitespace`, documentation and module-documentation parsers,
`Parser.tokenFn`, `Parser.fieldIdxFn` after a projection dot) with the carried-by
rule of section 4.2 and the list of V2b.8. Over the 222 audited sources it
reported no tokenization failure and no token carrying any word of that list;
its only hits were the two words not added, `stop` (19) and `#guard_msgs` (9).
This is a re-implementation, not the gate: the gate's own verdict with V2b.8
applied is the coordinator's to record (V2b.9).

Every added word also occurs in the string literals of the V2b rows of
`Gates/TrustSelfTest.lean`, which are not code.

| Word | Uses in code | Elsewhere |
| --- | --- | --- |
| `admit` | none. Identifiers that contain it are names under the whole-name shape: `admits`, `Admits`, `admits_iff`, `admitted`, `admitted_iff`, `tick_beginClose_admitted`, `admitAnswer`, `admitAnyInflight` and others in the production and test trees | prose in documentation and comments of many modules |
| `impossible` | none | none |
| `sorryAx` | none: the gate's `forbiddenAxioms` spells it as the name literal ``` ``sorryAx ``` | documentation of the gate, of `Gates/TrustSelfTest.lean` and of four axiom-report modules; a string literal of `Gates/TrustSelfTest.lean` |
| `warningAsError` | none | documentation and a label string of `Gates/TrustSelfTest.lean`; `lakefile.toml`, which is not an audited source |
| every other added word | none | none |
| `stop`, not added | 19 tokens on 18 lines, a local variable: `Gates/Census.lean` (9), `Gates/UrlCensusInput.lean` (6, on 5 lines), `Gates/UrlInventory.lean` (4) | prose |
| `#guard_msgs`, not added | 9 commands in `WhatwgTest/Html/Breakers.lean`, each wrapping `#check_failure`: 7 `#guard_msgs in`, 2 `#guard_msgs (drop info) in` | its module documentation |

No added word needs an exemption. The two words not added would each need an
exemption or a narrower rule:

- `stop`: the tactic and a local named `stop` are the same identifier token, so
  no one-token rule tells them apart, and an exemption would admit three
  tooling modules to every refused word. Once the eighteen locals are renamed a
  later addendum can refuse it; the rename is outside this packet's fence.
- `#guard_msgs`: an exemption for the HTML breakers would admit that module to
  every refused word. A rule that admits `#guard_msgs` only around
  `#check_failure`, or refuses its `drop error`, `drop warning` and `drop all`
  filters, needs more than one token of context, which the word list cannot
  express.

### V2b.5 Changes to earlier sections

- Section 13, the bullet "`set_option warningAsError false` is not refused":
  superseded. Its abuse is not only a `sorry`: `stop`, `grind +trace` and an
  elaborator built on the Meta API admit a goal with no refused word, and
  Lean's warning is the only check that sees them. `warningAsError` and
  `warn.sorry` are refused in code, whatever their value.
- Section 4.2, "The pass may stop at the first refused token or report every
  one": narrowed to "reports every refused token of every source", which the
  landed gate does. The frozen fixture `token-sorry.lean.txt` of V2-T07 now
  carries two refused words, `warningAsError` before `sorry`, and its row
  expects the `sorry` fragment. Each V2b fixture carries exactly one word, so
  no V2b row depends on this.
- Section 4.2's last-component shape: from the three forbidden axioms to those
  three, `sorryAx`, `Lean.reduceBool` and `Lean.reduceNat`.
- Section 8 holds for every row that predates this addendum: none is changed.
  With V2b.8 applied, each is expected to stay green: the same scratch scan
  finds no word of the extended list in any older acceptance fixture, and among
  the older rejection fixtures only `token-sorry.lean.txt` gains a word (V2b.9).
- Review clause R7 applies to V2b-T07's fragment as it does to V2-T16's.

### V2b.6 What a pass does not mean (extends section 13)

A green `lake exe trustselftest` with the V2b rows says that each V2b plant is
refused or accepted for its stated reason on Lean 4.33.1. In addition to
section 13, it does not say the following.

- `#guard_msgs` admits any `example`. Wrapped around one, `(drop error)`,
  `(drop all)` or a docstring that expects the errors consumes both the error
  of a failing proof (`#guard_msgs (drop error) in example : (1 : Nat) = 2 :=
  by decide` builds) and the "declaration uses `sorry`" error of an admitted
  goal. No word refuses it (V2b.4). The added spellings are refused inside it,
  and V2b-T01 to V2b-T09 are wrapped in it to show that; a failing proof,
  `stop`, `grind +trace` and a Meta-API elaborator are not. Until a later
  addendum adds a rule with context, a reviewer reads every `#guard_msgs`; at
  the base each wraps `#check_failure`.
- Admission that spells no refused word is caught by Lean, not by the gate.
  `stop`, `grind +trace`, and an elaborator or macro defined in an audited tree
  that closes a goal through `Lean.MVarId.admit`, `Lean.Elab.admitGoal`,
  `Lean.Meta.mkSorry` or `sorryAx` built from a name literal all reach
  "declaration uses `sorry`", which fails the build only because
  `lakefile.toml` sets `warningAsError = true` package-wide. The gate does not
  check the option's effective value, and an option set by `-D`, by
  `leanOptions` or `moreLeanArgs`, or by a metaprogram's `withOptions` or
  `modifyScope` stays invisible (section 13). A command elaborator defined in
  an audited tree can also discard an inner command's messages, as
  `#guard_msgs` does.
- `#exit` is not refused. Once `warningAsError` cannot be switched off in
  source, its own warning fails the build. In `WhatwgTest.lean`, a file-level
  `set_option warningAsError false` and `#exit` ahead of
  `#whatwg_streams_axiom_gate` stop the gate before it runs, so no pass refuses
  the switch there; the trust self-test still fails, since every rejection
  plant is then accepted and the narrow run V2-N1 finds no summary line.
- A theorem added without kernel checking is accepted by every pass.
  `Lean.Environment.addDeclCore … (doCheck := false)` inside `run_cmd` left
  `plantedUnchecked : False` with value `Nat.zero`; `#print axioms` reports it
  as reaching no axiom, and an `example : False` can use it. This is the class
  of section 13's second bullet: the leanchecker replay that ruling R-V6 made a
  CI step is the only check that refuses it, and neither `lake build` nor
  `lake exe trustselftest` runs that replay. Refusing `addDeclCore` or
  `doCheck` would not close it: the argument can be positional, and the option
  route of section 13 remains.
- `Lean.reduceBool` and `Lean.reduceNat` are refused as spellings. The
  evaluation they trigger stays reachable through metaprogramming, as for
  `Lean.ofReduceBool`.
- `debug.proofAsSorry` is not refused: it replaces theorem bodies only, and a
  theorem that reaches `sorryAx` is refused by the axiom pass.

### V2b.7 Plants

Breaker-owned and frozen by this addendum, beside the files of section 1: this
addendum; the fixtures `test/fixtures/trust-gate/benign-trust-tokens-v2b.lean.txt`
and `test/fixtures/trust-gate/token-{sorry-ax,sorry-ax-root,admit,impossible,apply-query,try-query,grind-query,by-as-sorry,terminal-tactics-as-sorry,warn-sorry,warning-as-error,reduce-bool,reduce-nat}.lean.txt`;
and the rows of `acceptancePlants` and `rejectionPlants` in
`Gates/TrustSelfTest.lean` whose labels begin `V2b-`. Those rows are appended
to each table with `++`, so every earlier line of the harness is unchanged, and
they use only the existing placements. The coordinator applies V2b.8 in
`WhatwgTest/Audit/AxiomGate.lean` and edits none of these files.

Placement as in section 9. Every plant is undone before the next.

Acceptance plant (the build must succeed):

| ID | Fixture | Target, placement | State at the freeze |
| --- | --- | --- | --- |
| V2b-A1 | `benign-trust-tokens-v2b.lean.txt` | `Whatwg.lean`, append | green |

Rejection plants (the build must fail and print the fragment):

| ID | Fixture | Target, placement | Expected fragment |
| --- | --- | --- | --- |
| V2b-T01 | `token-sorry-ax.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `sorryAx` trust token`` |
| V2b-T02 | `token-sorry-ax-root.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `sorryAx` trust token`` |
| V2b-T03 | `token-admit.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `admit` trust token`` |
| V2b-T04 | `token-impossible.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `impossible` trust token`` |
| V2b-T05 | `token-apply-query.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``TrustSelfTestPlant.lean contains an authored `apply?` trust token`` |
| V2b-T06 | `token-try-query.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``TrustSelfTestPlant.lean contains an authored `try?` trust token`` |
| V2b-T07 | `token-grind-query.lean.txt` | `Gates/TrustSelfTestToolingPlant.lean`, new module | ``TrustSelfTestToolingPlant.lean contains an authored `grind?` trust token`` |
| V2b-T08 | `token-by-as-sorry.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `debug.byAsSorry` trust token`` |
| V2b-T09 | `token-terminal-tactics-as-sorry.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `debug.terminalTacticsAsSorry` trust token`` |
| V2b-T10 | `token-warn-sorry.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``TrustSelfTestPlant.lean contains an authored `warn.sorry` trust token`` |
| V2b-T11 | `token-warning-as-error.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `warningAsError` trust token`` |
| V2b-T12 | `token-reduce-bool.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `Lean.reduceBool` trust token`` |
| V2b-T13 | `token-reduce-nat.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `Lean.reduceNat` trust token`` |

Why each plant is shaped as it is:

- Each rejection fixture is an `example` that elaborates at the base and admits
  `(1 : Nat) = 2`, except V2b-T12 and V2b-T13, whose true `example` is checked
  by compiled code. Each carries exactly one word of the extended list, so a
  gate that stops at the first refused token and one that reports every token
  print the same fragment, and each row names one fragment.
- V2b-T01 to V2b-T09 wrap their `example` in `#guard_msgs (drop all) in`, the
  switch that remains once `warningAsError` and `warn.sorry` are refused
  (V2b.6). It is why those spellings need words of their own.
- V2b-T10 closes its goal with an elaborator that builds `sorryAx` from a name
  literal, which no word can see: the route `warn.sorry` opens. V2b-T11 closes
  its goal with `grind +trace`, which no word spells: the route
  `warningAsError` opens.
- V2b-T05 and V2b-T06 are new test modules that import only `Init`, so library
  search runs over the core library and the plant is fast and stable. V2b-T07
  puts one plant in the tooling tree. V2b-T10 needs `import Lean`.
- V2b-T12 and V2b-T13 hand the hook a definition, which reaches no axiom: on
  this toolchain a literal argument fails to evaluate ("(interpreter) unknown
  declaration 'Bool.true'"). Each switches the deprecation linter off for one
  command, as V2-T13 to V2-T15 do.
- V2b-A1 pins what stays admitted: the added words in comments, documentation,
  strings and name literals; identifiers that only contain an added word, or
  carry a whole-name word as a component of a longer name; a local named
  `stop`; an ordinary `set_option`; and `#guard_msgs (drop info)` around
  `#check_failure`, the form the HTML breakers use.

The `V2b-` labels are stable identifiers and are never reused. As section 1
says of the `V2-` plants, they are not registered in
`test/counterexamples/REGISTER.md`. No module is red, so
`test/fixtures/trust-gate/known-red.txt` gains no entry.

### V2b.8 The change the coordinator applies

In `WhatwgTest/Audit/AxiomGate.lean`, `refusedWords` becomes, literally:

```lean
private def refusedWords : List RefusedWord :=
  ["native_decide", "bv_decide", "bv_decide?", "bv_check", "native", "sorry", "axiom",
    "implemented_by", "extern", "debug.skipKernelTC", "admit", "impossible", "apply?", "try?",
    "grind?", "debug.byAsSorry", "debug.terminalTacticsAsSorry", "warn.sorry",
    "warningAsError"].map refusedWord ++
  (forbiddenAxioms ++ [``Lean.reduceBool, ``Lean.reduceNat]).map refusedAxiomWord
```

`forbiddenAxioms` is ``` ``sorryAx :: forbiddenTrustAxioms ```, so the three
forbidden axioms keep their words and `sorryAx` joins them. Nothing else in the
gate changes. The documentation of `refusedWords`, `forbiddenTrustAxioms` and
`RefusedWord.lastComponent?`, and the trust self-test rows of `Gates/AGENTS.md`
and `WhatwgTest/AGENTS.md`, describe the old list and are the coordinator's to
update.

### V2b.9 Red state and freeze run

`lake build` is green on the base tree with this packet (it adds fixtures and
harness rows only). `lake exe trustselftest` fails, and fails exactly on the
thirteen V2b rejection rows, each "unexpectedly accepted": today's gate sees
neither a refused word nor a refused constant in them. V2b-A1, every older row
and both narrow runs pass.

Recorded on Windows 11, Lean 4.33.1, at the freeze tree, after a full build:
`lake build` exit 0, 380 jobs, its gate line `checked 222 source files and 16490
declarations; … 0 source-token exemption(s)`; then `lake exe trustselftest`
exit 1 in 6 min 13 s. Its result lines, in the order the harness checks them
(in a captured log the standard-output lines follow the standard-error lines,
as section 15 says):

```text
PASS declared red set matches the observed red set (0 module(s))
PASS trust gate accepted the unmodified source tree (the step-0 build)
PASS trust gate accepted comments, strings, and numeric projections
PASS trust gate accepted V2-A1 refused trust words in comments, documentation, strings and name literals, and identifiers that only contain them
PASS trust gate accepted V2-A2 an opaque with an authored body in the production tree
PASS trust gate accepted V2-S2 a theorem reaching Classical.choice in a new module under WhatwgTest
PASS trust gate accepted V2b-A1 the added trust words in comments, documentation, strings and name literals, identifiers that only contain them, a local named stop, an ordinary set_option, and #guard_msgs around #check_failure
PASS planted partial declaration rejected with the expected diagnostic: contains an authored `partial` declaration modifier
PASS planted unsafe declaration rejected with the expected diagnostic: contains an authored `unsafe` declaration modifier
PASS planted sorry in the production tree rejected with the expected diagnostic: declaration uses `sorry`
PASS planted native_decide in the production tree rejected with the expected diagnostic: (native_decide auxiliary)
PASS planted malformed string literal rejected
PASS planted malformed raw string literal rejected
PASS planted malformed decimal literal rejected
PASS planted unterminated comment rejected
PASS planted V2-E1 an axiom added through Lean.addDecl in a new test module rejected with the expected diagnostic: declaration plantedDeclaredAxiom is an axiom; no audited tree declares one
PASS planted V2-E2 a declared axiom in the production tree rejected with the expected diagnostic: declaration plantedProductionAxiom is an axiom; no audited tree declares one
PASS planted V2-E3 @[extern] attached through the attribute API in a new test module rejected with the expected diagnostic: declaration plantedExternTarget is `@[extern]`
PASS planted V2-E4 @[implemented_by] attached through the attribute API in a new test module rejected with the expected diagnostic: declaration plantedImplementedTarget is `@[implemented_by]`
PASS planted V2-E5 @[implemented_by] under its escaped name in the production tree rejected with the expected diagnostic: declaration plantedEscapedTarget is `@[implemented_by]`
PASS planted V2-E6 an opaque with no body in the production tree rejected with the expected diagnostic: declaration plantedBodylessOpaque is an `opaque` with no authored body
PASS planted V2-E7 a parameterised opaque with no body in a new tooling module rejected with the expected diagnostic: declaration plantedParameterisedOpaque is an `opaque` with no authored body
PASS planted V2-T01 native_decide inside an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `native_decide` trust token
PASS planted V2-T02 bv_decide inside an example in a new test module rejected with the expected diagnostic: TrustSelfTestPlant.lean contains an authored `bv_decide` trust token
PASS planted V2-T03 bv_decide? inside a tactic quotation in a new test module rejected with the expected diagnostic: TrustSelfTestPlant.lean contains an authored `bv_decide?` trust token
PASS planted V2-T04 bv_check inside a tactic quotation in a new test module rejected with the expected diagnostic: TrustSelfTestPlant.lean contains an authored `bv_check` trust token
PASS planted V2-T05 decide +native inside an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `native` trust token
PASS planted V2-T06 decide (native := true) inside an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `native` trust token
PASS planted V2-T07 sorry inside an example with warningAsError switched off rejected with the expected diagnostic: Whatwg.lean contains an authored `sorry` trust token
PASS planted V2-T08 axiom inside a command quotation in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `axiom` trust token
PASS planted V2-T09 extern inside a command quotation in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `extern` trust token
PASS planted V2-T10 implemented_by inside a command quotation in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `implemented_by` trust token
PASS planted V2-T11 debug.skipKernelTC on a theorem in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `debug.skipKernelTC` trust token
PASS planted V2-T12 the escaped spelling of debug.skipKernelTC in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `debug.skipKernelTC` trust token
PASS planted V2-T13 the qualified spelling Lean.ofReduceBool in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `Lean.ofReduceBool` trust token
PASS planted V2-T14 the short spelling ofReduceNat under open Lean in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `Lean.ofReduceNat` trust token
PASS planted V2-T15 the spelling _root_.Lean.trustCompiler in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `Lean.trustCompiler` trust token
PASS planted V2-T16 native_decide inside an example in a new tooling module rejected with the expected diagnostic: TrustSelfTestToolingPlant.lean contains an authored `native_decide` trust token
PASS planted V2-T17 native_decide inside an example in an entry point under bin/ rejected with the expected diagnostic: Citations.lean contains an authored `native_decide` trust token
PASS planted V2-S1 a theorem reaching Classical.choice in a new module under Whatwg.Ecma262 rejected with the expected diagnostic: declaration TrustSelfTestPlant.plantedChoice reaches Classical.choice under the strict ceiling of Whatwg.Ecma262
PASS planted V2-S3 a strict-ceiling exception naming no declaration rejected with the expected diagnostic: strict-ceiling exception names missing declaration TrustSelfTestPlant.plantedMissing
PASS planted V2-S4 a strict-ceiling exception naming a declaration that reaches no Classical.choice rejected with the expected diagnostic: stale strict-ceiling exception for TrustSelfTestPlant.plantedChoiceFree; it does not reach Classical.choice
PASS planted V2-S5 a strict-ceiling exception naming a declaration under no strict prefix rejected with the expected diagnostic: stale strict-ceiling exception for TrustSelfTestPlant.plantedChoice; its module WhatwgTest.TrustSelfTestPlant is under no strict prefix
PASS planted V2-S6 a strict-ceiling exception whose reason is blank rejected with the expected diagnostic: strict-ceiling exception for TrustSelfTestPlant.plantedChoice carries no reason
PASS planted V2-X1 a source-token exemption for a module that names no refused token rejected with the expected diagnostic: stale source-token exemption for WhatwgTest.TrustSelfTestPlant; its source contains no refused token
PASS planted V2-X2 a source-token exemption naming no module rejected with the expected diagnostic: source-token exemption names missing module WhatwgTest.TrustSelfTestPlantMissing
FAIL trust gate unexpectedly accepted V2b-T01 sorryAx inside an example whose messages #guard_msgs drops, in the production tree
FAIL trust gate unexpectedly accepted V2b-T02 the spelling _root_.sorryAx in the production tree
FAIL trust gate unexpectedly accepted V2b-T03 the admit tactic inside an example in the production tree
FAIL trust gate unexpectedly accepted V2b-T04 the impossible tactic inside an example in the production tree
FAIL trust gate unexpectedly accepted V2b-T05 apply? inside an example in a new test module
FAIL trust gate unexpectedly accepted V2b-T06 try? inside an example in a new test module
FAIL trust gate unexpectedly accepted V2b-T07 grind? inside an example in a new tooling module
FAIL trust gate unexpectedly accepted V2b-T08 debug.byAsSorry on an example in the production tree
FAIL trust gate unexpectedly accepted V2b-T09 debug.terminalTacticsAsSorry on an example in the production tree
FAIL trust gate unexpectedly accepted V2b-T10 warn.sorry on an example closed by an elaborator in a new test module
FAIL trust gate unexpectedly accepted V2b-T11 warningAsError switched off for an example closed by grind +trace in the production tree
FAIL trust gate unexpectedly accepted V2b-T12 the qualified spelling Lean.reduceBool inside an example in the production tree
FAIL trust gate unexpectedly accepted V2b-T13 the short spelling reduceNat under open Lean in the production tree
PASS planted unreachable test module rejected with the expected diagnostic: is not reachable from the WhatwgTest audit root
PASS trust gate accepted the restored source tree
PASS V2-N1 the axiom gate run narrowly as `lake env lean WhatwgTest.lean`: exit code 0 and a line matching each of [Whatwg module and axiom gate: checked <n> source files and <n> declarations; Classical.choice is reached by <n> of <n> declarations in Whatwg, <n> of <n> in WhatwgTest and <n> of <n> in Gates; strict ceiling propext and Quot.sound over <n> module prefix(es) with <n> exact exception(s); <n> source-token exemption(s)]
PASS V2-N2 the spec coverage gate run narrowly by its relative file name: exit code 0 and a line matching each of [Whatwg spec coverage gate: <n> frozen rows agree with ]
FAIL trust self-test
```

Turning the rows green needs V2b.8, an edit to `WhatwgTest/Audit/AxiomGate.lean`,
which is outside this packet's fence; the breaker seat did not run the gate
with it applied. The evidence the seat has is the scratch scan of V2b.4. Over
the fixtures it reports, for each V2b rejection fixture, exactly its own word
and no other word of the extended list; none for `benign-trust-tokens-v2b.lean.txt`
or any older acceptance fixture; and, among the older rejection fixtures,
`warningAsError` and `sorry` for `token-sorry.lean.txt` and an unchanged word
set for every other one. With V2b.8 applied, the expected run is every row
PASS, the gate line unchanged apart from its counts, and
`0 source-token exemption(s)`; the coordinator records the actual run at
landing.

Before every V2b fixture was planted, each was elaborated on its own from the
scratch directory with `lake env lean -DwarningAsError=true`: exit 0 for all
fourteen, with no message except V2b-T11's two warnings, which its
`set_option warningAsError false in` keeps as warnings. `lake exe citations`
and `lake exe vendorseal` pass at the freeze.

## Addendum V2c (2026-10-01)

Status: FROZEN / RED, V2c breaker seat, 2026-10-01, on branch
`review/v2c-gate-breaker`, based on `cb50951` (the commit that lands ruling
R-V10, which opens this addendum). The addendum is appended; no earlier
sentence of this file is changed. Where it and an earlier section differ, the
addendum governs, and V2c.10 names each place.

Authority: ruling R-V10 at the end of `COORDINATION.md`, from the review
findings B1, B2, B3 and S1 of R-V9. The reviewer found four ways past the gate
at the base that no document declared, each accepted by `lake build`:

- B1: the token pass reads every source with the *final* environment's token
  table, so a longer token a later module declares hides a refused word in an
  earlier source. Measured: `Whatwg/Ecma262/RvDesyncA.lean` with
  `example : (2 : Nat) + 2 = 4 := by (native_decide)` and
  `WhatwgTest/RvDesyncB.lean` with `syntax "(native_decide" : term`, both
  reached from `WhatwgTest.lean`; `lake build` exit 0. The gate reads
  `(native_decide` as one token and never sees the word.
- B2: `decide (config := ⟨false, true, true, false⟩)` turns native evaluation
  on without the word `native`. Every spelling of the configuration value the
  V2c measurement tried evaluates natively (anonymous constructor, `.mk …`,
  `DecideConfig.mk …`, a named value, `{ v with }`, `id …`, `if …`,
  `by exact …`, the escaped key `«config»`, `+kernel` with a `config` item, a
  macro expanding to any of these); `(cfg := …)` is not valid syntax.
- B3: a constant declared in the root `WhatwgTest.lean` itself, and anything
  after the gate command, is never audited, because the gate reads the imported
  modules' data and not the main module's own constants. Measured: a `run_cmd`
  that `addDecl`s an `axiomDecl` of `False` and a `theorem rvRootFalse :
  (1 : Nat) = 2` proved from it, placed before the gate command, build exit 0.
- S1: the gate never checks that every audited environment module maps to a
  source it scanned, so a source the extension test misses is never tokenized.
  Measured: `WhatwgTest/RvCase.LEAN` (uppercase extension) reached as
  `WhatwgTest.RvCase`; on this case-insensitive host the build passes and the
  gate scans 222 sources, not 223.

R-V10 also found that any imported module can replace the gate itself:
`macro_rules | `(#whatwg_streams_axiom_gate) => `(#check 1)` in an audited
module expands the gate command to something else, the build passes, and no
pass runs. The gate is a command inside the tree it audits, so the closure is a
set of rules about what audited code may do, checked from the tokens and the
environment together. The principle R-V10 states: *code in the audited trees
is object-level; it declares no syntax, macro or elaborator and runs no
metaprogram, except in modules named on an exact list.* None of B1, B2, B3 or
S1 invalidates a landed theorem or the strict-ceiling measurement, which rest
on the environment pass; they are gaps in where the gate looks.

A breaker (this seat) freezes the five rules, the fixtures and the plant rows;
a builder implements them in `WhatwgTest/Audit/AxiomGate.lean`; the reviewer
checks the delta. The builder edits none of the files of section 1 or this
addendum's V2c.9.

### V2c.1 Terms and the pass order

The terms of section 2 stand. Three are added.

- *Metaprogramming module*: an audited module named by an exact entry of a new
  list `metaprogrammingModules`, held as data in
  `WhatwgTest/Audit/AxiomGate.lean` beside the two lists of section 10. It is
  the one place where audited code may declare syntax, a macro or an elaborator,
  or run a metaprogram. A listed module is **still bound by every trust word of
  sections 4.2 and V2b.3**: the list relaxes only the metaprogramming-keyword
  refusal of V2c.2 and the environment-registration refusal of V2c.2, and no
  other check.
- *Final token table*: `Parser.Module.updateTokens (Parser.getTokenTable env)`
  at gate time, the table the source passes already tokenize with. *Base
  token*: a token the `lean` binary declares (`Parser.builtinTokenTable`) or a
  token an `Init.*` module declares. *Non-base token*: every other token of the
  final table, including the scoped entries of
  `(Parser.parserExtension.ext.getState env).scopedEntries`.
- *Root*: the module `WhatwgTest.lean`, which runs the gate command last.

The five rules slot into the six-step order of section 3 as follows; the gate
stops after the first step that has any finding, so the order fixes which rule
reports a plant two rules would refuse:

| Step of section 3 | V2c check added |
| --- | --- |
| before step 1 | V2c.5 the root pass (rule 4) |
| 1 module closure | V2c.6 reverse closure (rule 5) |
| 2 modifier pass | *(after it)* V2c.3 token-table hygiene (rule 2), a new pass over the final table |
| 3 environment pass | V2c.2 the environment half of the metaprogramming-module rule (rule 1): a non-listed audited module that registers a token, parser, syntax category, macro or elaborator |
| 4 axiom pass | *(unchanged)* |
| 5 trust-token pass | V2c.2 the token half of rule 1 (metaprogramming keywords outside the list) and V2c.4 the configuration-shape refusal (rule 3) |
| 6 summary line | *(unchanged counts; V2c adds no field)* |

Token-table hygiene (V2c.3) runs before the environment pass on purpose: it is
the last line of defence against a token that shadows a refused word (B1), and
it must fire even when a *listed* module declares that token, which the
environment and token halves of rule 1 permit. So a plant that declares a
shadowing token through `syntax` is reported by V2c.3, not by rule 1.

### V2c.2 Rule 1 — metaprogramming modules

**Statement.** Outside `metaprogrammingModules`, an audited source may not
spell a metaprogramming keyword in code, and an audited module may not register
a token, parser, syntax category, macro or elaborator, whatever spelled the
registration. A listed module may do both and remains bound by every trust word
of sections 4.2 and V2b.3.

**The keyword set.** The token half refuses these keyword atoms (each a token
of the final table in Lean 4.33.1; the gate's tokenizer reads each as an
`atom`, so the `carriedBy` rule of section 4.2, atom-text equality, catches it;
`local` and `scoped` prefixes do not fuse — `local syntax` tokenizes as the
atoms `local` then `syntax`, so refusing the keyword below catches its
`local`/`scoped`-prefixed form too, and `local` and `scoped` themselves are not
refused, since the tree uses `scoped` and `local` legitimately):

- *declaring*: `syntax`, `macro`, `macro_rules`, `elab`, `elab_rules`,
  `notation`, `infix`, `infixl`, `infixr`, `prefix`, `postfix`,
  `declare_syntax_cat`, `binder_predicate`, `declare_simp_like_tactic`,
  `simproc`, `dsimproc`, `simproc_decl`, `dsimproc_decl`, `builtin_simproc`,
  `builtin_dsimproc`, `builtin_simproc_decl`, `builtin_dsimproc_decl`,
  `register_simp_attr`, `register_option`, `register_builtin_option`,
  `register_label_attr`, `register_linter_set`, `register_grind_attr`,
  `register_sym_simp_attr`, `register_parser_alias`, `register_tactic_tag`,
  `register_error_explanation`, `declare_config_elab`,
  `declare_command_config_elab`;
- *running*: `run_cmd`, `run_elab`, `run_meta`, `by_elab`, `#eval`, `#eval!`,
  `initialize`, `builtin_initialize`, `test_extern`.

Measured in 4.33.1 with the gate's tokenizer: every word above is a keyword
`atom`. Four candidates are **not** keyword atoms and so are left to the
environment half (they tokenize as ordinary identifiers): `run_tac`,
`command_elab`, `term_elab`, `tactic`, `init`, `builtin_init`, `syntax_cat`.
Two keyword atoms that would otherwise belong are **excluded** because the tree
uses them as ordinary names, exactly as `stop` and `#guard_msgs` were excluded
in V2b.4: `meta` (the HTML `<meta>` element, always written `«meta»`, is an
identifier `meta`; refusing it would strike every such element) and `deriving`,
`open`, `attribute`, `#guard`, `#guard_msgs`, `#check_failure` (ordinary,
pervasive). The channel they would open is instead closed by the environment
half: `@[command_elab …]`, `deriving`-generated code and the rest register
through an environment extension, which V2c.2's environment half sees whatever
the token was.

Diagnostic fragment, token half (in the message style of section 4.2; a
position may follow):

```text
Whatwg source trust gate: <path> contains an authored `<keyword>` metaprogramming keyword
```

**The environment half.** An audited module not on `metaprogrammingModules` is
refused when it registers, in any environment extension the gate reads, a token,
a parser or parser alias, a syntax category, a macro, or a command/term/tactic
elaborator. The builder maps these to the extensions that hold them
(`Parser.parserExtension` for tokens, parsers and categories; the macro and
`*_elab` attributes for macros and elaborators), attributing each registration
to the module that owns the registering declaration. This half catches a
registration no token spells: `@[command_elab K] def f : CommandElab := …`
spells `command_elab` as an identifier, which the token half does not refuse,
yet registers an elaborator (measured: such a declaration builds exit 0 at the
base and the gate accepts it; V2c-E01).

Diagnostic fragment, environment half:

```text
Whatwg trust gate: module <m> registers a <kind> but is not a listed metaprogramming module
```

with `<kind>` one of `token`, `parser`, `syntax category`, `macro`,
`elaborator`.

**Tree measurement.** Over the 222 audited sources, scanned with the gate's own
tokenizer and the keyword set above, the only code occurrences of any listed
keyword are `elab` in the eight gate-command modules
(`WhatwgTest/Audit/AxiomGate.lean`, `Audit/SpecCoverage.lean`,
`Audit/CensusProfileIdentity.lean`, `Audit/WebIdl/CensusContract.lean`,
`Audit/WebIdl/CensusQ2Contract.lean`, `Audit/Ecma262/CensusContract.lean`,
`Audit/Ecma262/CensusQ2Contract.lean`, `Audit/Ecma262/EcmarkupScanner.lean`)
and `run_cmd` in the two constructive-contract batteries
(`WhatwgTest/Infra/IntegerConstructiveContract.lean`,
`WhatwgTest/Infra/ScalarConstructiveContract.lean`). The environment half's
registrations agree: the audited trees register exactly eight parser
descriptors, the eight `#…` gate commands, each a
`Lean.ParserDescr.symbol "#…_gate"` in one of those eight modules; no
`macro_rules`, `elab_rules`, `notation`, local or scoped syntax, `initialize`,
`#eval`, `run_elab`, `run_meta`, `run_tac`, and no other `run_cmd`. So the list
holds exactly those ten modules. (`deriving` generates `BEq`, `Repr` and
friends in many modules; it registers no syntax, macro or elaborator, only
instances, so the environment half does not refuse it, and `deriving` is not a
refused keyword.)

**The list, its shape and its checks.** `metaprogrammingModules` is a third list
of `WhatwgTest/Audit/AxiomGate.lean`, held as data and written one entry per
line below a frozen anchor comment, exactly as section 10 fixes the other two
lists. The anchor, which the gate carries once and the harness matches after
trimming ASCII whitespace:

```text
-- trust-selftest: metaprogramming-module entries are inserted below this line
```

It stands immediately before the body of the list, so inserting after it a line

```lean
  ⟨`Some.Module, "reason"⟩ ::
```

prepends that entry whatever the others. The element type is a structure (or
product) whose anonymous constructor takes the module's full `Name` then the
reason `String`, the name a single-backtick literal. The gate refuses:

| Condition | Diagnostic fragment (verbatim) |
| --- | --- |
| an entry names a module with no audited source | `Whatwg trust gate: metaprogramming-module entry names missing module <m>` |
| an entry names a module whose source spells no metaprogramming keyword and registers nothing | `Whatwg trust gate: stale metaprogramming-module entry for <m>; its source declares no syntax, macro or elaborator and registers nothing` |
| an entry's reason is empty after trimming ASCII whitespace | `Whatwg trust gate: metaprogramming-module entry for <m> carries no reason` |
| an entry is listed twice | `Whatwg trust gate: metaprogramming-module entry for <m> is listed more than once` |
| an entry names an entry point under `whatwgbin/` | `Whatwg trust gate: metaprogramming-module entry for <m> names an entry point under whatwgbin/, which cannot be a metaprogramming module` |

At the freeze the list holds the ten modules above, each with its reason; it has
no missing, stale, blank, duplicate or `whatwgbin/` entry.

### V2c.3 Rule 2 — token-table hygiene

**Statement (R-V10(2)).** Every non-base token of the final table must be
*inert*. The inert test is a decision procedure over the token's characters
`t`, using `Lean.isIdFirst`/`isIdRest` for identifier boundaries and the word
lists of sections 4.2 and V2b.3 (`refusedWords` as printed; the modifier words
`unsafe`, `partial`; and the last-component words `sorryAx`, `Lean.reduceBool`,
`Lean.reduceNat` and the three forbidden axioms). `t` is inert unless any holds:

- *(T1)* `t` contains a space, tab, carriage return, line feed, `"`, `«`, `»`,
  `--`, `/-` or `-/`;
- *(T2)* `t` ends in `-` or `/`; or `t` has a `'` at a position that is index 0
  or is preceded by a non-`isIdRest` character (a character-literal opener); or
  `t` begins a raw-string literal, i.e. an `r` at index 0 that `isIdFirst`-starts
  an identifier `r` whose next character is `#` or `"`;
- *(T3)* some identifier starts inside `t` — at index 0, or after a non-`isIdRest`
  character, or after a prefix of `t` that ends in a non-`isIdRest` character the
  token table splits on — and that identifier, read to where it meets a
  non-identifier character or the end of `t`, either **equals** a refused word, a
  refused last component, or a modifier keyword; or, when it runs to the end of
  `t` (so the next source character could extend it), is a **prefix** of one of
  those cut short by the token's end.

A builder implements T3 by walking each index `k` of `t`, and where an
identifier may begin there, reading its `Name` (escapes do not occur inside a
registered token) and testing equality against the whole-name words and the
last component against the last-component words; when the read reaches the end of
`t`, it also tests `isPrefixOf` against every such word, because the source
character after the token could continue the identifier and complete the word.
A token that begins no refused identifier, contains no forbidden character and
does not end in `-` or `/` is accepted.

**Measurement.** The final table holds 512 tokens (574 with the scoped entries);
239 are built into the binary and 277 are declared by `Init` modules, leaving
127 non-base tokens. All 127 pass the inert test today. Eight tokens of the
table contain a refused word as a substring and all pass, which fixes the
boundary logic:

- `axiom`, `sorry`, `unsafe`, `partial` — base keywords; each *equals* the
  word (for `axiom` and `sorry`) or the modifier word (`unsafe`, `partial`), so
  each is a hazard by T3, but each is a **base** token, which the rule does not
  test. The rule tests non-base tokens only; the words themselves are refused in
  *code* by the trust-token and modifier passes, not in the table.
- `partial_fixpoint` (non-base) — the identifier at index 0 reads to
  `partial_fixpoint`, which neither equals nor is a prefix of `partial`
  (`partial` is a prefix of it, not it of `partial`); no identifier starts at
  the `f` of `_fixpoint` because `_` is `isIdRest`. Inert.
- `test_extern` (non-base) — the whole-token identifier is `test_extern`, not
  `extern`; the `e` of `extern` is preceded by `_` (`isIdRest`), so no
  identifier starts there. Inert.
- `register_try?_tactic` (non-base) — the whole-token identifier is
  `register_try?_tactic`; `try?` is not at an identifier boundary (`try` is
  preceded by `_`). Inert.
- `#whatwg_streams_axiom_gate` (non-base) — `axiom` is preceded by `_`, not an
  identifier start. Inert.

Two base tokens would fail the inert test and are exempt as toolchain tokens,
outside the rule's scope: the scoped `#'` (`BitVec`, a character-literal quote
at index 1, T2) and `#reduce` (`Init.Notation`, whose last component `reduce` is
a prefix of `reduceBool` and `reduceNat`, T3). They are base tokens, which the
rule does not test; the rule covers the 127 non-base tokens only.

Diagnostic fragment:

```text
Whatwg source trust gate: token `<tok>` of the final token table is not inert: <reason>
```

### V2c.4 Rule 3 — configuration shape

**Statement (R-V10(3)).** Wherever the token `(` is immediately followed by an
identifier whose `Name`, with `«»` escapes removed, is `config`, and then the
token `:=`, the value that follows must be a plain literal brace group: the next
token is `{`, the brace group it opens contains no `with` token, and the token
immediately after the matching `}` is `)`. Any other shape is refused. The
escaped key `«config»` is treated as `config` (measured: `decide («config» :=
…)` tokenizes the key as the identifier `config` and evaluates natively, so it
must be caught). This is a syntactic backstop to the `native` word of section
4.2: it refuses `(config := ⟨…⟩)` and every non-brace or `with`-bearing value by
which B2 turns native evaluation on without the word `native`.

**Measurement.** The tree has 35 `(config := …)` sites, all exactly
`simp (config := { zetaDelta := true })` — a plain `{ … }` group, no `with`,
`)` after — which the rule accepts. Every B2 spelling the seat tried
(anonymous constructor, `.mk`, a named value, `{ v with }`, `id …`, `if …`,
`by exact …`, the escaped key) is refused, because its value either does not
open with `{` or opens a group containing `with`. The gate's existing
`simp (config := { zetaDelta := true })` sites and the one
`simp_all (maxDischargeDepth := 4)` (whose key is not `config`) are untouched;
`decide +kernel` carries no `config` token.

Diagnostic fragment (one line, a reason after the colon says which of the three
shape conditions failed — the value does not open with `{`, its brace group
contains `with`, or `)` does not follow the closing `}`):

```text
Whatwg source trust gate: <path> contains a non-literal `config` option
```

### V2c.5 Rule 4 — the root

**Statement (R-V10(4)).** The root `WhatwgTest.lean` holds only imports,
comments, module documentation and one command, `#whatwg_streams_axiom_gate`,
which is its last command; and at gate time the main module `WhatwgTest` has
declared no constant. The gate checks all three: tokenizing its own root source
(every code token is part of an `import` line or is the single gate-command
token), confirming the gate command is the last command, and reading the main
module's own constants (`env.constants.map₂`), which must be empty.

**Measurement.** The root's only code token outside its `import` lines is
`#whatwg_streams_axiom_gate`, and `env.constants.map₂` is empty when the gate
runs (0 constants; 2563 modules in the environment). This closes B3: a constant
`addDecl`ed in the root, or a declaration after the gate command, is one the
environment pass never audits.

Diagnostic fragments:

```text
Whatwg axiom gate: the root WhatwgTest.lean contains a command other than imports and #whatwg_streams_axiom_gate
Whatwg axiom gate: #whatwg_streams_axiom_gate is not the last command of the root
Whatwg axiom gate: the root module WhatwgTest has declared a constant when the gate runs; the root must declare none
```

### V2c.6 Rule 5 — reverse closure

**Statement (R-V10(5)).** Every environment module whose name is under an
audited tree prefix maps, by exact case-sensitive path through
`Lean.modToFilePath`, to exactly one source the gate scanned. Section 3's module
closure already refuses a scanned source no module imports; this is the reverse
direction, refusing an audited environment module no scanned source backs. It
closes S1: a source the extension filter (`path.extension == some "lean"`,
case-sensitive) misses — a `.LEAN` file on a case-insensitive host — is in the
environment but not in the scan.

**Measurement.** All 216 audited environment modules map to exactly one scanned
source by exact path today.

Diagnostic fragment:

```text
Whatwg module-closure gate: module <m> is in the environment under an audited prefix but maps to no scanned source
```

On a case-sensitive host (Linux) the S1 construction never reaches the gate:
Lake refuses `import WhatwgTest.RvCase` for `RvCase.LEAN` with `bad import`, a
build error before elaboration. So S1 is refused on every host — by Lake on a
case-sensitive one, by this rule on a case-insensitive one. It is frozen as a
review clause (V2c.8 R-C4), not a portable plant.

### V2c.7 Claim scope (extends sections 13 and V2b.6)

A green `lake exe whatwg_trustselftest` with the V2c rows says each V2c plant is
refused or accepted for its stated reason on Lean 4.33.1. In addition to
sections 13 and V2b.6, it does not say the following; each item names which
assurance route still catches it.

- **A dependency package's syntax and macros.** A `syntax`, `macro` or elaborator
  defined in a pinned dependency (`hash`, and core/`Std`/`Lean`) is not in an
  audited source and not refused; rule 1 governs audited modules only.
  Dependencies are pinned by digest and gated in their own repositories
  (`docs/PROVENANCE.md`). Nothing in this gate re-audits them; the
  `leanchecker` CI replay (`lake env leanchecker Whatwg WhatwgTest WhatwgGates`)
  re-checks every *audited* declaration in the kernel but does not police a
  dependency's metaprogramming.
- **The toolchain's own scoped tokens `#'` and `#reduce`.** They fail the inert
  test but are base tokens, which rule 2 does not test. A dependency or the
  toolchain could add another non-inert base token; the rule would not see it,
  because "base" is exactly "declared by the binary or an `Init` module". Only a
  reader of the toolchain, not this gate, catches a toolchain token that shadows
  a refused word. Neither CI replay nor the self-test catches this; it is a
  bounded trust in the pinned toolchain, recorded here.
- **A listed metaprogramming module misusing the Meta API.** The ten listed
  modules may run `MetaM`/`CommandElabM`/`IO` at elaboration and could, in
  principle, `addDecl` with the kernel check off, assign a goal through
  `Lean.MVarId.admit`, or build `sorryAx` from a name literal — none spelled by a
  refused word (V2b.6). The list is short and every entry is reviewed; a change
  to any listed module is a reviewer's item. Of these, a declaration added with
  the kernel check off (`addDeclCore … (doCheck := false)`, debt D55) is caught
  only by the `leanchecker` CI replay, not by `lake build` or the self-test; the
  others reach Lean's "declaration uses `sorry`" warning, which
  `warningAsError = true` turns into an error at build (V2b.6), a check this gate
  does not itself make.
- **Options passed outside the source.** `-D`, `leanOptions`, `moreLeanArgs` in
  `lakefile.toml`, or a metaprogram's `withOptions`/`modifyScope` can set
  `debug.skipKernelTC`, `warningAsError`, `warn.sorry`, `debug.byAsSorry` and the
  rest without a source token (sections 13 and V2b.6). The token passes are
  lexical and see none of them. A false statement admitted through
  `debug.skipKernelTC` set this way, or a declaration added with the kernel check
  off, is caught only by the `leanchecker` replay. `warningAsError` set to
  `false` outside the source re-enables the goal-admitting spellings of V2b; no
  pass catches that, and the self-test does not run with it.
- **A name built by metaprogramming**, inside a listed module or a dependency
  (`Lean.mkIdent`, `Name.mkStr`, concatenation), reaches `Lean.reduceBool`,
  `sorryAx` or another channel without a source token (section 13). The token
  passes do not see it; the axiom pass catches what it leaves as a reachable
  forbidden axiom in an audited constant, and the `leanchecker` replay catches a
  kernel-unchecked result.
- **B1 through a listed module.** Rule 2 (token-table hygiene) is the backstop
  here: a *listed* module may declare syntax, but a token it declares that
  shadows a refused word is still refused by rule 2, which tests the table
  whoever filled it. A listed module could still declare an inert token that is
  later composed in source to hide a word across token boundaries; the token
  passes read token by token and do not compose, a lexical limit sections 13 and
  V2b.7 already state.

Summary of routes: the `leanchecker` CI replay catches a kernel-unchecked
declaration and a false statement from `debug.skipKernelTC`/`reduceBool` however
the option or name was introduced; the trust self-test catches every lexical and
registration rule of V2/V2b/V2c on the audited sources and environment; nothing
in this repository catches a non-inert *base* token the pinned toolchain ships,
a dependency's own metaprogramming, or an option set outside the audited
sources — these are bounded trust in the pins and the host, recorded here and
not claimed closed.

### V2c.8 Review clauses (not planted)

Checked by the independent reviewer, because planting would need a seam in the
gate, a red acceptance row, or a host-specific file.

- R-C1. A listed metaprogramming module is accepted: its metaprogramming
  keywords and its registrations are admitted, and only by rule 1, and it is
  still refused for any trust word of section 4.2 or V2b.3. Not planted for the
  reason section 12 R2 gives: an acceptance row that needs the new anchor is red
  until the builder lands, and this packet's red state is fixed to rejection
  rows. The ten listed modules are the live witnesses: the gate accepts the
  unmodified tree, in which `elab` and `run_cmd` appear only there.
- R-C2. Token-table hygiene accepts the 127 non-base tokens of the unmodified
  tree (the step-0 build is the witness) and the inert test's decision procedure
  is the one V2c.3 states; the builder's implementation is checked against the
  measurement, not re-planted per token.
- R-C3. The summary line of section 7 is unchanged: V2c adds no field, and the
  three tree counts still sum to the declaration count.
- R-C4. S1 is refused on every host (V2c.6): `bad import` on a case-sensitive
  host, the reverse-closure diagnostic on a case-insensitive one. Not planted,
  because the plant is a `.LEAN` source whose behaviour is host-specific and the
  harness has no portable extension mechanism; the reviewer confirms the rule on
  this host and reads the Linux path.
- R-C5. The environment half of rule 1 attributes each registration to the
  module that owns the registering declaration, and the unmodified tree's only
  registrations are the eight gate-command parser descriptors, in listed
  modules. A registration the builder's extension map misses would be an
  under-refusal the next such registration exposes; V2c-E01 plants one concrete
  token-invisible registration (`@[command_elab …]`) to anchor the map.

### V2c.9 Plants

Breaker-owned and frozen by this addendum, beside the files of section 1 and
V2b.7: this addendum; the fixtures `test/fixtures/trust-gate/v2c-*.lean.txt`
named below; and the rows of `acceptancePlants` and `rejectionPlants` in
`WhatwgGates/TrustSelfTest.lean` whose labels begin `V2c-`, appended to each
table with `++`, together with the selector `metaprogrammingModuleAnchor`, the
root-gate constant `rootGateCommand`, the `Placement.beforeRootGate`
constructor and the one line it adds to `Edit.apply`. Every earlier line of the
harness is unchanged. The coordinator applies rules 1 through 5 in
`WhatwgTest/Audit/AxiomGate.lean` and edits none of these files.

Placement as in section 9, plus `beforeRootGate`: insert the fixture's lines
immediately before the root's `#whatwg_streams_axiom_gate` line. Every plant is
undone before the next. Fragments are substrings of the build output. The
`V2c-` labels are stable identifiers, never reused, and not registered in
`test/counterexamples/REGISTER.md` (section 1). No module is red, so
`test/fixtures/trust-gate/known-red.txt` gains no entry.

Acceptance plants (the build must succeed):

| ID | Fixture | Target, placement | State at the freeze |
| --- | --- | --- | --- |
| V2c-A1 | `v2c-config-control.lean.txt` | `Whatwg.lean`, append | green |
| V2c-A2 | `v2c-benign.lean.txt` | `Whatwg.lean`, append | green |

Rejection plants (the build must fail and print the fragment). "Reason" names
the rule; "expected" is the fragment any one of which proves the rejection:

| ID | Fixture | Target, placement; further edit | Expected fragment(s) |
| --- | --- | --- | --- |
| V2c-M01 | `v2c-meta-notation-prod.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains an authored `notation` metaprogramming keyword``; or `module Whatwg registers a` |
| V2c-M02 | `v2c-meta-run-cmd-test.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``TrustSelfTestPlant.lean contains an authored `run_cmd` metaprogramming keyword`` |
| V2c-M03 | `v2c-meta-gate-macro-rules.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``TrustSelfTestPlant.lean contains an authored `macro_rules` metaprogramming keyword``; or `registers a macro but is not a listed metaprogramming module` |
| V2c-E01 | `v2c-meta-attr-command-elab.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | `registers an elaborator but is not a listed metaprogramming module` |
| V2c-B1 | `v2c-token-shadow-decl.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module; new module `Whatwg/Ecma262/TrustSelfTestPlant.lean` from `v2c-token-shadow-use.lean.txt` | ``token `(native_decide` of the final token table is not inert``; or ``contains an authored `syntax` metaprogramming keyword`` |
| V2c-T1 | `v2c-token-cut-word.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``token `(nat` of the final token table is not inert`` |
| V2c-T2 | `v2c-token-comment-opener.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``of the final token table is not inert`` |
| V2c-T3 | `v2c-token-hidden-native.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``token `+native` of the final token table is not inert`` |
| V2c-C1 | `v2c-config-anon-ctor.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains a non-literal `config` option`` |
| V2c-C2 | `v2c-config-with.lean.txt` | `WhatwgTest/TrustSelfTestPlant.lean`, new module | ``TrustSelfTestPlant.lean contains a non-literal `config` option`` |
| V2c-C3 | `v2c-config-escaped-key.lean.txt` | `Whatwg.lean`, append | ``Whatwg.lean contains a non-literal `config` option`` |
| V2c-R1 | `v2c-root-before-gate.lean.txt` | `WhatwgTest.lean`, before the gate | `the root WhatwgTest.lean contains a command other than imports and #whatwg_streams_axiom_gate`; or `the root module WhatwgTest has declared a constant when the gate runs` |
| V2c-R2 | `v2c-root-after-gate.lean.txt` | `WhatwgTest.lean`, append | `#whatwg_streams_axiom_gate is not the last command of the root`; or `the root WhatwgTest.lean contains a command other than imports and #whatwg_streams_axiom_gate` |
| V2c-L1 | `v2c-meta-module-missing.lean.txt` | `WhatwgTest/Audit/AxiomGate.lean`, after the metaprogramming anchor | `metaprogramming-module entry names missing module WhatwgTest.TrustSelfTestPlantMissing` |
| V2c-L2 | `v2c-meta-module-stale.lean.txt` | the same anchor; new module `WhatwgTest/TrustSelfTestPlant.lean` from `strict-choice.lean.txt` | `stale metaprogramming-module entry for WhatwgTest.TrustSelfTestPlant; its source declares no syntax, macro or elaborator and registers nothing` |
| V2c-L3 | `v2c-meta-module-blank.lean.txt` | the same anchor; new module `WhatwgTest/TrustSelfTestPlant.lean` from `strict-choice.lean.txt` | `metaprogramming-module entry for WhatwgTest.TrustSelfTestPlant carries no reason` |

Why each plant is shaped as it is:

- V2c-M01 uses `notation` (a core keyword needing no import) so the production
  root builds at the base; it is caught by the token half, and by the
  environment half for the parser it registers, so two fragments are admitted.
- V2c-M02 uses `run_cmd`, which registers nothing, so only the token half
  applies and one fragment names it. V2c-M03's `macro_rules` suppresses the gate
  at the base (build exit 0, no summary line), which is exactly the
  gate-replacement hole; it imports the gate module to name its command syntax.
- V2c-E01 is the registration no token spells: `@[command_elab K]` on a no-op
  `CommandElab`, `command_elab` an identifier. It targets
  `Lean.Parser.Command.check`, a command the plant module does not invoke, so it
  builds exit 0 and perturbs nothing.
- V2c-B1 declares `(native_decide` in a test module and uses it in a new
  production module under `Whatwg.Ecma262`; the `example` leaves no constant, so
  only the token-table hygiene rule (or rule 1's `syntax` keyword) refuses it.
  Token-table hygiene runs before rule 1 (V2c.1), so the inert-failure fragment
  is the expected one, with the keyword fragment admitted as the backstop.
- V2c-T1 declares `(nat`, which cuts the word `native` short at the token's end;
  V2c-T2 declares a token containing `/-`, a comment opener; V2c-T3 declares
  `+native`, hiding the whole word `native`. Each is a non-inert token in the
  table with no bare refused word in code, caught only by rule 2.
- V2c-C1, C2 and C3 are B2 spellings: the anonymous constructor, the `{ v with }`
  record update (in a test module that imports `Lean` for `DecideConfig`), and
  the escaped key `«config»`. Each `example` leaves no constant, so only the
  configuration-shape rule refuses it.
- V2c-R1 inserts a `run_cmd`-added axiom and a false theorem before the gate in
  the root; V2c-R2 appends a declaration after the gate. Each is unaudited at the
  base (B3) and refused by the root pass.
- V2c-L1, L2 and L3 exercise the metaprogramming-module list's checks; like the
  other two lists' checks (V2-S3 to S6, V2-X1, V2-X2) they cannot plant until the
  builder adds the anchor, so at the freeze each fails to plant.

### V2c.10 Changes to earlier sections

- Section 3's pass order: V2c.1 inserts the root pass before step 1, reverse
  closure into step 1, token-table hygiene after step 2, the environment half of
  rule 1 into step 3, and the token half of rule 1 and the configuration-shape
  rule into step 5. No existing step's checks move.
- Section 13, the bullet "a name built by metaprogramming … are invisible to the
  token pass": still true, and V2c.7 says which route catches each residual.
- Sections 8 and V2b.5 hold for every row that predates this addendum: none is
  changed, and each older fixture is expected to stay green, since no new keyword
  of V2c.2, no non-inert token, no `(config := …)` and no root or reverse-closure
  condition appears in it. (The 35 existing `simp (config := { zetaDelta := true
  })` sites and the eight gate-command modules and two `run_cmd` batteries are
  the measured reason the unmodified tree still passes.)

### V2c.11 Red state and freeze run

`lake build` is green on the base tree with this packet (it adds fixtures and
harness rows only). `lake exe whatwg_trustselftest` fails, and fails exactly on
the `V2c-` rejection rows: V2c-M01, M02, M03, E01, B1, T1, T2, T3, C1, C2, C3,
R1 and R2 each "unexpectedly accepted" (the base gate has none of rules 1
through 5), and V2c-L1, L2 and L3 each "could not plant" (the metaprogramming
anchor does not exist yet). V2c-A1, V2c-A2, every V2/V2b row and both narrow
runs pass. The full listing is recorded below. Turning the `V2c-` rows green
needs the builder's rules 1 through 5 in `WhatwgTest/Audit/AxiomGate.lean`,
outside this packet's fence; the breaker did not run the gate with them applied.

Recorded on Windows 11, Lean 4.33.1, at the freeze tree, after a full build:
`lake build` exit 0, 386 jobs, its gate line `checked 222 source files and 16497
declarations; ... 0 source-token exemption(s)`; then `lake exe whatwg_trustselftest`
exit 1 in 525 s. Its result lines, in the order the harness checks them (in a
captured log the standard-output lines follow the standard-error lines, as
section 15 says), are 65 PASS and 17 FAIL: the 63 checks of the base and the two
V2c acceptance rows pass, exactly the sixteen V2c rejection rows fail, and the
last line is the summary:

```text
PASS declared red set matches the observed red set (0 module(s))
PASS trust gate accepted the unmodified source tree (the step-0 build)
PASS trust gate accepted comments, strings, and numeric projections
PASS trust gate accepted V2-A1 refused trust words in comments, documentation, strings and name literals, and identifiers that only contain them
PASS trust gate accepted V2-A2 an opaque with an authored body in the production tree
PASS trust gate accepted V2-S2 a theorem reaching Classical.choice in a new module under WhatwgTest
PASS trust gate accepted V2b-A1 the added trust words in comments, documentation, strings and name literals, identifiers that only contain them, a local named stop, an ordinary set_option, and #guard_msgs around #check_failure
PASS trust gate accepted V2c-A1 the one configuration shape the tree uses, simp (config := { zetaDelta := true })
PASS trust gate accepted V2c-A2 the new keywords and the identifier config in comments, strings, longer identifiers and an ordinary parameter
PASS planted partial declaration rejected with the expected diagnostic: contains an authored `partial` declaration modifier
PASS planted unsafe declaration rejected with the expected diagnostic: contains an authored `unsafe` declaration modifier
PASS planted sorry in the production tree rejected with the expected diagnostic: declaration uses `sorry`
PASS planted native_decide in the production tree rejected with the expected diagnostic: (native_decide auxiliary)
PASS planted malformed string literal rejected
PASS planted malformed raw string literal rejected
PASS planted malformed decimal literal rejected
PASS planted unterminated comment rejected
PASS planted V2-E1 an axiom added through Lean.addDecl in a new test module rejected with the expected diagnostic: declaration plantedDeclaredAxiom is an axiom; no audited tree declares one
PASS planted V2-E2 a declared axiom in the production tree rejected with the expected diagnostic: declaration plantedProductionAxiom is an axiom; no audited tree declares one
PASS planted V2-E3 @[extern] attached through the attribute API in a new test module rejected with the expected diagnostic: declaration plantedExternTarget is `@[extern]`
PASS planted V2-E4 @[implemented_by] attached through the attribute API in a new test module rejected with the expected diagnostic: declaration plantedImplementedTarget is `@[implemented_by]`
PASS planted V2-E5 @[implemented_by] under its escaped name in the production tree rejected with the expected diagnostic: declaration plantedEscapedTarget is `@[implemented_by]`
PASS planted V2-E6 an opaque with no body in the production tree rejected with the expected diagnostic: declaration plantedBodylessOpaque is an `opaque` with no authored body
PASS planted V2-E7 a parameterised opaque with no body in a new tooling module rejected with the expected diagnostic: declaration plantedParameterisedOpaque is an `opaque` with no authored body
PASS planted V2-T01 native_decide inside an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `native_decide` trust token
PASS planted V2-T02 bv_decide inside an example in a new test module rejected with the expected diagnostic: TrustSelfTestPlant.lean contains an authored `bv_decide` trust token
PASS planted V2-T03 bv_decide? inside a tactic quotation in a new test module rejected with the expected diagnostic: TrustSelfTestPlant.lean contains an authored `bv_decide?` trust token
PASS planted V2-T04 bv_check inside a tactic quotation in a new test module rejected with the expected diagnostic: TrustSelfTestPlant.lean contains an authored `bv_check` trust token
PASS planted V2-T05 decide +native inside an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `native` trust token
PASS planted V2-T06 decide (native := true) inside an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `native` trust token
PASS planted V2-T07 sorry inside an example with warningAsError switched off rejected with the expected diagnostic: Whatwg.lean contains an authored `sorry` trust token
PASS planted V2-T08 axiom inside a command quotation in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `axiom` trust token
PASS planted V2-T09 extern inside a command quotation in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `extern` trust token
PASS planted V2-T10 implemented_by inside a command quotation in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `implemented_by` trust token
PASS planted V2-T11 debug.skipKernelTC on a theorem in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `debug.skipKernelTC` trust token
PASS planted V2-T12 the escaped spelling of debug.skipKernelTC in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `debug.skipKernelTC` trust token
PASS planted V2-T13 the qualified spelling Lean.ofReduceBool in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `Lean.ofReduceBool` trust token
PASS planted V2-T14 the short spelling ofReduceNat under open Lean in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `Lean.ofReduceNat` trust token
PASS planted V2-T15 the spelling _root_.Lean.trustCompiler in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `Lean.trustCompiler` trust token
PASS planted V2-T16 native_decide inside an example in a new tooling module rejected with the expected diagnostic: TrustSelfTestToolingPlant.lean contains an authored `native_decide` trust token
PASS planted V2-T17 native_decide inside an example in an entry point under bin/ rejected with the expected diagnostic: Citations.lean contains an authored `native_decide` trust token
PASS planted V2-S1 a theorem reaching Classical.choice in a new module under Whatwg.Ecma262 rejected with the expected diagnostic: declaration TrustSelfTestPlant.plantedChoice reaches Classical.choice under the strict ceiling of Whatwg.Ecma262
PASS planted V2-S3 a strict-ceiling exception naming no declaration rejected with the expected diagnostic: strict-ceiling exception names missing declaration TrustSelfTestPlant.plantedMissing
PASS planted V2-S4 a strict-ceiling exception naming a declaration that reaches no Classical.choice rejected with the expected diagnostic: stale strict-ceiling exception for TrustSelfTestPlant.plantedChoiceFree; it does not reach Classical.choice
PASS planted V2-S5 a strict-ceiling exception naming a declaration under no strict prefix rejected with the expected diagnostic: stale strict-ceiling exception for TrustSelfTestPlant.plantedChoice; its module WhatwgTest.TrustSelfTestPlant is under no strict prefix
PASS planted V2-S6 a strict-ceiling exception whose reason is blank rejected with the expected diagnostic: strict-ceiling exception for TrustSelfTestPlant.plantedChoice carries no reason
PASS planted V2-X1 a source-token exemption for a module that names no refused token rejected with the expected diagnostic: stale source-token exemption for WhatwgTest.TrustSelfTestPlant; its source contains no refused token
PASS planted V2-X2 a source-token exemption naming no module rejected with the expected diagnostic: source-token exemption names missing module WhatwgTest.TrustSelfTestPlantMissing
PASS planted V2b-T01 sorryAx inside an example whose messages #guard_msgs drops, in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `sorryAx` trust token
PASS planted V2b-T02 the spelling _root_.sorryAx in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `sorryAx` trust token
PASS planted V2b-T03 the admit tactic inside an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `admit` trust token
PASS planted V2b-T04 the impossible tactic inside an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `impossible` trust token
PASS planted V2b-T05 apply? inside an example in a new test module rejected with the expected diagnostic: TrustSelfTestPlant.lean contains an authored `apply?` trust token
PASS planted V2b-T06 try? inside an example in a new test module rejected with the expected diagnostic: TrustSelfTestPlant.lean contains an authored `try?` trust token
PASS planted V2b-T07 grind? inside an example in a new tooling module rejected with the expected diagnostic: TrustSelfTestToolingPlant.lean contains an authored `grind?` trust token
PASS planted V2b-T08 debug.byAsSorry on an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `debug.byAsSorry` trust token
PASS planted V2b-T09 debug.terminalTacticsAsSorry on an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `debug.terminalTacticsAsSorry` trust token
PASS planted V2b-T10 warn.sorry on an example closed by an elaborator in a new test module rejected with the expected diagnostic: TrustSelfTestPlant.lean contains an authored `warn.sorry` trust token
PASS planted V2b-T11 warningAsError switched off for an example closed by grind +trace in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `warningAsError` trust token
PASS planted V2b-T12 the qualified spelling Lean.reduceBool inside an example in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `Lean.reduceBool` trust token
PASS planted V2b-T13 the short spelling reduceNat under open Lean in the production tree rejected with the expected diagnostic: Whatwg.lean contains an authored `Lean.reduceNat` trust token
FAIL trust gate unexpectedly accepted V2c-M01 a declaring metaprogramming keyword (notation) in the production tree
FAIL trust gate unexpectedly accepted V2c-M02 a running metaprogramming keyword (run_cmd) in a new test module
FAIL trust gate unexpectedly accepted V2c-M03 a macro_rules that replaces the gate command, in a new test module
FAIL trust gate unexpectedly accepted V2c-E01 an elaborator registered through @[command_elab], a token no source spells
FAIL trust gate unexpectedly accepted V2c-B1 a shadow token (native_decide hiding the word native_decide from the gate
FAIL trust gate unexpectedly accepted V2c-T1 a token that cuts a refused word short ((nat begins native)
FAIL trust gate unexpectedly accepted V2c-T2 a token that hides a comment opener (rvV2cTok/-)
FAIL trust gate unexpectedly accepted V2c-T3 a token that hides a whole refused word (+native)
FAIL trust gate unexpectedly accepted V2c-C1 the native flag through a config anonymous constructor in the production tree
FAIL trust gate unexpectedly accepted V2c-C2 the native config through a { v with } record update in a new test module
FAIL trust gate unexpectedly accepted V2c-C3 the escaped key «config» in the production tree
FAIL trust gate unexpectedly accepted V2c-R1 a false axiom and theorem in the root, before the gate command
FAIL trust gate unexpectedly accepted V2c-R2 a declaration after the gate command in the root
FAIL could not plant V2c-L1 a metaprogramming-module entry naming no module: <probe>\WhatwgTest\Audit\AxiomGate.lean: the anchor line `-- trust-selftest: metaprogramming-module entries are inserted below this line` occurs 0 time(s); exactly one is required
FAIL could not plant V2c-L2 a metaprogramming-module entry whose module declares no metaprogramming: <probe>\WhatwgTest\Audit\AxiomGate.lean: the anchor line `-- trust-selftest: metaprogramming-module entries are inserted below this line` occurs 0 time(s); exactly one is required
FAIL could not plant V2c-L3 a metaprogramming-module entry whose reason is blank: <probe>\WhatwgTest\Audit\AxiomGate.lean: the anchor line `-- trust-selftest: metaprogramming-module entries are inserted below this line` occurs 0 time(s); exactly one is required
PASS planted unreachable test module rejected with the expected diagnostic: is not reachable from the WhatwgTest audit root
PASS trust gate accepted the restored source tree
PASS V2-N1 the axiom gate run narrowly as `lake env lean WhatwgTest.lean`: exit code 0 and a line matching each of [Whatwg module and axiom gate: checked <n> source files and <n> declarations; Classical.choice is reached by <n> of <n> declarations in Whatwg, <n> of <n> in WhatwgTest and <n> of <n> in WhatwgGates; strict ceiling propext and Quot.sound over <n> module prefix(es) with <n> exact exception(s); <n> source-token exemption(s)]
PASS V2-N2 the spec coverage gate run narrowly by its relative file name: exit code 0 and a line matching each of [Whatwg spec coverage gate: <n> frozen rows agree with ]
FAIL trust self-test
```

A first run of this freeze reported V2c-M02 `rejected ... for an unexpected
reason`: its fixture's `run_cmd` needed `import Lean.Elab.Command`, so the module
did not build at the base. The fixture was repaired, not the expectation, and
the run above is the repaired one; every V2c rejection row now fails only because
the base gate lacks rules 1 through 5 or the metaprogramming anchor.
`lake exe whatwg_citations` and `lake exe whatwg_vendorseal` pass at the freeze.
