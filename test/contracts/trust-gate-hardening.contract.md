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
