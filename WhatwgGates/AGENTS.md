# Gates tooling routing

This boundary contains the repository's gates implemented in Lean: the digest
face of the required `hash` package, the vendor seal, the internal-citation
gate, the trust gate's library, configuration and executable, the trust
self-test in its two runs, the census, the URL inventory and census, the two schema
projections, of the HTML Standard and of SVG 2, the grammar gate of SVG 2's path data, and the
gate of the four productions of XML 1.0 that the XML serialization cites. It is
the sixth authored router because this tree has a distinct trust boundary
from the other five: it is tooling that reads files, spawns processes, and
produces projections. The axiom gate audits it like every other tree, under
ruling R-11's ceiling; no strict prefix of ruling R-V1 covers it.

Since ruling R-V3(c) the modules are `WhatwgGates.*`, the executable entry
points are `whatwgbin.*` under `whatwgbin/`, and every executable name carries
the `whatwg_` prefix, so that a package requiring this one can keep its own
`Gates.*` modules, `bin.*` roots and unprefixed executables
(`docs/AGENT-ROUTING.md`, "Packages cloned from this skeleton"). The
declarations keep the namespace `Gates.*`: `Gates.Census.cli` lives in the
module `WhatwgGates.Census`.

## Why the gates are Lean

Every check that decides whether the tree is green runs under the same
toolchain as the proofs and is itself audited by the axiom gate. A gate is
never a shell one-liner whose behaviour differs between hosts. Shell and
PowerShell files, where they exist, only orchestrate `lake exe` invocations;
they decide nothing.

## Rules

- No semantic declaration lives here. A definition that models the
  specification belongs under `Whatwg/Streams/` behind a contract.
- Totality holds: no `partial`, no `unsafe`. Loops are bounded by fuel or by
  the structure they traverse.
- The ceiling is `propext`, `Quot.sound`, and `Classical.choice`, the same
  as every other tree since ruling R-11; ruling R-V1 keeps this tree off the
  strict list. `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, and
  `Lean.trustCompiler` remain forbidden.
- Since ruling R-V2 the axiom gate's environment pass refuses here, as in
  every audited tree, a declared `axiom`, an `@[extern]` or
  `@[implemented_by]` declaration, and an `opaque` with no authored body; its
  token pass refuses, in code, the trust words no constant records (section
  4.2 of `test/contracts/trust-gate-hardening.contract.md`), in every file
  under `WhatwgGates/` and `whatwgbin/` alike. Write such a word in a comment or a string
  literal, never as code.
- No module here is a metaprogramming module (addendum V2c, ruling R-V10), and
  no file under `whatwgbin/` can be one, so the gate also refuses here a
  metaprogramming keyword in code (`syntax`, `macro`, `elab`, `notation`,
  `run_cmd`, `#eval`, `initialize` and the rest of V2c.2) and a module that
  registers a token, parser, syntax category, macro, elaborator or initializer.
  A tool runs as an executable or as an ordinary function a listed test module
  calls; it declares no syntax of its own.
- The trust gate's passes live here, in the gate library
  `WhatwgGates/Trust/*.lean`, namespace `Gates.Trust` (addendum V2e.3 of
  `test/contracts/trust-gate-hardening.contract.md`, ruling R-W7(a)). Two judges
  call `Gates.Trust.runPasses`: the in-tree command `#whatwg_streams_axiom_gate`
  of `WhatwgTest/Audit/AxiomGate.lean`, with the reads only an elaborating
  process can make, and the executable gate `lake exe whatwg_trustgate`
  (addendum V2e.5), whose host `WhatwgGates/Trust/Main.lean` reads the built
  `.olean` files through `WhatwgGates/Trust/Load.lean` with no extension loaded,
  so that no audited initializer, parser or elaborator runs in its process. The
  library takes the configuration as an argument and reads no elaboration
  state. `runPasses` reads the audited sources from disk and calls
  `Gates.Trust.runPassesOver`, which takes the source list and a scan function
  and holds every pass in order; the trust self-test calls `runPassesOver` with
  planted sources (addendum V2g), so a change to a pass or to their order is a
  change there. This repository's data, the audited trees, the two ceilings, the strict
  prefixes and the four anchored lists `strictCeilingExceptions`,
  `sourceTokenExemptions`, `metaprogrammingModules` and `extensionAllowlist`
  (the last read by the executable alone), lives in
  `WhatwgGates/TrustConfig.lean` (`Gates.TrustConfig.config`). That module
  imports only `WhatwgGates.Trust.Config` and is imported only by the gate
  module and the two entry points `whatwgbin/TrustGate.lean` and
  `whatwgbin/TrustSelfTest.lean`, each of which hands the value to a library: never by
  the umbrella `WhatwgGates`, by a `WhatwgGates.Trust` module or by anything a
  census battery imports (ruling R-W14(b)), so a plant after one of its anchors
  rebuilds no census battery and relinks the executable.
- The executable gate links the gate library, the loader and the config module
  and no other audited module, declares nothing `unsafe` or `partial`, never
  loads an extension or evaluates an imported constant, and has no
  `supportInterpreter`; it refuses a listed metaprogramming module in its own
  link closure. An import added to `WhatwgGates/Trust/Main.lean`, to a library
  module or to the entry point must keep that closure: it finds the project root
  with the library's `Gates.Trust.findProjectRoot`, not `Gates.Common`'s, for
  that reason.
- A gate reports a stable `PASS` or `FAIL` line stating exactly what was
  checked and, on failure, every offending item. It never truncates the
  failure list.
- A gate that writes a projection under `generated/` records that it did,
  names the file, and never writes an `AGENTS.md`.
- `WhatwgGates/Sha256.lean` holds no hash arithmetic and no self-test. Since step 6
  of `docs/HASH-PACKAGE-PLAN.md` every digest is `Hash.Sha256.sha256` and
  every hexadecimal spelling `Hash.Sha256.Hex.encode` from the required
  `hash` package, whose meaning is `Hash.Sha256.Bridge.sha256_bridge` and
  whose known-answer tests, axiom audit, and CAVP self-test run in that
  package. `WhatwgGates/VendorSeal.lean` computes its row digests through the same
  API. At the swap the vendor manifest regenerated byte-identically, which is
  the cutover proof. The former self-test's parsing rules are recorded here
  for the history of the pins: each record's `Len` field,
  not its `Msg` text, is the authority for the message length. Digests this gate
  produces are cross-checked against a second implementation at pin time and
  recorded in `docs/PROVENANCE.md`.
- Every gate resolves the repository root by searching upward for the
  production root `Whatwg.lean` (`Gates.Common.findProjectRoot`), joining a
  relative start to the working directory first, so an elaboration-time
  battery also runs by relative file name; none reads an environment variable
  for that.

## Gates

| Command | Checks | Writes |
| --- | --- | --- |
| `lake exe whatwg_vendorseal` | `vendor/` against `generated/vendor-manifest.tsv` in both directions; Windows path validity | nothing |
| `lake exe whatwg_vendorseal --write` | Windows path validity | `generated/vendor-manifest.tsv` |
| `lake exe whatwg_citations` | no line-numbered citation into a protected authored document | nothing |
| `lake exe whatwg_trustgate` (a default target; run after `lake build`, which it does not replay) | addendum V2e.5 of `test/contracts/trust-gate-hardening.contract.md`, in order: `lakefile.toml` sets no `weakLeanArgs` and no `lakefile.lean` exists; every module source has a built `.olean` and a fresh Lake trace that records that `.olean`, and stops otherwise; every trace records `-DwarningAsError=true`, no `warningAsError` off, `warn.sorry` or `debug.*` option, only `-D` arguments and no native library; the root's import set imports with no extension loaded, and stops otherwise; every pass of the in-tree command, with the token table rebuilt from raw parser entries and axioms from its own traversal; every environment extension holding an audited entry is on the extension allowlist, whose entries are each needed, reasoned and single; its own link closure holds no listed metaprogramming module. Prints `PASS whatwg_trustgate: ` and the in-tree summary line, exit 0; or `FAIL whatwg_trustgate: <n> finding(s)` after one `FAIL` line per finding, exit 1; exit 2 for an argument or an internal failure | nothing |
| `lake exe whatwg_trustselftest` (not a default target; run after `lake build`; about 40 s) | addendum V2g: the rows of the next line, each judged in one process with no build of the tree. A row's `judgement` says how: the gate library's run `Gates.Trust.runPassesOver`, with the executable's reads and its steps 0 and 5, over the row's planted texts and planted list entries (49 rows); the same after `lean` compiles the plant and it is imported beside the built tree (31 rows); `lean`'s own refusal with the freshness step (5); a one-module package built by Lake with the recorded-options step (3); the freshness step over an edited build directory (2); the two narrow runs as they are. Two rows whose fragment only the in-tree command prints are also judged by `lean` over the planted root. Controls: no declared red module; the tree built and fresh; no finding over the unplanted view; `lake exe whatwg_trustgate` and the in-tree command print the summary the run computed | throwaway directories outside the tree, removed afterwards |
| `lake exe whatwg_trustselftest --each` (the reference; about eighteen minutes; outside the development cycle, ruling R-S5) | the declared red set; then planted `partial`, `unsafe`, `sorry`, `native_decide`, malformed literals, and an unreachable module are each rejected for the stated reason; then the `V2-` plants of `test/contracts/trust-gate-hardening.contract.md`: the environment pass (declared axioms, `@[extern]`, `@[implemented_by]`, bodyless `opaque`), trust tokens in commands that leave no constant (`native_decide`, `bv_decide`, `bv_decide?`, `bv_check`, the `native` flag, `sorry`, `axiom`, `extern`, `implemented_by`, `debug.skipKernelTC`, the three forbidden axiom names) in the production, test and tooling trees and under `whatwgbin/`, the strict ceiling of ruling R-V1 with its four exception checks, and the source-token exemption checks, each rejected for its frozen reason; then the `V2b-` plants of addendum V2b (ruling R-V6): the goal-admitting spellings and message switches `sorryAx` (also as `_root_.sorryAx`), `admit`, `impossible`, `apply?`, `try?`, `grind?`, `debug.byAsSorry`, `debug.terminalTacticsAsSorry`, `warn.sorry`, `warningAsError`, `Lean.reduceBool` and `reduceNat`; then the `V2c-` plants of addendum V2c (ruling R-V10): metaprogramming keywords outside the metaprogramming-module list (`notation` in the production tree, `run_cmd`, a `macro_rules` that replaces the gate command), an elaborator registered through `@[command_elab]`, non-inert tokens of the final token table (a shadow token, a cut word, a comment opener, a hidden word), non-literal `config` values (an anonymous constructor, `{ v with }`, the escaped key `«config»`), a command before and a declaration after the gate in `WhatwgTest.lean`, and a missing, a stale and a blank metaprogramming-module entry, each rejected for its frozen reason; benign spellings of each addendum, an authored `opaque`, a `Classical.choice` theorem under `WhatwgTest` and the one configuration shape the tree uses accepted; and the gate and the coverage numerator run narrowly by relative file name; since addendum V2e every row and control is judged a second time by `lake exe whatwg_trustgate` in the probe, with the plant in place, and the `V2e-` rows the executable alone judges (an unimported source, a replaced gate command, `unif_hint`, `moreLeanArgs`, `leanOptions` and `weakLeanArgs` in `lakefile.toml`, a stale source, a removed `.olean`, and a stale, blank and repeated allowlist entry) are each refused for their frozen reason | a throwaway copy outside the tree, seeded from `.lake`, removed afterwards |
| `lake exe whatwg_htmlstandard` | the pinned `source` digest; the two projections `generated/html-standard-*.tsv`, `Whatwg/Html/Schema/Standard.lean` and the six generated modules (`Tags`, `Families`, `Attributes`, `ContentModel` and, since slice S3b of `docs/SVG-PACKAGE-PLAN.md`, `Foreign` under `Whatwg/Html/Schema/`, and `Whatwg/Html/Node/Combinators.lean`) are byte-identical to a fresh regeneration; each anchor of a foreign-content span occurs exactly once in the source | nothing |
| `lake exe whatwg_htmlstandard --write` | the pinned digest | those nine files |
| `lake exe whatwg_svgdefinitions` | each sealed svgwg file has its pinned digest and is ASCII; `master/publish.xml` lists exactly the pinned definitions files; the XML reader of `WhatwgGates/Xml.lean` accepts each and every entry carries only read attributes; each sentence has its reading in `Whatwg/Svg/Schema/Readings.lean`, by sentence and by digest; the four projections `generated/svg-*.tsv` and the four generated modules of `Whatwg/Svg/Schema/` are byte-identical to a fresh regeneration | nothing |
| `lake exe whatwg_svgdefinitions --write` | the same, apart from drift | those eight files |
|
|
|
| `lake exe whatwg_svggrammar` | the sealed chapter `master/paths.html` has its pinned digest; its one grammar block under `PathDataBNF` reads as EBNF with no construct refused, and `svg_path` reaches every production of it; the production `svg_path` and the erased expression of `Whatwg.Svg.Value.Path.syn` have one language, and so has each of 24 more productions and its named description, by a walk over the pairs of their Brzozowski derivatives in which a row found equal is one letter of the rows above it; seven controls differ, six of them a change to one sealed production and one the description of `d`, which also takes `none`, each with a shortest witness that a second matcher confirms. The gate is code that no theorem checks: a PASS is its verdict and no proof. It compares bare expressions and says nothing of the reader's longest-match rule (debt D95, ruling SV-37 of `docs/SVG-PACKAGE-PLAN.md`) | nothing |
| `lake exe whatwg_svggrammar --whole` | the same, and then `svg_path` and `Path.syn` over characters alone, with no row taken as a letter: the reference for the walk by parts | nothing |
| `lake exe whatwg_xmlproductions` | the sealed `vendor/w3c-xml-20081126/REC-xml-20081126.html` has its pinned digest; the anchors of the productions `Char`, `NameStartChar`, `NameChar` and `Name` each stand once, and each row reads as its number, its name, `::=` and a body with no construct refused; the sealed `Char`, `NameStartChar` and `NameChar` and the functions `isChar`, `isNameStartChar` and `isNameChar` of `Whatwg/Html/Print/Xml/Productions.lean` agree at every code point from U+0000 to U+10FFFF; the sealed body of `Name` is `NameStartChar (NameChar)*`, and `isName` agrees with that reading at every text of at most two characters over the ends of the sealed ranges and their neighbours; four controls differ, three of them a character production without one alternative and one `Name` with its two productions exchanged. The gate is code that no theorem checks: a PASS is its verdict and no proof (debt D105, ruling SV-42 of `docs/SVG-PACKAGE-PLAN.md`) | nothing |
| `lake exe whatwg_census` | the pinned `index.bs` digest; every census anchor occurs exactly once at its span start; every span digest recomputes; every row has exactly one disposition from the authored inputs under `census/`, with no unused entry; both projections are byte-identical to a fresh regeneration; and the numerator's coverage emit carries the same ids, order and dispositions as that regeneration, with no witness on an absent row and none on a row outside the denominator | nothing |
| `lake exe whatwg_census --write` | the same, apart from the emit, before writing | `generated/spec-algorithm-census.tsv` and `WhatwgTest/Audit/SpecCoverageRows.lean` |
| `lake exe whatwg_census --report` | the emit against a fresh regeneration, as above; then prints the coverage block of `docs/SPEC-COVERAGE.md` from the emit's states | nothing |

Every mode above takes an optional `--standard <key>`, which selects one of the
four censuses `Gates.Census.standards` registers (`streams`, the default;
`infra`; `webidl`; `ecma262`) and, with it, that standard's pinned input,
authored inputs under `census/<key>/`, projection and rows module.

The census executable is the one entry point under `whatwgbin/` that is not a bare
wrapper: its root imports `WhatwgTest/Audit/SpecCoverage.lean` and, since slice
Q2 of `docs/PROMISE-PACKAGE-PLAN.md`, `WhatwgTest/Audit/WebIdl/SpecCoverage.lean`
and `WhatwgTest/Audit/Ecma262/SpecCoverage.lean`, and hands
`Gates.Census.cli` a map from standard key to `emit`, because coverage states
are test-side and `WhatwgGates/` may not import them. A coverage block is therefore
printed from compiled Lean data that the numerator's elaboration-time gate has
already checked, and there is no generated coverage file to hand-edit. The cost
is a coupling: building this executable, and so every mode of it, needs all
three modules to elaborate. `--write` does not read an emit, so a census a
numerator's freeze has not caught up with is still regenerated by building
`WhatwgGates` alone and running `Gates.Census.write` under `lake env lean --run`.

`infra` has no entry in that map, so `lake exe whatwg_census --standard infra` ends its
PASS line "; no numerator exists for this standard yet, so no emit was checked"
and `lake exe whatwg_census --standard infra --report` refuses with exit code 2. That
refusal is the record that Infra has no numerator; inventing an empty emit to
make every standard reportable would be a defect.
