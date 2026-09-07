import Lean
import Gates

/-!
# ECMA-262 promise census contract battery

Breaker-owned and frozen before implementation. Packet:
`test/contracts/ecma262-census.contract.md`, which is the authority on every
number below and on the meaning of every name this file ascribes.

This battery is a tooling contract. It asserts no ECMAScript semantics, no
observation mask, no coverage state and no denominator claim: a census row is
a byte span of the pinned source with a joined disposition, nothing more.

Two red causes are expected before the builder lands the lane, and no other
error class:

1. the names ascribed in section 1 and section 2 do not exist
   (`Gates.Census.ecma262`, the seven new `Gates.Census.Kind` constructors,
   `Gates.Census.Profile.ecmarkup`, the `Gates.Ecmarkup` scanner); and
2. `Gates.Census.Standard.ofKey? "ecma262"` is `none`, so the projection gate
   in section 4 refuses before it can look at a file.

The frozen row table in section 3 was recomputed from the sealed bytes of
`vendor/ecma262-0248456c/spec.html` with PowerShell
(`[IO.File]::ReadAllBytes`, ISO-8859-1 decode so that character index equals
byte offset, `System.Security.Cryptography.SHA256`), independently of both
`Gates.Census` and the survey. The gate recomputes every digest with
`Gates.Sha256.hexDigest` over the pinned bytes, so the projection is checked
against two implementations of SHA-256 rather than against itself.
-/

set_option autoImplicit false

namespace WhatwgTest.Audit.Ecma262.CensusContract

open Lean Elab Command

/-! ## 1. The extended vocabulary

`Gates.Census.Kind` gains exactly seven constructors under ruling R-P2. The
existing six keep their constructors, their `name` spellings and their
`ofString?` entries; `Kind.all` lists the existing six first and then the
seven new ones in the order R-P2 writes them. -/

#check (Gates.Census.Kind.builtin : Gates.Census.Kind)
#check (Gates.Census.Kind.hook : Gates.Census.Kind)
#check (Gates.Census.Kind.property : Gates.Census.Kind)
#check (Gates.Census.Kind.record : Gates.Census.Kind)
#check (Gates.Census.Kind.field : Gates.Census.Kind)
#check (Gates.Census.Kind.term : Gates.Census.Kind)
#check (Gates.Census.Kind.clause : Gates.Census.Kind)

#guard Gates.Census.Kind.builtin.name == "builtin"
#guard Gates.Census.Kind.hook.name == "hook"
#guard Gates.Census.Kind.property.name == "property"
#guard Gates.Census.Kind.record.name == "record"
#guard Gates.Census.Kind.field.name == "field"
#guard Gates.Census.Kind.term.name == "term"
#guard Gates.Census.Kind.clause.name == "clause"

#guard Gates.Census.Kind.ofString? "builtin" == some Gates.Census.Kind.builtin
#guard Gates.Census.Kind.ofString? "hook" == some Gates.Census.Kind.hook
#guard Gates.Census.Kind.ofString? "property" == some Gates.Census.Kind.property
#guard Gates.Census.Kind.ofString? "record" == some Gates.Census.Kind.record
#guard Gates.Census.Kind.ofString? "field" == some Gates.Census.Kind.field
#guard Gates.Census.Kind.ofString? "term" == some Gates.Census.Kind.term
#guard Gates.Census.Kind.ofString? "clause" == some Gates.Census.Kind.clause

#guard Gates.Census.Kind.all.length == 13
#guard Gates.Census.Kind.all.map (·.name) ==
  ["idl", "op", "requirement", "rule", "slot", "type",
   "builtin", "hook", "property", "record", "field", "term", "clause"]

/-! ## 2. The `ecma262` standard and the ecmarkup scanner -/

#check (@Gates.Census.ecma262 : Gates.Census.Standard)
#check (Gates.Census.Profile.ecmarkup : Gates.Census.Profile)

#guard Gates.Census.ecma262.key == "ecma262"
#guard Gates.Census.ecma262.label == "ECMAScript ES2026 (0248456c)"
#guard Gates.Census.ecma262.inputRelativePath == "vendor/ecma262-0248456c/spec.html"
#guard Gates.Census.ecma262.inputDigest ==
  "ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0"
#guard Gates.Census.ecma262.censusRelativePath == "generated/ecma262-census.tsv"
#guard Gates.Census.ecma262.rowsRelativePath == "WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean"
#guard Gates.Census.ecma262.rowsNamespace == "WhatwgTest.Audit.Ecma262.SpecCoverageRows"
#guard Gates.Census.ecma262.authoredDir == "census/ecma262"
#guard Gates.Census.ecma262.regenerateCommand == "lake exe census --standard ecma262 --write"
#guard Gates.Census.ecma262.sectionsRelativePath == "census/ecma262/sections.tsv"
#guard Gates.Census.ecma262.dependenciesRelativePath == "census/ecma262/dependencies.tsv"
#guard Gates.Census.ecma262.externalsRelativePath == "census/ecma262/externals.tsv"
#guard (match Gates.Census.ecma262.profile with
        | .ecmarkup => true
        | .bikeshed _ => false)
#guard (Gates.Census.Standard.ofKey? "ecma262").isSome
#guard Gates.Census.standards.length == 4

/-! ### The scanner surface

`Gates/Ecmarkup.lean` is a pure scanner over a byte window `[b, e)` of the
pinned source. It never reads a file, never decides a disposition, and
refuses rather than skipping: every rejection is `Except.error` whose message
contains the decimal byte offset of the construct it refuses. -/

#check (@Gates.Ecmarkup.Clause : Type)
#check (@Gates.Ecmarkup.Clause.id : Gates.Ecmarkup.Clause → String)
#check (@Gates.Ecmarkup.Clause.kindAttr : Gates.Ecmarkup.Clause → String)
#check (@Gates.Ecmarkup.Clause.aoid : Gates.Ecmarkup.Clause → String)
#check (@Gates.Ecmarkup.Clause.title : Gates.Ecmarkup.Clause → String)
#check (@Gates.Ecmarkup.Clause.depth : Gates.Ecmarkup.Clause → Nat)
#check (@Gates.Ecmarkup.Clause.b : Gates.Ecmarkup.Clause → Nat)
#check (@Gates.Ecmarkup.Clause.e : Gates.Ecmarkup.Clause → Nat)

#check (@Gates.Ecmarkup.Step : Type)
#check (@Gates.Ecmarkup.Step.level : Gates.Ecmarkup.Step → Nat)
#check (@Gates.Ecmarkup.Step.b : Gates.Ecmarkup.Step → Nat)
#check (@Gates.Ecmarkup.Step.e : Gates.Ecmarkup.Step → Nat)

#check (@Gates.Ecmarkup.TableRow : Type)
#check (@Gates.Ecmarkup.TableRow.cells : Gates.Ecmarkup.TableRow → Array (Nat × Nat))
#check (@Gates.Ecmarkup.TableRow.b : Gates.Ecmarkup.TableRow → Nat)
#check (@Gates.Ecmarkup.TableRow.e : Gates.Ecmarkup.TableRow → Nat)

#check (@Gates.Ecmarkup.scanClauses :
  ByteArray → Nat → Nat → Except String (Array Gates.Ecmarkup.Clause))
#check (@Gates.Ecmarkup.scanSteps :
  ByteArray → Nat → Nat → Except String (Array Gates.Ecmarkup.Step))
#check (@Gates.Ecmarkup.scanTableRows :
  ByteArray → Nat → Nat → Except String (Array Gates.Ecmarkup.TableRow))
#check (@Gates.Ecmarkup.escapeId : String → String)
#check (@Gates.Ecmarkup.unescapeId : String → Option String)

/-! ### The R-P3 escaping

Every character of the safe alphabet `A-Z a-z 0-9 . % -` is written through
unchanged, so `.`, `%` and case survive; every other character `c` becomes
`~`, the lower-case hexadecimal of `c.toNat` with no leading zero, `~`. The
encoding is prefix-free because `~` is outside the safe alphabet, so
`escapeId` is injective and `unescapeId` inverts it. -/

#guard Gates.Ecmarkup.escapeId "promise.resolve" == "promise.resolve"
#guard Gates.Ecmarkup.escapeId "promise-resolve" == "promise-resolve"
#guard Gates.Ecmarkup.escapeId "promise.withResolvers" == "promise.withResolvers"
#guard Gates.Ecmarkup.escapeId "get-promise-%symbol.species%" == "get-promise-%symbol.species%"
#guard Gates.Ecmarkup.escapeId "promise.prototype-%symbol.tostringtag%" ==
  "promise.prototype-%symbol.tostringtag%"
#guard Gates.Ecmarkup.escapeId "Promise prototype object" == "Promise~20~prototype~20~object"
#guard Gates.Ecmarkup.escapeId "a_b" == "a~5f~b"
#guard Gates.Ecmarkup.escapeId "a~b" == "a~7e~b"
#guard Gates.Ecmarkup.escapeId "" == ""

#guard Gates.Ecmarkup.unescapeId "promise.resolve" == some "promise.resolve"
#guard Gates.Ecmarkup.unescapeId "Promise~20~prototype~20~object" ==
  some "Promise prototype object"
#guard Gates.Ecmarkup.unescapeId "a~7e~b" == some "a~b"
#guard Gates.Ecmarkup.unescapeId "a~zz~b" == none
#guard Gates.Ecmarkup.unescapeId "a~20b" == none

-- The named collision of ruling R-P3: `kebab` maps the two distinct clause
-- ids `sec-promise.resolve` and `sec-promise-resolve` to one string, and the
-- frozen escaping does not. The first line is the defect itself, checkable
-- against the generator as it stands today.
#guard Gates.Census.kebab "sec-promise.resolve" == Gates.Census.kebab "sec-promise-resolve"
#guard Gates.Ecmarkup.escapeId "promise.resolve" != Gates.Ecmarkup.escapeId "promise-resolve"

/-! ### Refusal probes

Each fixture is a literal source whose only defect is the stated one. The
expected byte offset is the offset of the refused construct: the opening tag
for a clause or an algorithm block, and the first byte of the line for a
step. -/

private def src (text : String) : ByteArray := text.toUTF8

private def refusesAt {α : Type} (result : Except String α) (offset : Nat) : Bool :=
  match result with
  | .error message => (message.splitOn (toString offset)).length > 1
  | .ok _ => false

private def refuses {α : Type} (result : Except String α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def accepts {α : Type} (result : Except String α) : Bool := !refuses result

private def whole (text : String) : ByteArray × Nat × Nat :=
  let bytes := src text
  (bytes, 0, bytes.size)

private def clauses (text : String) : Except String (Array Gates.Ecmarkup.Clause) :=
  let (bytes, b, e) := whole text
  Gates.Ecmarkup.scanClauses bytes b e

private def steps (text : String) : Except String (Array Gates.Ecmarkup.Step) :=
  let (bytes, b, e) := whole text
  Gates.Ecmarkup.scanSteps bytes b e

private def tableRows (text : String) : Except String (Array Gates.Ecmarkup.TableRow) :=
  let (bytes, b, e) := whole text
  Gates.Ecmarkup.scanTableRows bytes b e

-- ECMA-CEN-P01: the four observed `type` values are admitted and a fifth is refused.
#guard accepts (clauses "<emu-clause id=\"sec-x\"><h1>X</h1></emu-clause>")
#guard accepts (clauses
  "<emu-clause id=\"sec-x\" type=\"abstract operation\"><h1>X ( )</h1></emu-clause>")
#guard accepts (clauses
  "<emu-clause id=\"sec-x\" type=\"host-defined abstract operation\"><h1>X ( )</h1></emu-clause>")
#guard accepts (clauses
  "<emu-clause id=\"sec-x\" type=\"built-in function\"><h1>X ( )</h1></emu-clause>")
#guard refusesAt (clauses
  "<emu-clause id=\"sec-x\" type=\"grammar production\"><h1>X</h1></emu-clause>") 0

-- ECMA-CEN-P02: an unclosed or mismatched sectioning element is refused, never skipped.
#guard refusesAt (clauses "<emu-clause id=\"sec-x\"><h1>X</h1>") 0
#guard refusesAt (clauses "<emu-clause id=\"sec-x\"><h1>X</h1></emu-annex>") 0
#guard refuses (clauses "<emu-clause id=\"sec-x\"><h1>X</h1></emu-clause></emu-clause>")

-- ECMA-CEN-P03: a clause without an `id`, and a clause without an `<h1>`, are refused.
#guard refusesAt (clauses "<emu-clause><h1>X</h1></emu-clause>") 0
#guard refusesAt (clauses "<emu-clause id=\"sec-x\"></emu-clause>") 0

-- ECMA-CEN-P04: `<emu-alg>` bodies are `1. ` lines indented two spaces per level.
#guard accepts (steps "<emu-alg>\n  1. A.\n  1. B.\n</emu-alg>")
#guard accepts (steps "<emu-alg>\n  1. A.\n    1. B.\n  1. C.\n</emu-alg>")
#guard refusesAt (steps "<emu-alg>\n  Not a step.\n</emu-alg>") 10
#guard refusesAt (steps "<emu-alg>\n  1. A.\n   1. B.\n</emu-alg>") 18
#guard refusesAt (steps "<emu-alg>\n  1. A.\n      1. B.\n</emu-alg>") 18
#guard refusesAt (steps "<emu-alg replaces-step=\"x\">\n  1. A.\n</emu-alg>") 0
#guard refuses (steps "<emu-alg>\n  1. A.\n")

-- ECMA-CEN-P05: a character reference inside a scanned window is refused, not decoded.
#guard refuses (steps "<emu-alg>\n  1. A &amp; B.\n</emu-alg>")

-- ECMA-CEN-P06: a table needs three header cells and three cells per body row.
#guard accepts (tableRows
  "<emu-table id=\"t\"><table><thead><tr><th>A</th><th>B</th><th>C</th></tr></thead><tr><td>[[X]]</td><td>a Boolean</td><td>why</td></tr></table></emu-table>")
#guard refuses (tableRows
  "<emu-table id=\"t\"><table><thead><tr><th>A</th><th>B</th></tr></thead><tr><td>[[X]]</td><td>a Boolean</td></tr></table></emu-table>")
#guard refuses (tableRows
  "<emu-table id=\"t\"><table><thead><tr><th>A</th><th>B</th><th>C</th></tr></thead><tr><td>[[X]]</td><td>a Boolean</td></tr></table></emu-table>")
#guard refuses (tableRows
  "<emu-table id=\"t\"><table><thead><tr><th>A</th><th>B</th><th>C</th></tr></thead><tr><td>[[X]]</td><td>a Boolean</td><td>why</td></table></emu-table>")

/-! ## 3. The frozen census

Every row of `generated/ecma262-census.tsv`: its kind, its id, the half-open
byte interval of its span in the pinned source, the byte length of the anchor
`Gates.Census.chooseAnchorLength` selects for that span, and the SHA-256 of
the span. -/

private structure Frozen where
  kind : String
  id : String
  spanB : Nat
  spanE : Nat
  anchorLen : Nat
  digest : String
  deriving Inhabited

private def frozenRows : Array Frozen := #[
  ⟨"builtin", "builtin.get-promise-%symbol.species%", 2735737, 2736537, 32, "b019e293eb4a7b2349f33ab6e48abc9c20427063aa3f0acdbc3e233dac58a20a"⟩,
  ⟨"builtin", "builtin.promise-executor", 2708413, 2711495, 32, "765932794c01fd8b82164d88f54a765a96ed390f011de69396470e48f2575ea5"⟩,
  ⟨"builtin", "builtin.promise.all", 2711835, 2717026, 32, "86c966b7f88d69f50dda8100c3b3e1bc1af352fdc6d0e47a3fc7687fb9e65a90"⟩,
  ⟨"builtin", "builtin.promise.allsettled", 2717034, 2723460, 32, "083105d5a28c05d0f92325aef4b388e12d420abfc379d2c93551522b1d52e108"⟩,
  ⟨"builtin", "builtin.promise.any", 2723468, 2728545, 32, "10016318f59b61ad2f3e3e153be3dcc23881ce3a0c5611f9cd9fb6cf3dda4ed4"⟩,
  ⟨"builtin", "builtin.promise.prototype.catch", 2737067, 2737453, 48, "5fa520b7bc4b9fdb9599ae193385ee21dbb2188ee37f036a02d34903f6174f25"⟩,
  ⟨"builtin", "builtin.promise.prototype.finally", 2737669, 2740006, 48, "8900f09e03c588c6f990f5a511d98a0e8b90b65bd067a6d7d276b657deddbed6"⟩,
  ⟨"builtin", "builtin.promise.prototype.then", 2740014, 2743689, 48, "97a409281b34879a52da89b63be07cc15a9dfd70443035debcb4b38636dbd588"⟩,
  ⟨"builtin", "builtin.promise.race", 2728871, 2731537, 32, "68eabc5289e154aa5cf28ea5f159eb83daff9f1cff470c012f4f5882b5b61865"⟩,
  ⟨"builtin", "builtin.promise.reject", 2731545, 2732230, 32, "7b918a7dc1f44d633f07ded2e87864b7d841d669d50b5631e4c96475d8bf3ba5"⟩,
  ⟨"builtin", "builtin.promise.resolve", 2732238, 2733852, 32, "e38d9843379c55dc41c53b77e053048e86c125c752a9e999ed2a1ff1ef77cc7c"⟩,
  ⟨"builtin", "builtin.promise.try", 2733860, 2734885, 32, "498e54e44b5ef0d5b7faaa243a5b4f9c8505d90f820c9c3a01b33858f18b6535"⟩,
  ⟨"builtin", "builtin.promise.withResolvers", 2734893, 2735729, 32, "35bfc8591d8a2046a0d07a2943e44c5891f7a5a22bb93fd99148a419ddc99a45"⟩,
  ⟨"clause", "clause.jobs", 624525, 636548, 24, "871310fa2bcc46a2c06c2b0cc2e590632270246801336d7188185f0b4b3573bf"⟩,
  ⟨"clause", "clause.promise-abstract-operations", 2687651, 2702809, 32, "fa30b3b37aa9cfd702de3d7a9b8d1408ec959bd95381ef7dd7653f5c2675436f"⟩,
  ⟨"clause", "clause.promise-constructor", 2707565, 2711513, 32, "b7bb9e4831d34a8a4e091ccd90506e9cce8ad25ef7a1b66cccec25149c5fa1d1"⟩,
  ⟨"clause", "clause.promise-jobs", 2702815, 2707559, 32, "9ee19fb76c828986e3aff598ace336dfbacab6a69c51bcedc46c007ba1f1b7cb"⟩,
  ⟨"clause", "clause.promise-objects", 2686444, 2746707, 32, "21deb38546b2e5e928888349f91a40a16074a8cfa7f91469a0aec56c5bc7e9e0"⟩,
  ⟨"clause", "clause.properties-of-promise-instances", 2744135, 2746691, 48, "f3c8e70543376d039c9138e95afd153a99dd914f87398ba9208d8b76bd00aa0d"⟩,
  ⟨"clause", "clause.properties-of-the-promise-constructor", 2711519, 2736555, 48, "31a227af9032fdbb0e501b8419acf570bbee74959df62259fc4d57c4f6655b1a"⟩,
  ⟨"clause", "clause.properties-of-the-promise-prototype-object", 2736561, 2744129, 48, "f1599e711c81aceabca5ef33d796867271015536b12200fc2e04b12a14c212d4"⟩,
  ⟨"field", "field.jobcallback-records.Callback", 629684, 629930, 48, "0aa3d4ac28a7163324040babf2ffc96e492bf530e71b7c29e1222596bb86ab57"⟩,
  ⟨"field", "field.jobcallback-records.HostDefined", 629941, 630193, 256, "9edf19e8961f9d0341683b05f33c634d920df9b2f48412b1d1c623cda62a4446"⟩,
  ⟨"field", "field.promisecapability-records.Promise", 2688749, 2688997, 64, "59942a56a0e02b4fcc325226c71897937d87e435526b06ec2166a0e8c882cf64"⟩,
  ⟨"field", "field.promisecapability-records.Reject", 2689296, 2689567, 48, "0d38dbfc1eeaa69490e9efc8b8e68e16603c20f82f9cd20f4793fb65d70b9371"⟩,
  ⟨"field", "field.promisecapability-records.Resolve", 2689010, 2689283, 48, "c1b547ccba62ad0a5b2b5222643a00a19ee63336b5d9821ba27cb3501542f57c"⟩,
  ⟨"field", "field.promisereaction-records.Capability", 2691475, 2691802, 48, "67b47fd1bc6773cb099432f10db3b5b427d445cd1a10077db3ec90ec381d6a77"⟩,
  ⟨"field", "field.promisereaction-records.Handler", 2692151, 2692611, 48, "79e2058b8d3cfcbff3ace42ff8e52406429d38ea5252ebb18bd4b0fa56fa25ca"⟩,
  ⟨"field", "field.promisereaction-records.Type", 2691815, 2692138, 48, "9d8bbc74e5fa8aca1901755de043e11705ab76ee6dbaa10339cfc408f71fa8d2"⟩,
  ⟨"hook", "hook.host-promise-rejection-tracker", 2701220, 2702791, 32, "8b44c32c206fff92fefb2dbf3208efb4b53226fb18bd8cd42dfe1f72182fde07"⟩,
  ⟨"hook", "hook.hostcalljobcallback", 631447, 632699, 32, "8c71cf59d88d1e5d189be02e8a179a59d57dd35c0978b0419fcc02ea34d34267"⟩,
  ⟨"hook", "hook.hostenqueuegenericjob", 632705, 633441, 32, "3c4716a0db0dc18a9eb400f975a12026aa81cfdae6924d2b51e79348fd621b51"⟩,
  ⟨"hook", "hook.hostenqueuepromisejob", 633447, 635836, 32, "2dd7ba925b7ef8424773a60bdef524789cf044e2a97d7f1796fa74acec613b93"⟩,
  ⟨"hook", "hook.hostenqueuetimeoutjob", 635842, 636532, 32, "ee98ff2feb4f02946c4508ed8d47e5c1df82714138d1644cee02b912d6345870"⟩,
  ⟨"hook", "hook.hostmakejobcallback", 630253, 631441, 32, "f8ccca3399819ba3253b0dbec63f9663ed4fc3737ae74cc708e00e1235c46e4a"⟩,
  ⟨"op", "op.createresolvingfunctions", 2692679, 2695411, 32, "8227712c5eaa66d17942e1b7c13a8d6f7c29f24a03a591df81ce9868a90c8944"⟩,
  ⟨"op", "op.fulfillpromise", 2695419, 2696230, 24, "f0efa1ffede8b5b861cdb87a36f340ddbab87b2cdcd83abd7172d68e41a1c67e"⟩,
  ⟨"op", "op.getpromiseresolve", 2713285, 2713877, 32, "e3d4435301645c214ed0df54ef70ba2b71216c1c447f36c2e274c183125bf85b"⟩,
  ⟨"op", "op.ifabruptrejectpromise", 2689617, 2690417, 32, "7453862884877f7d2186444ab91e950c928cb0a711074025577311073a810ba9"⟩,
  ⟨"op", "op.ispromise", 2698778, 2699315, 32, "4762e66357e6408fde8f751a3008cda25dd492e99c5061b291f99c8514a121cf"⟩,
  ⟨"op", "op.newpromisecapability", 2696238, 2698770, 32, "9d0157b63bd72c38fb0951e4d0030b46997508ca43b46c5402eb901bb4f5c1d9"⟩,
  ⟨"op", "op.newpromisereactionjob", 2702885, 2705591, 48, "3225cb2f3907ae48b448c01a862587e80cd5e8b795b8ad5d610df68b5f291a7b"⟩,
  ⟨"op", "op.newpromiseresolvethenablejob", 2705599, 2707541, 48, "cde161e71ffde5bfde25825afa6b4e7c879c31d8056ab6c26f2d27c461f92e13"⟩,
  ⟨"op", "op.performpromiseall", 2713887, 2717006, 48, "a1c1fd99668df4f6b18316ccf4cfee9cd40d7137fb93e50da05c8abd5be5bfca"⟩,
  ⟨"op", "op.performpromiseallsettled", 2718509, 2723440, 48, "a9a3a64032ae6ac8500aa76e05a2ebd5751d2d0ef53fe9f4f23d714392ad9caa"⟩,
  ⟨"op", "op.performpromiseany", 2724939, 2728525, 48, "820398cb01553fc0bfe57e34aa9e430372e3639acee832fa85abb916ff98483d"⟩,
  ⟨"op", "op.performpromiserace", 2730549, 2731517, 48, "1061c0d5656d6fe17c945f326aac79e2938ef121d2d454f722e93a7b4edde680"⟩,
  ⟨"op", "op.performpromisethen", 2740635, 2743669, 48, "ff69ee65628ebe06e4fe2717feb6013c3d3089b3fa2b034fd90c085c3fa7e2ce"⟩,
  ⟨"op", "op.promise-resolve", 2732914, 2733832, 32, "9bfa14eade2e7991ee59dcdfdba99458d54bf48a8640dc0727e85df00ce649e6"⟩,
  ⟨"op", "op.rejectpromise", 2699323, 2700252, 24, "1006df0c95f76cd0a9edadadb8f68bf85446b0e8778485cfd8b913fb169fc056"⟩,
  ⟨"op", "op.triggerpromisereactions", 2700260, 2701212, 24, "ba03acae7a5640e794655f0fcb6e085859ce91eb4a8f899472ff01dc122c1839"⟩,
  ⟨"property", "property.promise.prototype", 2728553, 2728863, 48, "bdce2e364c2e0104a38b05bea65aa79f5c7262473ed8c83fafb37a756eaac56c"⟩,
  ⟨"property", "property.promise.prototype-%symbol.tostringtag%", 2743697, 2744111, 32, "dbe55bc57a9ab199033ca8ad2742c44d565f74431e43aa49e1c2b03ff8300eb3"⟩,
  ⟨"property", "property.promise.prototype.constructor", 2737461, 2737661, 48, "8176eb3689ce275615a724264dbf4b369621a8fe40f3db39e1bb2f81bf495a07"⟩,
  ⟨"record", "record.jobcallback-records", 628436, 630247, 24, "0fdda86da2a80f733a34298da2bec97f7a3c3da2cb173e0270813d63a9e85a1d"⟩,
  ⟨"record", "record.promisecapability-records", 2687751, 2690437, 32, "08c37430874eb8f162eb3e84825cfecf3aae49700ec1a28e9728864e79fe83ab"⟩,
  ⟨"record", "record.promisereaction-records", 2690445, 2692671, 32, "d66fc8081d7a889ffbdd77b8a4828c5ad87095a72fa04b257f808dbea8816743"⟩,
  ⟨"requirement", "requirement.hostcalljobcallback.1", 631993, 632098, 24, "1e479d75efd60b7e7342f9d2113a4237de99cfba08a1a29c1dc25a9a268bce96"⟩,
  ⟨"requirement", "requirement.hostenqueuepromisejob.1", 634193, 634410, 24, "7a33838fa1b5acbfb44c7f685abffc7c489667fdb590f30a80f8273c5a2f2e89"⟩,
  ⟨"requirement", "requirement.hostenqueuepromisejob.2", 634419, 634730, 24, "4041960ebfe66a4dc729e9f67acf868e6dc7049835b24a08552ffc3d4da696d6"⟩,
  ⟨"requirement", "requirement.hostenqueuepromisejob.3", 634739, 634841, 24, "6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65"⟩,
  ⟨"requirement", "requirement.hostmakejobcallback.1", 630615, 630699, 24, "398f9ac14e8275f65bf58957f19f8f0cceda1440f931d2b7293e78dd002aed01"⟩,
  ⟨"requirement", "requirement.jobs.1", 625769, 626250, 24, "c1afc33fed819c64bf74bbdfda723687b449fc135daaa0bb9dd9b73d0f5954e2"⟩,
  ⟨"requirement", "requirement.jobs.2", 626257, 626350, 24, "dec0ab05daf30a7def2efe98018bbdf58750e2f762313b2b50d8184b00720ec5"⟩,
  ⟨"requirement", "requirement.jobs.3", 626357, 626479, 24, "3cee57a0e02ed9d66b34bdaa1398995eebf32ac008eb9d493e15647bb9235378"⟩,
  ⟨"requirement", "requirement.jobs.4", 626486, 626589, 24, "22934fdf600a46d75443c562c8de0fdd4f441e8f67c4816d25ac4ec03aca194b"⟩,
  ⟨"slot", "slot.PromiseFulfillReactions", 2745630, 2745966, 48, "f13205764479117eddbc24d537a2981738b8e758dd5bd4f0d2042ce382fba3e0"⟩,
  ⟨"slot", "slot.PromiseIsHandled", 2746322, 2746637, 48, "c5e0730a73986eb475cb399584433d21e4aadecc069e3b2d61517937d39ed652"⟩,
  ⟨"slot", "slot.PromiseRejectReactions", 2745977, 2746311, 48, "d4c90d6b411a4b0359bfc0e9e75c1f9c25be373fb12d3a5bdbea60339a020f81"⟩,
  ⟨"slot", "slot.PromiseResult", 2745263, 2745619, 48, "c0c3b1b3c19902cdec5971211ec6f5cce01d5a5696f5728c480c61013cbb9a2f"⟩,
  ⟨"slot", "slot.PromiseState", 2744957, 2745252, 48, "b752fb3cead6b7d3063935ef7a5867b1af9f1f298b688dbe9d015540012f33fb"⟩,
  ⟨"term", "term.%Promise.prototype%", 2736764, 2736794, 24, "302fe81fc6fd80019abc332c6a47ba9dedd0e029fa784d49a7a328142294695e"⟩,
  ⟨"term", "term.%Promise%", 2707710, 2707730, 24, "bab66ccb5d0f0e98396dd6d48bb696c5f831210ac5edba920d191654b5003425"⟩,
  ⟨"term", "term.job", 624685, 624724, 24, "9be48048e1c5bbdd279753b6e574c4c1c10fe0b30daf54b1bbf468ee353a9fa5"⟩,
  ⟨"term", "term.job-activescriptormodule", 627006, 627070, 24, "189a5af3e9e04656c8e4196392fefc25a9cc1990eaf2792b0eb79fb2b5539ade"⟩,
  ⟨"term", "term.job-preparedtoevaluatecode", 627505, 627584, 24, "516906e43a51acff6bea69b650808674600154eadcaebbdfb147e455c32f01ec"⟩,
  ⟨"term", "term.Promise~20~prototype~20~object", 2736697, 2736732, 24, "362a4b141200ade425ce88a78c944ae6cd994fc2cfb7f1ab754a83d1c3a4b5cf"⟩
]

private def sourceRelativePath : String := "vendor/ecma262-0248456c/spec.html"

private def sourceDigest : String :=
  "ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0"

private def censusRelativePath : String := "generated/ecma262-census.tsv"

private def rowsRelativePath : String := "WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean"

private def regenerateCommand : String := "lake exe census --standard ecma262 --write"

private def expectedRowTotal : Nat := 77

-- Q2 amendment, `test/contracts/ecma262-census-q2.contract.md`, 2026-09-07:
-- 74 -> 75. Debt D4 moves `clause.promise-objects` from `evidenceOnly` to
-- `owned`, so it enters the denominator; the row total does not move.
private def expectedDenominator : Nat := 75

private def expectedHeader : String :=
  "#census format=1 generator=Gates.Census input=vendor/ecma262-0248456c/spec.html " ++
  "input-sha256=ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0 " ++
  "rows=77 regenerate=lake exe census --standard ecma262 --write"

private def expectedKindCounts : List (String × Nat) :=
  [("builtin", 13), ("clause", 8), ("field", 8), ("hook", 6), ("op", 16),
   ("property", 3), ("record", 3), ("requirement", 9), ("slot", 5), ("term", 6)]

-- Q2 amendment, `test/contracts/ecma262-census-q2.contract.md`, 2026-09-07:
-- `owned` 44 -> 45 and `evidenceOnly` 3 -> 2, the one row debt D4 moves. The
-- other four counts are unchanged, and the two sibling clauses
-- `clause.promise-abstract-operations` and `clause.promise-jobs` stay
-- `evidenceOnly`.
private def expectedDispositionCounts : List (String × Nat) :=
  [("owned", 45), ("foreignBoundary", 13), ("hostOnly", 10), ("requirement", 7),
   ("evidenceOnly", 2), ("refused", 0), ("targetOnly", 0)]

/-! ## 4. The projection gate -/

private def occurrencesOf (haystack needle : String) : Nat :=
  (haystack.splitOn needle).length - 1

open Elab Command in
elab "#ecma262_census_contract_gate" : command => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "ecma262 census contract: source file has no parent directory"
  let projectRoot ← liftIO <| Gates.Common.findProjectRoot sourceDirectory
  let some standard := Gates.Census.Standard.ofKey? "ecma262"
    | throwError "ecma262 census contract: no standard is registered under the key ecma262; ruling R-P1 requires `lake exe census --standard ecma262`"
  if standard.censusRelativePath != censusRelativePath then
    throwError "ecma262 census contract: the standard writes {standard.censusRelativePath}; the packet freezes {censusRelativePath}"
  let censusPath := projectRoot / censusRelativePath
  unless ← liftIO censusPath.pathExists do
    throwError "ecma262 census contract: missing {censusRelativePath}; run `{regenerateCommand}`"
  let sourcePath := projectRoot / sourceRelativePath
  unless ← liftIO sourcePath.pathExists do
    throwError "ecma262 census contract: missing the pinned source {sourceRelativePath}"
  let bytes ← liftIO <| IO.FS.readBinFile sourcePath
  let censusText ← liftIO <| IO.FS.readFile censusPath
  let allLines := Gates.Common.lines censusText
  let header := allLines.headD ""
  let dataLines := allLines.drop 1
  if header != expectedHeader then
    throwError "ecma262 census contract: the header line of {censusRelativePath} is not the frozen one"
  if dataLines.length != expectedRowTotal then
    throwError "ecma262 census contract: {censusRelativePath} carries {dataLines.length} rows; the packet freezes {expectedRowTotal}"
  -- Every line is a seven-field row whose id carries its own kind, and the file
  -- is strictly increasing in `Gates.Census.Row.sortKey`, so ids are unique.
  let mut parsed : Array (Array String) := #[]
  let mut lineNumber : Nat := 1
  for line in dataLines do
    lineNumber := lineNumber + 1
    match Gates.Census.splitRow line with
    | .error message =>
      throwError "ecma262 census contract: line {lineNumber}: {message}"
    | .ok fields =>
      if fields.size != 7 then
        throwError "ecma262 census contract: line {lineNumber}: expected seven fields, found {fields.size}"
      let kindText := fields.getD 0 ""
      let rowId := fields.getD 1 ""
      match Gates.Census.Kind.ofString? kindText with
      | none => throwError "ecma262 census contract: line {lineNumber}: unknown kind {kindText}"
      | some kind =>
        unless rowId.startsWith (kind.name ++ ".") do
          throwError "ecma262 census contract: line {lineNumber}: row id {rowId} does not carry its own kind"
      parsed := parsed.push fields
  for i in [1:parsed.size] do
    let previous := (parsed.getD (i - 1) #[]).getD 0 "" ++ "|" ++ (parsed.getD (i - 1) #[]).getD 1 ""
    let current := (parsed.getD i #[]).getD 0 "" ++ "|" ++ (parsed.getD i #[]).getD 1 ""
    unless previous < current do
      throwError "ecma262 census contract: rows {i} and {i + 1} are not strictly increasing in kind then id ({previous}, {current})"
  for (kindName, expected) in expectedKindCounts do
    let observed := parsed.foldl (fun acc fields => if fields.getD 0 "" == kindName then acc + 1 else acc) 0
    unless observed == expected do
      throwError "ecma262 census contract: {censusRelativePath} holds {observed} {kindName} row(s); the packet freezes {expected}"
  -- Every frozen row, byte for byte, with its digest recomputed from the pin.
  for row in frozenRows do
    let some fields := parsed.find? (fun f => f.getD 0 "" == row.kind && f.getD 1 "" == row.id)
      | throwError "ecma262 census contract: {censusRelativePath} has no {row.kind} row {row.id}"
    let anchorField := fields.getD 2 ""
    let startField := fields.getD 3 ""
    let endField := fields.getD 4 ""
    let digestField := fields.getD 5 ""
    if startField != toString row.spanB then
      throwError "ecma262 census contract: {row.id} starts at {startField}; the packet freezes {row.spanB}"
    if endField != toString row.spanE then
      throwError "ecma262 census contract: {row.id} ends at {endField}; the packet freezes {row.spanE}"
    if digestField != row.digest then
      throwError "ecma262 census contract: {row.id} records span digest {digestField}; the packet freezes {row.digest}"
    let recomputed := Gates.Sha256.hexDigest (bytes.extract row.spanB row.spanE)
    if recomputed != row.digest then
      throwError "ecma262 census contract: the pinned bytes [{row.spanB}, {row.spanE}) hash to {recomputed}; the packet freezes {row.digest} for {row.id}"
    let some anchor := Gates.Census.sliceString? bytes row.spanB (row.spanB + row.anchorLen)
      | throwError "ecma262 census contract: the {row.anchorLen}-byte anchor of {row.id} is not valid UTF-8"
    if anchorField != anchor then
      throwError "ecma262 census contract: the anchor of {row.id} is not the first {row.anchorLen} bytes of its span"
  -- The frozen coverage row list the same command writes.
  let rowsPath := projectRoot / rowsRelativePath
  unless ← liftIO rowsPath.pathExists do
    throwError "ecma262 census contract: missing {rowsRelativePath}; run `{regenerateCommand}`"
  let rowsText ← liftIO <| IO.FS.readFile rowsPath
  let rowsLines := Gates.Common.lines rowsText
  unless rowsLines.contains s!"def rowTotal : Nat := {expectedRowTotal}" do
    throwError "ecma262 census contract: {rowsRelativePath} does not record rowTotal {expectedRowTotal}"
  unless rowsLines.contains s!"def denominator : Nat := {expectedDenominator}" do
    throwError "ecma262 census contract: {rowsRelativePath} does not record denominator {expectedDenominator}"
  for (dispositionName, expected) in expectedDispositionCounts do
    let observed := occurrencesOf rowsText (", ." ++ dispositionName ++ ",")
    unless observed == expected do
      throwError "ecma262 census contract: {rowsRelativePath} carries {observed} {dispositionName} row(s); the packet freezes {expected}"
  logInfo
    m!"ecma262 census contract: {expectedRowTotal} rows, {frozenRows.size} frozen anchor rows verified against {sourceRelativePath} (SHA-256 {sourceDigest}), denominator {expectedDenominator}"

#ecma262_census_contract_gate

end WhatwgTest.Audit.Ecma262.CensusContract
