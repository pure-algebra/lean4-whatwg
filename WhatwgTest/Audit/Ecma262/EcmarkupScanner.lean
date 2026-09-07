import Lean
import Gates

/-!
# ECMA-262 ecmarkup scanner battery

Builder-authored, green. It is the parallel-development battery ruling R-P7
allows: `Gates/Ecmarkup.lean` is developed and checked as a pure scanner before
the `ecma262` `Gates.Census.Standard` exists, so that the frozen packet
`test/contracts/ecma262-census.contract.md` and its battery
`WhatwgTest/Audit/Ecma262/CensusContract.lean` have something to land on.

This battery imports no frozen module. Every number below is transcribed from
that contract as data and re-derived here from the sealed bytes of
`vendor/ecma262-0248456c/spec.html`, so an agreement between the two is an
agreement between two independent readings, not a tautology.

## Claim boundary

Tooling only. A row is a byte span of the pinned source. Nothing here is an
ECMAScript semantic claim, an observation mask, a coverage state, a
denominator, or any statement about `Whatwg.Ecma262`.

## What is checked where, and why

The elaboration-time gate runs the scanner over the two frozen clause windows
and asserts, against the contract's table: the 49 clause spans, the 4
`<emu-table>` blocks and their 13 body rows, the 9 requirement bullets, the 390
`<emu-alg>` step lines with their level histogram, the single `aoid`, the
structured-header facts, the encoding facts, and all 77 rows in kind, id,
start, end, anchor text and SHA-256 digest — the digest recomputed with
`Gates.Sha256.hexDigest` over the pinned bytes.

The **chosen anchor length** is asserted with the real
`Gates.Census.chooseAnchorLength` for three rows rather than for all 77, and
this is a deliberate cost decision, recorded so nobody reads it as coverage.
One call scans the whole 2,978,793-byte file for its 24-byte probe; under the
elaboration-time interpreter that is about 3.5 seconds a row, so all 77 cost
about four and a half minutes, which does not belong in a default build. The
three chosen are exactly the rows the ladder is interesting for and the three
the packet disagrees with the survey about: the only 256-byte rung
(`field.jobcallback-records.HostDefined`), the only 64-byte rung
(`field.promisecapability-records.Promise`), and the shortest anchor in the
lane (`term.%Promise%`, 24 bytes and not the survey's 20). The remaining 74
choices are checked by the compiled `lake exe census --standard ecma262` when
the standard is wired, and were measured once against this exact function; the
Q1 receipt in `docs/PROMISE-PACKAGE-PLAN.md` records that run.

**Review debt D6 (added by the Q2 tooling builder, 2026-09-07).** The Q1 review
found two refusal branches of `Gates/Ecmarkup.lean` with no probe: the nameless
`<dfn>` of `termRows` and the 4096-occurrence cap of `rootWindow`. Neither is
reachable from the pinned bytes, which is why neither had one and why both were
owed: a refusal nothing exercises is a refusal nobody knows still works.
Section 3 probes each on a synthetic input whose only defect is the stated one,
naming the message it expects rather than only that some refusal fired, with a
positive control beside it; and the gate of section 6 shows that neither fires
at the pin — every one of the nine in-scope `<dfn>` elements derives a non-empty
name, and both authored root clause ids resolve, which they cannot do if the
cap bites.

The second of those two pin checks is the expensive one and the cost is
recorded rather than hidden: `rootWindow` scans all 2,978,793 bytes twice per
call, so resolving both root ids adds about twelve seconds, taking this
module's elaboration from about fifteen seconds to about twenty-seven measured
with `lake env lean` on Windows x64. It is paid because the cap is the one
refusal in the scanner that a re-pin can start firing with no other symptom.
The synthetic probes of section 3 cost milliseconds, and the `<dfn>` pin check
is free: it reuses the tags the gate has already scanned.
-/

set_option autoImplicit false

namespace WhatwgTest.Audit.Ecma262.EcmarkupScanner

open Lean Elab Command

/-! ## 1. The scanner surface

The signatures ruling R-P1 and section 4 of the packet ascribe. -/

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

#check (@Gates.Ecmarkup.rows :
  ByteArray → Array (Nat × Nat) → Except String (Array Gates.Ecmarkup.RowSpec))
#check (@Gates.Ecmarkup.rootWindow : ByteArray → String → Except String (Nat × Nat))

/-! ## 2. The R-P3 escaping

The fourteen worked values the packet freezes, the named `kebab` collision the
escaping repairs, and the exactness of the inverse. -/

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

-- Outside the image in the other three ways: a leading zero, an upper-case
-- hexadecimal digit, and an escape of a character the safe alphabet keeps.
#guard Gates.Ecmarkup.unescapeId "a~05f~b" == none
#guard Gates.Ecmarkup.unescapeId "a~5F~b" == none
#guard Gates.Ecmarkup.unescapeId "a~61~b" == none
#guard Gates.Ecmarkup.unescapeId "a~~b" == none

-- The defect R-P3 names, and its repair.
#guard Gates.Census.kebab "sec-promise.resolve" == Gates.Census.kebab "sec-promise-resolve"
#guard Gates.Ecmarkup.escapeId "promise.resolve" != Gates.Ecmarkup.escapeId "promise-resolve"

/-! ## 3. Refusal probes

Each fixture is a literal source whose only defect is the stated one. The
expected byte offset is the offset of the refused construct: the opening tag
for a clause, a table row or an algorithm block, and the first byte of the line
for a step. -/

private def src (text : String) : ByteArray := text.toUTF8

private def refusesAt {α : Type} (result : Except String α) (offset : Nat) : Bool :=
  match result with
  | .error message => (message.splitOn (toString offset)).length > 1
  | .ok _ => false

private def refuses {α : Type} (result : Except String α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

/-- A refusal whose message carries `fragment`. Stronger than `refuses`: it
says *which* refusal fired, so a probe cannot pass because the fixture broke
somewhere else. -/
private def refusesWith {α : Type} (result : Except String α) (fragment : String) : Bool :=
  match result with
  | .error message => (message.splitOn fragment).length > 1
  | .ok _ => false

private def accepts {α : Type} (result : Except String α) : Bool := !refuses result

private def clauses (text : String) : Except String (Array Gates.Ecmarkup.Clause) :=
  let bytes := src text
  Gates.Ecmarkup.scanClauses bytes 0 bytes.size

private def steps (text : String) : Except String (Array Gates.Ecmarkup.Step) :=
  let bytes := src text
  Gates.Ecmarkup.scanSteps bytes 0 bytes.size

private def tableRows (text : String) : Except String (Array Gates.Ecmarkup.TableRow) :=
  let bytes := src text
  Gates.Ecmarkup.scanTableRows bytes 0 bytes.size

private def rowsOf (text : String) : Except String (Array Gates.Ecmarkup.RowSpec) :=
  let bytes := src text
  Gates.Ecmarkup.windowRows bytes 0 bytes.size

-- The three observed `type` values are admitted, an untyped clause is
-- admitted, and a fourth value is refused at its opening tag.
#guard accepts (clauses "<emu-clause id=\"sec-x\"><h1>X</h1></emu-clause>")
#guard accepts (clauses
  "<emu-clause id=\"sec-x\" type=\"abstract operation\"><h1>X ( )</h1></emu-clause>")
#guard accepts (clauses
  "<emu-clause id=\"sec-x\" type=\"host-defined abstract operation\"><h1>X ( )</h1></emu-clause>")
#guard accepts (clauses
  "<emu-clause id=\"sec-x\" type=\"built-in function\"><h1>X ( )</h1></emu-clause>")
#guard refusesAt (clauses
  "<emu-clause id=\"sec-x\" type=\"grammar production\"><h1>X</h1></emu-clause>") 0

-- Attribute order freedom: `oldids` before `id`, and `oldids` between `id` and
-- `type`, both read by name. Two in-scope clause tags write the first shape.
#guard accepts (clauses
  "<emu-clause oldids=\"sec-old\" id=\"sec-x\" type=\"built-in function\"><h1>X</h1></emu-clause>")
#guard (match clauses
    "<emu-clause oldids=\"sec-old\" id=\"sec-x\" type=\"built-in function\"><h1>X</h1></emu-clause>" with
  | .ok cs => (cs.getD 0 default).id == "sec-x" && (cs.getD 0 default).kindAttr == "built-in function"
  | .error _ => false)

-- A truncated clause: the sectioning element is never closed. Refused at the
-- opening tag, never skipped.
#guard refusesAt (clauses "<emu-clause id=\"sec-x\"><h1>X</h1>") 0

-- An out-of-order close tag: the close names a different sectioning element
-- than the open on top of the stack.
#guard refusesAt (clauses "<emu-clause id=\"sec-x\"><h1>X</h1></emu-annex>") 0

-- A stack underflow.
#guard refuses (clauses "<emu-clause id=\"sec-x\"><h1>X</h1></emu-clause></emu-clause>")

-- An unknown element shape: a tag with no element name, refused at its own
-- byte offset rather than skipped as unrecognised markup.
#guard refusesAt (clauses "<emu-clause id=\"sec-x\"><h1>X</h1><!--c--></emu-clause>") 33

-- A clause without an `id`, and a clause without an `<h1>` of its own.
#guard refusesAt (clauses "<emu-clause><h1>X</h1></emu-clause>") 0
#guard refusesAt (clauses "<emu-clause id=\"sec-x\"></emu-clause>") 0
#guard refusesAt (clauses
  "<emu-clause id=\"a\"><emu-clause id=\"b\"><h1>B</h1></emu-clause></emu-clause>") 0

-- Nested clauses with matching close tags, and the depth they carry.
#guard (match clauses
    "<emu-clause id=\"a\"><h1>A</h1><emu-clause id=\"b\"><h1>B</h1></emu-clause></emu-clause>" with
  | .ok cs =>
    cs.size == 2 && (cs.getD 0 default).id == "a" && (cs.getD 0 default).depth == 0 &&
      (cs.getD 1 default).id == "b" && (cs.getD 1 default).depth == 1
  | .error _ => false)

-- The structured header: only `<dt>description</dt>` is admitted.
#guard accepts (clauses
  "<emu-clause id=\"a\"><h1>A</h1><dl class=\"header\"><dt>description</dt><dd>d</dd></dl></emu-clause>")
#guard accepts (clauses "<emu-clause id=\"a\"><h1>A</h1><dl class=\"header\"></dl></emu-clause>")
#guard refuses (clauses
  "<emu-clause id=\"a\"><h1>A</h1><dl class=\"header\"><dt>effects</dt><dd>d</dd></dl></emu-clause>")

-- `<emu-alg>` bodies are `1. ` lines indented two spaces per level.
#guard accepts (steps "<emu-alg>\n  1. A.\n  1. B.\n</emu-alg>")
#guard accepts (steps "<emu-alg>\n  1. A.\n    1. B.\n  1. C.\n</emu-alg>")
#guard refusesAt (steps "<emu-alg>\n  Not a step.\n</emu-alg>") 10
#guard refusesAt (steps "<emu-alg>\n  1. A.\n   1. B.\n</emu-alg>") 18
#guard refusesAt (steps "<emu-alg>\n  1. A.\n      1. B.\n</emu-alg>") 18
#guard refusesAt (steps "<emu-alg replaces-step=\"x\">\n  1. A.\n</emu-alg>") 0
#guard refusesAt (steps "<emu-alg example>\n  1. A.\n</emu-alg>") 0
#guard refuses (steps "<emu-alg>\n  1. A.\n")

-- The literal `1.` is never read as an ordinal, and the level is relative to
-- the block's own minimum indent, never an absolute column: the same three
-- lines at base indent 8 give the same levels as at base indent 2.
#guard (match steps "<emu-alg>\n        1. A.\n          1. B.\n        1. C.\n</emu-alg>" with
  | .ok ss => ss.map (·.level) == #[0, 1, 0]
  | .error _ => false)

-- A character reference inside a scanned window is refused, not decoded.
#guard refuses (steps "<emu-alg>\n  1. A &amp; B.\n</emu-alg>")
#guard refuses (clauses "<emu-clause id=\"sec-x\"><h1>A &amp; B</h1></emu-clause>")

-- A table needs three header cells and three cells per body row.
#guard accepts (tableRows
  "<emu-table id=\"t\"><table><thead><tr><th>A</th><th>B</th><th>C</th></tr></thead><tr><td>[[X]]</td><td>a Boolean</td><td>why</td></tr></table></emu-table>")
#guard refuses (tableRows
  "<emu-table id=\"t\"><table><thead><tr><th>A</th><th>B</th></tr></thead><tr><td>[[X]]</td><td>a Boolean</td></tr></table></emu-table>")
#guard refuses (tableRows
  "<emu-table id=\"t\"><table><thead><tr><th>A</th><th>B</th><th>C</th></tr></thead><tr><td>[[X]]</td><td>a Boolean</td></tr></table></emu-table>")
#guard refuses (tableRows
  "<emu-table id=\"t\"><table><thead><tr><th>A</th><th>B</th><th>C</th></tr></thead><tr><td>[[X]]</td><td>a Boolean</td><td>why</td></table></emu-table>")

-- `rootWindow` resolves a root clause id, and refuses a duplicate or a miss.
#guard (match Gates.Ecmarkup.rootWindow
    (src "<emu-clause id=\"sec-a\"><h1>A</h1></emu-clause>") "sec-a" with
  | .ok (b, e) => b == 0 && e == 46
  | .error _ => false)
#guard refuses (Gates.Ecmarkup.rootWindow
  (src "<emu-clause id=\"sec-a\"><h1>A</h1></emu-clause>") "sec-b")
#guard refuses (Gates.Ecmarkup.rootWindow
  (src ("<emu-clause id=\"sec-a\"><h1>A</h1></emu-clause>" ++
        "<emu-clause id=\"sec-a\"><h1>A</h1></emu-clause>")) "sec-a")

/-! ### The two refusals review debt D6 found unprobed (2026-09-07)

The Q1 review of the ES2026 census found that two refusal branches of
`Gates/Ecmarkup.lean` had no probe: the nameless `<dfn>` in `termRows`, and the
occurrence cap in `rootWindow`. Neither can be reached from the pinned bytes —
which is exactly why neither had a probe, and exactly why one is owed: a
refusal nothing exercises is a refusal nobody knows still works. Each is probed
here on a synthetic input whose only defect is the stated one, with a positive
control beside it, and the gate of section 6 then shows that neither fires at
the pin. -/

-- A `<dfn>` with neither an `id` attribute nor text: refused at its own byte
-- offset, and named as the empty-name refusal rather than any other. The same
-- fixture with an id, and with text, is accepted, so what is refused is the
-- empty name and not the shape.
#guard refusesWith
  (rowsOf "<emu-clause id=\"sec-x\"><h1>X</h1><p><dfn></dfn></p></emu-clause>")
  "carries neither an id nor text"
#guard refusesAt (rowsOf "<emu-clause id=\"sec-x\"><h1>X</h1><p><dfn></dfn></p></emu-clause>") 36
#guard accepts (rowsOf "<emu-clause id=\"sec-x\"><h1>X</h1><p><dfn id=\"j\"></dfn></p></emu-clause>")
#guard accepts (rowsOf "<emu-clause id=\"sec-x\"><h1>X</h1><p><dfn>job</dfn></p></emu-clause>")

-- A `<dfn>` whose text is only markup is nameless too: `innerText` strips tags
-- before the emptiness test, so `<dfn><b></b></dfn>` is refused exactly as the
-- bare one is, and is not given the id `term.<b></b>`.
#guard refusesWith
  (rowsOf "<emu-clause id=\"sec-x\"><h1>X</h1><p><dfn><b></b></dfn></p></emu-clause>")
  "carries neither an id nor text"

/-- 4096 `<emu-clause>` openers: the smallest fixture that makes
`Gates.Ecmarkup.rootWindow`'s occurrence cap bite, since the cap is 4096 and
the test is `Nat.ble 4096 opens.size`. -/
private def cappedSource : ByteArray :=
  (String.join (List.replicate 4096 "<emu-clause>")).toUTF8

/-- One opener fewer. The scan then completes, so the refusal that follows is
the ordinary "no such clause id" one and not the cap: that is what makes the
probe above a probe of the cap rather than of the fixture's size. -/
private def uncappedSource : ByteArray :=
  (String.join (List.replicate 4095 "<emu-clause>")).toUTF8

#guard refusesWith (Gates.Ecmarkup.rootWindow cappedSource "sec-a")
  "reached its 4096 occurrence cap"
#guard refusesWith (Gates.Ecmarkup.rootWindow uncappedSource "sec-a")
  "occurs 0 time(s)"

/-! ## 4. The frozen census, transcribed from the packet

Section 9 of `test/contracts/ecma262-census.contract.md`, all 77 rows: kind,
id, the half-open byte interval of the span in the pinned source, the byte
length of the anchor `Gates.Census.chooseAnchorLength` selects, and the SHA-256
of the span. The packet's own table is printed in a collated order; the order
below is the generator's sort key, `kind.name ++ "|" ++ id` under Lean's
ordinal `String` order, which is what the projection must be increasing in. -/

private structure Frozen where
  kind : String
  id : String
  spanB : Nat
  spanE : Nat
  anchorLen : Nat
  digest : String
  deriving Inhabited, BEq

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
  ⟨"term", "term.%Promise%", 2707710, 2707730, 24, "bab66ccb5d0f0e98396dd6d48bb696c5f831210ac5edba920d191654b5003425"⟩,
  ⟨"term", "term.%Promise.prototype%", 2736764, 2736794, 24, "302fe81fc6fd80019abc332c6a47ba9dedd0e029fa784d49a7a328142294695e"⟩,
  ⟨"term", "term.Promise~20~prototype~20~object", 2736697, 2736732, 24, "362a4b141200ade425ce88a78c944ae6cd994fc2cfb7f1ab754a83d1c3a4b5cf"⟩,
  ⟨"term", "term.job", 624685, 624724, 24, "9be48048e1c5bbdd279753b6e574c4c1c10fe0b30daf54b1bbf468ee353a9fa5"⟩,
  ⟨"term", "term.job-activescriptormodule", 627006, 627070, 24, "189a5af3e9e04656c8e4196392fefc25a9cc1990eaf2792b0eb79fb2b5539ade"⟩,
  ⟨"term", "term.job-preparedtoevaluatecode", 627505, 627584, 24, "516906e43a51acff6bea69b650808674600154eadcaebbdfb147e455c32f01ec"⟩
]

#guard frozenRows.size == 77

private def expectedKindCounts : List (String × Nat) :=
  [("builtin", 13), ("clause", 8), ("field", 8), ("hook", 6), ("op", 16),
   ("property", 3), ("record", 3), ("requirement", 9), ("slot", 5), ("term", 6)]

#guard (expectedKindCounts.foldl (fun acc entry => acc + entry.2) 0) == 77
#guard expectedKindCounts.all
  (fun entry => frozenRows.foldl (fun acc r => if r.kind == entry.1 then acc + 1 else acc) 0
    == entry.2)

/-! ## 5. The pin and the two clause windows -/

private def sourceRelativePath : String := "vendor/ecma262-0248456c/spec.html"

private def sourceSize : Nat := 2978793

/-- Section 2 of the packet, and the two ids `census/ecma262/sections.tsv`
names. -/
private def windows : Array (Nat × Nat) := #[(624525, 636548), (2686444, 2746707)]

/-- The two root clause ids `census/ecma262/sections.tsv` authors, in the same
order as `windows`. `Gates.Ecmarkup.rootWindow` resolves each against the whole
pinned file, and review debt D6's second half is that its 4096-occurrence cap
had no probe; the gate resolves both here so that the cap refusal is shown not
to fire at this pin. -/
private def rootClauseIds : Array String := #["sec-jobs", "sec-promise-objects"]

private def expectedClauses : Nat := 49
private def expectedTables : Nat := 4
private def expectedBodyRows : Nat := 13
private def expectedBullets : Nat := 9
private def expectedSteps : Nat := 390
private def expectedAoids : Nat := 1
private def expectedTypedClauses : Nat := 34
private def expectedHeaderBlocks : Nat := 21
private def expectedDescriptions : Nat := 10
private def expectedNonAscii : Nat := 188
private def expectedDfns : Nat := 9

/-- The 390 step lines by level relative to their block minimum. -/
private def expectedLevels : List (Nat × Nat) := [(0, 175), (1, 120), (2, 74), (3, 21)]

/-- The rows whose chosen anchor length this battery asserts against the real
`Gates.Census.chooseAnchorLength`; see the module header for why it is three
and not seventy-seven. -/
private def anchorLengthProbes : List (String × Nat × Nat) :=
  [("field.jobcallback-records.HostDefined", 629941, 256),
   ("field.promisecapability-records.Promise", 2688749, 64),
   ("term.%Promise%", 2707710, 24)]

/-! ## 6. The gate -/

open Elab Command in
elab "#ecmarkup_scanner_gate" : command => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "ecmarkup scanner: source file has no parent directory"
  let projectRoot ← liftIO <| Gates.Common.findProjectRoot sourceDirectory
  let sourcePath := projectRoot / sourceRelativePath
  unless ← liftIO sourcePath.pathExists do
    throwError "ecmarkup scanner: missing the pinned source {sourceRelativePath}"
  let bytes ← liftIO <| IO.FS.readBinFile sourcePath
  unless bytes.size == sourceSize do
    throwError "ecmarkup scanner: {sourceRelativePath} is {bytes.size} bytes; the pin is {sourceSize}"
  -- The clause forest, the tables, the algorithm blocks, and the encoding
  -- facts of section 3 of the packet, over the two frozen windows.
  let mut clauseCount : Nat := 0
  let mut tableCount : Nat := 0
  let mut bodyRowCount : Nat := 0
  let mut stepCount : Nat := 0
  let mut aoidCount : Nat := 0
  let mut typedCount : Nat := 0
  let mut headerBlocks : Nat := 0
  let mut descriptions : Nat := 0
  let mut dfnCount : Nat := 0
  let mut namedDfns : Nat := 0
  let mut nonAscii : Nat := 0
  let mut tabs : Nat := 0
  let mut carriageReturns : Nat := 0
  let mut levelCounts : Array (Nat × Nat) := #[]
  for (windowB, windowE) in windows do
    for i in [windowB:windowE] do
      let byte := Gates.Ecmarkup.byteAt bytes i
      if byte.toNat ≥ 0x80 then nonAscii := nonAscii + 1
      if byte == 0x09 then tabs := tabs + 1
      if byte == 0x0d then carriageReturns := carriageReturns + 1
    let tags ←
      match Gates.Ecmarkup.scanTags bytes windowB windowE with
      | .error message => throwError "ecmarkup scanner: {message}"
      | .ok tags => pure tags
    for tag in tags do
      if tag.isClose then continue
      if tag.name == "emu-table" then tableCount := tableCount + 1
      if tag.name == "dfn" then dfnCount := dfnCount + 1
      if tag.name == "dl" && (Gates.Ecmarkup.attrValue? bytes tag.b tag.e "class").getD "" == "header" then
        headerBlocks := headerBlocks + 1
      if tag.name == "dt" then descriptions := descriptions + 1
    -- Review debt D6, first half: the nameless-`<dfn>` refusal does not fire at
    -- the pin. Every in-scope `<dfn>` derives a non-empty name, by the same
    -- ladder `Gates.Ecmarkup.termRows` uses — the `id` attribute, else the
    -- tag-stripped, whitespace-normalised inner text — re-implemented here from
    -- the public scanner surface rather than called, so the two readings are
    -- independent.
    for k in [0:tags.size] do
      let t := tags.getD k default
      if t.name != "dfn" || t.isClose then continue
      let some dc := Gates.Ecmarkup.matchClose tags k
        | throwError "ecmarkup scanner: the <dfn> opened at byte {t.b} is never closed"
      let text :=
        Gates.Ecmarkup.normalizeWhitespace
          (Gates.Ecmarkup.stripTags
            ((Gates.Ecmarkup.sliceString? bytes t.e (tags.getD dc default).b).getD ""))
      let name := (Gates.Ecmarkup.attrValue? bytes t.b t.e "id").getD text
      if name.isEmpty then
        throwError "ecmarkup scanner: the <dfn> at byte {t.b} derives an empty name, so the nameless-<dfn> refusal of Gates/Ecmarkup.lean fires at this pin"
      namedDfns := namedDfns + 1
    match Gates.Ecmarkup.scanClauses bytes windowB windowE with
    | .error message => throwError "ecmarkup scanner: {message}"
    | .ok cs =>
      clauseCount := clauseCount + cs.size
      for c in cs do
        if !c.aoid.isEmpty then aoidCount := aoidCount + 1
        if !c.kindAttr.isEmpty then
          typedCount := typedCount + 1
          unless Gates.Ecmarkup.clauseTypes.contains c.kindAttr do
            throwError "ecmarkup scanner: the clause {c.id} carries the unhandled type {c.kindAttr}"
        -- R-P3: the escaping round-trips on every in-scope clause id.
        let name := Gates.Ecmarkup.withoutSecPrefix c.id
        unless Gates.Ecmarkup.unescapeId (Gates.Ecmarkup.escapeId name) == some name do
          throwError "ecmarkup scanner: the R-P3 escaping does not round-trip on the clause id {c.id}"
    match Gates.Ecmarkup.scanTableRows bytes windowB windowE with
    | .error message => throwError "ecmarkup scanner: {message}"
    | .ok rs =>
      bodyRowCount := bodyRowCount + rs.size
      for r in rs do
        unless r.cells.size == 3 do
          throwError "ecmarkup scanner: the body row at byte {r.b} has {r.cells.size} cells"
    match Gates.Ecmarkup.scanSteps bytes windowB windowE with
    | .error message => throwError "ecmarkup scanner: {message}"
    | .ok ss =>
      stepCount := stepCount + ss.size
      for s in ss do
        if levelCounts.any (fun entry => entry.1 == s.level) then
          levelCounts := levelCounts.map
            (fun entry => if entry.1 == s.level then (entry.1, entry.2 + 1) else entry)
        else
          levelCounts := levelCounts.push (s.level, 1)
  unless clauseCount == expectedClauses do
    throwError "ecmarkup scanner: {clauseCount} clauses in scope; the packet freezes {expectedClauses}"
  unless tableCount == expectedTables do
    throwError "ecmarkup scanner: {tableCount} <emu-table> blocks; the packet freezes {expectedTables}"
  unless bodyRowCount == expectedBodyRows do
    throwError "ecmarkup scanner: {bodyRowCount} table body rows; the packet freezes {expectedBodyRows}"
  unless stepCount == expectedSteps do
    throwError "ecmarkup scanner: {stepCount} step lines; the packet freezes {expectedSteps}"
  unless aoidCount == expectedAoids do
    throwError "ecmarkup scanner: {aoidCount} aoid attributes; the packet freezes {expectedAoids}"
  unless typedCount == expectedTypedClauses do
    throwError "ecmarkup scanner: {typedCount} typed clauses; the packet freezes {expectedTypedClauses}"
  unless headerBlocks == expectedHeaderBlocks do
    throwError "ecmarkup scanner: {headerBlocks} <dl class=\"header\"> blocks; the packet freezes {expectedHeaderBlocks}"
  unless descriptions == expectedDescriptions do
    throwError "ecmarkup scanner: {descriptions} <dt> elements; the packet freezes {expectedDescriptions}"
  unless dfnCount == expectedDfns do
    throwError "ecmarkup scanner: {dfnCount} <dfn> elements; the packet freezes {expectedDfns}"
  unless namedDfns == expectedDfns do
    throwError "ecmarkup scanner: {namedDfns} of {expectedDfns} in-scope <dfn> elements derive a name"
  unless nonAscii == expectedNonAscii do
    throwError "ecmarkup scanner: {nonAscii} non-ASCII bytes in scope; the packet freezes {expectedNonAscii}"
  unless tabs == 0 && carriageReturns == 0 do
    throwError "ecmarkup scanner: {tabs} tab and {carriageReturns} CR bytes in scope; the packet freezes zero of each"
  for (level, expected) in expectedLevels do
    let observed :=
      levelCounts.foldl (fun acc entry => if entry.1 == level then acc + entry.2 else acc) 0
    unless observed == expected do
      throwError "ecmarkup scanner: {observed} step lines at level {level}; the packet freezes {expected}"
  unless levelCounts.size == expectedLevels.length do
    throwError "ecmarkup scanner: step levels {levelCounts.toList} outside the frozen four"
  -- The 77 rows, byte for byte.
  let produced ←
    match Gates.Ecmarkup.rows bytes windows with
    | .error message => throwError "ecmarkup scanner: {message}"
    | .ok rs => pure rs
  unless produced.size == frozenRows.size do
    throwError "ecmarkup scanner: the scanner produced {produced.size} rows; the packet freezes {frozenRows.size}"
  for (kindName, expected) in expectedKindCounts do
    let observed :=
      produced.foldl (fun acc r => if r.kind == kindName then acc + 1 else acc) 0
    unless observed == expected do
      throwError "ecmarkup scanner: {observed} {kindName} row(s); the packet freezes {expected}"
  let bulletCount :=
    produced.foldl (fun acc r => if r.kind == "requirement" then acc + 1 else acc) 0
  unless bulletCount == expectedBullets do
    throwError "ecmarkup scanner: {bulletCount} requirement bullets; the packet freezes {expectedBullets}"
  for i in [0:produced.size] do
    let got := produced.getD i default
    let want := frozenRows.getD i default
    unless got.kind == want.kind && got.id == want.id do
      throwError "ecmarkup scanner: row {i} is {got.kind} {got.id}; the packet freezes {want.kind} {want.id}"
    unless got.b == want.spanB && got.e == want.spanE do
      throwError "ecmarkup scanner: {want.id} spans [{got.b}, {got.e}); the packet freezes [{want.spanB}, {want.spanE})"
    let recomputed := Gates.Sha256.hexDigest (bytes.extract want.spanB want.spanE)
    unless recomputed == want.digest do
      throwError "ecmarkup scanner: the pinned bytes [{want.spanB}, {want.spanE}) hash to {recomputed}; the packet freezes {want.digest} for {want.id}"
    let some _ := Gates.Census.sliceString? bytes want.spanB (want.spanB + want.anchorLen)
      | throwError "ecmarkup scanner: the {want.anchorLen}-byte anchor of {want.id} is not valid UTF-8"
    unless want.spanB + want.anchorLen ≤ bytes.size do
      throwError "ecmarkup scanner: the anchor of {want.id} runs past the end of the pinned bytes"
  -- The file order is strictly increasing in the generator's sort key.
  for i in [1:produced.size] do
    let previous := (produced.getD (i - 1) default).sortKey
    let current := (produced.getD i default).sortKey
    unless previous < current do
      throwError "ecmarkup scanner: rows {i - 1} and {i} are not strictly increasing in kind then id ({previous}, {current})"
  -- The three anchor-length choices, against the real chooser.
  for (rowId, start, expected) in anchorLengthProbes do
    match Gates.Census.chooseAnchorLength bytes start with
    | .error rival =>
      throwError "ecmarkup scanner: no unique anchor for {rowId}; its span at byte {start} is repeated at byte {rival}"
    | .ok observed =>
      unless observed == expected do
        throwError "ecmarkup scanner: Gates.Census.chooseAnchorLength picks {observed} bytes for {rowId}; the packet freezes {expected}"
  -- Review debt D6, second half: the `rootWindow` occurrence cap does not fire
  -- at the pin. `rootWindow` is the one function of the scanner that reads the
  -- whole 2,978,793-byte file, and the cap hit is its first refusal, so an
  -- `.ok` for both authored root ids is the check that the cap still has room
  -- here. The two windows it returns must be the two the packet freezes.
  for i in [0:rootClauseIds.size] do
    let clauseId := rootClauseIds.getD i ""
    match Gates.Ecmarkup.rootWindow bytes clauseId with
    | .error message =>
      throwError "ecmarkup scanner: Gates.Ecmarkup.rootWindow refuses the authored root clause id {clauseId}: {message}"
    | .ok (observedB, observedE) =>
      let (wantB, wantE) := windows.getD i (0, 0)
      unless observedB == wantB && observedE == wantE do
        throwError "ecmarkup scanner: rootWindow resolves {clauseId} to [{observedB}, {observedE}); the packet freezes [{wantB}, {wantE})"
  logInfo
    m!"ecmarkup scanner: {clauseCount} clauses, {tableCount} tables, {bodyRowCount} body rows, {expectedBullets} requirement bullets, {stepCount} step lines, {aoidCount} aoid, {dfnCount} dfn all named, {nonAscii} non-ASCII bytes over the two frozen windows of {sourceRelativePath}; {produced.size} rows verified against the packet, 3 anchor lengths against Gates.Census.chooseAnchorLength, and both root clause ids resolved without the rootWindow occurrence cap firing"

#ecmarkup_scanner_gate

end WhatwgTest.Audit.Ecma262.EcmarkupScanner
