import WhatwgGates.DeclSnapshot
import WhatwgTest.Audit.Freeze

/-!
# Declaration snapshot contract battery

Breaker-owned and frozen before implementation. Packet:
`test/contracts/declaration-snapshot.contract.md`, which is the authority on
every number, spelling and message below. Ruling R-W5 of `COORDINATION.md`
adopts the snapshot (debt D47); design record
`docs/research/2026-10-01-w6-freeze-registry-design.md`, sections 2.7 and 6.3
and appendix B.

This battery is a tooling contract. It asserts no WHATWG semantics and grants
no coverage state. It exercises the pure core of `Gates.DeclSnapshot` over
small planted inputs: the walk, the loader and the files are `cli`'s, and
`cli` is only ascribed here.

It is red for one reason only: the module `WhatwgGates.DeclSnapshot` does not
exist yet. The builder creates it; the builder does not edit this file.

Sections:

1. the public declarations, by exact ascription, and the frozen constants;
2. the canonical type text and its digest, and the field escaping;
3. entry decoding, over values in the form `#whatwg_freeze` adds;
4. the authored inputs: record files and census projections;
5. rows and the rendered projection;
6. the nine join failures, each on a planted input, and two accepted
   controls.

Every `#guard` below was run against a scratch implementation of the pure
core before this file was committed (packet section 15).
-/

set_option autoImplicit false

/-! ## 1. Public declarations -/

#whatwg_freeze (@Gates.DeclSnapshot.Decl : Type)
#whatwg_freeze (@Gates.DeclSnapshot.Decl.mk :
  Lean.Name → Lean.Name → String → Bool → Nat → String → List Lean.Name →
    Gates.DeclSnapshot.Decl)
#whatwg_freeze (@Gates.DeclSnapshot.EntryData : Type)
#whatwg_freeze (@Gates.DeclSnapshot.EntryData.mk :
  Lean.Name → Lean.Name → Option (List Lean.Name) → Option String → Option String →
    Option String → List String → Gates.DeclSnapshot.EntryData)
#whatwg_freeze (@Gates.DeclSnapshot.Record : Type)
#whatwg_freeze (@Gates.DeclSnapshot.Record.mk :
  String → String → String → String → String → String → String → String → String →
    String → String → Gates.DeclSnapshot.Record)
#whatwg_freeze (@Gates.DeclSnapshot.CensusRow : Type)
#whatwg_freeze (@Gates.DeclSnapshot.CensusRow.mk : String → String → Gates.DeclSnapshot.CensusRow)
#whatwg_freeze (@Gates.DeclSnapshot.JoinInput : Type)
#whatwg_freeze (@Gates.DeclSnapshot.JoinInput.mk :
  List String → Array Gates.DeclSnapshot.Decl → Array Gates.DeclSnapshot.EntryData →
    Array Gates.DeclSnapshot.Record → Array Gates.DeclSnapshot.CensusRow → List String →
      Gates.DeclSnapshot.JoinInput)
#whatwg_freeze (@Gates.DeclSnapshot.Row : Type)
#whatwg_freeze (@Gates.DeclSnapshot.Row.mk :
  String → String → String → String → Nat → String → List String → List String → String →
    String → String → List String → String → String → Gates.DeclSnapshot.Row)

#whatwg_freeze (@Gates.DeclSnapshot.formatVersion : String)
#whatwg_freeze (@Gates.DeclSnapshot.regenerateCommand : String)
#whatwg_freeze (@Gates.DeclSnapshot.outputDirectory : String)
#whatwg_freeze (@Gates.DeclSnapshot.recordsDirectory : String)
#whatwg_freeze (@Gates.DeclSnapshot.recordedPrefixes : List String)
#whatwg_freeze (@Gates.DeclSnapshot.libraries : List (String × Lean.Name))
#whatwg_freeze (@Gates.DeclSnapshot.roles : List String)
#whatwg_freeze (@Gates.DeclSnapshot.dispositions : List String)
#whatwg_freeze (@Gates.DeclSnapshot.columns : List String)

#whatwg_freeze (@Gates.DeclSnapshot.libraryOf : Lean.Name → Option String)
#whatwg_freeze (@Gates.DeclSnapshot.escapeField : String → String)
#whatwg_freeze (@Gates.DeclSnapshot.levelText : Lean.Level → String)
#whatwg_freeze (@Gates.DeclSnapshot.typeText : Lean.Expr → String)
#whatwg_freeze (@Gates.DeclSnapshot.typeDigest : Lean.Expr → String)
#whatwg_freeze (@Gates.DeclSnapshot.kindOf : Lean.ConstantInfo → String)
#whatwg_freeze (@Gates.DeclSnapshot.isRecorded : List String → String → Bool)
#whatwg_freeze (@Gates.DeclSnapshot.entryDeclaration? : Lean.Name → Lean.Name → Option Lean.Name)
#whatwg_freeze (@Gates.DeclSnapshot.decodeName : Lean.Expr → Except String Lean.Name)
#whatwg_freeze (@Gates.DeclSnapshot.decodeEntry :
  Lean.Name → Lean.Expr → Except String Gates.DeclSnapshot.EntryData)
#whatwg_freeze (@Gates.DeclSnapshot.parseRecords :
  String → String → Except String (Array Gates.DeclSnapshot.Record))
#whatwg_freeze (@Gates.DeclSnapshot.parseCensus :
  String → Except String (Array Gates.DeclSnapshot.CensusRow))
#whatwg_freeze (@Gates.DeclSnapshot.duplicateRecords :
  Array Gates.DeclSnapshot.Record → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.duplicateCensusIds :
  Array Gates.DeclSnapshot.CensusRow → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.coveringRecord? :
  Array Gates.DeclSnapshot.Record → String → Option Gates.DeclSnapshot.Record)
#whatwg_freeze (@Gates.DeclSnapshot.rows :
  Gates.DeclSnapshot.JoinInput → Array Gates.DeclSnapshot.Row)
#whatwg_freeze (@Gates.DeclSnapshot.renderRow : Gates.DeclSnapshot.Row → String)
#whatwg_freeze (@Gates.DeclSnapshot.renderFile :
  String → Array Gates.DeclSnapshot.Row → String)
#whatwg_freeze (@Gates.DeclSnapshot.projection :
  Gates.DeclSnapshot.JoinInput → List (String × String))
#whatwg_freeze (@Gates.DeclSnapshot.unrecordedTypes : Gates.DeclSnapshot.JoinInput → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.uncoveredDeclarations :
  Gates.DeclSnapshot.JoinInput → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.danglingRecords : Gates.DeclSnapshot.JoinInput → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.sharedAnchors : Gates.DeclSnapshot.JoinInput → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.orphanRelations : Gates.DeclSnapshot.JoinInput → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.unknownAnchors : Gates.DeclSnapshot.JoinInput → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.unrecordedEntries : Gates.DeclSnapshot.JoinInput → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.disagreeingEntries :
  Gates.DeclSnapshot.JoinInput → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.byteDrift :
  List (String × String) → List (String × String) → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.joinFailures : Gates.DeclSnapshot.JoinInput → Array String)
#whatwg_freeze (@Gates.DeclSnapshot.cli : List String → IO UInt32)

namespace WhatwgTest.Audit.DeclSnapshotContract

open Gates.DeclSnapshot

-- The frozen constants. `recordedPrefixes` is empty at the landing (R-W5).
#guard formatVersion == "1"
#guard regenerateCommand == "lake exe whatwg_declsnapshot --write"
#guard outputDirectory == "generated/declarations"
#guard recordsDirectory == "test/records"
#guard recordedPrefixes == []
-- R-W17, 2026-10-01: an eighth library. This packet and promise slice Q5 were
-- frozen in parallel; Q5 landed the Lake library `WhatwgSignatures` (ruling
-- R-W3), and the generator refuses a production module that belongs to no
-- library, so the frozen seven became eight. Amended by the coordinator's
-- ruling; no other row of this battery changes meaning.
-- R-S4, 2026-10-11: a ninth library. Slice S2 of `docs/SVG-PACKAGE-PLAN.md` landed the
-- Lake library `WhatwgSvg`, and the generator refuses a production module that belongs to
-- no library. Amended by the seat under ruling R-S1; no other row changes meaning.
-- R-S10, 2026-10-11: a tenth library, `WhatwgAuto`, the named Aesop rule banks.
#guard libraries ==
  [("Whatwg", `Whatwg), ("WhatwgInfra", `Whatwg.Infra), ("WhatwgEcma262", `Whatwg.Ecma262),
   ("WhatwgWebIdl", `Whatwg.WebIdl), ("WhatwgUrl", `Whatwg.Url), ("WhatwgHtml", `Whatwg.Html),
   ("WhatwgStreams", `Whatwg.Streams), ("WhatwgSignatures", `Whatwg.Signatures),
   ("WhatwgSvg", `Whatwg.Svg), ("WhatwgAuto", `Whatwg.Auto)]
#guard roles ==
  ["canonical", "view", "adapter", "separate-calculus", "derived", "helper",
   "foreign-boundary", "target-only"]
#guard dispositions ==
  ["owned", "requirement", "foreignBoundary", "hostOnly", "refused", "evidenceOnly",
   "targetOnly", "-"]
#guard columns ==
  ["name", "module", "kind", "origin", "universes", "type-sha256", "axioms", "frozen-by",
   "mask", "anchor", "graph", "counterexamples", "record", "route"]

-- Library membership: the umbrella owns only itself; every other library
-- owns its root and everything under it; a module outside them has none.
#guard libraryOf `Whatwg == some "Whatwg"
#guard libraryOf `Whatwg.Streams == some "WhatwgStreams"
#guard libraryOf `Whatwg.Streams.Kernel.Step == some "WhatwgStreams"
#guard libraryOf `Whatwg.Infra.Text.Utf8 == some "WhatwgInfra"
#guard libraryOf `Whatwg.Effects == none
#guard libraryOf `WhatwgTest.Audit.Freeze == none

-- Recorded prefixes compare whole components of the rendered name.
#guard isRecorded ["Whatwg.Streams.Kernel"] "Whatwg.Streams.Kernel"
#guard isRecorded ["Whatwg.Streams.Kernel"] "Whatwg.Streams.Kernel.step"
#guard !isRecorded ["Whatwg.Streams.Kernel"] "Whatwg.Streams.KernelLaws.step"
#guard !isRecorded [] "Whatwg.Streams.Kernel.step"

-- The naming rule of `#whatwg_freeze`, inverted.
#guard entryDeclaration? `WhatwgTest.M `WhatwgTest.M.frozen.Whatwg.Streams.Kernel.step ==
  some `Whatwg.Streams.Kernel.step
#guard entryDeclaration? `WhatwgTest.M `WhatwgTest.M.frozen == none
#guard entryDeclaration? `WhatwgTest.M `WhatwgTest.N.frozen.Whatwg.a == none
#guard entryDeclaration? `WhatwgTest.M `WhatwgTest.M.helper == none

/-! ## 2. The canonical type text, its digest, and field escaping

`typeText` keeps binder names, binder annotations, universe levels, literals
and the `let`/`have` flag, and drops metadata. The digest is SHA-256 of its
UTF-8 bytes; the expected hexadecimal below was computed independently with
.NET `System.Security.Cryptography.SHA256`. -/

#guard levelText (.max (.succ .zero) (.param `u)) == "(max (s 0) (p u))"
#guard levelText (.imax .zero (.param `v)) == "(imax 0 (p v))"
#guard typeText (.forallE `α (.sort (.succ .zero)) (.forallE `x (.bvar 0) (.bvar 1) .default)
    .implicit) == "(P α i (S (s 0)) (P x d #0 #1))"
#guard typeText (.forallE `x (.const `Nat []) (.bvar 0) .strictImplicit) ==
  "(P x s (C Nat []) #0)"
#guard typeText (.forallE `x (.const `Nat []) (.bvar 0) .instImplicit) ==
  "(P x c (C Nat []) #0)"
#guard typeText (.const `List [.param `u, .zero]) == "(C List [(p u) 0])"
#guard typeText (.app (.const `f []) (.lit (.natVal 7))) == "(A (C f []) (N 7))"
#guard typeText (.lit (.strVal "a b")) == "(T 3 a b)"
#guard typeText (.lam `y (.const `Nat []) (.bvar 0) .default) == "(L y d (C Nat []) #0)"
#guard typeText (.letE `z (.const `Nat []) (.lit (.natVal 1)) (.bvar 0) true) ==
  "(E z h (C Nat []) (N 1) #0)"
#guard typeText (.letE `z (.const `Nat []) (.lit (.natVal 1)) (.bvar 0) false) ==
  "(E z l (C Nat []) (N 1) #0)"
#guard typeText (.mdata {} (.bvar 3)) == "#3"
#guard typeText (.proj `Prod 1 (.bvar 0)) == "(J Prod 1 #0)"
#guard typeDigest (.forallE `α (.sort (.succ .zero)) (.forallE `x (.bvar 0) (.bvar 1) .default)
    .implicit) == "1e4c2ba31ee3c58ae52ce67494ded78b83f5e8d2651165af793bdf81fc5544ff"
-- Binder names and annotations reach the digest (the freeze judgment ignores
-- both; the snapshot does not).
#guard typeDigest (.forallE `x (.const `Nat []) (.bvar 0) .default) !=
  typeDigest (.forallE `y (.const `Nat []) (.bvar 0) .default)
#guard typeDigest (.forallE `x (.const `Nat []) (.bvar 0) .default) !=
  typeDigest (.forallE `x (.const `Nat []) (.bvar 0) .implicit)

#guard escapeField "a\\b\tc\nd\re,f" == "a\\\\b\\tc\\nd\\re\\,f"
#guard escapeField "Whatwg.Streams.«term_+_»" == "Whatwg.Streams.«term_+_»"

/-! ## 3. Entry decoding

An entry's value is `WhatwgTest.Audit.Freeze.Entry.mk` applied to the
`Lean.toExpr` forms of its six fields, the mask as one of the three
constructor constants of `WhatwgTest.Audit.Freeze.ObservationMask` (contract
`test/contracts/freeze-registry.contract.md`, section 6). -/

private def maskType : Lean.Expr := .const `WhatwgTest.Audit.Freeze.ObservationMask []

private def noMask : Lean.Expr := Lean.mkApp (.const ``Option.none [.zero]) maskType

private def someMask (mask : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (.const ``Option.some [.zero]) maskType mask

private def entryValue (declaration : Lean.Name) (axioms : Option (List Lean.Name))
    (mask : Lean.Expr) (anchor graph : Option String) (counterexamples : List String) :
    Lean.Expr :=
  Lean.mkAppN (.const `WhatwgTest.Audit.Freeze.Entry.mk [])
    #[Lean.toExpr declaration, Lean.toExpr axioms, mask, Lean.toExpr anchor,
      Lean.toExpr graph, Lean.toExpr counterexamples]

#guard (decodeEntry `WhatwgTest.Streams.Kernel.KernelLaws
    (entryValue `Whatwg.Streams.Kernel.step_idle (some [`propext, `Quot.sound])
      (someMask (.const `WhatwgTest.Audit.Freeze.ObservationMask.chunksAndOutcome []))
      (some "op.fixture-step") (some "KERNEL-PG") ["WS-KERNEL-CE-002", "WS-KERNEL-CE-001"])).toOption ==
  some { recording := `WhatwgTest.Streams.Kernel.KernelLaws,
         declaration := `Whatwg.Streams.Kernel.step_idle,
         axioms := some [`propext, `Quot.sound], mask := some "M1",
         anchor := some "op.fixture-step", graph := some "KERNEL-PG",
         counterexamples := ["WS-KERNEL-CE-002", "WS-KERNEL-CE-001"] }

#guard (decodeEntry `WhatwgTest.M
    (entryValue `Whatwg.Streams.Kernel.step none
      (someMask (.const `WhatwgTest.Audit.Freeze.ObservationMask.settlementOrder [])) none none
      [])).toOption ==
  some { recording := `WhatwgTest.M, declaration := `Whatwg.Streams.Kernel.step,
         axioms := none, mask := some "M2", anchor := none, graph := none,
         counterexamples := [] }

#guard (decodeEntry `WhatwgTest.M
    (entryValue `Whatwg.Infra.ByteSequence.length (some [])
      (someMask (Lean.mkApp (.const `WhatwgTest.Audit.Freeze.ObservationMask.notApplicable [])
        (Lean.mkStrLit "an equation, so no observation"))) none none [])).toOption ==
  some { recording := `WhatwgTest.M, declaration := `Whatwg.Infra.ByteSequence.length,
         axioms := some [], mask := some "none:an equation, so no observation",
         anchor := none, graph := none, counterexamples := [] }

#guard (decodeEntry `WhatwgTest.M
    (entryValue `Whatwg.Url.PercentEncoding.percentEncodeByte_eq none noMask none none [])).toOption ==
  some { recording := `WhatwgTest.M, declaration := `Whatwg.Url.PercentEncoding.percentEncodeByte_eq,
         axioms := none, mask := none, anchor := none, graph := none, counterexamples := [] }

-- `Lean.toExpr` writes a name of at most eight string components with
-- `Lean.Name.mkStrN` and a longer one, or one with a numeric component, with
-- `Lean.Name.str` and `Lean.Name.num`; the decoder reads all three.
#guard (decodeName (Lean.toExpr `a.b.c)).toOption == some `a.b.c
#guard (decodeName (Lean.toExpr `a.b.c.d.e.f.g.h.i.j)).toOption == some `a.b.c.d.e.f.g.h.i.j
#guard (decodeName (Lean.toExpr (Lean.Name.num `a.b 3))).toOption == some (Lean.Name.num `a.b 3)
#guard (decodeName (Lean.toExpr Lean.Name.anonymous)).toOption == some Lean.Name.anonymous

-- A value of any other shape is refused, with the reason.
#guard (match decodeEntry `WhatwgTest.M (.const `Nat []) with
  | .error message =>
    message == "the value is not WhatwgTest.Audit.Freeze.Entry.mk applied to six fields"
  | .ok _ => false)
#guard (decodeEntry `WhatwgTest.M
    (entryValue `Whatwg.a none (someMask (.const `Nat [])) none none [])).toOption == none

/-! ## 4. The authored inputs -/

private def tab (fields : List String) : String := "\t".intercalate fields

private def kernelRecords : String :=
  "# w8a kernel records\n\n" ++
  tab ["Whatwg.Streams.Kernel.Config", "W8a breaker", "canonical", "-", "slot.fixture-config",
    "2222222222222222222222222222222222222222222222222222222222222222", "owned",
    "test/contracts/kernel.contract.md", "WhatwgTest.Streams.Kernel.KernelContract",
    "KERNEL-PG"] ++ "\n" ++
  tab ["Whatwg.Streams.Kernel.Config.*", "W8a breaker", "helper",
    "Whatwg.Streams.Kernel.Config", "-", "-", "-", "test/contracts/kernel.contract.md",
    "WhatwgTest.Streams.Kernel.KernelContract", "KERNEL-PG"] ++ "\n"

#guard (parseRecords "w8a-kernel" kernelRecords).toOption ==
  some #[
    { packet := "w8a-kernel", name := "Whatwg.Streams.Kernel.Config", owner := "W8a breaker",
      role := "canonical", related := "-", anchor := "slot.fixture-config",
      anchorDigest := "2222222222222222222222222222222222222222222222222222222222222222",
      disposition := "owned", contract := "test/contracts/kernel.contract.md",
      battery := "WhatwgTest.Streams.Kernel.KernelContract", route := "KERNEL-PG" },
    { packet := "w8a-kernel", name := "Whatwg.Streams.Kernel.Config.*", owner := "W8a breaker",
      role := "helper", related := "Whatwg.Streams.Kernel.Config", anchor := "-",
      anchorDigest := "-", disposition := "-", contract := "test/contracts/kernel.contract.md",
      battery := "WhatwgTest.Streams.Kernel.KernelContract", route := "KERNEL-PG" }]

private def refusal (packet text : String) : String :=
  match parseRecords packet text with
  | .error message => message
  | .ok _ => "accepted"

private def row (fields : List String) : String := tab fields ++ "\n"

private def goodFields : List String :=
  ["Whatwg.Streams.Kernel.step", "W8a breaker", "canonical", "-", "-", "-", "-",
   "test/contracts/kernel.contract.md", "WhatwgTest.Streams.Kernel.KernelContract",
   "KERNEL-PG"]

#guard refusal "p" (row goodFields) == "accepted"
#guard refusal "p" (row (goodFields.take 9)) ==
  "test/records/p.tsv line 1: 9 fields; a record has 10"
#guard refusal "p" ("# c\n" ++ row (goodFields.set 1 "")) ==
  "test/records/p.tsv line 2: field 2 is empty"
#guard refusal "p" (row (goodFields.set 0 "Whatwg.*.x")) ==
  "test/records/p.tsv line 1: Whatwg.*.x is neither a full name nor a family <prefix>.*"
#guard refusal "p" (row (goodFields.set 2 "owner")) ==
  "record p:Whatwg.Streams.Kernel.step: role owner is not one of canonical, view, adapter, separate-calculus, derived, helper, foreign-boundary, target-only"
#guard refusal "p" (row (goodFields.set 3 "Whatwg.Streams.Kernel.Config")) ==
  "record p:Whatwg.Streams.Kernel.step: a canonical record relates to nothing and every other record relates to a named declaration"
#guard refusal "p" (row ((goodFields.set 2 "view"))) ==
  "record p:Whatwg.Streams.Kernel.step: a canonical record relates to nothing and every other record relates to a named declaration"
#guard refusal "p" (row (goodFields.set 4 "op.fixture-step")) ==
  "record p:Whatwg.Streams.Kernel.step: an anchor and its span digest are written together or not at all"
#guard refusal "p" (row ((goodFields.set 4 "op.fixture-step").set 5 "ABC")) ==
  "record p:Whatwg.Streams.Kernel.step: the span digest is not 64 lowercase hexadecimal digits"
#guard refusal "p" (row (goodFields.set 6 "owned")) ==
  "record p:Whatwg.Streams.Kernel.step: a record carries a disposition exactly when it carries an anchor"
#guard refusal "p" (row (goodFields.set 6 "modelled")) ==
  "record p:Whatwg.Streams.Kernel.step: disposition modelled is not one of owned, requirement, foreignBoundary, hostOnly, refused, evidenceOnly, targetOnly, -"
#guard refusal "p" (row (goodFields.set 7 "docs/kernel.md")) ==
  "record p:Whatwg.Streams.Kernel.step: contract docs/kernel.md is not a path test/contracts/<name>.contract.md"
#guard refusal "p" (row (goodFields.set 8 "Whatwg.Streams.Kernel")) ==
  "record p:Whatwg.Streams.Kernel.step: battery Whatwg.Streams.Kernel is not a module under WhatwgTest"
#guard refusal "p" (row goodFields ++ row goodFields) ==
  "record p:Whatwg.Streams.Kernel.step: Whatwg.Streams.Kernel.step is recorded twice in test/records/p.tsv"
#guard refusal "p" (tab goodFields ++ "\r\n") ==
  "test/records/p.tsv carries a CR byte; authored records are LF"

-- Both census projection formats yield (row id, span digest).
#guard (parseCensus
    ("#census format=1 generator=Gates.Census input=x rows=2\n" ++
     "op|op.fixture-step|<div>|10|20|1111111111111111111111111111111111111111111111111111111111111111|x\n" ++
     "slot|slot.fixture-config|<dfn>|30|40|2222222222222222222222222222222222222222222222222222222222222222|y\\|z\n")).toOption ==
  some #[{ id := "op.fixture-step",
           digest := "1111111111111111111111111111111111111111111111111111111111111111" },
         { id := "slot.fixture-config",
           digest := "2222222222222222222222222222222222222222222222222222222222222222" }]
#guard (parseCensus
    ("#url-census format=1 generator=Gates.UrlCensusInput input-sha256=x rows=1\n" ++
     "#kind\tid\tbyte-start\tbyte-end\tspan-sha256\tanchor-end\n" ++
     "#input spans-sha256=y\n" ++
     "op\top.url-fixture\t5\t9\t3333333333333333333333333333333333333333333333333333333333333333\t7\n")).toOption ==
  some #[{ id := "op.url-fixture",
           digest := "3333333333333333333333333333333333333333333333333333333333333333" }]
#guard (parseCensus "#other format=1\n").toOption == none

-- Input refusals across files: a name recorded twice (in one packet or two)
-- and a census row id that occurs twice across the projections.
#guard duplicateRecords
    #[{ (default : Record) with packet := "a", name := "Whatwg.x" },
      { (default : Record) with packet := "b", name := "Whatwg.x" },
      { (default : Record) with packet := "b", name := "Whatwg.y" }] ==
  #["declaration snapshot: input: Whatwg.x is recorded 2 times: a:Whatwg.x, b:Whatwg.x"]
#guard duplicateCensusIds
    #[{ id := "op.a", digest := "1" }, { id := "op.b", digest := "2" },
      { id := "op.a", digest := "3" }] ==
  #["declaration snapshot: input: census row id op.a occurs 2 times across the census projections"]

/-! ## 5 and 6. The planted join input

`base` is a recorded prefix with complete records: every exported type has an
exact record, every exported declaration a covering record, every record a
declaration, every anchor one census row with its digest, every relation an
exact record, and the two entries for one declaration agree. -/

private def digestA : String := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

private def censusRows : Array CensusRow :=
  #[{ id := "op.fixture-step",
      digest := "1111111111111111111111111111111111111111111111111111111111111111" },
    { id := "slot.fixture-config",
      digest := "2222222222222222222222222222222222222222222222222222222222222222" }]

private def decl (name : Lean.Name) (kind : String) (authored : Bool)
    (axioms : List Lean.Name := []) : Decl :=
  { name, module := `Whatwg.Streams.Kernel.Step, kind, authored, universes := 0,
    typeDigest := digestA, axioms }

private def kernelDecls : Array Decl :=
  #[decl `Whatwg.Streams.Kernel.Config "inductive" true,
    decl `Whatwg.Streams.Kernel.Config.idle "constructor" true,
    decl `Whatwg.Streams.Kernel.Config.rec "recursor" false,
    decl `Whatwg.Streams.Kernel.Phase "inductive" true,
    decl `Whatwg.Streams.Kernel.step "definition" true,
    decl `Whatwg.Streams.Kernel.step_idle "theorem" true [`Quot.sound, `propext],
    { name := `Whatwg.Streams.Data.Queue, module := `Whatwg.Streams.Data.Queue,
      kind := "inductive", authored := true, universes := 1, typeDigest := digestA,
      axioms := [] }]

private def record (name role related anchor anchorDigest disposition : String) : Record :=
  { packet := "w8a-kernel", name, owner := "W8a breaker", role, related, anchor, anchorDigest,
    disposition, contract := "test/contracts/kernel.contract.md",
    battery := "WhatwgTest.Streams.Kernel.KernelContract", route := "KERNEL-PG" }

private def kernelRecordRows : Array Record :=
  #[record "Whatwg.Streams.Kernel.Config" "canonical" "-" "slot.fixture-config"
      "2222222222222222222222222222222222222222222222222222222222222222" "owned",
    record "Whatwg.Streams.Kernel.Config.*" "helper" "Whatwg.Streams.Kernel.Config" "-" "-" "-",
    record "Whatwg.Streams.Kernel.Phase" "canonical" "-" "-" "-" "-",
    record "Whatwg.Streams.Kernel.step" "canonical" "-" "op.fixture-step"
      "1111111111111111111111111111111111111111111111111111111111111111" "owned",
    record "Whatwg.Streams.Kernel.step_idle" "derived" "Whatwg.Streams.Kernel.step" "-" "-" "-"]

private def lawsEntry : EntryData :=
  { recording := `WhatwgTest.Streams.Kernel.KernelLaws,
    declaration := `Whatwg.Streams.Kernel.step_idle, axioms := some [`propext, `Quot.sound],
    mask := some "M1", anchor := some "op.fixture-step", graph := some "KERNEL-PG",
    counterexamples := ["WS-KERNEL-CE-002", "WS-KERNEL-CE-001"] }

private def contractEntry : EntryData :=
  { recording := `WhatwgTest.Streams.Kernel.KernelContract,
    declaration := `Whatwg.Streams.Kernel.step_idle, axioms := some [`propext, `Quot.sound],
    mask := none, anchor := none, graph := none, counterexamples := ["WS-KERNEL-CE-001"] }

private def base : JoinInput :=
  { recordedPrefixes := ["Whatwg.Streams.Kernel"], decls := kernelDecls,
    entries := #[lawsEntry, contractEntry], records := kernelRecordRows, census := censusRows,
    knownRed := [] }

/-! ### 5. Rows and the rendered projection -/

#guard (coveringRecord? kernelRecordRows "Whatwg.Streams.Kernel.Config.idle").map (·.name) ==
  some "Whatwg.Streams.Kernel.Config.*"
#guard (coveringRecord? kernelRecordRows "Whatwg.Streams.Kernel.Config").map (·.name) ==
  some "Whatwg.Streams.Kernel.Config"
#guard (coveringRecord? kernelRecordRows "Whatwg.Streams.Kernel.ConfigX").map (·.name) == none

#guard renderRow
    { name := "Whatwg.a", module := "Whatwg.M", kind := "theorem", origin := "authored",
      universes := 2, typeDigest := digestA, axioms := ["propext", "Quot.sound"],
      frozenBy := ["WhatwgTest.A", "WhatwgTest.B"], mask := "none:x, y\tz", anchor := "-",
      graph := "-", counterexamples := [], record := "-", route := "-" } ==
  "Whatwg.a\tWhatwg.M\ttheorem\tauthored\t2\t" ++ digestA ++
    "\tpropext,Quot.sound\tWhatwgTest.A,WhatwgTest.B\tnone:x\\, y\\tz\t-\t-\t-\t-\t-"

-- A generated declaration such as an equation lemma can be realized in
-- several modules, and each module's constants yield their own row: a name is
-- not a key, (name, module) is, and rows sort by name, then module.
private def plainRow (name module : String) : Row :=
  { name, module, kind := "theorem", origin := "generated", universes := 0,
    typeDigest := digestA, axioms := [], frozenBy := [], mask := "-", anchor := "-",
    graph := "-", counterexamples := [], record := "-", route := "-" }

#guard renderFile "WhatwgStreams"
    #[plainRow "Whatwg.b" "Whatwg.Streams.A", plainRow "Whatwg.a.eq_1" "Whatwg.Streams.Z",
      plainRow "Whatwg.a.eq_1" "Whatwg.Streams.B"] ==
  "#declarations format=1 generator=Gates.DeclSnapshot library=WhatwgStreams rows=3 " ++
    "regenerate=lake exe whatwg_declsnapshot --write\n" ++
  "#name\tmodule\tkind\torigin\tuniverses\ttype-sha256\taxioms\tfrozen-by\tmask\tanchor\t" ++
    "graph\tcounterexamples\trecord\troute\n" ++
  "Whatwg.a.eq_1\tWhatwg.Streams.B\ttheorem\tgenerated\t0\t" ++ digestA ++
    "\t-\t-\t-\t-\t-\t-\t-\t-\n" ++
  "Whatwg.a.eq_1\tWhatwg.Streams.Z\ttheorem\tgenerated\t0\t" ++ digestA ++
    "\t-\t-\t-\t-\t-\t-\t-\t-\n" ++
  "Whatwg.b\tWhatwg.Streams.A\ttheorem\tgenerated\t0\t" ++ digestA ++
    "\t-\t-\t-\t-\t-\t-\t-\t-\n"

private def streamsProjection : String :=
  "#declarations format=1 generator=Gates.DeclSnapshot library=WhatwgStreams rows=7 " ++
    "regenerate=lake exe whatwg_declsnapshot --write\n" ++
  "#name\tmodule\tkind\torigin\tuniverses\ttype-sha256\taxioms\tfrozen-by\tmask\tanchor\t" ++
    "graph\tcounterexamples\trecord\troute\n" ++
  "Whatwg.Streams.Data.Queue\tWhatwg.Streams.Data.Queue\tinductive\tauthored\t1\t" ++ digestA ++
    "\t-\t-\t-\t-\t-\t-\t-\t-\n" ++
  "Whatwg.Streams.Kernel.Config\tWhatwg.Streams.Kernel.Step\tinductive\tauthored\t0\t" ++
    digestA ++ "\t-\t-\t-\t-\t-\t-\tw8a-kernel:Whatwg.Streams.Kernel.Config\tKERNEL-PG\n" ++
  "Whatwg.Streams.Kernel.Config.idle\tWhatwg.Streams.Kernel.Step\tconstructor\tauthored\t0\t" ++
    digestA ++ "\t-\t-\t-\t-\t-\t-\tw8a-kernel:Whatwg.Streams.Kernel.Config.*\tKERNEL-PG\n" ++
  "Whatwg.Streams.Kernel.Config.rec\tWhatwg.Streams.Kernel.Step\trecursor\tgenerated\t0\t" ++
    digestA ++ "\t-\t-\t-\t-\t-\t-\tw8a-kernel:Whatwg.Streams.Kernel.Config.*\tKERNEL-PG\n" ++
  "Whatwg.Streams.Kernel.Phase\tWhatwg.Streams.Kernel.Step\tinductive\tauthored\t0\t" ++
    digestA ++ "\t-\t-\t-\t-\t-\t-\tw8a-kernel:Whatwg.Streams.Kernel.Phase\tKERNEL-PG\n" ++
  "Whatwg.Streams.Kernel.step\tWhatwg.Streams.Kernel.Step\tdefinition\tauthored\t0\t" ++
    digestA ++ "\t-\t-\t-\t-\t-\t-\tw8a-kernel:Whatwg.Streams.Kernel.step\tKERNEL-PG\n" ++
  "Whatwg.Streams.Kernel.step_idle\tWhatwg.Streams.Kernel.Step\ttheorem\tauthored\t0\t" ++
    digestA ++ "\tpropext,Quot.sound\tWhatwgTest.Streams.Kernel.KernelContract," ++
    "WhatwgTest.Streams.Kernel.KernelLaws\tM1\top.fixture-step\tKERNEL-PG\t" ++
    "WS-KERNEL-CE-001,WS-KERNEL-CE-002\tw8a-kernel:Whatwg.Streams.Kernel.step_idle\tKERNEL-PG\n"

private def emptyProjection (library : String) : String :=
  s!"#declarations format=1 generator=Gates.DeclSnapshot library={library} rows=0 " ++
    "regenerate=lake exe whatwg_declsnapshot --write\n" ++
  "#name\tmodule\tkind\torigin\tuniverses\ttype-sha256\taxioms\tfrozen-by\tmask\tanchor\t" ++
    "graph\tcounterexamples\trecord\troute\n"

-- One file per library, in the order of `libraries`, each with its header and
-- column line; rows sorted by name; an entry's recording modules sorted by
-- name; its counterexample ids merged and sorted.
#guard projection base ==
  [("generated/declarations/Whatwg.tsv", emptyProjection "Whatwg"),
   ("generated/declarations/WhatwgInfra.tsv", emptyProjection "WhatwgInfra"),
   ("generated/declarations/WhatwgEcma262.tsv", emptyProjection "WhatwgEcma262"),
   ("generated/declarations/WhatwgWebIdl.tsv", emptyProjection "WhatwgWebIdl"),
   ("generated/declarations/WhatwgUrl.tsv", emptyProjection "WhatwgUrl"),
   ("generated/declarations/WhatwgHtml.tsv", emptyProjection "WhatwgHtml"),
   ("generated/declarations/WhatwgStreams.tsv", streamsProjection),
   -- R-W17, 2026-10-01: the eighth library's file, empty in this fixture.
   ("generated/declarations/WhatwgSignatures.tsv", emptyProjection "WhatwgSignatures"),
   -- R-S4, 2026-10-11: the ninth library's file, empty in this fixture.
   ("generated/declarations/WhatwgSvg.tsv", emptyProjection "WhatwgSvg"),
   -- R-S10, 2026-10-11: the tenth library's file, empty in this fixture.
   ("generated/declarations/WhatwgAuto.tsv", emptyProjection "WhatwgAuto")]

/-! ### 6. The nine join failures

Accepted control 1: `base` passes every check. Accepted control 2: the
landing state, with no recorded prefix and no record, passes every check
although no declaration has a record and an entry exists: rules 1, 2, 3 and
7 bind nothing until a prefix joins. -/

#guard joinFailures base == #[]

#guard joinFailures { base with recordedPrefixes := [], records := #[] } == #[]

-- Rule 1: an exported type with its own declaration range, under a recorded
-- prefix, with no exact record (a family record covers it, so rule 2 holds).
#guard joinFailures { base with
    records := (kernelRecordRows.filter (·.name != "Whatwg.Streams.Kernel.Phase")).push
      (record "Whatwg.Streams.Kernel.*" "canonical" "-" "-" "-" "-") } ==
  #["declaration snapshot: rule 1: exported type Whatwg.Streams.Kernel.Phase of Whatwg.Streams.Kernel.Step under a recorded prefix has no exact record"]

-- Rule 2: an exported declaration under a recorded prefix that no record
-- covers, exactly or by family.
#guard joinFailures { base with
    decls := kernelDecls.push (decl `Whatwg.Streams.Kernel.extra "definition" true) } ==
  #["declaration snapshot: rule 2: exported declaration Whatwg.Streams.Kernel.extra of Whatwg.Streams.Kernel.Step under a recorded prefix has no covering record"]
-- A generated declaration (no declaration range of its own) is bound too.
#guard joinFailures { base with
    decls := kernelDecls.push (decl `Whatwg.Streams.Kernel.Phase.rec "recursor" false) } ==
  #["declaration snapshot: rule 2: exported declaration Whatwg.Streams.Kernel.Phase.rec of Whatwg.Streams.Kernel.Step under a recorded prefix has no covering record"]

-- Rule 3: a record naming no declaration, unless its battery is declared red.
private def danglingInput : JoinInput :=
  { base with
    records :=
      kernelRecordRows.push (record "Whatwg.Streams.Kernel.missing" "canonical" "-" "-" "-" "-") }

#guard joinFailures danglingInput ==
  #["declaration snapshot: rule 3: record w8a-kernel:Whatwg.Streams.Kernel.missing names no declaration, and its battery WhatwgTest.Streams.Kernel.KernelContract is not declared red"]
#guard joinFailures { danglingInput with
    knownRed := ["WhatwgTest.Streams.Kernel.KernelContract"] } == #[]
-- A family record covering nothing is dangling too; a record outside every
-- recorded prefix is not checked by rule 3.
#guard joinFailures { base with
    records := kernelRecordRows.push
      (record "Whatwg.Streams.Kernel.Phase.*" "helper" "Whatwg.Streams.Kernel.Phase" "-" "-" "-") } ==
  #["declaration snapshot: rule 3: record w8a-kernel:Whatwg.Streams.Kernel.Phase.* names no declaration, and its battery WhatwgTest.Streams.Kernel.KernelContract is not declared red"]
#guard joinFailures { base with
    records := kernelRecordRows.push
      (record "Whatwg.Infra.notYetDeclared" "canonical" "-" "-" "-" "-") } == #[]

-- Rule 4: two records claiming one census row.
#guard joinFailures { base with
    records := (kernelRecordRows.filter (·.name != "Whatwg.Streams.Kernel.Phase")).push
      (record "Whatwg.Streams.Kernel.Phase" "canonical" "-" "op.fixture-step"
        "1111111111111111111111111111111111111111111111111111111111111111" "owned") } ==
  #["declaration snapshot: rule 4: census row op.fixture-step is claimed by 2 records: w8a-kernel:Whatwg.Streams.Kernel.Phase, w8a-kernel:Whatwg.Streams.Kernel.step"]

-- Rule 5: a non-canonical record whose related owner has no exact record.
#guard joinFailures { base with
    records := (kernelRecordRows.filter (·.name != "Whatwg.Streams.Kernel.step_idle")).push
      (record "Whatwg.Streams.Kernel.step_idle" "derived" "Whatwg.Streams.Kernel.stepAux"
        "-" "-" "-") } ==
  #["declaration snapshot: rule 5: record w8a-kernel:Whatwg.Streams.Kernel.step_idle relates to Whatwg.Streams.Kernel.stepAux, which has no exact record"]

-- Rule 6: a record anchor that is no census row id, a record anchor whose
-- digest differs, and an entry anchor that is no census row id. It binds
-- with no recorded prefix too.
#guard joinFailures { base with
    records := (kernelRecordRows.filter (·.name != "Whatwg.Streams.Kernel.step")).push
      (record "Whatwg.Streams.Kernel.step" "canonical" "-" "op.unknown-step"
        "1111111111111111111111111111111111111111111111111111111111111111" "owned") } ==
  #["declaration snapshot: rule 6: record w8a-kernel:Whatwg.Streams.Kernel.step anchors op.unknown-step, which is no census row id"]
#guard joinFailures { base with
    records := (kernelRecordRows.filter (·.name != "Whatwg.Streams.Kernel.step")).push
      (record "Whatwg.Streams.Kernel.step" "canonical" "-" "op.fixture-step"
        "4444444444444444444444444444444444444444444444444444444444444444" "owned") } ==
  #["declaration snapshot: rule 6: record w8a-kernel:Whatwg.Streams.Kernel.step anchors op.fixture-step at 4444444444444444444444444444444444444444444444444444444444444444; the census span digest is 1111111111111111111111111111111111111111111111111111111111111111"]
#guard joinFailures { base with
    recordedPrefixes := [], records := #[],
    entries := #[{ lawsEntry with anchor := some "op.unknown-step" }] } ==
  #["declaration snapshot: rule 6: entry WhatwgTest.Streams.Kernel.KernelLaws.frozen.Whatwg.Streams.Kernel.step_idle anchors op.unknown-step, which is no census row id"]

-- Rule 7: an entry under a recorded prefix whose declaration has no exact
-- record (a family record covers the constructor, so rule 2 holds).
#guard joinFailures { base with
    entries := base.entries.push
      { recording := `WhatwgTest.Streams.Kernel.KernelContract,
        declaration := `Whatwg.Streams.Kernel.Config.idle, axioms := none, mask := none,
        anchor := none, graph := none, counterexamples := [] } } ==
  #["declaration snapshot: rule 7: entry WhatwgTest.Streams.Kernel.KernelContract.frozen.Whatwg.Streams.Kernel.Config.idle freezes Whatwg.Streams.Kernel.Config.idle, which has no exact record"]

-- Rule 8: two entries for one declaration that disagree on mask, anchor or
-- graph. An entry that writes no clause disagrees with nothing.
#guard joinFailures { base with
    entries := #[lawsEntry, { contractEntry with mask := some "M2" }] } ==
  #["declaration snapshot: rule 8: the entries for Whatwg.Streams.Kernel.step_idle in WhatwgTest.Streams.Kernel.KernelContract, WhatwgTest.Streams.Kernel.KernelLaws disagree on the mask"]
#guard joinFailures { base with
    entries :=
      #[lawsEntry, { contractEntry with graph := some "OTHER-PG", anchor := some "slot.fixture-config" }] } ==
  #["declaration snapshot: rule 8: the entries for Whatwg.Streams.Kernel.step_idle in WhatwgTest.Streams.Kernel.KernelContract, WhatwgTest.Streams.Kernel.KernelLaws disagree on the anchor",
    "declaration snapshot: rule 8: the entries for Whatwg.Streams.Kernel.step_idle in WhatwgTest.Streams.Kernel.KernelContract, WhatwgTest.Streams.Kernel.KernelLaws disagree on the graph"]

-- Each check reports only its own rule on these inputs.
#guard unrecordedTypes base == #[] && uncoveredDeclarations base == #[] &&
  danglingRecords base == #[] && sharedAnchors base == #[] && orphanRelations base == #[] &&
  unknownAnchors base == #[] && unrecordedEntries base == #[] && disagreeingEntries base == #[]

-- Rule 9: regenerated bytes that differ from the committed files, a missing
-- file, and a committed file the generator does not write; sorted by path.
#guard byteDrift [("generated/declarations/A.tsv", "x"), ("generated/declarations/B.tsv", "y")]
    [("generated/declarations/A.tsv", "x"), ("generated/declarations/C.tsv", "w")] ==
  #["declaration snapshot: rule 9: generated/declarations/B.tsv is missing; run lake exe whatwg_declsnapshot --write",
    "declaration snapshot: rule 9: generated/declarations/C.tsv is not a projection this generator writes"]
#guard byteDrift [("generated/declarations/A.tsv", "x\n")]
    [("generated/declarations/A.tsv", "x\r\n")] ==
  #["declaration snapshot: rule 9: generated/declarations/A.tsv differs from a fresh regeneration; run lake exe whatwg_declsnapshot --write"]
#guard byteDrift (projection base) (projection base) == #[]

end WhatwgTest.Audit.DeclSnapshotContract
