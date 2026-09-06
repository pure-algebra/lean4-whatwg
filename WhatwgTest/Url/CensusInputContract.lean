import Gates.UrlCensusInput

/-!
Breaker-owned U2c finite input/projection contract, frozen before implementation.
Authority: `docs/URL-CENSUS-INPUT-INTERFACE.md`.
Packet: `test/contracts/url-census-input.contract.md`.
Expected rows, candidates, offsets and hashes are independently fixed; no production function
computes an expected result. This is source tooling evidence, not URL semantic coverage.
-/

set_option autoImplicit false

namespace WhatwgTest.Url.CensusInputContract

#check (@Gates.UrlCensusInput.Inputs : Type)
#check (@Gates.UrlCensusInput.Inputs.mk :
  String → String → String → String → String → String → Gates.UrlCensusInput.Inputs)
#check (@Gates.UrlCensusInput.Inputs.spans : Gates.UrlCensusInput.Inputs → String)
#check (@Gates.UrlCensusInput.Inputs.explanations : Gates.UrlCensusInput.Inputs → String)
#check (@Gates.UrlCensusInput.Inputs.dispositions : Gates.UrlCensusInput.Inputs → String)
#check (@Gates.UrlCensusInput.Inputs.overrides : Gates.UrlCensusInput.Inputs → String)
#check (@Gates.UrlCensusInput.Inputs.dependencies : Gates.UrlCensusInput.Inputs → String)
#check (@Gates.UrlCensusInput.Inputs.externals : Gates.UrlCensusInput.Inputs → String)
#check (@Gates.UrlCensusInput.build : ByteArray → Gates.UrlCensusInput.Inputs →
  Except String (Array Gates.UrlCensus.SourceRow × Array Gates.UrlCensus.Assignment))
#check (@Gates.UrlCensusInput.project :
  ByteArray → Gates.UrlCensusInput.Inputs → Except String (String × String))
#check (@Gates.UrlCensusInput.cli : List String → IO UInt32)

open Gates.UrlCensusInput Gates.UrlCensus

private def blank : Inputs :=
  { spans := "", explanations := "", dispositions := "", overrides := "",
    dependencies := "", externals := "" }

private def row (kind : Gates.Census.Kind) (id : String) (b e anchorE : Nat)
    (disposition : Gates.Census.Disposition) (origins : Array Nat)
    (parent : Option String := none) (dependencies : Array String := #[]) : SourceRow :=
  { row := { kind, id, anchorB := b, anchorE, spanB := b, spanE := e },
    disposition, parent, dependencies, origins }

private def assignment (kind : Gates.UrlInventory.Kind) (b e : Nat) (label sectionId : String)
    (owner : Option String) (reason : String := "") : Assignment :=
  { candidate := { kind, b, e, label, «section» := sectionId }, owner, reason }

private def sameRow (a b : SourceRow) : Bool :=
  a.row.kind == b.row.kind && a.row.id == b.row.id &&
  a.row.anchorB == b.row.anchorB && a.row.anchorE == b.row.anchorE &&
  a.row.spanB == b.row.spanB && a.row.spanE == b.row.spanE &&
  a.disposition == b.disposition && a.parent == b.parent &&
  a.dependencies == b.dependencies && a.origins == b.origins

private def accepts (source : String) (inputs : Inputs) (expectedRows : Array SourceRow)
    (expectedAssignments : Array Assignment) : Bool :=
  match build source.toUTF8 inputs with
  | .error _ => false
  | .ok (rows, assignments) =>
    rows.size == expectedRows.size &&
    (rows.toList.zip expectedRows.toList).all (fun (a, b) ↦ sameRow a b) &&
    assignments == expectedAssignments

private def rejects (source : String) (inputs : Inputs) : Bool :=
  match build source.toUTF8 inputs with
  | .error _ => true
  | .ok _ => false

private def oneSource := "<dfn id=x>x</dfn>"
private def one : Inputs := { blank with
  spans := "type.x\t0\t17\t1\t-\n", overrides := "type.x\towned\treviewed\n",
  dependencies := "type.x\t-\n" }
private def oneRows := #[row .type "type.x" 0 17 17 .owned #[1]]
private def oneAssignments := #[assignment .definition 0 17 "x" "" (some "type.x")]
private def formFeed := String.singleton (Char.ofNat 12)

-- URL-INP-P01: empty input, short full-span anchor, comments, blank lines and CRLF.
#guard accepts "" blank #[] #[]
#guard accepts oneSource one oneRows oneAssignments
#guard accepts oneSource { one with
    spans := " \t# comment\r\n" ++ formFeed ++ "\n" ++ "type.x\t0\t17\t1\t-\r\n",
    overrides := "# reviewed\r\ntype.x\towned\treviewed\r\n",
    dependencies := "\t# metadata\r\ntype.x\t-\r\n" } oneRows oneAssignments

-- URL-INP-P02: all fields are strict; no numeric/identity normalization or inline comments.
#guard #["00", "01", "+0", "-1", " 0", "0 ", "０", "١"].all (fun n ↦
  rejects oneSource { one with spans := "type.x\t" ++ n ++ "\t17\t1\t-\n" })
#guard #[" type.x", "type.x ", "type/x", "type.é", "type.", "bogus.x"].all (fun id ↦
  rejects oneSource { one with spans := id ++ "\t0\t17\t1\t-\n" })
#guard #["", "1,", ",1", "1,,2", "01", "1, 2", "-"].all (fun origins ↦
  rejects oneSource { one with spans := "type.x\t0\t17\t" ++ origins ++ "\t-\n" })
#guard rejects oneSource { one with spans := "type.x\t0\t17\t1\n" }
#guard rejects oneSource { one with spans := "type.x\t0\t17\t1\t-\textra\n" }
#guard rejects oneSource { one with spans := "type.x\t0\t17\t1\t- # inline\n" }
#guard rejects oneSource { one with spans := "type.x\t0\t17\t1\t- \n" }
#guard rejects oneSource { one with spans := one.spans ++ one.spans }
#guard rejects oneSource { one with overrides := "type.x\towned\n" }
#guard rejects oneSource { one with overrides := "type.x\towned\treason\textra\n" }
#guard rejects oneSource { one with dependencies := "type.x\n" }
#guard rejects oneSource { one with dependencies := "type.x\t-\textra\n" }
#guard rejects oneSource { one with dependencies := "type.x\t- \n" }
#guard rejects oneSource { one with explanations := "0\t17\n" }
#guard rejects oneSource { one with explanations := "0\t17\treason\textra\n" }
#guard rejects oneSource { one with externals := "ext.x\textra\n" }

-- URL-INP-P03: exactly one metadata/disposition source per row and no unused authored lines.
#guard rejects oneSource { one with dependencies := "" }
#guard rejects oneSource { one with dependencies := one.dependencies ++ one.dependencies }
#guard rejects oneSource { one with dependencies := one.dependencies ++ "type.unused\t-\n" }
#guard rejects oneSource { one with overrides := "" }
#guard rejects oneSource { one with overrides := one.overrides ++ one.overrides }
#guard rejects oneSource { one with overrides := one.overrides ++ "type.unused\towned\tunused\n" }
#guard rejects oneSource { one with overrides := "type.x\tunknown\treason\n" }
#guard rejects oneSource { one with overrides := " type.x\towned\treason\n" }
#guard rejects oneSource { one with overrides := "type.x\towned\t \t\n" }
#guard rejects oneSource { one with overrides := "type.x\towned\t" ++ formFeed ++ "\n" }
#guard rejects oneSource { one with dispositions := "unused\t*\towned\n" }
#guard rejects oneSource { one with externals := "ext.unused\n" }
#guard rejects oneSource { one with dependencies := "type.x\text.x\n", externals := "other.x\n" }
#guard rejects oneSource { one with dependencies := "type.x\tother.x\n", externals := "other.x\n" }
#guard rejects oneSource { one with dependencies := "type.x\text.\n", externals := "ext.\n" }
#guard rejects oneSource { one with
  dependencies := "type.x\text.x\n", externals := "ext.x\next.x\n" }
#guard rejects oneSource { one with dependencies := "type.x\text.x\n", externals := " ext.x \n" }
#guard rejects oneSource { one with
  dependencies := "type.x\text.x,ext.x\n", externals := "ext.x\n" }
#guard rejects oneSource { one with dependencies := "type.x\ttype.x\n" }
#guard rejects oneSource { one with dependencies := "type.x\text.missing\n" }
#guard accepts oneSource { one with dependencies := "type.x\text.x\n", externals := "ext.x\n" }
  #[row .type "type.x" 0 17 17 .owned #[1] none #["ext.x"]] oneAssignments

-- URL-INP-P04: current heading only; punctuation in heading IDs; exact/wildcard/override priority.
private def sectionSource := "<h2 id=s:1>H</h2><dfn id=x>x</dfn>"
private def sectionInputs : Inputs := { blank with
  spans := "type.x\t17\t34\t2\t-\n", dispositions := "s:1\ttype\towned\n",
  dependencies := "type.x\t-\n" }
#guard accepts sectionSource sectionInputs #[row .type "type.x" 17 34 34 .owned #[2]] #[
  assignment .heading 0 17 "H" "s:1" none "structural heading",
  assignment .definition 17 34 "x" "s:1" (some "type.x")]
#guard rejects sectionSource { sectionInputs with dispositions := "s:1\ttype\towned\textra\n" }
#guard rejects sectionSource { sectionInputs with dispositions := "s:1\ttype\n" }
#guard rejects sectionSource { sectionInputs with dispositions := "s:1\tbogus\towned\n" }
#guard rejects sectionSource { sectionInputs with dispositions := "s:1\ttype\tbogus\n" }
#guard rejects sectionSource { sectionInputs with dispositions := "s:1 \ttype\towned\n" }
#guard rejects sectionSource { sectionInputs with
  dispositions := sectionInputs.dispositions ++ sectionInputs.dispositions }
#guard rejects "<h2 id=o>O</h2><h3 id=i>I</h3><dfn id=x>x</dfn>" { blank with
  spans := "type.x\t30\t47\t3\t-\n", dispositions := "o\t*\towned\n",
  dependencies := "type.x\t-\n" }
private def prioritySource :=
  "<h2 id=s>S</h2><dfn id=x>x</dfn><dfn id=y>y</dfn><dfn id=z>z</dfn>"
private def priorityInputs : Inputs := { blank with
  spans := "type.x\t15\t32\t2\t-\nop.y\t32\t49\t3\t-\nop.z\t49\t66\t4\t-\n",
  dispositions := "s\t*\trequirement\ns\ttype\towned\n",
  overrides := "op.z\thostOnly\texplicit override\n",
  dependencies := "type.x\t-\nop.y\t-\nop.z\t-\n" }
#guard accepts prioritySource priorityInputs #[
  row .op "op.y" 32 49 49 .requirement #[3], row .op "op.z" 49 66 66 .hostOnly #[4],
  row .type "type.x" 15 32 32 .owned #[2]] #[
  assignment .heading 0 15 "S" "s" none "structural heading",
  assignment .definition 15 32 "x" "s" (some "type.x"),
  assignment .definition 32 49 "y" "s" (some "op.y"),
  assignment .definition 49 66 "z" "s" (some "op.z")]
#guard rejects prioritySource { priorityInputs with
  dispositions := priorityInputs.dispositions ++ "s\tslot\towned\n" }

-- URL-INP-P05: anchors stay inside valid row spans and count overlapping occurrences.
#guard rejects (oneSource ++ oneSource) { one with explanations := "17\t34\tsecond copy\n" }
#guard rejects oneSource { one with spans := "type.x\t0\t0\t1\t-\n" }
#guard rejects oneSource { one with spans := "type.x\t0\t18\t1\t-\n" }
#guard rejects (oneSource ++ "é") { one with spans := "type.x\t0\t18\t1\t-\n" }
#guard match build (ByteArray.mk #[0xC3, 0x28]) blank with
  | .error _ => true
  | .ok _ => false
private def extendedSource :=
  "abcdefghijklmnopqrstuvwxA<dfn id=x>x</dfn>abcdefghijklmnopqrstuvwxB<dfn id=y>y</dfn>"
private def extendedInputs : Inputs := { blank with
  spans := "type.x\t0\t42\t1\t-\ntype.y\t42\t84\t2\t-\n",
  overrides := "type.x\towned\tfirst\ntype.y\towned\tsecond\n",
  dependencies := "type.x\t-\ntype.y\t-\n" }
#guard accepts extendedSource extendedInputs #[
  row .type "type.x" 0 42 32 .owned #[1], row .type "type.y" 42 84 74 .owned #[2]] #[
  assignment .definition 25 42 "x" "" (some "type.x"),
  assignment .definition 67 84 "y" "" (some "type.y")]
#guard accepts extendedSource { extendedInputs with
    spans := "type.y\t42\t84\t2\t-\ntype.x\t0\t42\t1\t-\n" } #[
  row .type "type.x" 0 42 32 .owned #[1], row .type "type.y" 42 84 74 .owned #[2]] #[
  assignment .definition 25 42 "x" "" (some "type.x"),
  assignment .definition 67 84 "y" "" (some "type.y")]
#guard accepts "aaaaaaaaaaaaaaaaaaaaaaaaa<dfn id=x>x</dfn>"
    { one with spans := "type.x\t0\t42\t1\t-\n" }
    #[row .type "type.x" 0 42 32 .owned #[1]]
    #[assignment .definition 25 42 "x" "" (some "type.x")]
#guard accepts "abcdefghijklmnopqrstuvwé<dfn id=x>x</dfn>"
    { one with spans := "type.x\t0\t42\t1\t-\n" }
    #[row .type "type.x" 0 42 25 .owned #[1]]
    #[assignment .definition 25 42 "x" "" (some "type.x")]
#guard accepts
    ("abcdefghijklmnopqrstuvwx<dfn id=x>x</dfn>" ++
      "abcdefghijklmnopqrstuvwx<dfn id=y>y</dfn>")
    { extendedInputs with spans := "type.x\t0\t41\t1\t-\ntype.y\t41\t82\t2\t-\n" } #[
  row .type "type.x" 0 41 41 .owned #[1], row .type "type.y" 41 82 82 .owned #[2]] #[
  assignment .definition 24 41 "x" "" (some "type.x"),
  assignment .definition 65 82 "y" "" (some "type.y")]

-- URL-INP-P06: build invokes the full U2b join rather than stopping after parsing metadata.
#guard rejects oneSource blank
#guard rejects oneSource { one with spans := "type.x\t0\t17\t0\t-\n" }
#guard rejects oneSource { one with spans := "type.x\t0\t17\t2\t-\n" }
#guard rejects oneSource { one with spans := "type.x\t0\t17\t1,1\t-\n" }
#guard rejects oneSource { one with spans := "type.x\t0\t17\t1\ttype.x\n" }
#guard rejects oneSource { one with explanations := "0\t17\tunused\n" }
#guard rejects oneSource { blank with explanations := "0\t17\t" ++ formFeed ++ "\n" }
#guard accepts oneSource { blank with explanations := "0\t17\t explanation # literal \n" } #[]
  #[assignment .definition 0 17 "x" "" none " explanation # literal "]

private def projectionSource := "<div algorithm=z><dfn id=a>a</dfn><dfn id=b>b</dfn></div>"
private def projectionInputs : Inputs := { blank with
  spans := "type.z\t0\t57\t3,1\t-\nop.a\t17\t34\t2\ttype.z\n",
  overrides := "type.z\towned\touter\nop.a\thostOnly\tinner\n",
  dependencies := "type.z\text.a\nop.a\text.z,type.z\n", externals := "ext.z\next.a\n" }
#guard accepts projectionSource projectionInputs #[
  row .op "op.a" 17 34 34 .hostOnly #[2] (some "type.z") #["ext.z", "type.z"],
  row .type "type.z" 0 57 24 .owned #[3, 1] none #["ext.a"]] #[
  assignment .algorithm 0 57 "z" "" (some "type.z"),
  assignment .definition 17 34 "a" "" (some "op.a"),
  assignment .definition 34 51 "b" "" (some "type.z")]
#guard rejects projectionSource { projectionInputs with
  spans := "type.z\t0\t57\t3,1\t-\nop.a\t17\t34\t2\t-\n" }

-- URL-INP-P07: exact projections, independently fixed SHA-256 values and authored-input hashes.
-- Hash literals were computed with .NET SHA256.HashData over independently supplied UTF-8 bytes.
private def emptyHash := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
private def sourceHash := "2b0685f8f22b8344b88c0241cb3d24c04346a45b533eee214bd47aaf8c365ab0"
private def aHash := "224c709d94a2947600273b22e87d35099fe4c9eb566ef0d939448143c95acb1a"
private def bHash := "a7d366a5d3db95b6d91ffe2f3f247ed120dc0d73efca6fc37e8f3c1c37c29e9b"
private def outerAnchorHash := "55330599bfc0ba1131ebac9dee3c8be92593f7a5b71d8d3ceae003c9836b104d"
private def spansHash := "f65bd166e2dbe2c8ac29df34b3081a3623bda806c632013b8cc80f0404aa5bc8"
private def commentedSpansHash := "09ff0a38b66674e9a2ef0b1218285f80d5243f10c9a1612979d5548bfbe93441"

private def censusColumns :=
  "#kind\tid\tbyte-start\tbyte-end\tspan-sha256\tanchor-end\tanchor-sha256\tparent\t" ++
  "origins\tdisposition\tdependencies\n"
private def assignmentColumns :=
  "#ordinal\tkind\tbyte-start\tbyte-end\tspan-sha256\tlabel\tsection\towner\treason\n"

private def emptyComments :=
  "#input spans-sha256=" ++ emptyHash ++ "\n" ++
  "#input explanations-sha256=" ++ emptyHash ++ "\n" ++
  "#input dispositions-sha256=" ++ emptyHash ++ "\n" ++
  "#input overrides-sha256=" ++ emptyHash ++ "\n" ++
  "#input dependencies-sha256=" ++ emptyHash ++ "\n" ++
  "#input externals-sha256=" ++ emptyHash ++ "\n"

#guard (project ByteArray.empty blank).toOption == some (
  "#url-census format=1 generator=Gates.UrlCensusInput input-sha256=" ++ emptyHash ++
    " rows=0\n" ++ censusColumns ++ emptyComments,
  "#url-source-assignments format=1 generator=Gates.UrlCensusInput input-sha256=" ++ emptyHash ++
    " candidates=0\n" ++ assignmentColumns ++ emptyComments)

private def projectionComments (spanInputHash : String) :=
  "#input spans-sha256=" ++ spanInputHash ++ "\n" ++
  "#input explanations-sha256=" ++ emptyHash ++ "\n" ++
  "#input dispositions-sha256=" ++ emptyHash ++ "\n" ++
  "#input overrides-sha256=" ++
    "0833b33c36a7e55c11d6a1b693c0c9c343c767f986f73e79dfc9105a98bee6e9\n" ++
  "#input dependencies-sha256=" ++
    "1c139aa91ea442cd1ef7a190e89bff00ae5c39ab2b83d70782442d8724ca0316\n" ++
  "#input externals-sha256=" ++
    "2cd901fe97733cbf20795f3e9d94a3ea69a4deabd0d0e12e34fe4b406accfc9c\n"

private def expectedProjection (spanInputHash : String) : String × String := (
  "#url-census format=1 generator=Gates.UrlCensusInput input-sha256=" ++ sourceHash ++
  " rows=2\n" ++ censusColumns ++ projectionComments spanInputHash ++
  "op\top.a\t17\t34\t" ++ aHash ++ "\t34\t" ++ aHash ++
  "\ttype.z\t2\thostOnly\text.z,type.z\n" ++
  "type\ttype.z\t0\t57\t" ++ sourceHash ++ "\t24\t" ++ outerAnchorHash ++
  "\t-\t3,1\towned\text.a\n",
  "#url-source-assignments format=1 generator=Gates.UrlCensusInput input-sha256=" ++ sourceHash ++
  " candidates=3\n" ++ assignmentColumns ++ projectionComments spanInputHash ++
  "1\talgorithm\t0\t57\t" ++ sourceHash ++ "\tz\t\ttype.z\t\n" ++
  "2\tdefinition\t17\t34\t" ++ aHash ++ "\ta\t\top.a\t\n" ++
  "3\tdefinition\t34\t51\t" ++ bHash ++ "\tb\t\ttype.z\t\n")

#guard (project projectionSource.toUTF8 projectionInputs).toOption ==
  some (expectedProjection spansHash)
#guard (project projectionSource.toUTF8 { projectionInputs with
    spans := "# provenance comment\n" ++ projectionInputs.spans }).toOption ==
  some (expectedProjection commentedSpansHash)
#guard match project oneSource.toUTF8 { one with dependencies := "" } with
  | .error _ => true
  | .ok _ => false

-- URL-INP-P08: textual escaping is exact; an ordinary vertical bar is retained unchanged.
private def escapedSource := "<dfn id='a\tb\nc\rd\\e|f'>x</dfn>"
private def escapedInputs : Inputs :=
  { blank with explanations := "0\t29\tbecause\\path\r detail|ok\n" }
private def escapedSourceHash := "373818ec3d5a794d29b19c67941e404bcd94aa60290e5d2fe99c7ced6bc70d4e"
private def escapedComments :=
  "#input spans-sha256=" ++ emptyHash ++ "\n" ++
  "#input explanations-sha256=" ++
    "ba6785b2688682199d63be710e4a843e6f552001aa47413f39b834548654b551\n" ++
  "#input dispositions-sha256=" ++ emptyHash ++ "\n" ++
  "#input overrides-sha256=" ++ emptyHash ++ "\n" ++
  "#input dependencies-sha256=" ++ emptyHash ++ "\n" ++
  "#input externals-sha256=" ++ emptyHash ++ "\n"
#guard (project escapedSource.toUTF8 escapedInputs).toOption == some (
  "#url-census format=1 generator=Gates.UrlCensusInput input-sha256=" ++ escapedSourceHash ++
  " rows=0\n" ++ censusColumns ++ escapedComments,
  "#url-source-assignments format=1 generator=Gates.UrlCensusInput input-sha256=" ++
  escapedSourceHash ++ " candidates=1\n" ++ assignmentColumns ++ escapedComments ++
  "1\tdefinition\t0\t29\t" ++ escapedSourceHash ++
  "\ta\\tb\\nc\\rd\\\\e|f\t\t-\tbecause\\\\path\\r detail|ok\n")

-- URL-INP-P09: disposition input hashing, structural heading receipts and raw CRLF sensitivity.
private def sectionHash := "6e6fa206c2fea71818e09d5dd87e00b86c9554c2067383be021dbabe67f47aac"
private def headingHash := "599df0924ec87f0fe8d53e43b588bc8053d00c1a440a2e62e22c1da290973fd7"
private def xHash := "050c7b7ae338346b5a56e1e43ec6f70d051cb194a74fadc5db7d1a924b7c1c2b"
private def sectionComments (ruleHash : String) :=
  "#input spans-sha256=68215fbb1eaecd49a9a253fabc6c390fe09851ca51e37ab24c426bedf7bd0788\n" ++
  "#input explanations-sha256=" ++ emptyHash ++ "\n" ++
  "#input dispositions-sha256=" ++ ruleHash ++ "\n" ++
  "#input overrides-sha256=" ++ emptyHash ++ "\n" ++
  "#input dependencies-sha256=" ++
    "dfc01edbe1aa113cfbde7658567eb19a4c2d3574ab99aac5d2bdfca7f775698b\n" ++
  "#input externals-sha256=" ++ emptyHash ++ "\n"
private def expectedSectionProjection (ruleHash : String) : String × String := (
  "#url-census format=1 generator=Gates.UrlCensusInput input-sha256=" ++ sectionHash ++
  " rows=1\n" ++ censusColumns ++ sectionComments ruleHash ++
  "type\ttype.x\t17\t34\t" ++ xHash ++ "\t34\t" ++ xHash ++ "\t-\t2\towned\t-\n",
  "#url-source-assignments format=1 generator=Gates.UrlCensusInput input-sha256=" ++ sectionHash ++
  " candidates=2\n" ++ assignmentColumns ++ sectionComments ruleHash ++
  "1\theading\t0\t17\t" ++ headingHash ++ "\tH\ts:1\t-\tstructural heading\n" ++
  "2\tdefinition\t17\t34\t" ++ xHash ++ "\tx\ts:1\ttype.x\t\n")
#guard (project sectionSource.toUTF8 sectionInputs).toOption == some (expectedSectionProjection
  "7cb76af4e372f3db88804ce07a1f411213762ad12a75fc093f4676426114e22e")
#guard (project sectionSource.toUTF8 { sectionInputs with
    dispositions := "s:1\ttype\towned\r\n" }).toOption == some (expectedSectionProjection
  "902fc6077f721c9a6bf799963d4d18409be643e95a400f2692e20441d22105f0")

end WhatwgTest.Url.CensusInputContract
