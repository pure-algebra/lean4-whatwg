import Gates.UrlCensus

/-!
Breaker-owned U2b finite contract, frozen before the assignment implementation.
Authority: `docs/URL-CENSUS-INTERFACE.md`; packet: `test/contracts/url-census.contract.md`.
These executable tooling probes assert no URL semantic theorem or coverage denominator.
Expected candidates and all their fields are literal, never obtained from a production scan.
-/

set_option autoImplicit false

namespace WhatwgTest.Url.CensusContract

#check (@Gates.UrlCensus.assign : ByteArray → Array Gates.UrlCensus.SourceRow →
  Array Gates.UrlCensus.Explanation → Array String →
  Except String (Array Gates.UrlCensus.Assignment))

open Gates.UrlCensus

private def row (kind : Gates.Census.Kind) (id : String) (b e anchorE : Nat)
    (origins : Array Nat) (parent : Option String := none)
    (dependencies : Array String := #[])
    (disposition : Gates.Census.Disposition := .owned) : SourceRow :=
  { row := { kind, id, anchorB := b, anchorE, spanB := b, spanE := e },
    disposition, parent, dependencies, origins }

private def assignment (kind : Gates.UrlInventory.Kind) (b e : Nat) (label sectionId : String)
    (owner : Option String) (reason : String := "") : Assignment :=
  { candidate := { kind, b, e, label, «section» := sectionId }, owner, reason }

private def run (src : String) (rows : Array SourceRow)
    (explanations : Array Explanation := #[]) (externalIds : Array String := #[]) :=
  (Gates.UrlCensus.assign src.toUTF8 rows explanations externalIds).toOption

private def oneSource := "<dfn id=x>x</dfn>"
private def twoSource := "<dfn id=x>x</dfn><dfn id=y>y</dfn>"
private def xRow := row .type "type.x" 0 17 10 #[1]
private def yRow := row .type "type.y" 17 34 27 #[2]
private def xAssignment := assignment .definition 0 17 "x" "" (some "type.x")
private def yAssignment := assignment .definition 17 34 "y" "" (some "type.y")

-- URL-CEN-P01: empty success, simple ownership, stable order despite reversed authored rows.
#guard run "" #[] == some #[]
#guard run "plain text" #[] == some #[]
#guard run oneSource #[xRow] == some #[xAssignment]
#guard run twoSource #[yRow, xRow] == some #[xAssignment, yAssignment]
#guard run oneSource #[{ xRow with disposition := .hostOnly }] == some #[xAssignment]
#guard run oneSource #[] == none

-- URL-CEN-P02: retain structural headings and explanations; regions may contain semantic rows.
private def headingSource := "<h2 id=s>S</h2>"
private def mixedSource := "<h2 id=s>S</h2><p>note</p><dfn id=x>x</dfn>"
private def mixedRow := row .type "type.x" 26 43 36 #[3]
private def mixedExplanation : Explanation := { b := 0, e := 43, reason := " Context  only " }
#guard run headingSource #[] ==
  some #[assignment .heading 0 15 "S" "s" none "structural heading"]
#guard run mixedSource #[mixedRow] #[mixedExplanation] == some #[
  assignment .heading 0 15 "S" "s" none "structural heading",
  assignment .prose 15 26 "note" "s" none " Context  only ",
  assignment .definition 26 43 "x" "s" (some "type.x")]
#guard run oneSource #[] #[{ b := 0, e := 17, reason := "explicit explanation" }] ==
  some #[assignment .definition 0 17 "x" "" none "explicit explanation"]
#guard run twoSource #[] #[
    { b := 0, e := 17, reason := "first" }, { b := 17, e := 34, reason := "second" }] == some #[
  assignment .definition 0 17 "x" "" none "first",
  assignment .definition 17 34 "y" "" none "second"]
#guard run mixedSource #[row .rule "rule.all" 0 43 9 #[1, 2, 3]] == some #[
  assignment .heading 0 15 "S" "s" (some "rule.all"),
  assignment .prose 15 26 "note" "s" (some "rule.all"),
  assignment .definition 26 43 "x" "s" (some "rule.all")]
#guard run mixedSource #[mixedRow] == none

-- URL-CEN-P03: smallest containing owner, immediate parents, and several origins for one row.
private def nestedSource :=
  "A<dfn id=a>a</dfn>B<dfn id=b>b</dfn>C<dfn id=c>c</dfn>DEF"
private def outerRow := row .type "type.a" 0 57 1 #[1]
private def middleRow := row .op "op.b" 18 56 19 #[2] (some "type.a")
private def innerRow := row .rule "rule.c" 36 55 37 #[3] (some "op.b")
#guard run nestedSource #[innerRow, outerRow, middleRow] == some #[
  assignment .definition 1 18 "a" "" (some "type.a"),
  assignment .definition 19 36 "b" "" (some "op.b"),
  assignment .definition 37 54 "c" "" (some "rule.c")]
#guard run "<div algorithm=a><dfn id=x>x</dfn></div>"
    #[row .op "op.a" 0 40 17 #[1, 2]] == some #[
  assignment .algorithm 0 40 "a" "" (some "op.a"),
  assignment .definition 17 34 "x" "" (some "op.a")]

-- URL-CEN-P04: unused/overlapping explanations, whitespace reasons and invalid region bounds.
#guard run oneSource #[xRow] #[{ b := 0, e := 17, reason := "unused" }] == none
#guard run headingSource #[] #[{ b := 0, e := 15, reason := "unused heading region" }] == none
#guard run (oneSource ++ "Z") #[xRow] #[{ b := 17, e := 18, reason := "unused suffix" }] == none
#guard run twoSource #[] #[
  { b := 0, e := 18, reason := "first" }, { b := 17, e := 34, reason := "second" }] == none
#guard run twoSource #[] #[
  { b := 0, e := 34, reason := "first" }, { b := 0, e := 34, reason := "second" }] == none
#guard run oneSource #[] #[{ b := 0, e := 17, reason := " \t\r\n " }] == none
#guard run oneSource #[] #[{ b := 0, e := 17, reason := "" }] == none
#guard run oneSource #[] #[{ b := 0, e := 0, reason := "empty" }] == none
#guard run oneSource #[] #[{ b := 0, e := 18, reason := "overrun" }] == none
#guard run oneSource #[] #[{ b := 17, e := 0, reason := "reversed" }] == none

-- URL-CEN-P05: row IDs have exactly the declared kind prefix and a nonempty suffix.
#guard run oneSource #[{ xRow with row := { xRow.row with id := "" } }] == none
#guard run oneSource #[{ xRow with row := { xRow.row with id := "type." } }] == none
#guard run oneSource #[{ xRow with row := { xRow.row with id := "op.x" } }] == none
#guard run oneSource #[{ xRow with row := { xRow.row with id := "x" } }] == none
#guard run twoSource #[xRow, { yRow with row := { yRow.row with id := "type.x" } }] == none

-- URL-CEN-P06: source spans and anchors are distinct validated UTF-8 byte ranges.
#guard run ("é" ++ oneSource) #[row .type "type.x" 0 19 2 #[1]] ==
  some #[assignment .definition 2 19 "x" "" (some "type.x")]
#guard run oneSource #[{ xRow with row := { xRow.row with spanE := 0 } }] == none
#guard run oneSource #[{ xRow with row := { xRow.row with spanE := 18 } }] == none
#guard run oneSource #[{ xRow with row := { xRow.row with spanB := 17 } }] == none
#guard run oneSource #[{ xRow with row := { xRow.row with anchorB := 1 } }] == none
#guard run oneSource #[{ xRow with row := { xRow.row with anchorE := 0 } }] == none
#guard run twoSource #[{ xRow with row := { xRow.row with anchorE := 18 } }, yRow] == none
#guard run twoSource #[{ xRow with row := { xRow.row with anchorE := 4 } }, yRow] == none
#guard run (oneSource ++ "é") #[row .type "type.x" 0 18 10 #[1]] == none
#guard run ("é" ++ oneSource) #[row .type "type.x" 0 19 1 #[1]] == none
#guard run ("é" ++ oneSource) #[] #[{ b := 1, e := 19, reason := "split UTF-8" }] == none
#guard (Gates.UrlCensus.assign (ByteArray.mk #[0xC3, 0x28]) #[] #[] #[]).toOption == none
#guard run "<dfn>" #[] == none

-- URL-CEN-P07: origins are existing, nonempty, unique and contained one-based ordinals.
#guard run oneSource #[{ xRow with origins := #[] }] == none
#guard run oneSource #[{ xRow with origins := #[0] }] == none
#guard run oneSource #[{ xRow with origins := #[2] }] == none
#guard run oneSource #[{ xRow with origins := #[1, 1] }] == none
#guard run twoSource #[{ xRow with origins := #[2] }]
    #[{ b := 17, e := 34, reason := "second entity" }] == none
#guard run nestedSource #[{ outerRow with origins := #[1, 2] }, middleRow, innerRow] == none
-- Unique ordinals can still be stolen by a nested row: origin 2 ultimately belongs to op.b.
#guard run nestedSource #[{ outerRow with origins := #[2] },
    { middleRow with origins := #[3] }] == none

-- URL-CEN-P08: crossing/equal spans and non-immediate or invented parent relationships fail.
private def crossingSource := "A<dfn id=x>x</dfn>BC<dfn id=y>y</dfn>D"
#guard run crossingSource #[
  row .type "type.x" 0 20 1 #[1], row .type "type.y" 18 38 19 #[2]] == none
#guard run crossingSource #[
  row .type "type.x" 0 38 1 #[1], row .type "type.y" 0 38 1 #[2]] == none
#guard run nestedSource #[outerRow, { middleRow with parent := none }, innerRow] == none
#guard run nestedSource #[outerRow, middleRow,
    { innerRow with parent := some "type.a" }] == none
#guard run nestedSource #[{ outerRow with parent := some "op.b" }, middleRow, innerRow] == none
#guard run nestedSource #[outerRow, { middleRow with parent := some "op.b" }, innerRow] == none
#guard run nestedSource #[outerRow, { middleRow with parent := some "missing" }, innerRow] == none
#guard run nestedSource #[outerRow,
    { middleRow with parent := some "rule.c" }, innerRow] == none
#guard run twoSource #[xRow, { yRow with parent := some "type.x" }] == none

-- URL-CEN-P09: dependency cycles are allowed, while parent cycles are not.
#guard run twoSource #[{ xRow with dependencies := #["type.y"] },
    { yRow with dependencies := #["type.x"] }] == some #[xAssignment, yAssignment]
#guard run oneSource #[{ xRow with dependencies := #["infra.external"] }] #[]
    #["infra.external"] == some #[xAssignment]
#guard run twoSource #[{ xRow with dependencies := #["missing"] }, yRow] == none
#guard run twoSource #[{ xRow with dependencies := #["type.y", "type.y"] }, yRow] == none
#guard run oneSource #[{ xRow with dependencies := #["type.x"] }] == none
#guard run oneSource #[xRow] #[] #["infra.unused"] == none
#guard run oneSource #[{ xRow with dependencies := #["infra.external"] }] #[]
    #["infra.external", "infra.external"] == none
#guard run oneSource #[{ xRow with dependencies := #[""] }] #[] #[""] == none
#guard run twoSource #[xRow, { yRow with dependencies := #["type.x"] }] #[] #["type.x"] == none

end WhatwgTest.Url.CensusContract
