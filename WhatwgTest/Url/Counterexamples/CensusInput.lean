import Gates.UrlCensusInput

/-!
Independent review regression `URL-INP-CE-001`, frozen before repair.
Attack record: `test/counterexamples/url/CENSUS-INPUT.md`.
These are finite executable format probes, not URL semantic theorems or general parser laws.
The original `WhatwgTest.Url.CensusInputContract` battery remains unchanged.
-/

set_option autoImplicit false

namespace WhatwgTest.Url.Counterexamples.CensusInput

#check (@Gates.UrlCensusInput.build : ByteArray → Gates.UrlCensusInput.Inputs →
  Except String (Array Gates.UrlCensus.SourceRow × Array Gates.UrlCensus.Assignment))
#check (@Gates.UrlCensusInput.project :
  ByteArray → Gates.UrlCensusInput.Inputs → Except String (String × String))

private def source := "<h2 id=s:1>H</h2><dfn id=x>x</dfn>"

private def inputs (dispositions : String) : Gates.UrlCensusInput.Inputs :=
  { spans := "type.x\t17\t34\t2\t-\n", explanations := "", dispositions,
    overrides := "", dependencies := "type.x\t-\n", externals := "" }

private def accepts (dispositions : String) : Bool :=
  match Gates.UrlCensusInput.build source.toUTF8 (inputs dispositions) with
  | .error _ => false
  | .ok (rows, assignments) =>
    match rows.toList with
    | [r] =>
      r.row.kind == .type && r.row.id == "type.x" &&
      r.row.anchorB == 17 && r.row.anchorE == 34 &&
      r.row.spanB == 17 && r.row.spanE == 34 &&
      r.disposition == .owned && r.parent == none &&
      r.dependencies == #[] && r.origins == #[2] && assignments == #[
        { candidate := { kind := .heading, b := 0, e := 17, label := "H", «section» := "s:1" },
          owner := none, reason := "structural heading" },
        { candidate := { kind := .definition, b := 17, e := 34, label := "x", «section» := "s:1" },
          owner := some "type.x", reason := "" }]
    | _ => false

-- One terminal CR is removed, both before LF and at the end of the final line.
#guard accepts "s:1\ttype\towned\r\n"
#guard accepts "s:1\ttype\towned\r"

-- URL-INP-CE-001: a second CR remains part of the token and makes it noncanonical.
#guard match Gates.UrlCensusInput.build source.toUTF8 (inputs "s:1\ttype\towned\r\r\n") with
  | .error _ => true
  | .ok _ => false

#guard match Gates.UrlCensusInput.build source.toUTF8 (inputs "s:1\ttype\towned\r\r") with
  | .error _ => true
  | .ok _ => false

-- Projection must retain the same refusal rather than render malformed authored data.
#guard match Gates.UrlCensusInput.project source.toUTF8 (inputs "s:1\ttype\towned\r\r\n") with
  | .error _ => true
  | .ok _ => false

end WhatwgTest.Url.Counterexamples.CensusInput
