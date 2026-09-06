import Gates.UrlCensus

/-!
Independent census review regression `URL-CEN-CE-001`, frozen before repair.
Attack record: `test/counterexamples/url/CENSUS.md`.
These are finite executable tooling refusals, not URL semantic theorems or general join laws.
The frozen base battery `WhatwgTest.Url.CensusContract` remains unchanged.
-/

set_option autoImplicit false

namespace WhatwgTest.Url.Counterexamples.Census

#check (@Gates.UrlCensus.assign : ByteArray → Array Gates.UrlCensus.SourceRow →
  Array Gates.UrlCensus.Explanation → Array String →
  Except String (Array Gates.UrlCensus.Assignment))

private def source := "<dfn id=x>x</dfn>"
private def formFeed : String := String.singleton (Char.ofNat 12)

-- URL-CEN-CE-001: form feed alone cannot justify an explanatory assignment.
#guard match Gates.UrlCensus.assign source.toUTF8 #[]
    #[{ b := 0, e := 17, reason := formFeed }] #[] with
  | .error _ => true
  | .ok _ => false

-- A mixture of all five ASCII whitespace characters still provides no justification.
#guard match Gates.UrlCensus.assign source.toUTF8 #[]
    #[{ b := 0, e := 17, reason := " \t\n" ++ formFeed ++ "\r" }] #[] with
  | .error _ => true
  | .ok _ => false

end WhatwgTest.Url.Counterexamples.Census
