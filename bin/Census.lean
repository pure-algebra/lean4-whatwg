import Gates.Census
import WhatwgTest.Audit.SpecCoverage
import WhatwgTest.Audit.WebIdl.SpecCoverage
import WhatwgTest.Audit.Ecma262.SpecCoverage

/-- Entry point only; the audited logic is Gates.Census.cli. The coverage
emits are the test-side numerators', which `Gates/` may not import, keyed by
`Gates.Census.Standard.key`. Infra has no numerator and therefore no entry,
which is what makes `--standard infra --report` refuse. -/
def main (args : List String) : IO UInt32 :=
  Gates.Census.cli
    [("streams", WhatwgTest.Audit.SpecCoverage.emit),
     ("webidl", WhatwgTest.Audit.WebIdl.SpecCoverage.emit),
     ("ecma262", WhatwgTest.Audit.Ecma262.SpecCoverage.emit)]
    args
