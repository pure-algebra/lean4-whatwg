import WhatwgGates.SvgGrammar

/-- Entry point only; the audited logic is Gates.SvgGrammar.cli, which reads the sealed
chapter `master/paths.html` and the description of path data in Whatwg.Svg.Value.Path. -/
def main (args : List String) : IO UInt32 := Gates.SvgGrammar.cli args
