import WhatwgGates.SvgDefinitionsEmit

/-- Entry point only; the audited logic is Gates.SvgDefinitionsEmit.cli, which reads the
sealed definitions through Gates.SvgDefinitions. -/
def main (args : List String) : IO UInt32 := Gates.SvgDefinitionsEmit.cli args
