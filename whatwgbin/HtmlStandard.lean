import WhatwgGates.HtmlStandardEmit

/-- Entry point only; the audited logic is Gates.HtmlStandardEmit.cli, which
runs the projection check of Gates.HtmlStandard first. -/
def main (args : List String) : IO UInt32 := Gates.HtmlStandardEmit.cli args
