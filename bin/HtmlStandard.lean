import Gates.HtmlStandard

/-- Entry point only; the audited logic is Gates.HtmlStandard.cli. -/
def main (args : List String) : IO UInt32 := Gates.HtmlStandard.cli args
