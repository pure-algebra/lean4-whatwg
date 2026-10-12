import WhatwgGates.XmlProductions

/-- Entry point only; the audited logic is Gates.XmlProductions.cli, which reads the sealed
XML 1.0 and the productions transcribed in Whatwg.Html.Print.Xml.Productions. -/
def main (args : List String) : IO UInt32 := Gates.XmlProductions.cli args
