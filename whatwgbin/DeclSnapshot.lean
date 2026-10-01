import WhatwgGates.DeclSnapshot

/-- Entry point only; the audited logic is Gates.DeclSnapshot.cli. -/
def main (args : List String) : IO UInt32 := Gates.DeclSnapshot.cli args
