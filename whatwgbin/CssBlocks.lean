import WhatwgGates.CssBlocksEmit

/-- Entry point only; the audited logic is Gates.CssBlocksEmit.cli, which reads the sealed
CSS modules through Gates.CssBlocks. -/
def main (args : List String) : IO UInt32 := Gates.CssBlocksEmit.cli args