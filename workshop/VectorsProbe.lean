import Whatwg.Svg.Scene.Vector

/-! A probe that writes the readings of motion as a table (slice S17; ask W3 of
`docs/research/2026-10-12-whatwg-requests.md`). Run it from the repository root after
`lake build`:

    lake env lean workshop/VectorsProbe.lean

It writes `motion-readings.tsv` into `docs/research/2026-10-12-motion-probe/`, or into the
directory that the environment variable `WHATWG_VECTORS_DIR` names. No module imports this
file, and no gate reads its output.

The file is `Case.text Case.battery` of `Whatwg/Svg/Scene/Vector.lean`: the kit's battery, one
line for each case. That module's header says how a line reads. A program in another language
that samples the kit's tracks is tested against it: lean4-effect4's player in C reads each line
with `fscanf`, computes the readings from the numbers given, and compares.

A consumer can write the same file from its own build, at its own pin, and add cases of its
own look to it:

    IO.FS.writeFile "readings.tsv" (Case.text (Case.battery ++ [Case.easing "mine" e]))

The probe prints what it wrote: the count of cases of each kind, the count of numbers, the
lines and the bytes. It then reads the text back and says whether every line gave its case's
numbers again. -/

open Whatwg.Svg.Scene

/-- Where the table goes. -/
def outDir : IO System.FilePath := do
  return (← IO.getEnv "WHATWG_VECTORS_DIR").getD "docs/research/2026-10-12-motion-probe"

/-- A line of the text read back: its two words, and its two lists of numbers. -/
def readLine (line : String) : Option (String × String × List Int × List Int) := do
  let kind :: name :: rest := line.splitOn "\t" | none
  let g :: rest ← rest.mapM String.toInt? | none
  let given := rest.take g.toNat
  let r :: readings := rest.drop g.toNat | none
  if readings.length == r.toNat && given.length == g.toNat then some (kind, name, given, readings)
  else none

/-- Whether the text of a list of cases reads back as those cases, after the line of the
format. -/
def readsBack (cases : List Case) : Bool :=
  let lines := ((Case.text cases).splitOn "\n").dropLast
  lines.map readLine ==
    (Case.format :: cases).map fun c => some (c.kind, c.name, c.given, c.readings)

/-- Write the table, and say what was written. -/
def writeTable : IO Unit := do
  let cases : List Case := Case.battery
  let text : String := Case.text cases
  let file : System.FilePath := (← outDir) / "motion-readings.tsv"
  IO.FS.writeFile file text
  for kind in ["mix", "at", "of", "timed", "track"] do
    let these : List Case := cases.filter fun (c : Case) => c.kind == kind
    let readings : Nat := (these.map fun (c : Case) => c.readings.length).sum
    IO.println s!"{kind}: {these.length} cases, {readings} readings"
  let numbers : Nat := (cases.map fun (c : Case) => c.given.length + c.readings.length).sum
  IO.println s!"{cases.length} cases, {numbers} numbers"
  let lines : List String := text.splitOn "\n"
  IO.println s!"{lines.length - 1} lines, {text.utf8ByteSize} bytes"
  IO.println s!"the longest line: {(lines.map String.length).foldl max 0} characters"
  IO.println s!"reads back: {readsBack cases}"
  IO.println s!"written: {file}"

#eval writeTable