import WhatwgGates.Common
import WhatwgGates.Sha256
import Whatwg.Html.Print.Xml.Productions

/-!
# Gates.XmlProductions

The gate of debt D105: it compares four transcribed productions of XML 1.0 with the sealed
document. The document is Extensible Markup Language (XML) 1.0 (Fifth Edition), at
`vendor/w3c-xml-20081126/REC-xml-20081126.html`. `Whatwg/Html/Print/Xml/Productions.lean`
transcribes `Char`, `NameStartChar`, `NameChar` and `Name` by hand as Boolean functions, for
the "require well-formed" checks of the XML serialization.

What it decides, for each of `Char`, `NameStartChar` and `NameChar`: the set of code points
that the sealed production writes is the set where the library's function is true, by a
comparison at every code point from U+0000 to U+10FFFF. For `Name` it decides that the sealed
body is `NameStartChar (NameChar)*`, and that `isName` agrees with the reading of that body, a
first character of the one production and then characters of the other, at every text of at
most two characters over the ends of the sealed ranges and their neighbours.

How:

1. `readDocument` refuses a document whose SHA-256 is not the pinned one.
2. `findRow` finds a production by its anchor, `id="NT-Char"` for `Char`. The anchor must stand
   once. `readRow` reads the row: it opens with the production's number, one cell holds the
   name, `::=` follows once, and the next cell holds the body. `unlink` replaces a link to
   another production by its text and refuses any other markup and any character reference.
3. `readBody` reads the body as alternatives between bars. An alternative is a hexadecimal
   character such as `#x9`, a range such as `[#x20-#xD7FF]` or `[A-Z]`, one character in double
   quotes, or the name of a production read before it. Any other text is refused.
4. `tallyOf` walks the code points. A surrogate is no `Char` of Lean, so the library's side is
   false there, and a sealed production that held one would be a difference.

Controls run on every invocation. For each character production, one alternative is removed
from the sealed side, and the comparison must then find a difference. For `Name`, the reading
with the two productions exchanged must differ from `isName`. A procedure that always answers
"equal" fails each of them.

What this gate does not claim. It is code that no theorem checks: a PASS is the verdict of
this procedure, not a proof. It reads four productions of one document and no prose. The
comparison of `Name` is over short texts: it tells the first character from the later ones,
and it is no proof for a text of every length. It says nothing of the serialization itself
(`Whatwg/Html/Print/Xml.lean`), which uses the functions.

Exit codes: 0 when every comparison agrees and every control differs. 1 for a difference or a
control that does not differ. 2 when there is no verdict: an argument, a missing or changed
document, or a refused construct.

Totality: every loop is a fold, is structural, or runs over a range.
-/

namespace Gates.XmlProductions

open Whatwg.Html.Print.Xml (isChar isNameStartChar isNameChar isName)

/-! ## The sealed document and the rows -/

/-- The sealed document, under the repository root. -/
def documentPath : String := "vendor/w3c-xml-20081126/REC-xml-20081126.html"

/-- Its SHA-256. -/
def documentDigest : String :=
  "f58a4b9e1e5b8bac13fb55c4e5c7c8c5e2c176aa45ee68e2f1ab2498511927ec"

/-- The module of the library that holds the functions. -/
def libraryModule : String := "Whatwg.Html.Print.Xml"

/-- A character production with its function in the library. `number` is the production's
number as the document writes it. `control` is one alternative of it, as written, whose
removal the gate must notice. -/
structure Row where
  name : String
  number : String
  function : String
  library : Char → Bool
  control : String

/-- The three character productions, in an order where each names only those before it. -/
def rows : List Row :=
  [{ name := "Char", number := "[2]", function := "isChar", library := isChar,
     control := "#x9" },
   { name := "NameStartChar", number := "[4]", function := "isNameStartChar",
     library := isNameStartChar, control := "\"_\"" },
   { name := "NameChar", number := "[4a]", function := "isNameChar", library := isNameChar,
     control := "#xB7" }]

/-- The production of a name. -/
def nameProduction : String := "Name"

/-- Its number. -/
def nameNumber : String := "[5]"

/-- Its body, with each link replaced by its text. The gate reads this body and no other. -/
def nameBody : String := "NameStartChar (NameChar)*"

/-! ## Finding a production -/

/-- The offsets at which `needle` stands in a text whose first character is at `offset`. -/
def occurrences (needle : List Char) : List Char → Nat → Array Nat → Array Nat
  | [], _, found => found
  | c :: rest, offset, found =>
    occurrences needle rest (offset + 1)
      (if needle.isPrefixOf (c :: rest) then found.push offset else found)

/-- A text without the spaces at its two ends. -/
def trim (text : List Char) : List Char :=
  ((text.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse

/-- The text between the first `opening` and the next `closing`, and what follows that
`closing`. -/
def cell (opening closing : String) (text : List Char) : Option (List Char × List Char) :=
  match (occurrences opening.toList text 0 #[]).toList with
  | [] => none
  | start :: _ =>
    let inside := text.drop (start + opening.toList.length)
    match (occurrences closing.toList inside 0 #[]).toList with
    | [] => none
    | stop :: _ => some (inside.take stop, inside.drop (stop + closing.toList.length))

/-- The table row of a production: the text from its anchor to the end of the row. The anchor
must stand once in the document. -/
def findRow (text : List Char) (name : String) : Except String (List Char) := do
  let mark := s!"id=\"NT-{name}\"".toList
  match (occurrences mark text 0 #[]).toList with
  | [start] =>
    let rest := text.drop (start + mark.length)
    match (occurrences "</tr>".toList rest 0 #[]).toList with
    | stop :: _ => pure (rest.take stop)
    | [] => throw s!"the row of `{name}` has no end"
  | found =>
    throw (s!"the anchor `{String.ofList mark}` stands {found.length} time(s), and it must " ++
      "stand once")

/-- What `unlink` has read of a cell: the text kept, the open tag with its characters in
reverse, and the first refusal. -/
structure Unlinked where
  kept : Array Char := #[]
  tag : Option (List Char) := none
  refusal : Option String := none

/-- One character of a cell. A tag is dropped if it is a link to a production or the end of a
link, and it is refused otherwise. A character reference is refused. -/
def Unlinked.step (state : Unlinked) (c : Char) : Unlinked :=
  match state.tag with
  | some reversed =>
    if c == '>' then
      let tag := reversed.reverse
      if tag == "/a".toList || "a href=\"#NT-".toList.isPrefixOf tag then
        { state with tag := none }
      else
        { state with
          tag := none
          refusal := state.refusal <|>
            some s!"the tag `<{String.ofList tag}>` is not a link to a production" }
    else { state with tag := some (c :: reversed) }
  | none =>
    if c == '<' then { state with tag := some [] }
    else if c == '&' then
      { state with refusal := state.refusal <|> some "a character reference stands in it" }
    else { state with kept := state.kept.push c }

/-- A cell's text with each link to a production replaced by the text that the link holds. -/
def unlink (cellText : List Char) : Except String (List Char) :=
  let state := cellText.foldl Unlinked.step {}
  match state.refusal, state.tag with
  | some reason, _ => .error reason
  | none, some _ => .error "a tag in it does not close"
  | none, none => .ok state.kept.toList

/-- The body of a production, from its row. The row opens with the production's number, one
cell holds its name, `::=` stands once after it, and the next cell holds the body. -/
def readRow (name number : String) (row : List Char) : Except String (List Char) := do
  unless ("/>" ++ number).toList.isPrefixOf row do
    throw s!"the row of `{name}` does not open with the number {number}"
  let some (written, afterName) := cell "<code>" "</code>" row
    | throw s!"the row of `{name}` has no cell for the name"
  unless written == name.toList do
    throw s!"the row under the anchor of `{name}` defines `{String.ofList written}`"
  let some (body, _) := cell "<code>" "</code>" afterName
    | throw s!"the row of `{name}` has no cell for the body"
  let opened := (occurrences "<code>".toList afterName 0 #[])[0]?.getD 0
  unless (occurrences "::=".toList (afterName.take opened) 0 #[]).size == 1 do
    throw s!"`::=` does not stand once between the name `{name}` and its body"
  (unlink body).mapError fun reason => s!"the body of `{name}`: {reason}"

/-! ## Reading a body -/

/-- The last code point. -/
def lastCodePoint : Nat := 0x10FFFF

/-- The value of a hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n && n ≤ 0x39 then some (n - 0x30)
  else if 0x41 ≤ n && n ≤ 0x46 then some (n - 0x41 + 10)
  else if 0x61 ≤ n && n ≤ 0x66 then some (n - 0x61 + 10)
  else none

/-- A hexadecimal number of one digit or more. -/
def hex? (digits : List Char) : Option Nat :=
  if digits.isEmpty then none
  else digits.foldlM (fun value c => (hexDigit? c).map (value * 16 + ·)) 0

/-- One end of a range and what follows it: `#x` with hexadecimal digits, or one letter or
digit. -/
def endpoint? : List Char → Option (Nat × List Char)
  | '#' :: 'x' :: rest =>
    let digits := rest.takeWhile fun c => (hexDigit? c).isSome
    (hex? digits).map fun value => (value, rest.drop digits.length)
  | c :: rest => if c.isAlphanum then some (c.toNat, rest) else none
  | [] => none

/-- One alternative of a character production: a closed range of code points, or the name of
a production. -/
inductive Item where
  | range (lo hi : Nat)
  | ref (name : String)

/-- A range, if it is in order and ends at a code point. -/
def range? (lo hi : Nat) : Option Item :=
  if lo ≤ hi && hi ≤ lastCodePoint then some (.range lo hi) else none

/-- Read one alternative: `#x9`, `[#x20-#xD7FF]`, `[A-Z]`, `":"`, or the name of a production.
Any other text has no reading. -/
def readItem (text : List Char) : Option Item :=
  match text with
  | ['"', c, '"'] => range? c.toNat c.toNat
  | '[' :: rest =>
    match endpoint? rest with
    | some (lo, '-' :: more) =>
      match endpoint? more with
      | some (hi, [']']) => range? lo hi
      | _ => none
    | _ => none
  | '#' :: 'x' :: digits => (hex? digits).bind fun value => range? value value
  | _ =>
    if !text.isEmpty && text.all Char.isAlpha then some (.ref (String.ofList text)) else none

/-- An alternative: its text as the document writes it, and the ranges it holds. -/
structure Alternative where
  text : List Char
  ranges : List (Nat × Nat)

/-- The texts between the bars of a body. -/
def splitBars (body : List Char) : List (List Char) :=
  body.foldr (fun c parts =>
    match c, parts with
    | '|', _ => [] :: parts
    | _, part :: more => (c :: part) :: more
    | _, [] => [[c]]) [[]]

/-- The alternatives of a body. A name is replaced by the ranges of its production, which
must be one of `known`: a production read before this one. -/
def readBody (known : List (String × List (Nat × Nat))) (name : String) (body : List Char) :
    Except String (List Alternative) :=
  (splitBars body).mapM fun part => do
    let text := trim part
    match readItem text with
    | some (.range lo hi) => pure { text, ranges := [(lo, hi)] }
    | some (.ref other) =>
      match known.lookup other with
      | some ranges => pure { text, ranges }
      | none =>
        throw s!"the production `{name}` names `{other}`, which this gate has not read before it"
    | none =>
      throw (s!"the production `{name}` has the alternative `{String.ofList text}`, which " ++
        "this gate does not read")

/-- The ranges of a production: those of its alternatives, in order. -/
def rangesOf (alternatives : List Alternative) : List (Nat × Nat) :=
  alternatives.flatMap (·.ranges)

/-- The three character productions of the document, in the order of `rows`. -/
def readRows (text : List Char) : Except String (List (Row × List Alternative)) := do
  let mut known : List (String × List (Nat × Nat)) := []
  let mut done : List (Row × List Alternative) := []
  for row in rows do
    let body ← readRow row.name row.number (← findRow text row.name)
    let alternatives ← readBody known row.name body
    known := known ++ [(row.name, rangesOf alternatives)]
    done := done ++ [(row, alternatives)]
  return done

/-! ## The comparison -/

/-- A code point is in one of the ranges. -/
def member (ranges : List (Nat × Nat)) (n : Nat) : Bool :=
  ranges.any fun range => range.1 ≤ n && n ≤ range.2

/-- A code point is a `Char` of Lean: it is no surrogate, and it is not above the last one. -/
def isScalar (n : Nat) : Bool := n < 0xD800 || (0xDFFF < n && n ≤ lastCodePoint)

/-- A function of the library at a code point. It is false at a code point that is no `Char`:
no production holds a surrogate. -/
def atCodePoint (library : Char → Bool) (n : Nat) : Bool :=
  if isScalar n then library (Char.ofNat n) else false

/-- What a walk over every code point found: how many the sealed ranges hold, at how many
the two sides differ, and the least of those. -/
structure Tally where
  held : Nat
  differing : Nat
  earliest : Option Nat

/-- Compare the sealed ranges with a function of the library at every code point. -/
def tallyOf (ranges : List (Nat × Nat)) (library : Char → Bool) : Tally := Id.run do
  let mut held := 0
  let mut differing := 0
  let mut earliest : Option Nat := none
  for n in [0:lastCodePoint + 1] do
    let inDocument := member ranges n
    if inDocument then held := held + 1
    if inDocument != atCodePoint library n then
      differing := differing + 1
      if earliest.isNone then earliest := some n
  return { held, differing, earliest }

/-- A code point as a message writes it: `U+0009`. -/
def codePoint (n : Nat) : String :=
  let digits := (Nat.toDigits 16 n).map Char.toUpper
  "U+" ++ String.ofList (List.replicate (4 - digits.length) '0' ++ digits)

/-- The characters at each end of each range, and the neighbour outside each end. -/
def boundaries (ranges : List (Nat × Nat)) : List Char :=
  let points := ranges.flatMap fun range => [range.1 - 1, range.1, range.2, range.2 + 1]
  (points.eraseDups.filter isScalar).map Char.ofNat

/-- The body `NameStartChar (NameChar)*` as the gate reads it over the sealed ranges: a first
character of `start`, and then characters of `later`. -/
def nameReading (start later : List (Nat × Nat)) : List Char → Bool
  | [] => false
  | c :: more => member start c.toNat && more.all fun d => member later d.toNat

/-- The texts of at most two characters over an alphabet. -/
def shortTexts (alphabet : List Char) : List (List Char) :=
  [[]] ++ alphabet.map (fun a => [a]) ++ alphabet.flatMap fun a => alphabet.map fun b => [a, b]

/-- A text as a message writes it: its code points. -/
def spelled (text : List Char) : String :=
  if text.isEmpty then "the empty text" else " ".intercalate (text.map fun c => codePoint c.toNat)

/-- One line of the report. -/
structure Line where
  passed : Bool
  text : String

/-- Every comparison and every control over the document's text. An error is a refusal: the
document does not read as the gate expects, and there is no verdict. -/
def judge (text : List Char) : Except String (List Line) := do
  let done ← readRows text
  let mut lines : List Line := []
  for (row, alternatives) in done do
    let tally := tallyOf (rangesOf alternatives) row.library
    let subject := s!"`{row.name}` {row.number} and {libraryModule}.{row.function}"
    let line : Line :=
      match tally.earliest with
      | none =>
        ⟨true, s!"PASS xml productions: {subject} agree at every code point from U+0000 to " ++
          s!"{codePoint lastCodePoint}; {alternatives.length} alternatives hold {tally.held} " ++
          "code points"⟩
      | some n =>
        ⟨false, s!"FAIL xml productions: {subject} differ at {tally.differing} code " ++
          s!"point(s), the least {codePoint n}"⟩
    lines := lines ++ [line]
  for (row, alternatives) in done do
    let kept := alternatives.filter fun alternative => alternative.text != row.control.toList
    unless kept.length + 1 == alternatives.length do
      throw (s!"the control of `{row.name}` removes the alternative `{row.control}`, which " ++
        s!"stands {alternatives.length - kept.length} time(s) in the production; it must " ++
        "stand once")
    let tally := tallyOf (rangesOf kept) row.library
    let subject :=
      s!"`{row.name}` without `{row.control}` and {libraryModule}.{row.function}"
    let line : Line :=
      match tally.earliest with
      | some n =>
        ⟨true, s!"PASS xml productions control: {subject} differ at {tally.differing} code " ++
          s!"point(s), the least {codePoint n}"⟩
      | none =>
        ⟨false, s!"FAIL xml productions control: {subject} agree at every code point, so " ++
          "the comparison shows nothing"⟩
    lines := lines ++ [line]
  let body ← readRow nameProduction nameNumber (← findRow text nameProduction)
  unless body == nameBody.toList do
    throw (s!"the production `{nameProduction}` reads `{String.ofList body}`, and this gate " ++
      s!"reads `{nameBody}` alone")
  let sealedRanges (name : String) : Except String (List (Nat × Nat)) :=
    match done.find? fun entry => entry.1.name == name with
    | some entry => pure (rangesOf entry.2)
    | none => throw s!"internal: no row `{name}`"
  let start ← sealedRanges "NameStartChar"
  let later ← sealedRanges "NameChar"
  let alphabet := boundaries (start ++ later)
  let texts := shortTexts alphabet
  let subject :=
    s!"`{nameProduction}` {nameNumber}, read as `{nameBody}`, and {libraryModule}.isName"
  let over :=
    s!"{texts.length} texts of at most two characters over {alphabet.length} characters at " ++
    "the ends of the sealed ranges"
  let nameLine : Line :=
    match texts.filter fun candidate => nameReading start later candidate != isName candidate with
    | [] => ⟨true, s!"PASS xml productions: {subject} agree at each of {over}"⟩
    | witness :: more =>
      ⟨false, s!"FAIL xml productions: {subject} differ at {more.length + 1} of {over}, " ++
        s!"the first {spelled witness}"⟩
  let exchanged : Line :=
    match texts.filter fun candidate => nameReading later start candidate != isName candidate with
    | witness :: more =>
      ⟨true, s!"PASS xml productions control: `{nameProduction}` with its two productions " ++
        s!"exchanged and {libraryModule}.isName differ at {more.length + 1} of {texts.length} " ++
        s!"texts, the first {spelled witness}"⟩
    | [] =>
      ⟨false, s!"FAIL xml productions control: `{nameProduction}` with its two productions " ++
        s!"exchanged and {libraryModule}.isName agree at every text, so the comparison shows " ++
        "nothing"⟩
  return lines ++ [nameLine, exchanged]

/-! ## The command -/

def usage : String :=
  "usage: lake exe whatwg_xmlproductions   compare the productions `Char`, `NameStartChar`, " ++
  "`NameChar` and `Name` of the sealed XML 1.0 with their functions, and run the controls"

/-- Read the sealed document, and refuse a digest that is not the pinned one. -/
def readDocument (root : System.FilePath) : IO (Except String (List Char)) := do
  let path := root / documentPath
  unless ← path.pathExists do
    return .error s!"missing input {documentPath}"
  let bytes ← IO.FS.readBinFile path
  let digest := Gates.Sha256.hexDigest bytes
  unless digest == documentDigest do
    return .error (s!"{documentPath} has digest {digest}, expected the pinned " ++
      s!"{documentDigest}; read the productions again before pinning")
  match String.fromUTF8? bytes with
  | some text => return .ok text.toList
  | none => return .error s!"{documentPath}: the bytes are not UTF-8"

/-- Print a report: a PASS line to the standard output and a FAIL line to the standard error,
each in full. The last line is the verdict. -/
def printReport (lines : List Line) : IO UInt32 := do
  for line in lines do
    if line.passed then IO.println line.text else IO.eprintln line.text
  let failed := (lines.filter fun line => !line.passed).length
  if failed == 0 then
    IO.println (s!"PASS xml productions: the productions `Char`, `NameStartChar`, `NameChar` " ++
      s!"and `Name` of {documentPath} and their functions in {libraryModule} agree; " ++
      s!"{rows.length + 1} controls differ")
    return 0
  IO.eprintln s!"FAIL xml productions: {failed} of {lines.length} lines failed"
  return 1

/-- Command-line entry, invoked by `whatwgbin/XmlProductions.lean`. -/
def cli (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln usage
    return 2
  let root ← Gates.Common.projectRoot
  match (← readDocument root) >>= judge with
  | .ok lines => printReport lines
  | .error reason =>
    IO.eprintln s!"FAIL xml productions: {reason}"
    return 2

end Gates.XmlProductions
