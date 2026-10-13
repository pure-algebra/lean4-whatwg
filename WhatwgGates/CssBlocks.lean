import WhatwgGates.Census
import WhatwgGates.Sha256

/-!
# Gates.CssBlocks

Owner: the extractor of slice K1 of `docs/CSS-PACKAGE-PLAN.md` (rulings CS-2 and CS-3).

A CSS module is one Bikeshed source, sealed whole. Some of its blocks are data already. This
module finds them and turns each into rows that hold the block's own text:

- a `pre` element of class `propdef` or `descdef`: a property or a descriptor, field by field;
- an element of class `prod`, and a `pre` element with no attribute that opens a line with a
  `dfn` element and `=`: productions, each a name and a right-hand side;
- a `pre` element of class `railroad`: a diagram, as the nodes of its tree;
- a table under a listed anchor (`wantedTables`): its headings and its marked cells.

Each row carries the byte span of its block in the sealed source and the SHA-256 of those
bytes, so a reading that somebody authors later can pin the block it reads.

What it does not do. It interprets nothing: it does not read the value definition syntax, it
does not say what a field or a node means, and it does not say which token a heading of a
table names. It undoes Bikeshed's spelling of a production, by the rules of `undo`, and changes
nothing else.

It refuses what it does not know, so a block is never half read: a field name outside
`propertyFields` and `descriptorFields`, a node outside `nodeShapes`, an element or a character
reference inside a production outside the lists of `undo`, a class or an attribute beside a
block's own, a block class on an element that is not read, a block with no closing tag, and a
`div` or a `dl` that is not closed. A later pin that adds one of these fails here and is read on
purpose.

What it passes over. A comment, and a `script`, a `style` and an `xmp` element that is no
block, are passed over whole. An opening tag with a block class in one of them gives no row,
and is counted (`Extract.passed`). A second scan, which looks at every `<` of the source and
knows nothing of comments or elements, counts the opening tags with a block class; `extract`
refuses a source in which that number is not the blocks read and the tags passed over, so no
such tag goes unseen.

This is code that no theorem checks. `Gates.CssBlocksEmit` holds its controls.

Totality: every loop runs over a range of the input's size or over the structure of a list.
-/

namespace Gates.CssBlocks

open Gates.Census (byteNat matchesAt sliceString? normalizeWhitespace)

/-! ## The pin -/

/-- One sealed module: its name, which is its directory in `w3c/csswg-drafts`; the path of its
source under the repository root; the SHA-256 of that file. -/
structure Module where
  name : String
  path : String
  digest : String
  deriving Repr, BEq, Inhabited

/-- The directory of the pin, under the repository root. -/
def pinDirectory : String := "vendor/w3c-csswg-drafts-50337328"

/-- The record of a module of the pin: its source is `Overview.bs` in its own directory. -/
def sealedAt (name digest : String) : Module :=
  { name, path := s!"{pinDirectory}/{name}/Overview.bs", digest }

/-- The sealed modules: each digest is the module's row of `generated/vendor-manifest.tsv`.
A module joins this list, at its end, when its source joins `vendor/`, and the gate then
writes its tables and its row of the index. -/
def sealedModules : List Module :=
  [sealedAt "css-syntax-3" "690223b6eb537625eb92e0d144bfacab2009fb4f3912bbe1a1e8457b930701d3",
   sealedAt "css-transforms-1" "efa546b47442be30a773fd60b1a236b206720ea7942d88cfd539ebc6b32c95ee",
   sealedAt "css-values-4" "2004252d1473a1b6b3d72f0a7fcda4ff4e6821d774a1f4d7c0dc82ba220cdf46",
   sealedAt "css-animations-1" "2727c211033d4568621965aa5b2b9f3873a49ab8ae85223e8272803f143a3ccf",
   sealedAt "css-animations-2" "518624a57f5496f8f804b3f079da9efdc5493e18e9b00439b9c54ccf3fd9df34",
   sealedAt "css-easing-2" "650cdccf65fe523627ce7917c8d1bef1361dac6bf62a82f8f75c89524a521554",
   sealedAt "css-transforms-2" "088bd50ed41701612c3f9b6672c5092c5749991d4a54fe49d74ea9c903bdd078",
   sealedAt "mediaqueries-5" "aaf84f652a8363510be733bc9a5498aac24f16fb803e4aa6ce228cd080dce026",
   sealedAt "cssom-1" "b5dddd12b06f24336fab26f5c0f878f5eee92c2e2973a119234ac48710d0f948",
   sealedAt "css-color-4" "c06655afa62f635cd7bfeb58612a1506bec775fbb683e9bb254879918b56ca6a",
   sealedAt "css-variables-1" "99b56b75eac13bf1c9d0dea99140cb177a08586e693493f2761d37cd07e4c724"]

/-- The data tables that are read: a module, and the `id` of the table or of a `div` around
it. A listed anchor with no table under it is refused. -/
def wantedTables : List (String × String) := [("css-syntax-3", "serialization-tables")]

/-! ## Bytes and text -/

/-- A byte of white space: space, tab, line feed, form feed, carriage return. -/
def isSpace (n : Nat) : Bool := n == 0x20 || n == 0x09 || n == 0x0a || n == 0x0c || n == 0x0d

/-- An ASCII letter. -/
def isLetter (n : Nat) : Bool := (0x41 ≤ n && n ≤ 0x5a) || (0x61 ≤ n && n ≤ 0x7a)

/-- An ASCII digit. -/
def isDigit (n : Nat) : Bool := 0x30 ≤ n && n ≤ 0x39

/-- A byte of an element name or an attribute name. -/
def isNameByte (n : Nat) : Bool := isLetter n || isDigit n || n == 0x2d || n == 0x3a || n == 0x5f

/-- A character of white space. -/
def blank (c : Char) : Bool := isSpace c.toNat

/-- The first offset at or after `start` whose byte fails `p`, or the input's size. -/
def skipWhile (bs : ByteArray) (start : Nat) (p : Nat → Bool) : Nat := Id.run do
  let mut i := start
  for _ in [start:bs.size] do
    if !p (byteNat bs i) then return i
    i := i + 1
  return i

/-- The first offset from `start` and before `stop` where `pat` stands. -/
def find (bs pat : ByteArray) (start stop : Nat) : Option Nat := Id.run do
  for i in [start:stop] do
    if matchesAt bs pat i then return some i
  return none

/-- The bytes from `b` to `e` as text. -/
def textAt (bs : ByteArray) (b e : Nat) : String := (sliceString? bs b e).getD ""

/-- White space removed from both ends. -/
def trim (s : String) : String := Gates.Common.trimmed s

/-- Runs of white space as one space, and both ends trimmed. -/
def collapse (s : String) : String :=
  normalizeWhitespace (s.map fun c => if c.toNat == 0x0c then ' ' else c)

/-- The part of `cs` before the first `pat` and the part after it. -/
def breakOn (pat : List Char) : List Char → List Char → Option (List Char × List Char)
  | _, [] => none
  | acc, c :: cs =>
    if pat.isPrefixOf (c :: cs) then some (acc.reverse, (c :: cs).drop pat.length)
    else breakOn pat (c :: acc) cs

/-- The inside of a tag, from after its `<`, and what follows its `>`. A `>` inside a quoted
attribute value does not close the tag. -/
def splitTag : Option Char → List Char → List Char → Option (List Char × List Char)
  | _, _, [] => none
  | none, acc, c :: rest =>
    if c == '>' then some (acc.reverse, rest)
    else if c == '"' || c == '\'' then splitTag (some c) (c :: acc) rest
    else splitTag none (c :: acc) rest
  | some quote, acc, c :: rest =>
    if c == quote then splitTag none (c :: acc) rest else splitTag (some quote) (c :: acc) rest

/-- The element that the inside of a tag names, in lower case. -/
def tagName (inside : List Char) : String :=
  let body := if inside.head? == some '/' then inside.drop 1 else inside
  (String.ofList (body.takeWhile fun c => isNameByte c.toNat)).toLower

/-! ## Tags of the source -/

/-- An opening tag: the element's name and the attributes' names in lower case, and the offset
after its `>`. -/
structure Tag where
  name : String
  attrs : Array (String × String)
  stop : Nat
  deriving Inhabited

/-- The value of the attribute `key`, or the empty text when the tag has none. -/
def Tag.attr (t : Tag) (key : String) : String :=
  ((t.attrs.find? (·.1 == key)).map (·.2)).getD ""

/-- The words of the `class` attribute, as written. -/
def Tag.words (t : Tag) : List String :=
  ((normalizeWhitespace (t.attr "class")).splitOn " ").filter (· != "")

/-- The opening tag at `b`, when the bytes there read as one: `<`, a name, attributes that are
bare, quoted or without a value, and `>`. Bikeshed writes `<` for other things too
(`<<length>>`, a `<` in a diagram), and those read as no tag. -/
def readTag (bs : ByteArray) (b : Nat) : Option Tag := Id.run do
  if byteNat bs b != 0x3c || !isLetter (byteNat bs (b + 1)) then return none
  let nameEnd := skipWhile bs (b + 1) isNameByte
  let name := (textAt bs (b + 1) nameEnd).toLower
  let mut i := nameEnd
  let mut attrs : Array (String × String) := #[]
  for _ in [0:bs.size + 1] do
    let before := i
    i := skipWhile bs i isSpace
    if i ≥ bs.size then return none
    if byteNat bs i == 0x3e then return some { name, attrs, stop := i + 1 }
    if byteNat bs i == 0x2f && byteNat bs (i + 1) == 0x3e then
      return some { name, attrs, stop := i + 2 }
    if i == before then return none
    let keyStart := i
    i := skipWhile bs i isNameByte
    if i == keyStart then return none
    let key := (textAt bs keyStart i).toLower
    let equals := skipWhile bs i isSpace
    if byteNat bs equals != 0x3d then
      attrs := attrs.push (key, "")
    else
      let valueStart := skipWhile bs (equals + 1) isSpace
      let quote := byteNat bs valueStart
      if quote == 0x22 || quote == 0x27 then
        let valueEnd := skipWhile bs (valueStart + 1) (· != quote)
        if valueEnd ≥ bs.size then return none
        attrs := attrs.push (key, textAt bs (valueStart + 1) valueEnd)
        i := valueEnd + 1
      else
        let valueEnd := skipWhile bs valueStart fun n => !isSpace n && n != 0x3e
        if valueEnd == valueStart then return none
        attrs := attrs.push (key, textAt bs valueStart valueEnd)
        i := valueEnd
  return none

/-- The closing tag of the element `name` at or after `start`: where it opens, and the offset
after its `>`. -/
def findClose (bs : ByteArray) (name : String) (start : Nat) : Option (Nat × Nat) := Id.run do
  let pat := ("</" ++ name).toUTF8
  let mut cursor := start
  for _ in [0:bs.size + 1] do
    let some hit := find bs pat cursor bs.size | return none
    let after := hit + pat.size
    let gt := skipWhile bs after isSpace
    if !isNameByte (byteNat bs after) && byteNat bs gt == 0x3e then return some (hit, gt + 1)
    cursor := hit + 1
  return none

/-- Where an element `name` opens between `a` and `b`, if one does. -/
def opensInside (bs : ByteArray) (name : String) (a b : Nat) : Option Nat := Id.run do
  let pat := ("<" ++ name).toUTF8
  let mut cursor := a
  for _ in [0:bs.size + 1] do
    let some hit := find bs pat cursor b | return none
    if !isNameByte (byteNat bs (hit + pat.size)) then return some hit
    cursor := hit + 1
  return none

/-! ## Bikeshed's spelling of a production, undone -/

/-- The elements whose tags are dropped from a production: the text they hold stays. -/
def textElements : List String := ["dfn", "a", "var", "l", "sup"]

/-- The elements that stand for white space in a production. -/
def spaceElements : List String := ["br"]

/-- The character references that are read, each with its character. `&nbsp;` lays a grammar
out over several lines, and is a space. -/
def references : List (String × Char) := [("lt", '<'), ("gt", '>'), ("amp", '&'), ("nbsp", ' ')]

/-- Whether the characters after a `<` open a tag: a letter, or `/` and a letter. -/
def opensTag : List Char → Bool
  | '/' :: c :: _ => isLetter c.toNat
  | c :: _ => isLetter c.toNat
  | [] => false

/-- `undo` over characters, with what is written so far in reverse. The fuel is more than the
characters left, and every step takes at least one. -/
def undoFrom : Nat → List Char → List Char → Except String (List Char)
  | _, [], out => .ok out.reverse
  | 0, _ :: _, _ => .error "the text is longer than its own length"
  | fuel + 1, c :: rest, out =>
    if c == '<' && rest.head? == some '<' then
      match breakOn ['>', '>'] [] (rest.drop 1) with
      | none => .error "a `<<` has no `>>` after it"
      | some (inner, after) =>
        if inner.isEmpty || inner.any (fun x => x == '<' || x == '\n') then
          .error s!"the unread type `<<{String.ofList inner}>>`"
        else undoFrom fuel after ('>' :: inner.reverse ++ '<' :: out)
    else if c == '<' && opensTag rest then
      match splitTag none [] rest with
      | none => .error "a tag is not closed"
      | some (inside, after) =>
        let name := tagName inside
        if textElements.contains name then undoFrom fuel after out
        else if spaceElements.contains name then undoFrom fuel after (' ' :: out)
        else .error s!"the unread element `{name}`"
    else if c == '&' then
      let name := rest.takeWhile fun x => x.isAlphanum || x == '#'
      match rest.drop name.length with
      | ';' :: after =>
        if name.isEmpty then undoFrom fuel rest (c :: out)
        else
          match references.find? (·.1 == String.ofList name) with
          | some (_, character) => undoFrom fuel after (character :: out)
          | none => .error s!"the unread character reference `&{String.ofList name};`"
      | _ => undoFrom fuel rest (c :: out)
    else if c == '\'' && rest.head? == some '\'' then
      match breakOn ['\'', '\''] [] (rest.drop 1) with
      | none => .error "a `''` has no `''` after it"
      | some (inner, after) =>
        if inner.isEmpty || inner.any (fun x => x == '\'' || x == '\n' || x == '/' || x == '<') then
          .error s!"the unread keyword `''{String.ofList inner}''`"
        else undoFrom fuel after (inner.reverse ++ out)
    else undoFrom fuel rest (c :: out)

/-- A production's text as the value definition syntax writes it, with white space collapsed.
These spellings of Bikeshed are undone, and nothing else is changed:

- `<<name>>` is `<name>`;
- `&lt;`, `&gt;` and `&amp;` are their characters, and `&nbsp;` is a space;
- `''keyword''` is `keyword`;
- a `dfn`, `a`, `var`, `l` or `sup` element is its text, and a `br` element is a space.

Any other element or character reference is refused, and so is a `''keyword''` that names
what it is a keyword of (`''property/keyword''`). In an `xmp` element (`raw`) the text is
literal, and nothing is undone. -/
def undo (raw : Bool) (s : String) : Except String String :=
  if raw then .ok (collapse s)
  else (undoFrom (s.length + 1) s.toList []).map fun cs => collapse (String.ofList cs)

/-! ## Fields: `propdef` and `descdef` -/

/-- The fields of a `propdef` block that are read. A block's label matches one of these
without regard to case, as Bikeshed's does. -/
def propertyFields : List String :=
  ["Name", "Value", "New values", "Initial", "Applies to", "Inherited", "Percentages",
   "Computed value", "Used value", "Canonical order", "Animation type"]

/-- The fields of a `descdef` block that are read. -/
def descriptorFields : List String := ["Name", "For", "Value", "Type"]

/-- The class words that a `propdef` block may carry beside `propdef`. -/
def propertyFlags : List String := ["partial", "shorthand"]

/-- The class words that a `descdef` block may carry beside `descdef`. -/
def descriptorFlags : List String := ["mq"]

/-- A line's label and what follows it, when the line opens with a label: at most three words
of letters, then a colon. -/
def labelOf (line : String) : Option (String × String) :=
  let cs := line.toList
  let label := cs.takeWhile (· != ':')
  match cs.drop label.length with
  | ':' :: value =>
    let name := collapse (String.ofList label)
    if !name.isEmpty && label.all (fun c => isLetter c.toNat || c == ' ') &&
        (name.splitOn " ").length ≤ 3 then
      some (name, trim (String.ofList value))
    else none
  | _ => none

/-- The fields of a block, in the block's order, each under its name in `known`. A line that
opens with no label continues the field above it. A label outside `known`, a field that
stands twice, an empty field and text before the first field are refused. -/
def readFields (known : List String) (body : String) : Except String (List (String × String)) := do
  let mut out : Array (String × String) := #[]
  for line in body.splitOn "\n" do
    let text := trim line
    if text.isEmpty then continue
    match labelOf text with
    | some (label, value) =>
      match known.find? fun k => k.toLower == label.toLower with
      | none => throw s!"the unread field `{label}`"
      | some key =>
        if out.any (·.1 == key) then throw s!"the field `{key}` stands twice"
        out := out.push (key, value)
    | none =>
      if out.isEmpty then throw s!"text stands before the first field: {text}"
      out := out.modify (out.size - 1) fun (key, value) => (key, value ++ " " ++ text)
  let fields := out.toList.map fun (key, value) => (key, collapse value)
  for (key, value) in fields do
    if value.isEmpty then throw s!"the field `{key}` is empty"
  return fields

/-- The text of the field `key`, when the block states it. -/
def fieldOf (fields : List (String × String)) (key : String) : Option String :=
  (fields.find? (·.1 == key)).map (·.2)

/-! ## Productions -/

/-- The name a line opens with, in one of the forms a production's name takes: the `dfn` tag
around it if it has one, the name as written, and what follows it. -/
def nameOf (raw : Bool) (cs : List Char) : Option (String × List Char × List Char) :=
  let atName : Option (String × List Char × List Char) :=
    match cs with
    | '@' :: rest =>
      let body := rest.takeWhile fun c => isLetter c.toNat || isDigit c.toNat || c == '-'
      if body.isEmpty then none else some ("", '@' :: body, rest.drop body.length)
    | _ => none
  if raw then
    match cs with
    | '<' :: c :: _ =>
      if isLetter c.toNat then
        (breakOn ['>'] [] cs).map fun (name, rest) => ("", name ++ ['>'], rest)
      else none
    | _ => atName
  else if "<dfn".toList.isPrefixOf cs && !isNameByte ((cs.drop 4).head?.getD ' ').toNat then
    match splitTag none [] (cs.drop 1) with
    | none => none
    | some (inside, after) =>
      (breakOn "</dfn>".toList [] after).map fun (name, rest) =>
        ("<" ++ String.ofList inside ++ ">", name, rest)
  else if "<<".toList.isPrefixOf cs then
    (breakOn ['>', '>'] [] (cs.drop 2)).map fun (inner, rest) =>
      ("", "<<".toList ++ inner ++ ">>".toList, rest)
  else if "&lt;".toList.isPrefixOf cs then
    let body := (cs.drop 4).takeWhile fun c => c != '>' && c != '&' && !blank c
    match cs.drop (4 + body.length) with
    | '>' :: rest => some ("", "&lt;".toList ++ body ++ ['>'], rest)
    | rest =>
      if "&gt;".toList.isPrefixOf rest then
        some ("", "&lt;".toList ++ body ++ "&gt;".toList, rest.drop 4)
      else none
  else atName

/-- A line that opens a production: a name, then `=`, then white space or the line's end.
The answer is the `dfn` tag, the name as written, and the line after the `=`. -/
def headOf (raw : Bool) (line : List Char) : Option (String × List Char × List Char) :=
  match nameOf raw (line.dropWhile blank) with
  | none => none
  | some (tag, name, rest) =>
    match rest.dropWhile blank with
    | '=' :: after =>
      if after.isEmpty || blank (after.head?.getD ' ') then some (tag, name, after) else none
    | _ => none

/-- Whether a `pre` element with no class holds definitions: one of its lines opens a
production whose name is a `dfn` element. -/
def holdsDefinition (body : String) : Bool :=
  (body.splitOn "\n").any fun line =>
    match headOf false line.toList with
    | some (tag, _, _) => !tag.isEmpty
    | none => false

/-- One production of a block. `name` is empty when the block holds an expression and
defines no name. `head` is the `dfn` tag around the name, or empty when the name stands
bare, as it does where a production restates a name that is defined elsewhere. -/
structure Production where
  name : String
  head : String
  rhs : String
  deriving Repr, BEq, Inhabited

/-- The productions of a block, in order. A line that opens no production continues the one
above it. A block with no such line is one expression. -/
def readProductions (raw : Bool) (body : String) : Except String (List Production) := do
  let mut found : Array (String × List Char × List String) := #[]
  let mut before : List String := []
  for line in body.splitOn "\n" do
    match headOf raw line.toList with
    | some (tag, name, rest) => found := found.push (tag, name, [String.ofList rest])
    | none =>
      if found.isEmpty then before := before ++ [line]
      else found := found.modify (found.size - 1) fun (tag, name, ls) => (tag, name, ls ++ [line])
  if found.isEmpty then
    let rhs ← undo raw body
    if rhs.isEmpty then throw "the block is empty"
    return [{ name := "", head := "", rhs }]
  unless (collapse ("\n".intercalate before)).isEmpty do
    throw "text stands before the first production"
  let mut out : Array Production := #[]
  for (tag, written, ls) in found do
    let name ← undo raw (String.ofList written)
    if name.isEmpty then throw "a production has no name"
    let rhs ← undo raw ("\n".intercalate ls)
    if rhs.isEmpty then throw s!"the production `{name}` has no right-hand side"
    out := out.push { name, head := tag, rhs }
  return out.toList

/-! ## Railroad diagrams -/

/-- What a node of a diagram carries: a text, nothing, or the nodes under it. -/
inductive Shape where
  | text | bare | group
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The nodes that are read, by the name the diagram writes. Two names that Bikeshed draws
alike (`Opt` and `Optional`) stay two names here. -/
def nodeShapes : List (String × Shape) :=
  [("T", .text), ("N", .text), ("C", .text), ("S", .bare), ("Skip", .bare),
   ("Seq", .group), ("And", .group), ("Stack", .group), ("Choice", .group), ("Or", .group),
   ("Star", .group), ("ZeroOrMore", .group), ("Plus", .group), ("OneOrMore", .group),
   ("Opt", .group), ("Optional", .group)]

/-- The arguments that a group may carry after its colon: none; a number after `Choice` and
`Or`; `skip` after `Opt` and `Optional`. -/
def groupArgument (kind arg : String) : Bool :=
  arg.isEmpty ||
  ((kind == "Choice" || kind == "Or") && arg.toList.all fun c => isDigit c.toNat) ||
  ((kind == "Opt" || kind == "Optional") && arg == "skip")

/-- One node of a diagram: how deep it stands, its name, its shape, and its text. The text
of a group is its argument. The nodes of a diagram in the order of its lines are its tree:
a node's children are the nodes one step deeper that follow it. -/
structure Node where
  level : Nat
  kind : String
  shape : Shape
  text : String
  deriving Repr, BEq, Inhabited

/-- The nodes of a diagram. The first line sets the margin, and the first line that stands
deeper sets the step. A line that is not a whole number of steps from the margin is refused,
and so are a line more than one step deeper than the line above it, a line under a node that
holds none, a group that holds none, and a node or an argument outside the lists. -/
def readDiagram (body : String) : Except String (List Node) := do
  let lines := (body.splitOn "\n").filter fun line => !(trim line).isEmpty
  let lead (line : String) : List Char := line.toList.takeWhile fun c => c == ' ' || c == '\t'
  let some first := lines.head? | throw "the diagram is empty"
  let margin := lead first
  let mut step : List Char := []
  let mut nodes : Array Node := #[]
  for line in lines do
    let shown := trim line
    let indent := lead line
    unless margin.isPrefixOf indent do
      throw s!"the line `{shown}` stands left of the first line"
    let extra := indent.drop margin.length
    if step.isEmpty then step := extra
    let level := if step.isEmpty then 0 else extra.length / step.length
    unless extra == (List.replicate level step).flatten do
      throw s!"the line `{shown}` is not indented by a whole number of steps"
    let rest := line.toList.drop indent.length
    let kind := rest.takeWhile fun c => isLetter c.toNat
    let text ←
      match rest.drop kind.length with
      | ':' :: after => pure (trim (String.ofList after))
      | _ => throw s!"the line `{shown}` does not open with a node's name and a colon"
    let kind := String.ofList kind
    let some (_, shape) := nodeShapes.find? (·.1 == kind)
      | throw s!"the unread node `{kind}`"
    match shape with
    | .text => if text.isEmpty then throw s!"the node `{kind}` has no text"
    | .bare => unless text.isEmpty do throw s!"the node `{kind}` carries the text `{text}`"
    | .group =>
      unless groupArgument kind text do
        throw s!"the node `{kind}` carries the unread argument `{text}`"
    match nodes.back? with
    | none => pure ()
    | some above =>
      if level > above.level + 1 then
        throw s!"the line `{shown}` stands more than one step deeper than the line above it"
      if level == above.level + 1 && above.shape != .group then
        throw s!"the line `{shown}` stands under the node `{above.kind}`, which holds none"
      if level ≤ above.level && above.shape == .group then
        throw s!"the node `{above.kind}` holds no node"
    nodes := nodes.push { level, kind, shape, text }
  if let some last := nodes.back? then
    if last.shape == .group then throw s!"the node `{last.kind}` holds no node"
  return nodes.toList

/-- A text between double quotes: a backslash and a double quote each take a backslash. -/
def quoted (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\" else if c == '"' then "\\\"" else String.singleton c) ++ "\""

/-- A diagram's tree on one line. A node with a text is `(T "text")`, a node with nothing is
`(S)`, and a group is `(Choice 1 …)`: its name, its argument if it has one, then its
children. The nodes at the top stand side by side. -/
def printTree (nodes : List Node) : String := Id.run do
  let mut out := ""
  let mut depth := 0
  for node in nodes do
    for _ in [node.level:depth] do out := out ++ ")"
    depth := node.level
    unless out.isEmpty do out := out ++ " "
    match node.shape with
    | .text => out := out ++ "(" ++ node.kind ++ " " ++ quoted node.text ++ ")"
    | .bare => out := out ++ "(" ++ node.kind ++ ")"
    | .group =>
      out := out ++ "(" ++ node.kind ++ (if node.text.isEmpty then "" else " " ++ node.text)
      depth := depth + 1
  for _ in [0:depth] do out := out ++ ")"
  return out

/-! ## Tables -/

/-- The mark of a marked cell: U+2717. -/
def mark : String := String.singleton (Char.ofNat 0x2717)

/-- A table as read: its column headings, its row headings, and its marked cells, each as
its row heading and its column heading. -/
structure Table where
  columns : List String
  rows : List String
  marked : List (String × String)
  deriving Repr, BEq, Inhabited

/-- The rows of a table, each as its cells: whether the cell is a heading, and its text. The
only tags read are `tr`, `th` and `td` with no attribute, and their closing tags. -/
def tableCells : Nat → List Char → Array (Array (Bool × String)) →
    Except String (Array (Array (Bool × String)))
  | _, [], rows => .ok rows
  | 0, _ :: _, _ => .error "the table is longer than its own length"
  | fuel + 1, c :: rest, rows =>
    if c == '<' then
      match splitTag none [] rest with
      | none => .error "a tag of the table is not closed"
      | some (inside, after) =>
        let name := tagName inside
        let closing := inside.head? == some '/'
        let bare := (String.ofList inside).toLower == (if closing then "/" ++ name else name)
        if !["tr", "th", "td"].contains name then
          .error s!"the unread element `{name}` in the table"
        else if !bare then .error s!"a `{name}` tag of the table carries an attribute"
        else if closing then tableCells fuel after rows
        else if name == "tr" then tableCells fuel after (rows.push #[])
        else if rows.isEmpty then .error "a cell stands before the first row"
        else tableCells fuel after (rows.modify (rows.size - 1) (·.push (name == "th", "")))
    else
      match rows.back? with
      | none =>
        if blank c then tableCells fuel rest rows else .error "text stands before the first row"
      | some row =>
        if row.isEmpty then
          if blank c then tableCells fuel rest rows
          else .error "text stands in a row before its first cell"
        else
          tableCells fuel rest (rows.modify (rows.size - 1) fun r =>
            r.modify (r.size - 1) fun (heading, text) => (heading, text.push c))

/-- A table of marks. The first row is an empty corner cell and the column headings. Each
other row is its heading and one cell for each column, marked with `mark` or empty. A cell
that is neither, a heading that stands twice and a row of another length are refused. -/
def readTable (body : String) : Except String Table := do
  let cells ← tableCells (body.length + 1) body.toList #[]
  let rows := cells.toList.map fun cellsOf =>
    cellsOf.toList.map fun (heading, text) => (heading, collapse text)
  let headings :: lines := rows | throw "the table has no row"
  let (false, "") :: columnCells := headings
    | throw "the first row does not open with an empty corner cell"
  let mut columns : List String := []
  for (heading, text) in columnCells do
    unless heading && !text.isEmpty && !text.toList.contains '&' do
      throw s!"the first row holds the cell `{text}`, which is no column heading"
    if columns.contains text then throw s!"the column heading `{text}` stands twice"
    columns := columns ++ [text]
  if columns.isEmpty then throw "the table has no column"
  let mut names : List String := []
  let mut marked : List (String × String) := []
  for line in lines do
    let (true, name) :: cellsOf := line | throw "a row does not open with its heading"
    if name.isEmpty || name.toList.contains '&' then throw "a row's heading is empty or unread"
    if names.contains name then throw s!"the row heading `{name}` stands twice"
    unless cellsOf.length == columns.length do
      throw (s!"the row `{name}` has {cellsOf.length} cells, and the table has " ++
        s!"{columns.length} columns")
    for ((heading, text), column) in cellsOf.zip columns do
      if heading then throw s!"the row `{name}` holds a second heading"
      if text == mark then marked := marked ++ [(name, column)]
      else unless text.isEmpty do
        throw s!"the cell `{text}` of the row `{name}` is neither marked nor empty"
    names := names ++ [name]
  if names.isEmpty then throw "the table has no row under its headings"
  return { columns, rows := names, marked }

/-! ## The walk over a source -/

/-- A block as found: its kind (`propdef`, `descdef`, `prod`, `railroad`, or `pre` for a `pre`
element with no class that holds definitions), its element, its class words, the offsets of
its opening tag, of its body and of its end, the class of each `div` around it, and the `dt`
before it in its `dl`. -/
structure Block where
  kind : String
  element : String
  classes : List String
  start : Nat
  bodyStart : Nat
  bodyStop : Nat
  stop : Nat
  within : String
  term : String
  termId : String
  deriving Repr, Inhabited

/-- A `table` element as found, with the `id` of each `div` around it. -/
structure TableSpan where
  id : String
  around : List String
  start : Nat
  bodyStart : Nat
  bodyStop : Nat
  stop : Nat
  within : String
  deriving Repr, Inhabited

/-- An open `div`. -/
structure Div where
  start : Nat
  classes : String
  id : String

/-- An open `dl`: the text and the `id` of its last `dt`, and where a `dt` that is still open
began. -/
structure Dl where
  start : Nat
  term : String := ""
  termId : String := ""
  termStart : Option Nat := none

/-- What the walk has seen. `passed` holds the spans it passed over and read nothing of: the
comments, and the `script`, `style` and `xmp` elements that are no block. `preStop` is the
end of the `pre` element that the walk is inside, when that element is no block. -/
structure Walk where
  blocks : Array Block := #[]
  tables : Array TableSpan := #[]
  metadata : Array (Nat × Nat) := #[]
  passed : Array (Nat × Nat) := #[]
  divs : List Div := []
  dls : List Dl := []
  preStop : Nat := 0

/-- The class of each `div` around the walk's place, the outermost first. -/
def Walk.within (w : Walk) : String :=
  " > ".intercalate ((w.divs.reverse.map fun d => normalizeWhitespace d.classes).filter (· != ""))

/-- End the text of the open `dt`, if one is open, at `i`. -/
def Walk.endTerm (bs : ByteArray) (w : Walk) (i : Nat) : Walk :=
  match w.dls with
  | dl :: rest =>
    match dl.termStart with
    | some start =>
      { w with dls := { dl with term := textAt bs start i, termStart := none } :: rest }
    | none => w
  | [] => w

/-- The class words that make an element a block. -/
def blockClasses : List String := ["propdef", "descdef", "prod", "railroad"]

/-- Take the element at `i` as a block. Its opening tag carries `class` alone, it has a
closing tag, and no element of its own name opens inside it. -/
def Walk.block (bs : ByteArray) (w : Walk) (i : Nat) (tag : Tag) (kind : String) :
    Except String (Walk × Nat) := do
  if i < w.preStop then
    throw s!"offset {i}: a `{kind}` block stands inside a `pre` element that is no block"
  for (key, _) in tag.attrs do
    unless key == "class" do
      throw s!"offset {i}: the opening tag of a `{kind}` block carries the unread attribute `{key}`"
  let some (close, stop) := findClose bs tag.name tag.stop
    | throw s!"offset {i}: the `{tag.name}` element of a `{kind}` block has no closing tag"
  if let some inner := opensInside bs tag.name tag.stop close then
    throw s!"offset {i}: a `{tag.name}` element opens inside a `{kind}` block, at offset {inner}"
  let (term, termId) :=
    match w.dls with
    | dl :: _ => if dl.termStart.isNone then (dl.term, dl.termId) else ("", "")
    | [] => ("", "")
  let block : Block :=
    { kind, element := tag.name, classes := tag.words, start := i, bodyStart := tag.stop,
      bodyStop := close, stop, within := w.within, term, termId }
  return ({ w with blocks := w.blocks.push block }, stop)

/-- Read the opening tag at `i`: the walk after it, and the offset to go on from. -/
def Walk.opening (bs : ByteArray) (w : Walk) (i : Nat) (tag : Tag) :
    Except String (Walk × Nat) := do
  let marks := tag.words.filter blockClasses.contains
  let unread : Except String (Walk × Nat) :=
    throw s!"offset {i}: the unread element `{tag.name}` of class `{" ".intercalate marks}`"
  let closed (_ : Unit) : Except String (Nat × Nat) :=
    match findClose bs tag.name tag.stop with
    | some span => pure span
    | none => throw s!"offset {i}: the `{tag.name}` element has no closing tag"
  if tag.name == "script" || tag.name == "style" then
    unless marks.isEmpty do return ← unread
    let (close, stop) ← closed ()
    return ({ w with passed := w.passed.push (tag.stop, close) }, stop)
  if tag.name == "xmp" then
    if marks == ["prod"] then return ← w.block bs i tag "prod"
    unless marks.isEmpty do return ← unread
    let (close, stop) ← closed ()
    return ({ w with passed := w.passed.push (tag.stop, close) }, stop)
  if tag.name == "pre" then
    match marks with
    | [kind] => return ← w.block bs i tag kind
    | _ :: _ :: _ => return ← unread
    | [] =>
      if i < w.preStop then throw s!"offset {i}: a `pre` element opens inside a `pre` element"
      let (close, stop) ← closed ()
      if tag.words.contains "metadata" then
        return ({ w with metadata := w.metadata.push (tag.stop, close) }, stop)
      if tag.attrs.isEmpty && holdsDefinition (textAt bs tag.stop close) then
        return ← w.block bs i tag "pre"
      return ({ w with preStop := stop }, tag.stop)
  if (tag.name == "span" || tag.name == "code") && marks == ["prod"] then
    return ← w.block bs i tag "prod"
  unless marks.isEmpty do return ← unread
  if i < w.preStop then return (w, tag.stop)
  if tag.name == "div" then
    let div : Div := { start := i, classes := tag.attr "class", id := tag.attr "id" }
    return ({ w with divs := div :: w.divs }, tag.stop)
  if tag.name == "dl" then return ({ w with dls := { start := i } :: w.dls }, tag.stop)
  if tag.name == "dt" then
    let w := w.endTerm bs i
    match w.dls with
    | dl :: rest =>
      let dl := { dl with term := "", termId := tag.attr "id", termStart := some tag.stop }
      return ({ w with dls := dl :: rest }, tag.stop)
    | [] => return (w, tag.stop)
  if tag.name == "dd" then return (w.endTerm bs i, tag.stop)
  if tag.name == "table" then
    let (close, stop) ← closed ()
    let span : TableSpan :=
      { id := tag.attr "id", around := (w.divs.map (·.id)).filter (· != ""), start := i,
        bodyStart := tag.stop, bodyStop := close, stop, within := w.within }
    return ({ w with tables := w.tables.push span }, tag.stop)
  return (w, tag.stop)

/-- Read the closing tag of `name` at `i`. -/
def Walk.closing (bs : ByteArray) (w : Walk) (i : Nat) (name : String) : Except String Walk := do
  if i < w.preStop then return w
  if name == "div" then
    match w.divs with
    | _ :: rest => return { w with divs := rest }
    | [] => throw s!"offset {i}: a `</div>` closes no `div`"
  if name == "dl" then
    match (w.endTerm bs i).dls with
    | _ :: rest => return { w with dls := rest }
    | [] => throw s!"offset {i}: a `</dl>` closes no `dl`"
  if name == "dt" then return w.endTerm bs i
  return w

/-- Walk a source from its first byte to its last. A comment is passed over, and so are a
`script`, a `style` and an `xmp` element that is no block: nothing inside them is read. A
`<<` is Bikeshed's and opens no tag. -/
def walk (bs : ByteArray) : Except String Walk := do
  let mut w : Walk := {}
  let mut i := 0
  for _ in [0:bs.size + 1] do
    i := skipWhile bs i (· != 0x3c)
    if i ≥ bs.size then break
    if matchesAt bs "<!--".toUTF8 i then
      let some stop := find bs "-->".toUTF8 (i + 4) bs.size
        | throw s!"offset {i}: a comment is not closed"
      w := { w with passed := w.passed.push (i + 4, stop) }
      i := stop + 3
    else if byteNat bs (i + 1) == 0x3c then
      i := i + 2
    else if byteNat bs (i + 1) == 0x2f then
      let nameEnd := skipWhile bs (i + 2) isNameByte
      let gt := skipWhile bs nameEnd isSpace
      if nameEnd == i + 2 || byteNat bs gt != 0x3e then
        i := i + 1
      else
        w ← w.closing bs i (textAt bs (i + 2) nameEnd).toLower
        i := gt + 1
    else
      match readTag bs i with
      | none => i := i + 1
      | some tag =>
        let (after, next) ← w.opening bs i tag
        w := after
        i := next
  if let some div := w.divs.head? then
    throw s!"offset {div.start}: a `div` element is not closed"
  if let some dl := w.dls.head? then
    throw s!"offset {dl.start}: a `dl` element is not closed"
  return w

/-- How many opening tags between `a` and `b` carry a block class. -/
def blockTagsIn (bs : ByteArray) (a b : Nat) : Nat := Id.run do
  let mut count := 0
  for i in [a:b] do
    if byteNat bs i == 0x3c then
      if let some tag := readTag bs i then
        if tag.words.any blockClasses.contains then count := count + 1
  return count

/-! ## Rows -/

/-- Where a row comes from: its module, the kind of its block, the block's byte span in the
sealed source, the SHA-256 of those bytes, and the class of each `div` around the block, the
outermost first. A block inside a `div` of class `example` is an illustration, and defines
nothing. -/
structure Origin where
  module : String
  kind : String
  start : Nat
  stop : Nat
  digest : String
  within : String
  deriving Repr, BEq, Inhabited

/-- One property of a `propdef` block, or one descriptor of a `descdef` block. A block that
names several is several rows. `grammar` is the block's `Value`, or its `New values`, with
Bikeshed's spelling undone as a production's is. `fields` holds the other fields as written. -/
structure FieldRow where
  origin : Origin
  name : String
  grammar : String
  fields : List (String × String)
  deriving Repr, BEq, Inhabited

/-- One production, with its place among the productions of its block. -/
structure ProductionRow where
  origin : Origin
  ordinal : Nat
  production : Production
  deriving Repr, BEq, Inhabited

/-- One diagram: the text and the `id` of the `dt` before it, both empty when it stands in no
`dl`, and its nodes. -/
structure DiagramRow where
  origin : Origin
  name : String
  anchor : String
  nodes : List Node
  deriving Repr, BEq, Inhabited

/-- One table under a listed anchor. -/
structure TableRow where
  origin : Origin
  anchor : String
  table : Table
  deriving Repr, BEq, Inhabited

/-- Everything read from one module. `blocks` counts the blocks of each kind. `passed` counts
the opening tags with a block class that stand in a comment or in a `script`, `style` or `xmp`
element that is no block: the walk passed over them, and no row comes from them. -/
structure Extract where
  module : Module
  title : String
  size : Nat
  blocks : List (String × Nat)
  passed : Nat
  properties : List FieldRow
  descriptors : List FieldRow
  productions : List ProductionRow
  diagrams : List DiagramRow
  tables : List TableRow
  deriving Repr, Inhabited

/-- The module's title: the one `Title` line of its metadata blocks. -/
def titleOf (bs : ByteArray) (w : Walk) : Except String String := do
  let mut titles : List String := []
  for (a, b) in w.metadata do
    for line in (textAt bs a b).splitOn "\n" do
      if let some (label, value) := labelOf (trim line) then
        if label == "Title" then titles := titles ++ [value]
  match titles with
  | [title] => if title.isEmpty then throw "the `Title` line is empty" else return title
  | [] => throw "no metadata block has a `Title` line"
  | _ => throw "two `Title` lines"

/-- The rows of a `propdef` or `descdef` block: one for each name of its `Name` field. -/
def fieldRows (origin : Origin) (known flags classes : List String) (own body : String) :
    Except String (List FieldRow) := do
  for word in classes do
    unless word == own || flags.contains word do
      throw s!"the unread class `{word}` beside `{own}`"
  let fields ← readFields known body
  let some names := fieldOf fields "Name" | throw "the block has no `Name` field"
  let names := ((names.splitOn ",").map trim).filter (· != "")
  if names.isEmpty then throw "the `Name` field names nothing"
  for name in names do
    if name.toList.any blank then throw s!"the name `{name}` holds white space"
  let grammar ←
    match fieldOf fields "Value", fieldOf fields "New values" with
    | some value, none => undo false value
    | none, some value => undo false value
    | none, none => pure ""
    | some _, some _ => throw "the block states both `Value` and `New values`"
  return names.map fun name =>
    { origin, name, grammar, fields := fields.filter (·.1 != "Name") }

/-- Every row of one module, with the tables under `anchors`. A refusal names the module and
the offset of the block. -/
def extractWith (anchors : List String) (m : Module) (bs : ByteArray) : Except String Extract := do
  let inModule {α : Type} (x : Except String α) : Except String α :=
    x.mapError (s!"{m.name}: " ++ ·)
  let digestOf (start stop : Nat) : String := Gates.Sha256.hexDigest (bs.extract start stop)
  unless (String.fromUTF8? bs).isSome do throw s!"{m.name}: the bytes are not UTF-8"
  let w ← inModule (walk bs)
  let title ← inModule (titleOf bs w)
  let passed := w.passed.foldl (fun n (a, b) => n + blockTagsIn bs a b) 0
  let classed := (w.blocks.filter (·.kind != "pre")).size
  let seen := blockTagsIn bs 0 bs.size
  unless seen == classed + passed do
    throw (s!"{m.name}: {seen} opening tags carry a block class, and {classed} were read as " ++
      s!"blocks and {passed} passed over in comments and raw text")
  let mut properties : Array FieldRow := #[]
  let mut descriptors : Array FieldRow := #[]
  let mut productions : Array ProductionRow := #[]
  let mut diagrams : Array DiagramRow := #[]
  for block in w.blocks do
    let inBlock {α : Type} (x : Except String α) : Except String α :=
      x.mapError (s!"{m.name}: offset {block.start}: the `{block.kind}` block: " ++ ·)
    let body := textAt bs block.bodyStart block.bodyStop
    let origin (kind : String) : Origin :=
      { module := m.name, kind, start := block.start, stop := block.stop,
        digest := digestOf block.start block.stop, within := block.within }
    let words := " ".intercalate block.classes
    if block.kind == "propdef" then
      properties := properties ++ (← inBlock
        (fieldRows (origin words) propertyFields propertyFlags block.classes "propdef" body))
    else if block.kind == "descdef" then
      descriptors := descriptors ++ (← inBlock
        (fieldRows (origin words) descriptorFields descriptorFlags block.classes "descdef" body))
    else if block.kind == "railroad" then
      unless block.classes == ["railroad"] do
        throw s!"{m.name}: offset {block.start}: a class stands beside `railroad`"
      let nodes ← inBlock (readDiagram body)
      let name ← inBlock (undo false block.term)
      diagrams := diagrams.push { origin := origin "railroad", name, anchor := block.termId, nodes }
    else
      let kind ←
        if block.kind == "pre" then pure "pre"
        else if block.classes == ["prod"] then pure (block.element ++ ".prod")
        else throw s!"{m.name}: offset {block.start}: a class stands beside `prod`"
      let found ← inBlock (readProductions (block.element == "xmp") body)
      for (production, ordinal) in found.zipIdx do
        productions := productions.push
          { origin := origin kind, ordinal := ordinal + 1, production }
  let mut tables : Array TableRow := #[]
  for anchor in anchors do
    let spans := w.tables.filter fun t => t.id == anchor || t.around.contains anchor
    if spans.isEmpty then throw s!"{m.name}: no table stands under the anchor `{anchor}`"
    for span in spans do
      if let some inner := opensInside bs "table" span.bodyStart span.bodyStop then
        throw (s!"{m.name}: offset {span.start}: a table opens inside the table under " ++
          s!"`{anchor}`, at offset {inner}")
      let table ← (readTable (textAt bs span.bodyStart span.bodyStop)).mapError
        (s!"{m.name}: offset {span.start}: the table under `{anchor}`: " ++ ·)
      let origin : Origin :=
        { module := m.name, kind := "table", start := span.start, stop := span.stop,
          digest := digestOf span.start span.stop, within := span.within }
      tables := tables.push { origin, anchor, table }
  let count (kind : String) : String × Nat := (kind, (w.blocks.filter (·.kind == kind)).size)
  return {
    module := m, title, size := bs.size
    blocks := (blockClasses ++ ["pre"]).map count ++ [("table", tables.size)]
    passed
    properties := properties.toList, descriptors := descriptors.toList
    productions := productions.toList, diagrams := diagrams.toList, tables := tables.toList }

/-- Every row of one module, with the tables that `wantedTables` lists for it. -/
def extract (m : Module) (bs : ByteArray) : Except String Extract :=
  extractWith ((wantedTables.filter (·.1 == m.name)).map (·.2)) m bs

end Gates.CssBlocks
