/-!
# Gates.Xml

A total reader for the XML subset that the sealed svgwg definitions use (slice S2 of
`docs/SVG-PACKAGE-PLAN.md`): elements, attributes in either quote, comments, character data
and the five named character references. It reads no document type, no processing
instruction, no CDATA section and no numeric reference: it refuses each with the offset where
it stands, so a later pin that uses one fails closed.

Three choices keep its answers exact:

- It reads ASCII only, and refuses any other character at its offset. A character offset is
  then a byte offset, so an element's offsets name its exact bytes and no caller checks.
- A name opens with a letter, `_` or `:`, the ASCII part of XML's `NameStartChar`.
- An attribute value is normalised as XML 1.0 section 3.3.3 says: each white-space character
  becomes a space. Character data is kept as written.

Totality: every loop is structural on a list or on fuel. `read` hands out one unit of fuel for
each character and one more, and each recursive call consumes a character first. So the
branches that report "ran out of fuel" are dead: they are there for the structural check.
This module reads no file.
-/

namespace Gates.Xml

/-- A node of a read document. Comments are dropped. An element keeps the offset of its first
character and of the character after its last. -/
inductive Node where
  | element (name : String) (attrs : List (String × String)) (children : List Node)
      (start stop : Nat)
  | text (content : String)
  deriving Inhabited

namespace Node

/-- The element's name; `none` for character data. -/
def name? : Node → Option String
  | .element name _ _ _ _ => some name
  | .text _ => none

/-- The value of an attribute of an element, when the element carries it. -/
def attr? (key : String) : Node → Option String
  | .element _ attrs _ _ _ => (attrs.find? (·.1 == key)).map (·.2)
  | .text _ => none

/-- The value of an attribute, or the empty string. -/
def attr (key : String) (node : Node) : String := (node.attr? key).getD ""

/-- The names of an element's attributes, in the order written. -/
def attrNames : Node → List String
  | .element _ attrs _ _ _ => attrs.map (·.1)
  | .text _ => []

/-- The children of an element. -/
def children : Node → List Node
  | .element _ _ children _ _ => children
  | .text _ => []

/-- The child elements whose name is `name`, in order. -/
def childrenNamed (name : String) (node : Node) : List Node :=
  node.children.filter (·.name? == some name)

/-- The offsets of an element: its first character, and the character after its last.
Character data has none. -/
def span? : Node → Option (Nat × Nat)
  | .element _ _ _ start stop => some (start, stop)
  | .text _ => none

mutual

/-- The character data under a node, in order, with markup removed. -/
def textContent : Node → String
  | .element _ _ children _ _ => textContentList children
  | .text content => content

/-- The character data under each node of a list, joined. -/
def textContentList : List Node → String
  | [] => ""
  | node :: rest => textContent node ++ textContentList rest

end

end Node

/-- A position in the input: what is left to read, and how much was read. -/
structure Cursor where
  rest : List Char
  pos : Nat

def isSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- The first character of a name: a letter, `_` or `:`. -/
def isNameStart (c : Char) : Bool := c.isAlpha || c == '_' || c == ':'

/-- A later character of a name: a first character, a digit, `-` or `.`. -/
def isNameChar (c : Char) : Bool := isNameStart c || c.isDigit || c == '-' || c == '.'

namespace Cursor

/-- Read the longest run of characters that satisfy `p`. -/
def take (p : Char → Bool) (c : Cursor) : String × Cursor :=
  let (taken, rest) := c.rest.span p
  (String.ofList taken, { rest, pos := c.pos + taken.length })

def skipSpace (c : Cursor) : Cursor := (c.take isSpace).2

/-- Read a name. The answer is empty when the input does not open with a name's first
character. -/
def takeName (c : Cursor) : String × Cursor :=
  match c.rest with
  | first :: _ => if isNameStart first then c.take isNameChar else ("", c)
  | [] => ("", c)

/-- The cursor after `literal`, when the input continues with it. -/
def expect? (literal : String) (c : Cursor) : Option Cursor :=
  let chars := literal.toList
  if chars.isPrefixOf c.rest then
    some { rest := c.rest.drop chars.length, pos := c.pos + chars.length }
  else none

def startsWith (literal : String) (c : Cursor) : Bool := literal.toList.isPrefixOf c.rest

end Cursor

/-- A refusal: the offset, then what the reader does not accept there. -/
def refuse {α : Type} (c : Cursor) (why : String) : Except String α :=
  .error s!"offset {c.pos}: {why}"

/-- The five named character references, each as the characters after its `&`. -/
def namedReferences : List (List Char × Char) :=
  [("lt;".toList, '<'), ("gt;".toList, '>'), ("amp;".toList, '&'), ("quot;".toList, '"'),
   ("apos;".toList, '\'')]

/-- Replace each named character reference of a run of text. An `&` that opens none of the
five is an error. The loop runs on fuel, because the tail after a reference is a `drop`. -/
def decodeReferences (chars : List Char) : Except String (List Char) :=
  go chars (chars.length + 1)
where
  go : List Char → Nat → Except String (List Char)
    | [], _ => .ok []
    | _ :: _, 0 => .error "internal: the reference decoder ran out of fuel"
    | '&' :: rest, fuel + 1 =>
      match namedReferences.find? (fun entry => entry.1.isPrefixOf rest) with
      | some (spelling, char) => (go (rest.drop spelling.length) fuel).map (char :: ·)
      | none => .error "a character reference that is not one of lt, gt, amp, quot, apos"
    | c :: rest, fuel + 1 => (go rest fuel).map (c :: ·)

/-- The cursor after the comment that opens at `c`, which stands at `<!--`. -/
def skipComment (c : Cursor) : Except String Cursor :=
  match c.expect? "<!--" with
  | none => refuse c "internal: not a comment"
  | some body => go body.rest body.pos
where
  go : List Char → Nat → Except String Cursor
    | '-' :: '-' :: '>' :: rest, pos => .ok { rest, pos := pos + 3 }
    | _ :: rest, pos => go rest (pos + 1)
    | [], pos => .error s!"offset {pos}: a comment that does not end"

/-- One attribute value, which opens at a quote. A `<` inside it is refused. Each white-space
character of the value becomes a space, then the references are decoded. -/
def readValue (c : Cursor) : Except String (String × Cursor) :=
  match c.rest with
  | quote :: rest =>
    if quote == '\'' || quote == '"' then
      let (raw, after) := rest.span (· != quote)
      match after with
      | [] => refuse c "an attribute value that does not end"
      | _ :: tail =>
        if raw.contains '<' then refuse c "`<` in an attribute value" else
        match decodeReferences (raw.map fun char => if isSpace char then ' ' else char) with
        | .ok value => .ok (String.ofList value, { rest := tail, pos := c.pos + raw.length + 2 })
        | .error e => refuse c e
    else refuse c "an attribute value without a quote"
  | [] => refuse c "the input ends where an attribute value is expected"

/-- The attributes of a start tag, up to its `>` or `/>`. A repeated name is refused. -/
def readAttrs : Nat → Cursor → List (String × String) → Except String (List (String × String) × Cursor)
  | 0, c, _ => refuse c "internal: the attribute reader ran out of fuel"
  | fuel + 1, c, acc =>
    let c := c.skipSpace
    if c.startsWith ">" || c.startsWith "/>" then .ok (acc.reverse, c) else
    if c.rest.isEmpty then refuse c "the input ends inside a start tag" else
    let (name, afterName) := c.takeName
    if name.isEmpty then refuse c "an attribute name is expected" else
    if acc.any (·.1 == name) then refuse c s!"the attribute `{name}` is given twice" else
    match afterName.skipSpace.expect? "=" with
    | none => refuse afterName s!"`=` is expected after the attribute name `{name}`"
    | some afterEquals =>
      match readValue afterEquals.skipSpace with
      | .ok (value, afterValue) => readAttrs fuel afterValue ((name, value) :: acc)
      | .error e => .error e

mutual

/-- One element, which opens at `<`. -/
def readElement : Nat → Cursor → Except String (Node × Cursor)
  | 0, c => refuse c "internal: the element reader ran out of fuel"
  | fuel + 1, c =>
    match c.expect? "<" with
    | none => refuse c "an element is expected"
    | some afterOpen =>
      let (name, afterName) := afterOpen.takeName
      if name.isEmpty then refuse afterOpen "an element name is expected" else
      match readAttrs (afterName.rest.length + 1) afterName [] with
      | .error e => .error e
      | .ok (attrs, afterAttrs) =>
        match afterAttrs.expect? "/>" with
        | some done => .ok (.element name attrs [] c.pos done.pos, done)
        | none =>
          match afterAttrs.expect? ">" with
          | none => refuse afterAttrs "`>` or `/>` is expected"
          | some inside =>
            match readContent fuel inside [] with
            | .error e => .error e
            | .ok (children, afterContent) =>
              match afterContent.expect? ("</" ++ name) with
              | none => refuse afterContent s!"the end tag `</{name}>` is expected"
              | some afterEnd =>
                match afterEnd.skipSpace.expect? ">" with
                | none => refuse afterEnd s!"`>` is expected in the end tag of `{name}`"
                | some done => .ok (.element name attrs children c.pos done.pos, done)

/-- The content of an element, up to an end tag or the end of the input. -/
def readContent : Nat → Cursor → List Node → Except String (List Node × Cursor)
  | 0, c, _ => refuse c "internal: the content reader ran out of fuel"
  | fuel + 1, c, acc =>
    if c.rest.isEmpty || c.startsWith "</" then .ok (acc.reverse, c)
    else if c.startsWith "<!--" then
      match skipComment c with
      | .ok after => readContent fuel after acc
      | .error e => .error e
    else if c.startsWith "<![CDATA[" then refuse c "a CDATA section"
    else if c.startsWith "<!" then refuse c "a declaration"
    else if c.startsWith "<?" then refuse c "a processing instruction"
    else if c.startsWith "<" then
      match readElement fuel c with
      | .ok (node, after) => readContent fuel after (node :: acc)
      | .error e => .error e
    else
      let (raw, rest) := c.rest.span (· != '<')
      match decodeReferences raw with
      | .ok chars =>
        readContent fuel { rest, pos := c.pos + raw.length } (.text (String.ofList chars) :: acc)
      | .error e => refuse c e

end

/-- Skip the white space and the comments between markup at the top level. -/
def skipMisc : Nat → Cursor → Except String Cursor
  | 0, c => refuse c "internal: the prolog reader ran out of fuel"
  | fuel + 1, c =>
    let c := c.skipSpace
    if c.startsWith "<!--" then
      match skipComment c with
      | .ok after => skipMisc fuel after
      | .error e => .error e
    else .ok c

/-- The offset of the first character outside ASCII, when the text holds one. -/
def firstNonAscii? (chars : List Char) : Option Nat :=
  chars.findIdx? fun char => char.toNat ≥ 128

/-- Read a document: comments, one root element, comments. A character outside ASCII is
refused first, so every offset of the answer is a byte offset. -/
def read (text : String) : Except String Node :=
  let chars := text.toList
  let fuel := chars.length + 1
  match firstNonAscii? chars with
  | some offset => .error s!"offset {offset}: a character outside ASCII"
  | none =>
    match skipMisc fuel { rest := chars, pos := 0 } with
    | .error e => .error e
    | .ok start =>
      if start.startsWith "<?" then refuse start "a processing instruction"
      else if start.startsWith "<!" then refuse start "a declaration"
      else
        match readElement fuel start with
        | .error e => .error e
        | .ok (root, after) =>
          match skipMisc fuel after with
          | .error e => .error e
          | .ok finish =>
            if finish.rest.isEmpty then .ok root
            else refuse finish "content after the root element"

end Gates.Xml
