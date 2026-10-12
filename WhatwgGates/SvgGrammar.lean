import Std.Data.HashMap
import Std.Data.HashSet
import WhatwgGates.Common
import WhatwgGates.Sha256
import WhatwgGates.SvgDefinitions
import Whatwg.Svg.Value.Path

/-!
# Gates.SvgGrammar

The gate of debt D95: it compares a transcribed grammar with the productions of its sealed
chapter. The chapter is `master/paths.html` of the svgwg pin. Under the heading `PathDataBNF`
it states the grammar of path data as EBNF, in one block. `Whatwg/Svg/Value/Path.lean`
transcribes that grammar by hand as a description, a value of `Syn`. Node V3a ties the reader
to the erased expression of the description. This gate ties that expression to the chapter.

What it decides: the sealed production `svg_path` and the expression
`Whatwg.Svg.Value.Path.syn.erase` have the same language. It decides the same for each
production that has a named description in the library, so that a difference shows where it
is made.

How:

1. `findBlock` finds the block. The heading mark and the block mark each stand once in the
   chapter, the block follows the heading, and no other heading opens between them. Otherwise
   the gate refuses.
2. `readGrammar` reads the notation into first-order data, `Ebnf`: `::=`, `|`, parentheses,
   `*`, `+`, `?`, a string literal in double quotes, a hexadecimal character such as `#x20`,
   and a production name. It refuses any other construct with its offset.
3. `production` turns a production into a `Regex`. A name is replaced by its production. A
   production of the shape `x ::= a | (b x)` becomes `b* a`, its least solution. Any other
   recursion is refused.
4. `explore` decides whether two expressions have one language. It walks the pairs of their
   Brzozowski derivatives, breadth first. An expression is kept up to similarity: `alt` is
   associative, commutative and idempotent, and units and zeros are removed. One character
   stands for each class of ASCII characters that the sets of the two expressions do not tell
   apart, and one more for the characters outside ASCII. A pair where one side takes the empty
   text and the other does not is a difference. The way to the first such pair is a shortest
   witness.
5. `accepts` is a second matcher. It follows `Regex.Matches` case by case and takes no
   derivative. Each witness is checked with it against both expressions as they were given.

Parts. The automaton of `svg_path` over characters is large: a run of digits may be one
number or several, in a sequence that repeats, and the walk reaches about 50,000 pairs. So the
rows are compared from the characters up. When a row has one language, its two expressions
become a part. In a later row a part is taken whole: it is one letter of the alphabet, and
the walk does not look inside it. Two expressions that have one language over letters keep
one language when each letter is replaced by a language, so the verdict holds for the
expressions as written (`derivative` states the law that the walk rests on). The verdict of
`svg_path` then rests on the verdicts of the rows below it, each made by the same walk. A
difference found with a part taken whole proves nothing, so that row is walked again over
characters alone. `--whole` adds the reference: `svg_path` and the description of a path, over
characters alone, with no part taken whole.

Controls run on every invocation. Each of six changes one sealed production, and the changed
`svg_path` must differ from the sealed one: first by a walk that takes parts whole, which
must not answer "one language", and then over characters alone, where the witness is found.
One more compares `svg_path` with the description of the value of `d`, which also takes
`none`, over characters alone. A procedure that always answers "equal" fails each of them.

What this gate does not claim. It is code that no theorem checks: a PASS is the verdict of
this procedure, not a proof. A difference is better founded than an equality, because the
second matcher confirms its witness. The gate compares bare expressions. It says nothing of
the reader's rule, which takes the longest match and refuses some texts of the expression
(`Whatwg/Svg/Value/Greedy.lean`). It reads no prose of the chapter. It reads one block of one
chapter: `points`, `viewBox` and `transform` have no gate here.

Exit codes: 0 when every comparison is equal and every control differs. 1 for a difference
or a control that does not differ. 2 when there is no verdict: an unknown argument, a missing
or changed chapter, a refused construct, or fuel that ran out.

Totality: every loop is a fold, is structural, or runs on fuel. Fuel that runs out is a
refusal, never an answer.
-/

namespace Gates.SvgGrammar

open Whatwg.Svg.Value (CharSet Regex)

/-! ## The sealed block -/

/-- The sealed chapter: its path under the pin directory, and its SHA-256. -/
def chapter : Gates.SvgDefinitions.Input :=
  { relative := "master/paths.html"
    digest := "cd818a1b7c5f82a1ab1709eb4020170e27ff5f01822f0e3e791663c42e109fbd" }

/-- The chapter's path under the repository root. -/
def chapterPath : String := Gates.SvgDefinitions.pinDirectory ++ "/" ++ chapter.relative

/-- The mark of the heading that the grammar stands under. -/
def headingMark : String := "id=\"PathDataBNF\""

/-- The opening of the block that holds the grammar. -/
def blockMark : String := "<pre class='grammar"

/-- The end of that block. -/
def blockEnd : String := "</pre>"

/-- The production the gate is about. -/
def startSymbol : String := "svg_path"

/-- Why the gate refuses the sealed text: the offset of the construct, in characters from the
start of the chapter, and the reason. -/
structure Refusal where
  offset : Nat
  reason : String

/-- A text as a message prints it: in double quotes, with an escape for each character that
is not a visible ASCII character or a space. -/
def quote (text : List Char) : String :=
  let escape (c : Char) : String :=
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n" else if c == '\t' then "\\t" else if c == '\r' then "\\r"
    else if 0x20 ≤ c.toNat && c.toNat < 0x7f then c.toString
    else
      let digits := String.ofList (Nat.toDigits 16 c.toNat)
      if c.toNat < 0x10 then "\\x0" ++ digits
      else if c.toNat < 0x100 then "\\x" ++ digits
      else "\\u{" ++ digits ++ "}"
  "\"" ++ String.join (text.map escape) ++ "\""

/-- An offset as a refusal prints it, with its line and column in the chapter. -/
def place (text : List Char) (offset : Nat) : String :=
  let before := text.take offset
  let line := (before.filter (· == '\n')).length + 1
  let column := (before.reverse.takeWhile (· != '\n')).length + 1
  s!"offset {offset} (line {line}, column {column})"

/-- The offsets at which `needle` stands in a text whose first character is at `offset`. -/
def occurrences (needle : List Char) : List Char → Nat → Array Nat → Array Nat
  | [], _, found => found
  | c :: rest, offset, found =>
    occurrences needle rest (offset + 1)
      (if needle.isPrefixOf (c :: rest) then found.push offset else found)

/-- The grammar block of the chapter: its characters, each with its offset. The heading mark
and the block mark each stand once, the block follows the heading, and no other heading opens
between the two. -/
def findBlock (text : List Char) : Except String (List (Char × Nat)) := do
  let headings := (occurrences headingMark.toList text 0 #[]).toList
  let blocks := (occurrences blockMark.toList text 0 #[]).toList
  let (heading, block) ←
    match headings, blocks with
    | [heading], [block] => pure (heading, block)
    | _, _ =>
      throw (s!"the heading mark `{headingMark}` stands {headings.length} time(s) and the " ++
        s!"block mark `{blockMark}` stands {blocks.length} time(s); each must stand once")
  unless heading < block do
    throw s!"the block mark `{blockMark}` stands before the heading mark `{headingMark}`"
  let between := (text.drop heading).take (block - heading)
  let levels := ["<h1", "<h2", "<h3", "<h4", "<h5", "<h6"]
  unless levels.all fun level => (occurrences level.toList between 0 #[]).isEmpty do
    throw s!"another heading opens between `{headingMark}` and `{blockMark}`"
  let opened := text.drop block
  let tag := opened.takeWhile (· != '>')
  let start := block + tag.length + 1
  let body := opened.drop (tag.length + 1)
  match (occurrences blockEnd.toList body 0 #[]).toList with
  | [] => throw s!"the block that opens with `{blockMark}` has no `{blockEnd}`"
  | stop :: _ => pure ((body.take stop).zip (List.range' start stop))

/-- The block's characters with each character reference decoded. A decoded character keeps
the offset of its `&`. A `<` is markup, and the block holds none. The block of this pin holds
no reference either; the five named ones are read so that the same text, written with
`&quot;` or `&lt;`, is the same grammar. -/
def decode : Nat → List (Char × Nat) → Array (Char × Nat) → Except Refusal (List (Char × Nat))
  | _, [], done => pure done.toList
  | 0, (_, offset) :: _, _ => throw ⟨offset, "internal: the decoder ran out of fuel"⟩
  | fuel + 1, (c, offset) :: rest, done =>
    if c == '<' then throw ⟨offset, "markup inside the grammar block"⟩
    else if c == '&' then
      let ahead := (rest.take 8).map (·.1)
      match Gates.Xml.namedReferences.find? fun entry => entry.1.isPrefixOf ahead with
      | some (spelling, char) => decode fuel (rest.drop spelling.length) (done.push (char, offset))
      | none =>
        throw ⟨offset, "a character reference that is not one of lt, gt, amp, quot, apos"⟩
    else decode fuel rest (done.push (c, offset))

/-! ## The notation -/

/-- An expression of the notation, as first-order data. A literal holds its characters, and
a hexadecimal character is a literal of one. A name keeps the offset it stands at. A sequence
and a choice of several items nest to the left. A parenthesis is not kept. -/
inductive Ebnf where
  | ref (name : String) (offset : Nat)
  | lit (chars : List Char)
  | seq (a b : Ebnf)
  | alt (a b : Ebnf)
  | star (a : Ebnf)
  | plus (a : Ebnf)
  | opt (a : Ebnf)
  deriving Inhabited

/-- One production: its name, the offset of the name, and its expression. -/
structure Production where
  name : String
  offset : Nat
  body : Ebnf

/-- One token of the notation. A hexadecimal character is a literal of one character. -/
inductive Token where
  | name (text : String)
  | define
  | bar
  | lparen
  | rparen
  | star
  | plus
  | question
  | literal (chars : List Char)

/-- White space between two tokens. -/
def isBlank (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- The first character of a production name: a letter or `_`. -/
def isNameStart (c : Char) : Bool := c.isAlpha || c == '_'

/-- A later character of a production name: a letter, a digit, `_` or `-`. -/
def isNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-'

/-- The value of a hexadecimal digit, if the character is one. -/
def hexDigit? (c : Char) : Option Nat :=
  let code := c.toNat
  if 48 ≤ code && code ≤ 57 then some (code - 48)
  else if 97 ≤ code && code ≤ 102 then some (code - 87)
  else if 65 ≤ code && code ≤ 70 then some (code - 55)
  else none

/-- Why a character of a literal is refused, if it is: the sets of the library are sets of
ASCII characters, so no expression of the library takes another character. -/
def outsideAscii : String :=
  "a character outside ASCII, which no set of the library holds"

/-- The tokens of the block, each with its offset. Each round reads one token or one blank,
so the length of the block bounds the rounds. -/
def lex : Nat → List (Char × Nat) → Array (Token × Nat) → Except Refusal (Array (Token × Nat))
  | _, [], tokens => pure tokens
  | 0, (_, offset) :: _, _ => throw ⟨offset, "internal: the tokenizer ran out of fuel"⟩
  | fuel + 1, (c, offset) :: rest, tokens =>
    if isBlank c then lex fuel rest tokens
    else if c == '|' then lex fuel rest (tokens.push (.bar, offset))
    else if c == '(' then lex fuel rest (tokens.push (.lparen, offset))
    else if c == ')' then lex fuel rest (tokens.push (.rparen, offset))
    else if c == '*' then lex fuel rest (tokens.push (.star, offset))
    else if c == '+' then lex fuel rest (tokens.push (.plus, offset))
    else if c == '?' then lex fuel rest (tokens.push (.question, offset))
    else if c == ':' then
      match rest with
      | (':', _) :: ('=', _) :: after => lex fuel after (tokens.push (.define, offset))
      | _ => throw ⟨offset, "a `:` that does not open `::=`"⟩
    else if c == '"' then
      let body := rest.takeWhile fun entry => entry.1 != '"' && entry.1 != '\n'
      match rest.drop body.length with
      | ('"', _) :: after =>
        match body.find? fun entry => entry.1.toNat ≥ 128 with
        | some (_, spot) => throw ⟨spot, outsideAscii⟩
        | none => lex fuel after (tokens.push (.literal (body.map (·.1)), offset))
      | _ => throw ⟨offset, "a string literal that does not close on its line"⟩
    else if c == '#' then
      match rest with
      | ('x', _) :: more =>
        let digits := (more.takeWhile fun entry => (hexDigit? entry.1).isSome).map (·.1)
        let code := digits.foldl (fun value digit => 16 * value + (hexDigit? digit).getD 0) 0
        if digits.isEmpty then throw ⟨offset, "`#x` with no hexadecimal digit after it"⟩
        else if code ≥ 128 then throw ⟨offset, outsideAscii⟩
        else lex fuel (more.drop digits.length) (tokens.push (.literal [Char.ofNat code], offset))
      | _ => throw ⟨offset, "a `#` that does not open a hexadecimal character `#x`"⟩
    else if isNameStart c then
      let more := (rest.takeWhile fun entry => isNameChar entry.1).map (·.1)
      lex fuel (rest.drop more.length) (tokens.push (.name (String.ofList (c :: more)), offset))
    else throw ⟨offset, s!"the character {quote [c]} is outside the notation"⟩

/-- What the reader holds inside one parenthesis, or inside a production's expression: the
alternatives that are closed, the items of the open one, and the offset it opens at. Each list
has its latest entry first. -/
structure Frame where
  alternatives : List Ebnf := []
  items : List Ebnf := []
  offset : Nat

namespace Frame

/-- The items of the open alternative as one expression. An alternative with no item is
refused. -/
def sequence (frame : Frame) (offset : Nat) : Except Refusal Ebnf :=
  match frame.items.reverse with
  | [] => throw ⟨offset, "an alternative with nothing in it"⟩
  | first :: more => pure (more.foldl .seq first)

/-- The frame as one expression: the choice of its alternatives. -/
def close (frame : Frame) (offset : Nat) : Except Refusal Ebnf := do
  let last ← frame.sequence offset
  match frame.alternatives.reverse with
  | [] => pure last
  | first :: more => pure ((more ++ [last]).foldl .alt first)

/-- One more item. -/
def push (frame : Frame) (item : Ebnf) : Frame := { frame with items := item :: frame.items }

/-- The latest item under `*`, `+` or `?`. -/
def wrap (frame : Frame) (shape : Ebnf → Ebnf) (offset : Nat) : Except Refusal Frame :=
  match frame.items with
  | [] => throw ⟨offset, "a `*`, `+` or `?` with nothing before it"⟩
  | last :: before => pure { frame with items := shape last :: before }

end Frame

/-- The state of the reader: the productions read, the name and offset of the one being read,
the open frames with the innermost first, and whether the latest token is a name. A name
before `::=` is read as an item first, and taken back when the `::=` comes. -/
structure Reader where
  finished : Array Production := #[]
  current : Option (String × Nat) := none
  frames : List Frame
  bare : Bool := false

namespace Reader

/-- Read one token. -/
def step (reader : Reader) (token : Token) (offset : Nat) : Except Refusal Reader :=
  match token, reader.frames with
  | _, [] => throw ⟨offset, "internal: the reader holds no frame"⟩
  | .name text, frame :: below =>
    pure { reader with frames := frame.push (.ref text offset) :: below, bare := true }
  | .literal chars, frame :: below =>
    pure { reader with frames := frame.push (.lit chars) :: below, bare := false }
  | .lparen, frames => pure { reader with frames := { offset } :: frames, bare := false }
  | .rparen, frame :: outer :: below => do
    let inner ← frame.close offset
    pure { reader with frames := outer.push inner :: below, bare := false }
  | .rparen, [_] => throw ⟨offset, "a `)` with no `(` before it"⟩
  | .bar, frame :: below => do
    let one ← frame.sequence offset
    let next := { frame with alternatives := one :: frame.alternatives, items := [] }
    pure { reader with frames := next :: below, bare := false }
  | .star, frame :: below => do
    pure { reader with frames := (← frame.wrap .star offset) :: below, bare := false }
  | .plus, frame :: below => do
    pure { reader with frames := (← frame.wrap .plus offset) :: below, bare := false }
  | .question, frame :: below => do
    pure { reader with frames := (← frame.wrap .opt offset) :: below, bare := false }
  | .define, [frame] =>
    match reader.bare, frame.items with
    | true, .ref name spot :: before => do
      let finished ←
        match reader.current with
        | none =>
          if before.isEmpty && frame.alternatives.isEmpty then pure reader.finished
          else throw ⟨frame.offset, "text before the first production"⟩
        | some (current, opened) => do
          let body ← Frame.close { frame with items := before } spot
          pure (reader.finished.push { name := current, offset := opened, body })
      if finished.any (·.name == name) then
        throw ⟨spot, s!"the production `{name}` is defined twice"⟩
      pure { finished, current := some (name, spot), frames := [{ offset := spot }] }
    | _, _ => throw ⟨offset, "a `::=` with no production name before it"⟩
  | .define, frame :: _ :: _ =>
    throw ⟨offset, s!"a `::=` inside the parenthesis that opens at offset {frame.offset}"⟩

/-- The productions, once the block ends. -/
def finish (reader : Reader) (offset : Nat) : Except Refusal (List Production) :=
  match reader.current, reader.frames with
  | none, _ => throw ⟨offset, "the block holds no production"⟩
  | some (name, opened), [frame] => do
    let body ← frame.close offset
    pure (reader.finished.push { name, offset := opened, body }).toList
  | some _, frame :: _ :: _ => throw ⟨frame.offset, "a `(` that does not close"⟩
  | some _, [] => throw ⟨offset, "internal: the reader holds no frame"⟩

end Reader

/-- The productions of a block, in order. -/
def readGrammar (block : List (Char × Nat)) : Except Refusal (List Production) := do
  let start := (block.head?.map (·.2)).getD 0
  let stop := start + block.length
  let decoded ← decode (block.length + 1) block #[]
  let tokens ← lex (decoded.length + 1) decoded #[]
  let mut reader : Reader := { frames := [{ offset := start }] }
  for (token, offset) in tokens do
    reader ← reader.step token offset
  reader.finish stop

namespace Ebnf

/-- The expression names the production. -/
def mentions (name : String) : Ebnf → Bool
  | .ref other _ => other == name
  | .lit _ => false
  | .seq a b | .alt a b => a.mentions name || b.mentions name
  | .star a | .plus a | .opt a => a.mentions name

/-- The names the expression holds, in order, each with its offset. -/
def references : Ebnf → List (String × Nat)
  | .ref name offset => [(name, offset)]
  | .lit _ => []
  | .seq a b | .alt a b => a.references ++ b.references
  | .star a | .plus a | .opt a => a.references

/-- The names the expression holds, in order. -/
def names (e : Ebnf) : List String := e.references.map (·.1)

/-- The alternatives of the expression, in order. A parenthesis is not kept, so the
alternatives of a choice inside a choice are the outer one's own. -/
def alternatives : Ebnf → List Ebnf
  | .alt a b => a.alternatives ++ b.alternatives
  | other => [other]

/-- Rewrite from the top: where `rule` answers, take its answer and go no deeper. The number
is that of the places rewritten. -/
def rewrite (rule : Ebnf → Option Ebnf) (e : Ebnf) : Ebnf × Nat :=
  match rule e with
  | some changed => (changed, 1)
  | none =>
    match e with
    | .seq a b =>
      let (a', n) := a.rewrite rule
      let (b', m) := b.rewrite rule
      (.seq a' b', n + m)
    | .alt a b =>
      let (a', n) := a.rewrite rule
      let (b', m) := b.rewrite rule
      (.alt a' b', n + m)
    | .star a => let (a', n) := a.rewrite rule; (.star a', n)
    | .plus a => let (a', n) := a.rewrite rule; (.plus a', n)
    | .opt a => let (a', n) := a.rewrite rule; (.opt a', n)
    | leaf => (leaf, 0)

/-- The expression is the name. -/
def isRef (name : String) : Ebnf → Bool
  | .ref other _ => other == name
  | _ => false

/-- The expression is the literal. -/
def isLit (chars : List Char) : Ebnf → Bool
  | .lit other => other == chars
  | _ => false

end Ebnf

/-! ## From the notation to an expression -/

/-- A literal as an expression: its characters in order. -/
def literal : List Char → Regex
  | [] => .eps
  | [c] => .set (.single c)
  | c :: rest => .seq (.set (.single c)) (literal rest)

/-- An expression of the notation as a regular expression. `resolve` answers a name.
`a+` is `a a*`, and `a?` is `a` or the empty text. -/
def expression (resolve : String → Nat → Except Refusal Regex) : Ebnf → Except Refusal Regex
  | .ref name offset => resolve name offset
  | .lit chars => pure (literal chars)
  | .seq a b => do pure (.seq (← expression resolve a) (← expression resolve b))
  | .alt a b => do pure (.alt (← expression resolve a) (← expression resolve b))
  | .star a => do pure (.star (← expression resolve a))
  | .plus a => do
    let one ← expression resolve a
    pure (.seq one (.star one))
  | .opt a => do pure (.alt (← expression resolve a) .eps)

/-- Several expressions as one choice. An empty list has none. -/
def choice : List Regex → Option Regex
  | [] => none
  | first :: more => some (more.foldl .alt first)

/-- The shape of recursion that `production` reads. -/
def recursionShape : String := "`x ::= a | (b x)`, where `a` and `b` do not name `x`"

/-- The production `name` as a regular expression. `opened` holds the productions being
replaced, so a name among them is a recursion.

A production that does not name itself is its expression, with each name replaced. A
production that names itself must have the shape `x ::= a | (b x)`: each alternative is free
of `x`, or is a sequence that ends in `x` and is free of it before. Its language is the least
solution of `x = b x | a`, which is `b* a`. With several alternatives of each kind, `b` and
`a` are their choices. `fuel` bounds the depth of replacement, which the number of
productions bounds. -/
def production (productions : List Production) :
    Nat → List String → String → Nat → Except Refusal Regex
  | 0, _, _, offset => throw ⟨offset, "internal: the conversion ran out of fuel"⟩
  | fuel + 1, opened, name, offset => do
    if opened.contains name then
      throw ⟨offset, s!"the production `{name}` is recursive outside the shape {recursionShape}"⟩
    let some found := productions.find? (·.name == name)
      | throw ⟨offset, s!"the name `{name}` has no production"⟩
    let resolve := production productions fuel (name :: opened)
    let choices := found.body.alternatives
    let loops := choices.filter fun one => one.mentions name
    if loops.isEmpty then
      expression resolve found.body
    else
      let outside : Refusal :=
        ⟨found.offset, s!"the production `{name}` names itself outside the shape {recursionShape}"⟩
      let leads ← loops.mapM fun one =>
        match one with
        | .seq lead (.ref last _) =>
          if last == name && !lead.mentions name then expression resolve lead else throw outside
        | _ => throw outside
      let bases ← (choices.filter fun one => !one.mentions name).mapM (expression resolve)
      match choice leads, choice bases with
      | some lead, some base => pure (.seq (.star lead) base)
      | _, _ => throw outside

/-- The names that the names of `todo` reach, added to `seen`. Each round takes one name, so
the number of names written in the block bounds the rounds. -/
def reach (productions : List Production) : Nat → List String → List String →
    Option (List String)
  | _, [], seen => some seen
  | 0, _ :: _, _ => none
  | fuel + 1, name :: todo, seen =>
    if seen.contains name then reach productions fuel todo seen
    else
      let more := ((productions.find? (·.name == name)).map (·.body.names)).getD []
      reach productions fuel (more ++ todo) (name :: seen)

/-! ## A second matcher -/

/-- A repetition, by `Regex.Matches.starNil` and `starCons`: the rest of the text, or one
more copy that is not empty and then the repetition again. A copy that is empty adds nothing
to the language, so the length of the text bounds the copies. `copy` matches one. -/
def acceptsStar (copy : List Char → (List Char → Bool) → Bool) :
    Nat → List Char → (List Char → Bool) → Bool
  | 0, text, rest => rest text
  | fuel + 1, text, rest =>
    rest text || copy text fun left => left.length < text.length && acceptsStar copy fuel left rest

/-- The expression matches a head of the text, and `rest` holds of what is left. One case for
each constructor of `Regex.Matches`. -/
def acceptsHead : Regex → List Char → (List Char → Bool) → Bool
  | .eps, text, rest => rest text
  | .set _, [], _ => false
  | .set s, c :: tail, rest => s.mem c && rest tail
  | .seq a b, text, rest => acceptsHead a text fun left => acceptsHead b left rest
  | .alt a b, text, rest => acceptsHead a text rest || acceptsHead b text rest
  | .star a, text, rest => acceptsStar (acceptsHead a) text.length text rest

/-- The expression matches the whole text. This matcher takes no derivative, so it is a
second opinion on a witness. It tries every way to split the text, so it is for a short
one. -/
def accepts (r : Regex) (text : List Char) : Bool := acceptsHead r text List.isEmpty

/-! ## Expressions up to similarity -/

/-- A choice of two sets as the set of their union: the language is the same, and fewer sets
tell fewer characters apart. -/
def fuse : Regex → Regex
  | .eps => .eps
  | .set s => .set s
  | .seq a b => .seq (fuse a) (fuse b)
  | .alt a b =>
    match fuse a, fuse b with
    | .set x, .set y => .set (x.union y)
    | left, right => .alt left right
  | .star a => .star (fuse a)

/-- The sets of an expression, each once, added to `found`. -/
def setsOf : Regex → List Nat → List Nat
  | .eps, found => found
  | .set s, found => if found.contains s.bits then found else s.bits :: found
  | .seq a b, found | .alt a b, found => setsOf b (setsOf a found)
  | .star a, found => setsOf a found

/-- How well a character stands for its class in a witness: a visible character before a
space, and a space before a control character. -/
def rank (code : Nat) : Nat :=
  if 0x21 ≤ code && code ≤ 0x7e then 0 else if code == 0x20 then 1 else 2

/-- One character for each class of the alphabet. Two ASCII characters are of one class when
each set holds both or neither. The derivative of an expression by a character depends on the
character through its sets alone, so one character of a class stands for all of them. No set
holds a character outside ASCII (`CharSet.mem`), so those are one class, and `U+0080` stands
for it. -/
def classes (sets : List Nat) : List Char :=
  let found := (List.range 128).foldl (init := ([] : List (Nat × Nat))) fun found code =>
    let signature := sets.foldl (fun mask bits => 2 * mask + (bits.testBit code).toNat) 0
    if found.any (·.1 == signature) then
      found.map fun entry =>
        if entry.1 == signature && rank code < rank entry.2 then (signature, code) else entry
    else found ++ [(signature, code)]
  found.map (fun entry => Char.ofNat entry.2) ++ [Char.ofNat 0x80]

/-- An expression with its children named by number: the similar forms of one expression
are one node. `zero` is the empty language. A set holds a member. Neither side of a `seq` is
`zero` or `eps`. The items of an `alt` are sorted, are two or more, and none is `zero` or an
`alt`. -/
inductive Node where
  | zero
  | eps
  | set (bits : Nat)
  | seq (a b : Nat)
  | alt (items : List Nat)
  | star (a : Nat)
  deriving BEq, Hashable, Inhabited

/-- A letter of a comparison: a character, or a part taken whole. -/
inductive Letter where
  | char (c : Char)
  | part (number : Nat)
  deriving BEq, Inhabited

/-- A number for each letter: a character's code point, or a part's number after the last
code point. -/
def Letter.code : Letter → Nat
  | .char c => c.toNat
  | .part number => 0x110000 + number

/-- The nodes made so far. A node's number is its index, and each child of a node has a
smaller number. `nullable` says whether a node takes the empty text. `derivatives` keeps each
derivative taken by a character with no part closed: it is the node's own, and holds for the
whole run.

`parts` gives a node its part number: two nodes with one number were found to have one
language. `closed` holds the parts that the comparison at hand takes whole.
`closedDerivatives` keeps the derivatives taken with a part closed, and `met` the parts that
were met as letters; both hold for that comparison alone. -/
structure Table where
  nodes : Array Node
  nullable : Array Bool
  ids : Std.HashMap Node Nat
  derivatives : Std.HashMap (Nat × Nat) Nat
  parts : Std.HashMap Nat Nat
  partCount : Nat
  closed : Std.HashMap Nat Nat
  closedDerivatives : Std.HashMap (Nat × Nat) Nat
  met : Std.HashSet Nat

/-- The number of `zero`. -/
def zeroId : Nat := 0

/-- The number of `eps`. -/
def epsId : Nat := 1

namespace Table

/-- The table with `zero` and `eps`, and no part. -/
def initial : Table :=
  { nodes := #[.zero, .eps]
    nullable := #[false, true]
    ids := (({} : Std.HashMap Node Nat).insert .zero zeroId).insert .eps epsId
    derivatives := {}
    parts := {}
    partCount := 0
    closed := {}
    closedDerivatives := {}
    met := {} }

/-- The derivative kept for a node and a letter, if one is. -/
def known (table : Table) (key : Nat × Nat) : Option Nat :=
  if table.closed.isEmpty then table.derivatives[key]? else table.closedDerivatives[key]?

/-- Keep a derivative: for the run with no part closed, and for the comparison at hand
otherwise. -/
def keep (table : Table) (key : Nat × Nat) (result : Nat) : Table :=
  if table.closed.isEmpty then
    { table with derivatives := table.derivatives.insert key result }
  else { table with closedDerivatives := table.closedDerivatives.insert key result }

end Table

/-- A computation over the table. An error is fuel that ran out, or the two matchers at
odds. -/
abbrev Run := StateT Table (Except String)

/-- The node of a number. -/
def nodeOf (id : Nat) : Run Node := do
  return (← get).nodes.getD id .zero

/-- Whether a node takes the empty text. -/
def nullableOf (id : Nat) : Run Bool := do
  return (← get).nullable.getD id false

/-- The number of a node: the one it has, or the next free one. -/
def intern (node : Node) (nullable : Bool) : Run Nat :=
  modifyGet fun table =>
    match table.ids[node]? with
    | some id => (id, table)
    | none =>
      let id := table.nodes.size
      (id, { table with
        nodes := table.nodes.push node
        nullable := table.nullable.push nullable
        ids := table.ids.insert node id })

/-- `a` then `b`: `zero` if either is, and the other if one is `eps`. -/
def mkSeq (a b : Nat) : Run Nat := do
  if a == zeroId || b == zeroId then return zeroId
  if a == epsId then return b
  if b == epsId then return a
  intern (.seq a b) ((← nullableOf a) && (← nullableOf b))

/-- `a` repeated: the star of `zero`, of `eps` or of a star adds nothing. -/
def mkStar (a : Nat) : Run Nat := do
  if a == zeroId || a == epsId then return epsId
  match ← nodeOf a with
  | .star _ => return a
  | _ => intern (.star a) true

/-- Add a number to a sorted list with no repeat. -/
def insertSorted (id : Nat) : List Nat → List Nat
  | [] => [id]
  | first :: rest =>
    if id < first then id :: first :: rest
    else if id == first then first :: rest
    else first :: insertSorted id rest

/-- The choice of some nodes, up to similarity: a choice inside is opened, `zero` is dropped,
and the rest is sorted with no repeat. No item left is `zero`, and one item left is itself. -/
def mkAlt (ids : List Nat) : Run Nat := do
  let mut flat : List Nat := []
  for id in ids do
    match ← nodeOf id with
    | .zero => pure ()
    | .alt items => flat := items.foldl (fun flat item => insertSorted item flat) flat
    | _ => flat := insertSorted id flat
  match flat with
  | [] => return zeroId
  | [one] => return one
  | _ => intern (.alt flat) (← flat.anyM nullableOf)

/-- The node of an expression. A set with no ASCII member is `zero`. -/
def internRegex : Regex → Run Nat
  | .eps => pure epsId
  | .set s =>
    let bits := s.bits % 2 ^ 128
    if bits == 0 then pure zeroId else intern (.set bits) false
  | .seq a b => do mkSeq (← internRegex a) (← internRegex b)
  | .alt a b => do mkAlt [← internRegex a, ← internRegex b]
  | .star a => do mkStar (← internRegex a)

/-- The Brzozowski derivative of a node by a letter. By a character `c` it is the node of
the texts `t` such that the node takes `c` followed by `t`. A closed part is not looked into:
its derivative by its own letter is the empty text, and by any other letter the empty
language. Each child of a node has a smaller number, so the node's number bounds the depth,
and `fuel` is that bound.

The law that the walk rests on. Write `L n` for the language of a node. Let a character
stand for its class, and the letter of a part for the texts of that part other than the empty
one. Then `L n` is the empty text, if `n` takes it, together with the texts `u ++ t` where `u`
is of a letter `x` and `t` is of `L (derivative x n)`. It holds for a closed part because the
nodes of one part have one language, and for every other node by its shape, because each
constructor keeps the language of what it builds. No letter holds the empty text. So if every
pair that a walk reaches agrees on the empty text, then, by induction on the length of a
text, the two nodes of each pair take the same texts. -/
def derivative (letter : Letter) : Nat → Nat → Run Nat
  | 0, _ => throw "internal: a derivative ran out of fuel"
  | fuel + 1, id => do
    if let some number := (← get).closed[id]? then
      modify fun table => { table with met := table.met.insert number }
      return if letter == .part number then epsId else zeroId
    let key := (id, letter.code)
    if let some known := (← get).known key then return known
    let result ←
      match ← nodeOf id with
      | .zero => pure zeroId
      | .eps => pure zeroId
      | .set bits =>
        match letter with
        | .char c => pure (if (CharSet.mk bits).mem c then epsId else zeroId)
        | .part _ => pure zeroId
      | .seq a b => do
        let first ← mkSeq (← derivative letter fuel a) b
        if ← nullableOf a then mkAlt [first, ← derivative letter fuel b] else pure first
      | .alt items => do mkAlt (← items.mapM (derivative letter fuel))
      | .star a => do mkSeq (← derivative letter fuel a) id
    modify fun table => table.keep key result
    return result

/-! ## The decision -/

/-- The answer to one comparison: whether the two languages are one, how many pairs of
derivatives were reached, and how many parts were met as letters. When the languages differ,
`witness` is a shortest text that one side takes and the other does not, and `byLeft` says
that the left side takes it. -/
structure Outcome where
  equal : Bool
  witness : List Char
  byLeft : Bool
  pairs : Nat
  met : Nat

/-- The text that leads to a pair: the characters on the way from the first pair. `steps`
holds, for each pair, the pair it was reached from and the letter taken. A pair is reached
from an earlier one, so its index bounds the way. A witness is asked for with no part closed,
so each letter on its way is a character. -/
def textTo (steps : Array (Nat × Letter)) : Nat → Nat → List Char → List Char
  | 0, _, text => text
  | fuel + 1, index, text =>
    if index == 0 then text
    else
      let step := steps.getD index (0, .char ' ')
      match step.2 with
      | .char c => textTo steps fuel step.1 (c :: text)
      | .part _ => textTo steps fuel step.1 text

/-- The most pairs of derivatives that one comparison may reach. -/
def pairFuel : Nat := 200000

/-- Walk the pairs of derivatives of two nodes, breadth first, by each letter of the
alphabet. With no part closed, two languages differ exactly when some text leads to a pair of
which one side takes the empty text and the other does not. Pairs are taken in the order they
are reached, so the first such pair has a shortest text. A pair of one node twice has one
language and is walked no further. The derivatives of an expression are finitely many up to
similarity, so the walk ends; `pairFuel` bounds it all the same. -/
def explore (alphabet : List Letter) (left right : Nat) : Run Outcome := do
  let mut pairs : Array (Nat × Nat) := #[(left, right)]
  let mut steps : Array (Nat × Letter) := #[(0, .char ' ')]
  let mut seen : Std.HashSet (Nat × Nat) := ({} : Std.HashSet (Nat × Nat)).insert (left, right)
  let mut head := 0
  for _ in [0:pairFuel] do
    if head ≥ pairs.size then
      let met := (← get).met.size
      return { equal := true, witness := [], byLeft := false, pairs := pairs.size, met }
    let (l, r) := pairs.getD head (zeroId, zeroId)
    let leftTakes ← nullableOf l
    let rightTakes ← nullableOf r
    if leftTakes != rightTakes then
      let witness := textTo steps (head + 1) head []
      let met := (← get).met.size
      return { equal := false, witness, byLeft := leftTakes, pairs := pairs.size, met }
    if l != r then
      for letter in alphabet do
        let next := (← derivative letter (l + 1) l, ← derivative letter (r + 1) r)
        unless seen.contains next do
          seen := seen.insert next
          pairs := pairs.push next
          steps := steps.push (head, letter)
    head := head + 1
  throw s!"a comparison ran out of fuel after {pairFuel} pairs of derivatives"

/-- Begin a comparison: the parts of `closed` are taken whole in it, and nothing is kept
from the comparison before. -/
def beginComparison (closed : Std.HashMap Nat Nat) : Run Unit :=
  modify fun table => { table with closed, closedDerivatives := {}, met := {} }

/-- Whether two expressions have one language, with the nodes of the two.

With `closeParts`, each part is taken whole, apart from the two expressions themselves. If
that walk finds one language, the expressions have one language. If it finds a difference and
met a part, the difference proves nothing, and the walk is made again over characters alone.
A walk that met no part is a walk over characters.

A witness comes from a walk over characters. It is checked with the second matcher against
both expressions as they were given: it must be a text of the one side and not of the
other. -/
def sameLanguage (closeParts : Bool) (left right : Regex) : Run (Outcome × Nat × Nat) := do
  let l := fuse left
  let r := fuse right
  let characters := (classes (setsOf r (setsOf l []))).map Letter.char
  let leftId ← internRegex l
  let rightId ← internRegex r
  let parts := (← get).parts
  let partCount := (← get).partCount
  let closed : Std.HashMap Nat Nat :=
    if closeParts then (parts.erase leftId).erase rightId else {}
  let alphabet :=
    if closed.isEmpty then characters
    else characters ++ (List.range partCount).map Letter.part
  beginComparison closed
  let mut outcome ← explore alphabet leftId rightId
  if !outcome.equal && outcome.met > 0 then
    beginComparison {}
    let again ← explore characters leftId rightId
    outcome := { again with pairs := outcome.pairs + again.pairs }
  beginComparison {}
  unless outcome.equal do
    unless accepts left outcome.witness == outcome.byLeft &&
        accepts right outcome.witness == !outcome.byLeft do
      throw s!"internal: the two matchers are at odds on the text {quote outcome.witness}"
  return (outcome, leftId, rightId)

/-- Record that two nodes have one language: from now on they are one part, and one letter
where parts are closed. A set, the empty text and the empty language stay open: a set is one
node on both sides, and its characters are letters already. -/
def registerPart (left right : Nat) : Run Unit := do
  let plain (node : Node) : Bool :=
    match node with
    | .zero | .eps | .set _ => true
    | _ => false
  if plain (← nodeOf left) || plain (← nodeOf right) then return
  modify fun table =>
    let number := ((table.parts[left]?).or (table.parts[right]?)).getD table.partCount
    { table with
      parts := (table.parts.insert left number).insert right number
      partCount := max table.partCount (number + 1) }

/-! ## The comparisons -/

/-- One comparison: a sealed expression, written as the chapter writes it, and the library's
description of it. `declaration` is the description's name under `Whatwg.Svg.Value`. -/
structure Row where
  label : String
  chapterSide : Ebnf
  declaration : String
  librarySide : Regex

/-- A production by its name, as the sealed side of a row. -/
def named (name : String) : Ebnf := .ref name 0

/-- The namespace of the library's descriptions. -/
def libraryNamespace : String := "Whatwg.Svg.Value."

open Whatwg.Svg.Value in
/-- The comparisons. The first is the gate's subject: `svg_path` and the description of a
path. Each of the others is a production with a named description, from the commands down to
the characters. `exponentPart` describes `exponent?`, and `wspSet` is the set of `wsp`. The
sequence productions have no name in the library: each is compared inside its command.

The order matters to the cost alone: a row stands before the rows it is built from, and the
run judges the list from its end, so that each row finds its parts made. -/
def rows : List Row :=
  [⟨startSymbol, named startSymbol, "Path.syn", Path.syn.erase⟩,
   ⟨"drawto_command", named "drawto_command", "Command.syn", Command.syn.erase⟩,
   ⟨"moveto", named "moveto", "Drawto.moveto", Drawto.moveto.erase⟩,
   ⟨"closepath", named "closepath", "Drawto.closepath", Drawto.closepath.erase⟩,
   ⟨"lineto", named "lineto", "Drawto.lineto", Drawto.lineto.erase⟩,
   ⟨"horizontal_lineto", named "horizontal_lineto", "Drawto.horizontalLineto",
     Drawto.horizontalLineto.erase⟩,
   ⟨"vertical_lineto", named "vertical_lineto", "Drawto.verticalLineto",
     Drawto.verticalLineto.erase⟩,
   ⟨"curveto", named "curveto", "Drawto.curveto", Drawto.curveto.erase⟩,
   ⟨"smooth_curveto", named "smooth_curveto", "Drawto.smoothCurveto",
     Drawto.smoothCurveto.erase⟩,
   ⟨"quadratic_bezier_curveto", named "quadratic_bezier_curveto",
     "Drawto.quadraticBezierCurveto", Drawto.quadraticBezierCurveto.erase⟩,
   ⟨"smooth_quadratic_bezier_curveto", named "smooth_quadratic_bezier_curveto",
     "Drawto.smoothQuadraticBezierCurveto", Drawto.smoothQuadraticBezierCurveto.erase⟩,
   ⟨"elliptical_arc", named "elliptical_arc", "Drawto.ellipticalArc",
     Drawto.ellipticalArc.erase⟩,
   ⟨"elliptical_arc_argument", named "elliptical_arc_argument", "Arc.syn", Arc.syn.erase⟩,
   ⟨"coordinate_pair_double", named "coordinate_pair_double", "coordinatePairDouble",
     coordinatePairDouble.erase⟩,
   ⟨"coordinate_pair_triplet", named "coordinate_pair_triplet", "coordinatePairTriplet",
     coordinatePairTriplet.erase⟩,
   ⟨"coordinate_pair", named "coordinate_pair", "Point.syn", Point.syn.erase⟩,
   ⟨"coordinate", named "coordinate", "Decimal.syn", Decimal.syn.erase⟩,
   ⟨"number", named "number", "Magnitude.syn", Magnitude.syn.erase⟩,
   ⟨"fractional-constant", named "fractional-constant", "fractionalConstant",
     fractionalConstant.erase⟩,
   ⟨"exponent?", .opt (named "exponent"), "exponentPart", exponentPart.erase⟩,
   ⟨"sign", named "sign", "sign", sign.erase⟩,
   ⟨"flag", named "flag", "flag", flag.erase⟩,
   ⟨"comma_wsp", named "comma_wsp", "commaWsp", commaWsp.erase⟩,
   ⟨"wsp", named "wsp", "wspSet", .set wspSet⟩,
   ⟨"digit", named "digit", "digit", digit.erase⟩]

/-- One control: a production, a change to it in words, and the change as a rule that must
rewrite one place. -/
structure Control where
  label : String
  target : String
  edit : String
  rule : Ebnf → Option Ebnf

/-- A rule that drops the alternative `which` picks from a choice of two. -/
def dropAlternative (which : Ebnf → Bool) : Ebnf → Option Ebnf
  | .alt a b => if which b then some a else if which a then some b else none
  | _ => none

/-- The controls: each change makes `svg_path` another language. The first five take texts
away, and the last one adds some. -/
def controls : List Control :=
  [{ label := "no closepath", target := "drawto_command"
     edit := "without the alternative `closepath`"
     rule := dropAlternative (Ebnf.isRef "closepath") },
   { label := "separator required", target := "coordinate_pair"
     edit := "with `comma_wsp?` made `comma_wsp`"
     rule := fun e =>
       match e with
       | .opt a => if a.isRef "comma_wsp" then some a else none
       | _ => none },
   { label := "no small e", target := "exponent"
     edit := "without the alternative \"e\""
     rule := dropAlternative (Ebnf.isLit ['e']) },
   { label := "no form feed", target := "wsp"
     edit := "without the alternative #xC"
     rule := dropAlternative (Ebnf.isLit ['\x0c']) },
   { label := "no bare fraction", target := "fractional-constant"
     edit := "with `digit*` made `digit+`"
     rule := fun e =>
       match e with
       | .star a => if a.isRef "digit" then some (.plus a) else none
       | _ => none },
   { label := "separator optional", target := "elliptical_arc_argument"
     edit := "with its one `comma_wsp` made `comma_wsp?`"
     rule := fun e =>
       match e with
       | .seq a b => if b.isRef "comma_wsp" then some (.seq a (.opt b)) else none
       | _ => none }]

/-- The productions with a control's change made. The rule must rewrite one place of the
target, or the control is refused: a control that changes nothing shows nothing. -/
def Control.apply (control : Control) (productions : List Production) :
    Except String (List Production) := do
  let some found := productions.find? (·.name == control.target)
    | throw s!"the control `{control.label}` names `{control.target}`, which has no production"
  let (body, places) := found.body.rewrite control.rule
  unless places == 1 do
    throw (s!"the control `{control.label}` rewrites {places} place(s) of " ++
      s!"`{control.target}`, and it must rewrite one")
  return productions.map fun entry =>
    if entry.name == control.target then { entry with body } else entry

/-- What a run has to compare: each row with its sealed side as an expression, the start
symbol, and each control with the start symbol under its change. -/
structure Prepared where
  count : Nat
  rows : List (Row × Regex)
  start : Regex
  controls : List (Control × Regex)

/-- A refusal as a message. -/
def Refusal.message (text : List Char) (refusal : Refusal) : String :=
  s!"{place text refusal.offset}: {refusal.reason}"

/-- A sealed expression over the productions, as a regular expression. -/
def sealedExpression (productions : List Production) (e : Ebnf) : Except Refusal Regex :=
  expression (production productions (productions.length + 1) []) e

/-- Read the chapter's block and prepare the comparisons. The block must hold the start
symbol, and a production for each name it writes. Every production of the block must be
reached from the start symbol: the gate compares what `svg_path` reaches, and a production it
does not reach would stand in the block unread. -/
def prepare (text : List Char) : Except String Prepared := do
  let block ← (findBlock text).mapError fun reason => s!"{chapterPath}: {reason}"
  let refused {α : Type} (step : Except Refusal α) : Except String α :=
    step.mapError fun refusal => s!"{chapterPath}: {refusal.message text}"
  let productions ← refused (readGrammar block)
  unless productions.any (·.name == startSymbol) do
    throw s!"{chapterPath}: the block has no production `{startSymbol}`"
  for entry in productions do
    for (name, offset) in entry.body.references do
      unless productions.any (·.name == name) do
        let refusal : Refusal := ⟨offset, s!"the name `{name}` has no production"⟩
        throw s!"{chapterPath}: {refusal.message text}"
  let written := productions.foldl (fun total entry => total + entry.body.names.length) 0
  let some reached := reach productions (written + 2) [startSymbol] []
    | throw "internal: the search for the reached productions ran out of fuel"
  let unreached := (productions.filter fun entry => !reached.contains entry.name).map (·.name)
  unless unreached.isEmpty do
    let names := ", ".intercalate unreached
    throw (s!"{chapterPath}: `{startSymbol}` does not reach the production(s) {names}, " ++
      "so this gate would not compare them")
  let mut prepared : List (Row × Regex) := []
  for row in rows do
    for name in row.chapterSide.names do
      unless productions.any (·.name == name) do
        throw s!"{chapterPath}: the row `{row.label}` names `{name}`, which has no production"
    prepared := prepared ++ [(row, ← refused (sealedExpression productions row.chapterSide))]
  let start ← refused (sealedExpression productions (named startSymbol))
  let mut changed : List (Control × Regex) := []
  for control in controls do
    let edited ← control.apply productions
    changed := changed ++ [(control, ← refused (sealedExpression edited (named startSymbol)))]
  return { count := productions.length, rows := prepared, start, controls := changed }

/-- One line of the report: whether it is a PASS, its text, and the pairs of derivatives that
its comparison reached. -/
structure Line where
  passed : Bool
  text : String
  pairs : Nat

/-- What a run found: the number of productions read, a line for each row and each control,
the line of the reference when it was asked for, and the number of nodes made. -/
structure Report where
  count : Nat
  rows : List Line
  controls : List Line
  whole : Option Line
  nodes : Nat

/-- A witness in words: the text, and the side that takes it. -/
def witnessed (outcome : Outcome) (left right : String) : String :=
  s!"{quote outcome.witness} is a text of {if outcome.byLeft then left else right} only"

/-- A count with its noun: `1 pair`, `5 pairs`. -/
def counted (count : Nat) (noun : String) : String :=
  if count == 1 then s!"1 {noun}" else s!"{count} {noun}s"

/-- A walk in words: its pairs, and whether it met parts taken whole. -/
def walked (outcome : Outcome) : String :=
  let pairs := counted outcome.pairs "pair"
  let parts := counted outcome.met "part"
  if outcome.met == 0 then s!"{pairs} over characters" else s!"{pairs}, {parts} taken whole"

/-- The line of one row. A row that has one language becomes a part for the rows above it. -/
def judgeRow (row : Row) (chapterSide : Regex) : Run Line := do
  let (outcome, sealedId, libraryId) ← sameLanguage true chapterSide row.librarySide
  let name := libraryNamespace ++ row.declaration
  if outcome.equal then
    registerPart sealedId libraryId
    return ⟨true, s!"PASS {row.label} = {name}: one language ({walked outcome})", outcome.pairs⟩
  let found := witnessed outcome "the sealed production" "the library's expression"
  return ⟨false, s!"FAIL {row.label} and {name} differ: {found} ({walked outcome})",
    outcome.pairs⟩

/-- The line of a control: the sealed start symbol and another expression must differ.
`other` names the other side. With `closeParts` the walk first takes parts whole, as a row's
walk does. A verdict of one language there fails the control. A difference there sends the
walk over characters alone, as for a row, and the witness is of that walk. -/
def judgeControl (closeParts : Bool) (subject other : String) (start changed : Regex) :
    Run Line := do
  let (outcome, _, _) ← sameLanguage closeParts start changed
  if outcome.equal then
    return ⟨false, s!"FAIL control {subject} was not told from the sealed `{startSymbol}`: " ++
      s!"the walk answers one language ({walked outcome})", outcome.pairs⟩
  let found := witnessed outcome s!"the sealed `{startSymbol}`" other
  return ⟨true, s!"PASS control {subject} differs: {found} ({walked outcome})", outcome.pairs⟩

/-- The line of the reference: a row over characters alone, with no part taken whole. -/
def judgeWhole (row : Row) (chapterSide : Regex) : Run Line := do
  let (outcome, _, _) ← sameLanguage false chapterSide row.librarySide
  let subject := s!"whole {row.label} = {libraryNamespace}{row.declaration}"
  if outcome.equal then
    return ⟨true, s!"PASS {subject}: one language ({walked outcome}, no part taken whole)",
      outcome.pairs⟩
  let found := witnessed outcome "the sealed production" "the library's expression"
  return ⟨false, s!"FAIL {subject}: they differ, {found} ({walked outcome})", outcome.pairs⟩

/-- The control on the library's side, in words: the value of `d` also takes `none`, so its
description must differ from the sealed start symbol. -/
def keywordSubject : String :=
  s!"keyword: {libraryNamespace}PathData.syn, which also takes `none`,"

/-- Every comparison of a run, over one table. The rows are judged from the last to the
first, which is from the characters up: each row stands before the rows it is built from.
Then the controls: each changed start symbol by a walk that takes parts whole first, as a
row's does, and the keyword over characters alone. With `reference`, the first row is then
judged whole. -/
def judge (prepared : Prepared) (reference : Bool) : Run Report := do
  let mut rowLines : List Line := []
  for (row, chapterSide) in prepared.rows.reverse do
    rowLines := (← judgeRow row chapterSide) :: rowLines
  let mut controlLines : List Line := []
  for (control, changed) in prepared.controls do
    let subject := s!"{control.label}: `{control.target}` {control.edit}"
    let other := s!"the changed `{startSymbol}`"
    controlLines := controlLines ++ [← judgeControl true subject other prepared.start changed]
  let keyword := Whatwg.Svg.Value.PathData.syn.erase
  controlLines := controlLines ++
    [← judgeControl false keywordSubject "the library's expression" prepared.start keyword]
  let whole ←
    match reference, prepared.rows.head? with
    | true, some (row, chapterSide) => some <$> judgeWhole row chapterSide
    | _, _ => pure none
  return { count := prepared.count, rows := rowLines, controls := controlLines, whole,
           nodes := (← get).nodes.size }

/-! ## Driver -/

def usage : String :=
  "usage: lake exe whatwg_svggrammar          compare the sealed grammar of path data with " ++
  "its description, row by row, and run the controls\n" ++
  "       lake exe whatwg_svggrammar --whole  the same, and then `svg_path` whole, over " ++
  "characters alone"

/-- Read the sealed chapter, and refuse a digest that is not the pinned one. -/
def readChapter (root : System.FilePath) : IO (Except String (List Char)) := do
  let path := root / chapterPath
  unless ← path.pathExists do
    return .error s!"missing input {chapterPath}"
  let bytes ← IO.FS.readBinFile path
  let digest := Gates.Sha256.hexDigest bytes
  unless digest == chapter.digest do
    return .error (s!"{chapterPath} has digest {digest}, expected the pinned " ++
      s!"{chapter.digest}; read the grammar again before pinning")
  match String.fromUTF8? bytes with
  | some text => return .ok text.toList
  | none => return .error s!"{chapterPath}: the bytes are not UTF-8"

/-- Print a report: a PASS line to the standard output and a FAIL line to the standard
error, each in full. The last line is the verdict. -/
def printReport (report : Report) : IO UInt32 := do
  let lines := report.rows ++ report.controls ++ report.whole.toList
  for line in lines do
    if line.passed then IO.println line.text else IO.eprintln line.text
  let failed := (lines.filter fun line => !line.passed).length
  let pairs := lines.foldl (fun total line => total + line.pairs) 0
  let counts :=
    s!"{report.count} productions read from the block under `PathDataBNF` of {chapterPath}; " ++
    s!"{pairs} pairs of derivatives reached over {lines.length} comparisons, with " ++
    s!"{report.nodes} expressions up to similarity"
  if failed == 0 then
    let reference := if report.whole.isSome then "the reference over characters agrees; " else ""
    IO.println (s!"PASS svg grammar: the sealed production `{startSymbol}` and the erased " ++
      s!"expression of {libraryNamespace}Path.syn have one language, and so have " ++
      s!"{report.rows.length - 1} more productions and their descriptions; " ++
      s!"{report.controls.length} controls differ; {reference}{counts}")
    return 0
  IO.eprintln (s!"FAIL svg grammar: {failed} of {lines.length} comparisons failed; {counts}")
  return 1

/-- Command-line entry, invoked by `whatwgbin/SvgGrammar.lean`. -/
def cli (args : List String) : IO UInt32 := do
  let reference ←
    match args with
    | [] => pure false
    | ["--whole"] => pure true
    | _ =>
      IO.eprintln usage
      return 2
  let root ← Gates.Common.projectRoot
  let prepared ←
    match (← readChapter root) >>= prepare with
    | .ok prepared => pure prepared
    | .error reason =>
      IO.eprintln s!"FAIL svg grammar: {reason}"
      return 2
  match (judge prepared reference).run' Table.initial with
  | .ok report => printReport report
  | .error reason =>
    IO.eprintln s!"FAIL svg grammar: {reason}"
    return 2

end Gates.SvgGrammar
