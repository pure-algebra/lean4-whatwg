import Gates.Common

/-!
# Gates.Ecmarkup

The ecmarkup source scanner: the second source shape the census reads, added
for the ECMA-262 lane under ruling R-P1. Its packet is
`test/contracts/ecma262-census.contract.md`, which owns every name, meaning
and refusal below; its source evidence is
`docs/research/2026-09-06-ecma262-promise-census-survey.md`.

ecmarkup is not Bikeshed. Sections are `<emu-clause id type>`, the operation
name lives only in the structured `<h1>` (`aoid` occurs once in 22 in-scope
operations), record fields and internal slots live in `<emu-table>` bodies, and
`<emu-alg>` bodies are indentation-nested `1. ` **text lines**, not HTML lists.
Attribute order is not fixed: two in-scope clause tags write `oldids` before
`id`, so every attribute is read by name with the whitespace-before-name rule.

This module is a **pure scanner over a byte window**. It reads no file, decides
no disposition, and **refuses rather than skipping**: every rejection is
`Except.error` whose message carries the decimal byte offset of the refused
construct — the opening tag for a clause, a table row or an algorithm block,
and the first byte of the line for a step. That diagnostic text is part of the
frozen contract, and it matches the `Gates.Census` message style.

## Why the byte primitives are re-spelled here

`Gates/Census.lean` must import this module to serve
`Gates.Census.Profile.ecmarkup`, so the dependency cannot also run the other
way and the handful of byte helpers below cannot be taken from `Gates.Census`.
They are the same rules, deliberately: total `byteAt`, ASCII-first
classification (every structural byte this scanner tests is below 0x80, and the
188 non-ASCII bytes in scope are only ever copied), fuel-bounded structural
recursion with the fuel taken from a size the data carries, and accumulation
into one linearly-threaded `Array`. No `partial`, no `unsafe`, no well-founded
recursion.

Anchors, span digests and excerpts are **not** computed here. A row this module
produces is a kind spelling, an id and a half-open byte span;
`Gates.Census.chooseAnchorLength`, `Gates.Sha256.hexDigest` and
`Gates.Census.renderRow` give it its anchor, digest and excerpt on exactly the
path the other standards take, so there is one anchor ladder in the repository
and one row-rendering rule.
-/

namespace Gates.Ecmarkup

/-! ## Byte primitives -/

/-- Total byte access: out of range reads as zero, so no scan can panic. -/
@[inline] def byteAt (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0

@[inline] def isSpaceByte (b : UInt8) : Bool :=
  b == 0x20 || b == 0x0a || b == 0x09 || b == 0x0d

private def matchAux (bs pat : ByteArray) (i j : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
    if Nat.ble pat.size j then true
    else if byteAt bs (i + j) == byteAt pat j then matchAux bs pat i (j + 1) fuel
    else false

/-- Whether `pat` occurs in `bs` starting exactly at `i`. -/
def matchesAt (bs pat : ByteArray) (i : Nat) : Bool :=
  Nat.ble (i + pat.size) bs.size && matchAux bs pat i 0 (pat.size + 1)

private def findAux (bs pat : ByteArray) (i limit : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if !Nat.ble (i + pat.size) limit then none
    else if matchesAt bs pat i then some i
    else findAux bs pat (i + 1) limit fuel

/-- The first occurrence of `pat` at or after `start` and ending at or before
`limit`. Fuel is one per byte of the window. -/
def findIn (bs pat : ByteArray) (start limit : Nat) : Option Nat :=
  findAux bs pat start limit (limit + 1)

private def collectAux (bs pat : ByteArray) (i limit : Nat) (acc : Array Nat) (cap : Nat) :
    Nat → Array Nat
  | 0 => acc
  | fuel + 1 =>
    if Nat.ble cap acc.size then acc
    else if !Nat.ble (i + pat.size) limit then acc
    else if matchesAt bs pat i then collectAux bs pat (i + 1) limit (acc.push i) cap fuel
    else collectAux bs pat (i + 1) limit acc cap fuel

/-- Every offset in `[start, limit)` at which `pat` occurs, in increasing
order, stopping once `cap` offsets have been collected. -/
def occurrencesIn (bs pat : ByteArray) (start limit cap : Nat) : Array Nat :=
  collectAux bs pat start limit #[] cap (limit + 1)

/-- The bytes `[b, e)` decoded as text, when they are valid UTF-8. -/
def sliceString? (bs : ByteArray) (b e : Nat) : Option String :=
  String.fromUTF8? (bs.extract b e)

/-! ## Small text utilities

These operate on `String` and are used only for names, titles and predicates,
never to compute a byte offset. -/

/-- Every `<…>` run removed. In scope no attribute value contains `>`, and the
only callers are `<h1>`, `<p>`, `<li>`, `<dt>`, `<td>` and `<dfn>` bodies. -/
def stripTags (text : String) : String := Id.run do
  let mut out : String := ""
  let mut inTag := false
  for c in text.toList do
    if c == '<' then inTag := true
    else if c == '>' then inTag := false
    else if !inTag then out := out.push c
  return out

/-- Every run of space, tab, carriage return and newline collapsed to one
space, with no leading or trailing space. -/
def normalizeWhitespace (text : String) : String := Id.run do
  let mut out : String := ""
  let mut pendingSpace := false
  for c in text.toList do
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
      pendingSpace := true
    else
      if pendingSpace && !out.isEmpty then out := out.push ' '
      pendingSpace := false
      out := out.push c
  return out

/-- Whether `needle` occurs in `haystack`. -/
def containsText (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- The leading run of non-space characters. -/
def firstToken (text : String) : String :=
  String.ofList (text.toList.takeWhile (fun c => c != ' '))

/-- `text` without a leading `sec-`. -/
def withoutSecPrefix (text : String) : String :=
  if text.startsWith "sec-" then Gates.Common.dropChars text 4 else text

/-! ## The R-P3 escaping

`escapeId` writes every character of the safe alphabet `A-Z a-z 0-9 . % -`
through unchanged — so `.`, `%` and case survive, which is what R-P3 requires —
and writes every other character `c` as `~`, the lower-case hexadecimal of
`c.toNat` with no leading zero, `~`. Because `~` is outside the safe alphabet
the encoding is prefix-free, so `escapeId` is injective and `unescapeId`
inverts it exactly, returning `none` on any string outside the image. The
collision this repairs is `Gates.Census.kebab "sec-promise.resolve"` against
`Gates.Census.kebab "sec-promise-resolve"`, which are the same string. -/

/-- The safe alphabet: ASCII letters, ASCII digits, `.`, `%` and `-`. -/
def isSafeIdChar (c : Char) : Bool :=
  let n := c.toNat
  (Nat.ble 0x41 n && Nat.ble n 0x5a) || (Nat.ble 0x61 n && Nat.ble n 0x7a)
    || (Nat.ble 0x30 n && Nat.ble n 0x39) || c == '.' || c == '%' || c == '-'

private def hexDigitChar (n : Nat) : Char :=
  if Nat.blt n 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + n - 10)

private def hexValue? (c : Char) : Option Nat :=
  let n := c.toNat
  if Nat.ble 0x30 n && Nat.ble n 0x39 then some (n - 0x30)
  else if Nat.ble 0x61 n && Nat.ble n 0x66 then some (n - 0x61 + 10)
  else none

/-- Lower-case hexadecimal with no leading zero. A `Char` code point needs at
most six digits, so eight steps always suffice. -/
def toHexLower (n : Nat) : String := Id.run do
  if n == 0 then return "0"
  let mut digits : List Char := []
  let mut v := n
  for _ in [0:8] do
    if v == 0 then break
    digits := hexDigitChar (v % 16) :: digits
    v := v / 16
  return String.ofList digits

/-- The injective, prefix-free escaping ruling R-P3 requires. -/
def escapeId (text : String) : String := Id.run do
  let mut out : String := ""
  for c in text.toList do
    if isSafeIdChar c then out := out.push c
    else out := out ++ "~" ++ toHexLower c.toNat ++ "~"
  return out

/-- The hexadecimal run up to the closing `~`, and the rest. -/
private def splitHex : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: rest, acc =>
    if c == '~' then some (acc.reverse, rest)
    else
      match hexValue? c with
      | some _ => splitHex rest (c :: acc)
      | none => none

private def unescapeAux : Nat → List Char → String → Option String
  | 0, _, _ => none
  | _ + 1, [], acc => some acc
  | fuel + 1, c :: rest, acc =>
    if c == '~' then
      match splitHex rest [] with
      | none => none
      | some (digits, tail) =>
        if digits.isEmpty then none
        else if Nat.blt 1 digits.length && digits.headD '0' == '0' then none
        else
          let n := digits.foldl (fun a d => a * 16 + (hexValue? d).getD 0) 0
          if Nat.ble 0x110000 n then none
          else if Nat.ble 0xd800 n && Nat.ble n 0xdfff then none
          else
            let ch := Char.ofNat n
            if isSafeIdChar ch then none
            else unescapeAux fuel tail (acc.push ch)
    else if isSafeIdChar c then unescapeAux fuel rest (acc.push c)
    else none

/-- The exact inverse of `escapeId`: `none` on any string outside its image. -/
def unescapeId (text : String) : Option String :=
  let cs := text.toList
  unescapeAux (cs.length + 1) cs ""

/-! ## Tags

One pass over the window collects every tag. `'<'` occurs about 1,500 times in
the two in-scope windows, so a single byte test per position plus one
classification per tag is the whole lexical cost, and every later scanner reads
this array rather than the bytes again.

Refusing `&` here is ruling R7 of the survey: zero character references occur in
scope, they do occur elsewhere in the file, and a re-pin that introduces one
must be a visible failure rather than a silent mis-decode. -/

structure Tag where
  /-- The element name, lower-cased. -/
  name : String
  isClose : Bool
  /-- Offset of the `<`. -/
  b : Nat
  /-- Just past the `>`. -/
  e : Nat
  deriving Inhabited, BEq

/-- Just past the element name that starts at `i`. Names in scope are at most
sixteen bytes; the bound is a data-carried size, not a magic number. -/
private def tagNameEnd (bs : ByteArray) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:32] do
    let n := (byteAt bs j).toNat
    let isName :=
      (Nat.ble 0x61 n && Nat.ble n 0x7a) || (Nat.ble 0x41 n && Nat.ble n 0x5a)
        || (Nat.ble 0x30 n && Nat.ble n 0x39) || n == 0x2d
    if isName then j := j + 1 else break
  return j

/-- Just past the `>` that closes the tag, skipping quoted attribute values. -/
private def tagEndAux (bs : ByteArray) (i limit : Nat) (inQuote : Bool) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if Nat.ble limit i then none
    else
      let c := byteAt bs i
      if inQuote then
        tagEndAux bs (i + 1) limit (!(c == 0x22)) fuel
      else if c == 0x22 then tagEndAux bs (i + 1) limit true fuel
      else if c == 0x3e then some (i + 1)
      else tagEndAux bs (i + 1) limit false fuel

private def scanTagsAux (bs : ByteArray) (i e : Nat) (acc : Array Tag) :
    Nat → Except String (Array Tag)
  | 0 => .error s!"ecmarkup: the tag scan exhausted its fuel at byte {i}"
  | fuel + 1 =>
    if Nat.ble e i then .ok acc
    else
      let c := byteAt bs i
      if c == 0x26 then
        .error s!"ecmarkup: a character reference starts at byte {i}; this scanner refuses entities in a scanned window rather than decoding them"
      else if c == 0x3c then
        let isClose := byteAt bs (i + 1) == 0x2f
        let nameB := if isClose then i + 2 else i + 1
        let nameE := tagNameEnd bs nameB
        if nameE == nameB then
          .error s!"ecmarkup: a tag with no element name starts at byte {i}"
        else
          match tagEndAux bs nameE e false (e - nameE + 1) with
          | none => .error s!"ecmarkup: unterminated tag at byte {i}"
          | some te =>
            match sliceString? bs nameB nameE with
            | none => .error s!"ecmarkup: the element name at byte {i} is not valid UTF-8"
            | some nm =>
              scanTagsAux bs te e
                (acc.push { name := nm.map Char.toLower, isClose := isClose, b := i, e := te })
                fuel
      else scanTagsAux bs (i + 1) e acc fuel

/-- Every tag in the byte window `[b, e)`, in document order. -/
def scanTags (bs : ByteArray) (b e : Nat) : Except String (Array Tag) :=
  scanTagsAux bs b e #[] (e - b + 1)

/-- The value of attribute `name` inside the tag `[tagB, tagE)`. The attribute
name must be preceded by whitespace, so `id=` is never read out of `oldids=`;
two in-scope clause tags write `oldids` before `id`, which is why nothing here
is positional. -/
def attrValue? (bs : ByteArray) (tagB tagE : Nat) (name : String) : Option String := Id.run do
  let key := (name ++ "=").toUTF8
  let quote := ByteArray.mk #[0x22]
  for i in [tagB:tagE] do
    if matchesAt bs key i && Nat.blt tagB i && isSpaceByte (byteAt bs (i - 1)) then
      let vs := i + key.size
      if byteAt bs vs == 0x22 then
        match findIn bs quote (vs + 1) tagE with
        | some ve => return sliceString? bs (vs + 1) ve
        | none => return none
      else
        let mut ve := vs
        for _ in [vs:tagE] do
          let c := byteAt bs ve
          if isSpaceByte c || c == 0x3e then break
          ve := ve + 1
        return sliceString? bs vs ve
  return none

/-- The index in `tags` of the close tag matching the open tag at index `oi`,
counting nested opens of the same element. -/
def matchClose (tags : Array Tag) (oi : Nat) : Option Nat := Id.run do
  let name := (tags.getD oi default).name
  let mut depth := 0
  for k in [oi + 1 : tags.size] do
    let t := tags.getD k default
    if t.name == name then
      if t.isClose then
        if depth == 0 then return some k else depth := depth - 1
      else depth := depth + 1
  return none

/-- The whitespace-normalised text of an element, tags removed. -/
private def innerText (bs : ByteArray) (openE closeB : Nat) : String :=
  match sliceString? bs openE closeB with
  | none => ""
  | some raw => normalizeWhitespace (stripTags raw)

/-! ## Clauses -/

structure Clause where
  /-- The `id` attribute. -/
  id : String
  /-- The `type` attribute, empty where the tag carries none. -/
  kindAttr : String
  /-- The `aoid` attribute, empty where absent. -/
  aoid : String
  /-- The `<h1>` inner text with runs of whitespace collapsed to one space. -/
  title : String
  /-- `0` for a clause with no clause ancestor inside the scanned window, one
  more than its parent's otherwise. -/
  depth : Nat
  /-- Start of the whole element. -/
  b : Nat
  /-- Just past the closing tag. -/
  e : Nat
  deriving Inhabited, BEq

/-- The three `type` values observed at the pin. A fourth is refused. -/
def clauseTypes : List String :=
  ["abstract operation", "built-in function", "host-defined abstract operation"]

private def isSectioning (name : String) : Bool :=
  name == "emu-clause" || name == "emu-annex" || name == "emu-intro"

private def buildClause (bs : ByteArray) (tags : Array Tag) (oi ci depth : Nat) :
    Except String Clause := Id.run do
  let ot := tags.getD oi default
  let ct := tags.getD ci default
  let some id := attrValue? bs ot.b ot.e "id"
    | return .error s!"ecmarkup: the <emu-clause> at byte {ot.b} carries no id attribute"
  if id.isEmpty then
    return .error s!"ecmarkup: the <emu-clause> at byte {ot.b} carries an empty id attribute"
  let kindAttr := (attrValue? bs ot.b ot.e "type").getD ""
  if !kindAttr.isEmpty && !clauseTypes.contains kindAttr then
    return .error s!"ecmarkup: the <emu-clause> at byte {ot.b} carries the unhandled type {kindAttr}"
  let aoid := (attrValue? bs ot.b ot.e "aoid").getD ""
  let mut titleIdx : Option Nat := none
  for k in [oi + 1 : ci] do
    let t := tags.getD k default
    if isSectioning t.name && !t.isClose then break
    if t.name == "h1" && !t.isClose then
      titleIdx := some k
      break
  let some hi := titleIdx
    | return .error s!"ecmarkup: the <emu-clause> at byte {ot.b} has no <h1> of its own"
  let some hc := matchClose tags hi
    | return .error s!"ecmarkup: the <h1> at byte {(tags.getD hi default).b} is never closed"
  if !Nat.blt hc ci then
    return .error s!"ecmarkup: the <h1> at byte {(tags.getD hi default).b} closes outside its clause"
  let title := innerText bs (tags.getD hi default).e (tags.getD hc default).b
  return .ok { id := id, kindAttr := kindAttr, aoid := aoid, title := title,
               depth := depth, b := ot.b, e := ct.e }

/-- The structured header: every `<dl class="header">` in the window carries
only `<dt>description</dt>`. Ten of the twenty-one in scope carry one and
eleven are empty; no other `<dt>` occurs. -/
def checkHeaders (bs : ByteArray) (tags : Array Tag) : Except String Unit := Id.run do
  for k in [0:tags.size] do
    let t := tags.getD k default
    if t.name == "dl" && !t.isClose && (attrValue? bs t.b t.e "class").getD "" == "header" then
      let some dc := matchClose tags k
        | return .error s!"ecmarkup: the <dl class=\"header\"> at byte {t.b} is never closed"
      for j in [k + 1 : dc] do
        let d := tags.getD j default
        if d.name == "dt" && !d.isClose then
          let some dtc := matchClose tags j
            | return .error s!"ecmarkup: the <dt> at byte {d.b} is never closed"
          let text := innerText bs d.e (tags.getD dtc default).b
          if text != "description" then
            return .error s!"ecmarkup: the <dt> at byte {d.b} of the structured header reads {text}, not description"
  return .ok ()

/-- Every `<emu-clause>` in the byte window `[b, e)`, in document order.

Sectioning elements are matched with a stack over `<emu-clause>`,
`<emu-annex>` and `<emu-intro>`; a close whose element name does not match the
open on top, a stack underflow, and an element left open are each refused with
a byte offset. `<emu-annex>` and `<emu-intro>` are tracked for nesting and
produce no clause: neither occurs in scope. -/
def clausesOfTags (bs : ByteArray) (tags : Array Tag) : Except String (Array Clause) := Id.run do
  match checkHeaders bs tags with
  | .error message => return .error message
  | .ok () => pure ()
  let mut out : Array Clause := #[]
  let mut stack : Array Nat := #[]
  let mut clauseDepth : Nat := 0
  for k in [0:tags.size] do
    let t := tags.getD k default
    if !isSectioning t.name then continue
    if t.isClose then
      if stack.isEmpty then
        return .error s!"ecmarkup: the close tag </{t.name}> at byte {t.b} has no open sectioning element on the stack"
      let oi := stack.getD (stack.size - 1) 0
      let ot := tags.getD oi default
      if ot.name != t.name then
        return .error s!"ecmarkup: the close tag </{t.name}> at byte {t.b} does not match <{ot.name}> opened at byte {ot.b}"
      stack := stack.pop
      if ot.name == "emu-clause" then
        clauseDepth := clauseDepth - 1
        match buildClause bs tags oi k clauseDepth with
        | .error message => return .error message
        | .ok clause => out := out.push clause
    else
      stack := stack.push k
      if t.name == "emu-clause" then clauseDepth := clauseDepth + 1
  if !stack.isEmpty then
    let ot := tags.getD (stack.getD (stack.size - 1) 0) default
    return .error s!"ecmarkup: the sectioning element <{ot.name}> opened at byte {ot.b} is never closed"
  return .ok (out.qsort (fun a b => Nat.blt a.b b.b))

/-- Every `<emu-clause>` of the byte window `[b, e)`. -/
def scanClauses (bs : ByteArray) (b e : Nat) : Except String (Array Clause) := do
  clausesOfTags bs (← scanTags bs b e)

/-! ## Algorithm steps

`<emu-alg>` bodies are indented text lines, not HTML lists. Nesting is two
spaces per level **relative to the block's own minimum indent**, because the
absolute base indent is 8, 10 or 12 depending on how deeply the clause nests;
an absolute column is therefore never read as an ordinal, and neither is the
literal `1.`. -/

structure Step where
  /-- Nesting level relative to the block's own minimum indent, `0` for a
  top-level step. -/
  level : Nat
  /-- First byte of the line, indentation included. -/
  b : Nat
  /-- Just past the last byte of the line, the newline excluded. -/
  e : Nat
  deriving Inhabited, BEq

private def lineEndIn (bs : ByteArray) (i limit : Nat) : Nat → Nat
  | 0 => limit
  | fuel + 1 =>
    if Nat.ble limit i then limit
    else if byteAt bs i == 0x0a then i
    else lineEndIn bs (i + 1) limit fuel

private def collectLinesAux (bs : ByteArray) (i limit : Nat) (acc : Array (Nat × Nat)) :
    Nat → Array (Nat × Nat)
  | 0 => acc
  | fuel + 1 =>
    if Nat.ble limit i then acc
    else
      let j := lineEndIn bs i limit (limit - i + 1)
      collectLinesAux bs (j + 1) limit (acc.push (i, j)) fuel

/-- The `[start, end)` interval of every line of `[b, e)`, newlines excluded. -/
def collectLines (bs : ByteArray) (b e : Nat) : Array (Nat × Nat) :=
  collectLinesAux bs b e #[] (e - b + 1)

private def leadingSpaces (bs : ByteArray) (b e : Nat) : Nat := Id.run do
  let mut n := 0
  for i in [b:e] do
    if byteAt bs i == 0x20 then n := n + 1 else break
  return n

private def stepsOfBlock (bs : ByteArray) (contentB contentE : Nat) :
    Except String (Array Step) := Id.run do
  let lines := collectLines bs contentB contentE
  let mut minIndent : Option Nat := none
  for (lb, le) in lines do
    let indent := leadingSpaces bs lb le
    if Nat.ble le (lb + indent) then continue
    match minIndent with
    | none => minIndent := some indent
    | some m => if Nat.blt indent m then minIndent := some indent
  let some base := minIndent
    | return .ok #[]
  let stepPattern := "1. ".toUTF8
  let mut out : Array Step := #[]
  let mut previous : Nat := 0
  let mut first := true
  for (lb, le) in lines do
    let indent := leadingSpaces bs lb le
    if Nat.ble le (lb + indent) then continue
    if !matchesAt bs stepPattern (lb + indent) then
      return .error s!"ecmarkup: the line at byte {lb} inside an <emu-alg> is not a step: it does not match a leading `1. `"
    if Nat.blt indent base then
      return .error s!"ecmarkup: the step line at byte {lb} is indented less than its block minimum"
    let relative := indent - base
    if relative % 2 != 0 then
      return .error s!"ecmarkup: the step line at byte {lb} is indented {relative} past the block minimum, which is not a multiple of two"
    let level := relative / 2
    if first then
      if level != 0 then
        return .error s!"ecmarkup: the first step line at byte {lb} is not at the block minimum indent"
      first := false
    else if Nat.blt (previous + 1) level then
      return .error s!"ecmarkup: the step line at byte {lb} jumps from level {previous} to level {level}"
    previous := level
    out := out.push { level := level, b := lb, e := le }
  return .ok out

/-- Every step line of every `<emu-alg>` block in the window, in document
order. An `<emu-alg>` carrying any attribute (`example`, `replaces-step`,
`type`) is refused at its opening tag: all thirty-two blocks in scope are the
bare tag. -/
def stepsOfTags (bs : ByteArray) (tags : Array Tag) : Except String (Array Step) := Id.run do
  let mut out : Array Step := #[]
  for k in [0:tags.size] do
    let t := tags.getD k default
    if t.name != "emu-alg" || t.isClose then continue
    let nameEnd := t.b + 1 + t.name.length
    for i in [nameEnd : t.e - 1] do
      if !isSpaceByte (byteAt bs i) then
        return .error s!"ecmarkup: the <emu-alg> at byte {t.b} carries an attribute; every block in scope is the bare tag"
    let some ci := matchClose tags k
      | return .error s!"ecmarkup: the <emu-alg> opened at byte {t.b} is never closed"
    match stepsOfBlock bs t.e (tags.getD ci default).b with
    | .error message => return .error message
    | .ok steps => out := out ++ steps
  return .ok out

/-- Every `<emu-alg>` step line of the byte window `[b, e)`. -/
def scanSteps (bs : ByteArray) (b e : Nat) : Except String (Array Step) := do
  stepsOfTags bs (← scanTags bs b e)

/-! ## Table rows -/

structure TableRow where
  /-- The three `<td>` content intervals, in order. -/
  cells : Array (Nat × Nat)
  /-- Start of the `<tr>`. -/
  b : Nat
  /-- Just past the `</tr>`. -/
  e : Nat
  deriving Inhabited, BEq

/-- Every body `<tr>` of every `<emu-table>` in the window. A `<thead>` with
other than three `<th>`, a body row with other than three `<td>`, and an
unterminated row are each refused with a byte offset. -/
def tableRowsOfTags (tags : Array Tag) : Except String (Array TableRow) :=
    Id.run do
  let mut out : Array TableRow := #[]
  for k in [0:tags.size] do
    let t := tags.getD k default
    if t.name != "emu-table" || t.isClose then continue
    let some tc := matchClose tags k
      | return .error s!"ecmarkup: the <emu-table> opened at byte {t.b} is never closed"
    let mut headIdx : Option Nat := none
    for j in [k + 1 : tc] do
      let h := tags.getD j default
      if h.name == "thead" && !h.isClose then
        if headIdx.isSome then
          return .error s!"ecmarkup: the <emu-table> at byte {t.b} carries more than one <thead>"
        headIdx := some j
    let some hi := headIdx
      | return .error s!"ecmarkup: the <emu-table> at byte {t.b} has no <thead>"
    let some hc := matchClose tags hi
      | return .error s!"ecmarkup: the <thead> of the <emu-table> at byte {t.b} is never closed"
    let mut headerCells := 0
    for j in [hi + 1 : hc] do
      let h := tags.getD j default
      if h.name == "th" && !h.isClose then headerCells := headerCells + 1
    if headerCells != 3 then
      return .error s!"ecmarkup: the <thead> of the <emu-table> at byte {t.b} has {headerCells} header cells, not three"
    for j in [hc + 1 : tc] do
      let r := tags.getD j default
      if r.name != "tr" || r.isClose then continue
      let some rc := matchClose tags j
        | return .error s!"ecmarkup: the body <tr> at byte {r.b} is never closed"
      if !Nat.blt rc tc then
        return .error s!"ecmarkup: the body <tr> at byte {r.b} closes outside its <emu-table>"
      let mut cells : Array (Nat × Nat) := #[]
      let mut bad : Option String := none
      for c in [j + 1 : rc] do
        let d := tags.getD c default
        if d.name != "td" || d.isClose then continue
        match matchClose tags c with
        | none => bad := some s!"ecmarkup: the <td> at byte {d.b} is never closed"
        | some dc => cells := cells.push (d.e, (tags.getD dc default).b)
      match bad with
      | some message => return .error message
      | none => pure ()
      if cells.size != 3 then
        return .error s!"ecmarkup: the body <tr> at byte {r.b} has {cells.size} cells, not three"
      out := out.push { cells := cells, b := r.b, e := (tags.getD rc default).e }
  return .ok out

/-- Every body `<tr>` of the byte window `[b, e)`. -/
def scanTableRows (bs : ByteArray) (b e : Nat) : Except String (Array TableRow) := do
  tableRowsOfTags (← scanTags bs b e)

/-! ## Row assembly

The 77 rows the ECMA-262 packet freezes: one primary row per clause, one
`field` or `slot` row per body `<tr>`, one `requirement` row per normative
bullet, and one `term` row per `<dfn>` that is not a record's own name. The
kind is carried as its contract spelling; `Gates.Census` maps it to
`Gates.Census.Kind` and gives the row its anchor, digest and excerpt. -/

structure RowSpec where
  /-- The contract spelling of the row kind. -/
  kind : String
  id : String
  /-- Start of the row's span. -/
  b : Nat
  /-- Just past the end of the row's span. -/
  e : Nat
  deriving Inhabited, BEq

def RowSpec.sortKey (r : RowSpec) : String := r.kind ++ "|" ++ r.id

/-- The row kind of a clause, decided by the tag and the `<h1>` in this order:
the three `type` values; then an `aoid`; then a title ending `" Records"`; then
a first title token containing a `.`; then a structural clause. -/
def clauseKind (c : Clause) : String :=
  if c.kindAttr == "abstract operation" then "op"
  else if c.kindAttr == "host-defined abstract operation" then "hook"
  else if c.kindAttr == "built-in function" then "builtin"
  else if !c.aoid.isEmpty then "op"
  else if c.title.endsWith " Records" then "record"
  else if (firstToken c.title).contains '.' then "property"
  else "clause"

/-- The innermost clause whose span contains `off`. -/
def innermost? (clauses : Array Clause) (off : Nat) : Option Clause := Id.run do
  let mut best : Option Clause := none
  for c in clauses do
    if Nat.ble c.b off && Nat.blt off c.e then
      match best with
      | none => best := some c
      | some p => if Nat.blt p.depth c.depth then best := some c
  return best

/-- `[[Name]]` with the brackets removed, case preserved. -/
def slotName? (text : String) : Option String :=
  if text.startsWith "[[" && text.endsWith "]]" && Nat.blt 4 text.length then
    some (Gates.Common.dropLastChars (Gates.Common.dropChars text 2) 2)
  else none

/-- The marker that makes a `<ul>` a requirement list: the immediately
preceding `<p>` says the implementation "must conform to the" something. Four
of the eleven in-scope `<ul>` match. -/
def requirementMarker : String := "must conform to the"

private def onlyWhitespaceBetween (bs : ByteArray) (b e : Nat) : Bool := Id.run do
  for i in [b:e] do
    if !isSpaceByte (byteAt bs i) then return false
  return true

/-- The requirement bullets of one window: the top-level `<li>` of every `<ul>`
whose immediately preceding `<p>` carries `requirementMarker`. Their ids are
positional inside the owning clause (ruling R-P3); none of the nine carries an
`id`, and the span digest guards the index. -/
private def requirementRows (bs : ByteArray) (tags : Array Tag) (clauses : Array Clause) :
    Except String (Array RowSpec) := Id.run do
  let mut out : Array RowSpec := #[]
  for k in [0:tags.size] do
    let t := tags.getD k default
    if t.name != "ul" || t.isClose then continue
    let some uc := matchClose tags k
      | return .error s!"ecmarkup: the <ul> opened at byte {t.b} is never closed"
    -- the immediately preceding `</p>`
    let mut closeIdx : Option Nat := none
    for j in [0:k] do
      let p := tags.getD j default
      if p.name == "p" && p.isClose then closeIdx := some j
    let some pc := closeIdx
      | continue
    let pct := tags.getD pc default
    if !onlyWhitespaceBetween bs pct.e t.b then continue
    let mut openIdx : Option Nat := none
    for j in [0:pc] do
      let p := tags.getD j default
      if p.name == "p" && !p.isClose then openIdx := some j
    let some po := openIdx
      | continue
    let text := innerText bs (tags.getD po default).e pct.b
    if !containsText text requirementMarker then continue
    let some owner := innermost? clauses t.b
      | return .error s!"ecmarkup: the requirement list at byte {t.b} lies in no clause"
    let ownerName := escapeId (withoutSecPrefix owner.id)
    let mut index := 0
    let mut skipTo := 0
    for j in [k + 1 : uc] do
      if Nat.blt j skipTo then continue
      let li := tags.getD j default
      if li.name != "li" || li.isClose then continue
      let some lc := matchClose tags j
        | return .error s!"ecmarkup: the <li> at byte {li.b} is never closed"
      if !Nat.blt lc uc then
        return .error s!"ecmarkup: the <li> at byte {li.b} closes outside its <ul>"
      index := index + 1
      skipTo := lc + 1
      out := out.push
        { kind := "requirement", id := s!"requirement.{ownerName}.{index}",
          b := li.b, e := (tags.getD lc default).e }
  return .ok out

/-- The `term` rows of one window: every `<dfn>` that is not the first `<dfn>`
of a `record` clause, which is the exclusion that keeps the three record names
from being counted twice. Only three of the nine in scope carry an `id`. -/
private def termRows (bs : ByteArray) (tags : Array Tag) (clauses : Array Clause) :
    Except String (Array RowSpec) := Id.run do
  let mut out : Array RowSpec := #[]
  let mut namedRecords : Array String := #[]
  for k in [0:tags.size] do
    let t := tags.getD k default
    if t.name != "dfn" || t.isClose then continue
    let some dc := matchClose tags k
      | return .error s!"ecmarkup: the <dfn> opened at byte {t.b} is never closed"
    let some owner := innermost? clauses t.b
      | return .error s!"ecmarkup: the <dfn> at byte {t.b} lies in no clause"
    if clauseKind owner == "record" && !namedRecords.contains owner.id then
      namedRecords := namedRecords.push owner.id
      continue
    let text := innerText bs t.e (tags.getD dc default).b
    let name := (attrValue? bs t.b t.e "id").getD text
    if name.isEmpty then
      return .error s!"ecmarkup: the <dfn> at byte {t.b} carries neither an id nor text"
    out := out.push
      { kind := "term", id := "term." ++ escapeId name, b := t.b, e := (tags.getD dc default).e }
  return .ok out

/-- Every census row of one clause window `[b, e)`, unsorted. -/
def windowRows (bs : ByteArray) (b e : Nat) : Except String (Array RowSpec) := do
  let tags ← scanTags bs b e
  let clauses ← clausesOfTags bs tags
  let mut out : Array RowSpec := #[]
  for c in clauses do
    let kind := clauseKind c
    out := out.push
      { kind := kind, id := kind ++ "." ++ escapeId (withoutSecPrefix c.id), b := c.b, e := c.e }
  let bodyRows ← tableRowsOfTags tags
  for r in bodyRows do
    let (cb, ce) := r.cells.getD 0 (0, 0)
    let cellText := innerText bs cb ce
    match slotName? cellText, innermost? clauses r.b with
    | none, _ =>
      .error s!"ecmarkup: the body <tr> at byte {r.b} does not name an internal slot in its first cell"
    | _, none =>
      .error s!"ecmarkup: the body <tr> at byte {r.b} lies in no clause"
    | some slot, some owner =>
      if clauseKind owner == "record" then
        out := out.push
          { kind := "field",
            id := "field." ++ escapeId (withoutSecPrefix owner.id) ++ "." ++ escapeId slot,
            b := r.b, e := r.e }
      else
        out := out.push { kind := "slot", id := "slot." ++ escapeId slot, b := r.b, e := r.e }
  out := out ++ (← requirementRows bs tags clauses)
  out := out ++ (← termRows bs tags clauses)
  return out

/-- Every census row of every clause window, sorted by kind then id, with
duplicate ids and empty or reversed spans refused. -/
def rows (bs : ByteArray) (windows : Array (Nat × Nat)) : Except String (Array RowSpec) := do
  let mut all : Array RowSpec := #[]
  for (b, e) in windows do
    if !Nat.blt b e then
      .error s!"ecmarkup: the clause window starting at byte {b} is empty or reversed"
    all := all ++ (← windowRows bs b e)
  let sorted := all.qsort (fun x y => x.sortKey < y.sortKey)
  let mut duplicates : Array String := #[]
  for i in [1:sorted.size] do
    if (sorted.getD i default).id == (sorted.getD (i - 1) default).id then
      duplicates := duplicates.push (sorted.getD i default).id
  if !duplicates.isEmpty then
    .error s!"ecmarkup: duplicate row id(s): {duplicates.toList}"
  for r in sorted do
    if !Nat.blt r.b r.e then
      .error s!"ecmarkup: the span of {r.id} at byte {r.b} is empty or reversed"
  return sorted

/-! ## Resolving a clause window from its id

`census/<key>/sections.tsv` names root clause ids; the executable resolves each
to its byte window here. Each id must occur exactly once as an
`<emu-clause id=…>` in the pinned bytes. This is the one function that reads
the whole file rather than a window, so it uses the same
occurrence-and-match-close shape `Gates.Census.scanOps` uses for `<div>`. -/

private def matchCloseAux (opens closes : Array Nat) (closeLen : Nat) (oi ci depth : Nat) :
    Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    match closes[ci]? with
    | none => none
    | some cv =>
      match opens[oi]? with
      | some ov =>
        if Nat.blt ov cv then matchCloseAux opens closes closeLen (oi + 1) ci (depth + 1) fuel
        else if depth == 0 then some (cv + closeLen)
        else matchCloseAux opens closes closeLen oi (ci + 1) (depth - 1) fuel
      | none =>
        if depth == 0 then some (cv + closeLen)
        else matchCloseAux opens closes closeLen oi (ci + 1) (depth - 1) fuel

private def firstIndexAfter (xs : Array Nat) (bound : Nat) : Nat := Id.run do
  let mut i := 0
  for x in xs do
    if Nat.blt bound x then return i
    i := i + 1
  return i

/-- The byte window of the `<emu-clause>` whose `id` is `clauseId`, which must
occur exactly once in `bs`. -/
def rootWindow (bs : ByteArray) (clauseId : String) : Except String (Nat × Nat) := Id.run do
  let clauseOpen := "<emu-clause".toUTF8
  let clauseClose := "</emu-clause>".toUTF8
  let opens := occurrencesIn bs clauseOpen 0 bs.size 4096
  let closes := occurrencesIn bs clauseClose 0 bs.size 4096
  if Nat.ble 4096 opens.size || Nat.ble 4096 closes.size then
    return .error s!"ecmarkup: the <emu-clause> scan reached its 4096 occurrence cap; a cap hit is an error, never a truncation"
  let gt := ByteArray.mk #[0x3e]
  let mut found : Array Nat := #[]
  for i in opens do
    match findIn bs gt i bs.size with
    | none => return .error s!"ecmarkup: unterminated <emu-clause> tag at byte {i}"
    | some tagE =>
      if (attrValue? bs i (tagE + 1) "id").getD "" == clauseId then found := found.push i
  if found.size != 1 then
    return .error s!"ecmarkup: the clause id {clauseId} occurs {found.size} time(s) as an <emu-clause id>; the census requires exactly one"
  let b := found.getD 0 0
  let oi := firstIndexAfter opens b
  let ci := firstIndexAfter closes b
  match matchCloseAux opens closes clauseClose.size oi ci 0 (opens.size + closes.size + 1) with
  | none => return .error s!"ecmarkup: the <emu-clause> at byte {b} is never closed"
  | some e => return .ok (b, e)

end Gates.Ecmarkup
