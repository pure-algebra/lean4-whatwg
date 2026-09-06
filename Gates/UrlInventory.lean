import Gates.Census

/-!
Byte-oriented lexical inventory of the pinned URL Bikeshed source.
Interface/assurance owner: `docs/URL-INVENTORY-INTERFACE.md`.
This is tooling, not URL semantics or a specification coverage denominator.
Every loop is bounded by the input size; exhausted scans report an error.
-/

namespace Gates.UrlInventory

open Gates.Census

inductive TokenKind where
  | text | comment | tag
  deriving Repr, BEq, DecidableEq, Inhabited

structure Token where
  kind : TokenKind
  b : Nat
  e : Nat
  name : String := ""
  closing : Bool := false
  selfClosing : Bool := false
  attrs : Array (String × String) := #[]
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Kind where
  | definition | algorithm | idl | prose | table | list | heading
  deriving Repr, BEq, DecidableEq, Inhabited

structure Entry where
  kind : Kind
  b : Nat
  e : Nat
  label : String
  «section» : String
  deriving Repr, BEq, DecidableEq, Inhabited

private def space (n : Nat) : Bool :=
  n == 0x20 || n == 0x09 || n == 0x0a || n == 0x0c || n == 0x0d

private def normalize (s : String) : String :=
  normalizeWhitespace (s.map fun c => if c.toNat == 0x0c then ' ' else c)

private def asciiLetter (n : Nat) : Bool :=
  (0x41 ≤ n && n ≤ 0x5a) || (0x61 ≤ n && n ≤ 0x7a)

private def nameByte (n : Nat) : Bool :=
  asciiLetter n || (0x30 ≤ n && n ≤ 0x39) || n == 0x2d || n == 0x3a || n == 0x5f

private def advance (bs : ByteArray) (start : Nat) (p : Nat → Bool) : Nat := Id.run do
  let mut i := start
  for _ in [start:bs.size] do
    if !p (byteNat bs i) then return i
    i := i + 1
  return i

private def textAt (bs : ByteArray) (b e : Nat) : String :=
  (sliceString? bs b e).getD ""

private def parseTag (bs : ByteArray) (b : Nat) : Except String Token := do
  let closing := byteNat bs (b + 1) == 0x2f
  let start := b + if closing then 2 else 1
  if !asciiLetter (byteNat bs start) then throw s!"invalid tag name at byte {b}"
  let nameEnd := advance bs start nameByte
  let name := (textAt bs start nameEnd).toLower
  let mut i := nameEnd
  let mut attrs := #[]
  for _ in [0:bs.size + 1] do
    let beforeSpace := i
    i := advance bs i space
    if i ≥ bs.size then throw s!"unclosed tag at byte {b}"
    if byteNat bs i == 0x3e then
      return { kind := .tag, b, e := i + 1, name, closing, attrs }
    if byteNat bs i == 0x2f && byteNat bs (i + 1) == 0x3e && !closing then
      return { kind := .tag, b, e := i + 2, name, closing, selfClosing := true, attrs }
    if closing then throw s!"closing tag has attributes at byte {b}"
    if i == beforeSpace then throw s!"missing attribute separator at byte {i}"
    let a := i
    i := advance bs i nameByte
    if i == a then throw s!"invalid attribute name at byte {i}"
    let key := (textAt bs a i).toLower
    if attrs.any (fun kv => kv.1 == key) then throw s!"duplicate attribute {key} at byte {a}"
    let afterName := i
    i := advance bs i space
    if byteNat bs i != 0x3d then
      attrs := attrs.push (key, "")
      i := afterName
    else
      i := advance bs (i + 1) space
      let q := byteNat bs i
      if q == 0x22 || q == 0x27 then
        let v := i + 1
        i := advance bs v (· != q)
        if i ≥ bs.size then throw s!"unclosed quoted attribute at byte {v}"
        attrs := attrs.push (key, textAt bs v i)
        i := i + 1
      else
        let v := i
        i := advance bs i (fun n => !space n && n != 0x3e)
        if i == v then throw s!"missing attribute value at byte {v}"
        for j in [v:i] do
          if [0, 0x22, 0x27, 0x3c, 0x3d, 0x60].contains (byteNat bs j) then
            throw s!"invalid bare attribute value at byte {j}"
        attrs := attrs.push (key, textAt bs v i)
  throw s!"tag scan did not terminate at byte {b}"

private def rawTextClose (bs : ByteArray) (start : Nat) : Except String Token := do
  for i in [start:bs.size] do
    if byteNat bs i == 0x3c && (textAt bs i (i + 5)).toLower == "</xmp" &&
        (space (byteNat bs (i + 5)) || byteNat bs (i + 5) == 0x3e) then
      return ← parseTag bs i
  throw s!"unclosed raw xmp content at byte {start}"

/-- Lex the whole UTF-8 input, preserving text and comments as partition members. -/
def tokenize (bs : ByteArray) : Except String (Array Token) := do
  if (String.fromUTF8? bs).isNone then throw "input is not UTF-8"
  let mut i := 0
  let mut out := #[]
  for _ in [0:bs.size + 1] do
    if i == bs.size then return out
    if matchesAt bs "<!--".toUTF8 i then
      let some e := findFrom bs "-->".toUTF8 (i + 4)
        | throw s!"unclosed comment at byte {i}"
      out := out.push { kind := .comment, b := i, e := e + 3 }
      i := e + 3
    else if byteNat bs i == 0x3c then
      let tag ← parseTag bs i
      out := out.push tag
      i := tag.e
      if tag.name == "xmp" && !tag.closing && !tag.selfClosing then
        let closing ← rawTextClose bs i
        if i < closing.b then out := out.push { kind := .text, b := i, e := closing.b }
        out := out.push closing
        i := closing.e
    else
      let e := advance bs i (· != 0x3c)
      out := out.push { kind := .text, b := i, e }
      i := e
  throw "token scan did not consume the entire input"

/-- Exact adjacent, nonempty spans starting at zero and ending at `size`. -/
def checkPartition (size : Nat) (tokens : Array Token) : Bool := Id.run do
  let mut previous := 0
  for t in tokens do
    if t.b != previous || t.e ≤ t.b || size < t.e then return false
    previous := t.e
  return previous == size

private def attr (t : Token) (name : String) : String :=
  ((t.attrs.find? (·.1 == name)).map (·.2)).getD ""

private def hasAttr (t : Token) (name : String) : Bool := t.attrs.any (·.1 == name)

private def heading (name : String) : Bool :=
  ["h1", "h2", "h3", "h4", "h5", "h6"].contains name

private def container (name : String) : Bool :=
  heading name || ["dfn", "div", "table", "ol", "ul", "dl", "pre", "xmp"].contains name

private def block (name : String) : Bool :=
  heading name ||
    ["address", "article", "aside", "blockquote", "body", "caption", "center", "colgroup",
      "dd", "details", "dialog", "dir", "div", "dl", "dt", "fieldset", "figcaption",
      "figure", "footer", "form", "head", "header", "hgroup", "hr", "html", "li", "listing",
      "main", "menu", "nav", "ol", "p", "pre", "search", "section", "summary", "table",
      "tbody", "td", "tfoot", "th", "thead", "tr", "ul", "xmp"].contains name

/-- Stack only the containers whose end tags are mandatory for this inventory. -/
private def closeMap (tokens : Array Token) : Except String (Array Nat) := do
  let mut stack : List (String × Nat) := []
  let mut ends := Array.replicate tokens.size 0
  for i in [:tokens.size] do
    let t := tokens[i]!
    if t.kind != .tag || !container t.name then continue
    if t.selfClosing then
      ends := ends.set! i i
    else if t.closing then
      match stack with
      | (name, j) :: rest =>
        if name != t.name then throw s!"crossed {name}/{t.name} containers at byte {t.b}"
        ends := ends.set! j i
        stack := rest
      | [] => throw s!"unmatched closing {t.name} at byte {t.b}"
    else stack := (t.name, i) :: stack
  match stack with
  | [] => return ends
  | (name, i) :: _ => throw s!"unclosed {name} at byte {(tokens[i]!).b}"

private def visible (bs : ByteArray) (tokens : Array Token) (b e : Nat) : String := Id.run do
  let mut out := ""
  for t in tokens do
    if t.b ≥ e then break
    if t.kind == .text && b < t.e then
      out := out ++ textAt bs (max b t.b) (min e t.e)
  return normalize out

private def definitionLabel (bs : ByteArray) (tokens : Array Token) (ends : Array Nat)
    (i : Nat) : String := Id.run do
  let t := tokens[i]!
  let id := attr t "id"
  if !id.isEmpty then return id
  let owner := normalize (attr t "for")
  let lt := normalize ((attr t "lt").splitOn "|" |>.headD "")
  let label := if lt.isEmpty then visible bs tokens t.e (tokens[ends[i]!]!).b else lt
  return (if owner.isEmpty then "" else owner ++ "/") ++ label

private def trimEnd (bs : ByteArray) (b e : Nat) : Nat := Id.run do
  let mut j := e
  for _ in [b:e] do
    if !space (byteNat bs (j - 1)) then return j
    j := j - 1
  return j

private def withoutAttributes (s : String) : String := Id.run do
  let mut chars := s.toList
  for _ in [:s.length + 1] do
    chars := chars.dropWhile Char.isWhitespace
    if chars.head? != some '[' then return String.ofList chars
    let after := chars.dropWhile (· != ']')
    if after.isEmpty then return ""
    chars := after.drop 1
  return ""

/-- The last semicolon must not be the terminator of an encoded character reference. -/
private def statementEnd (s : String) : Bool := Id.run do
  if !s.endsWith ";" then return false
  let back := s.toList.reverse.drop 1
  let rest := back.dropWhile (fun c => c.isAlphanum || c == '#')
  return rest.head? != some '&'

private def idlName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | first :: rest =>
    (asciiLetter first.toNat || first == '_') && rest.all (fun c =>
      asciiLetter c.toNat || (0x30 ≤ c.toNat && c.toNat ≤ 0x39) || c == '_' || c == '-')

private def interfaceHeader (s : String) : Bool :=
  let normalized := normalize ((withoutAttributes s).replace ":" " : " |>.replace "{" " { ")
  let words := normalized.splitOn " "
  match words with
  | ["interface", name, "{"] => idlName name
  | ["interface", name, ":", parent, "{"] => idlName name && idlName parent
  | _ => false

private def scanIdl (bs : ByteArray) (b e : Nat) (sectionId : String) :
    Except String (Array Entry) := do
  let mut cursor := b
  let mut start : Option Nat := none
  let mut opened := false
  let mut out := #[]
  for _ in [b:e + 1] do
    if cursor ≥ e then break
    let stop := min e (advance bs cursor (· != 0x0a))
    let a := min stop (advance bs cursor space)
    let z := trimEnd bs a stop
    if a < z then
      let first := start.getD a
      start := some first
      let label := normalize (textAt bs first z)
      if label == "};" then
        if !opened then throw s!"stray IDL interface close at byte {first}"
        opened := false
        start := none
      else if label.endsWith "{" then
        if opened || !interfaceHeader label then
          throw s!"unsupported IDL header at byte {first}: {label}"
        out := out.push { kind := .idl, b := first, e := z, label, «section» := sectionId }
        opened := true
        start := none
      else if statementEnd label then
        if !opened || label.endsWith "};" then
          throw s!"unsupported or unterminated IDL statement at byte {first}: {label}"
        out := out.push { kind := .idl, b := first, e := z, label, «section» := sectionId }
        start := none
    cursor := stop + 1
  if opened || start.isSome then throw s!"unfinished IDL block at byte {b}"
  return out

private def kindOrder : Kind → Nat
  | .definition => 0 | .algorithm => 1 | .idl => 2 | .prose => 3
  | .table => 4 | .list => 5 | .heading => 6

/-- All lexical candidates in source order. Classification and semantic spans come later. -/
def scan (bs : ByteArray) : Except String (Array Entry) := do
  let tokens ← tokenize bs
  if !checkPartition bs.size tokens then throw "token partition is invalid"
  let ends ← closeMap tokens
  let mut sectionId := ""
  let mut out := #[]
  for i in [:tokens.size] do
    let t := tokens[i]!
    if t.kind != .tag || t.closing then continue
    let last := tokens[ends[i]!]!
    if heading t.name then
      sectionId := attr t "id"
      out := out.push {
        kind := .heading, b := t.b, e := last.e,
        label := visible bs tokens t.e last.b, «section» := sectionId }
    if t.name == "dfn" then
      out := out.push {
        kind := .definition, b := t.b, e := last.e,
        label := definitionLabel bs tokens ends i, «section» := sectionId }
    if t.name == "div" && hasAttr t "algorithm" then
      let mut label := attr t "algorithm"
      if label.isEmpty then label := attr t "id"
      if label.isEmpty then
        for j in [i + 1:ends[i]!] do
          let d := tokens[j]!
          if d.kind == .tag && d.name == "dfn" && !d.closing then
            label := definitionLabel bs tokens ends j
            break
      out := out.push { kind := .algorithm, b := t.b, e := last.e, label, «section» := sectionId }
    if ["table", "ol", "ul", "dl"].contains t.name then
      out := out.push {
        kind := if t.name == "table" then .table else .list,
        b := t.b, e := last.e, label := t.name, «section» := sectionId }
    if t.name == "p" then
      let mut e := bs.size
      let mut contentEnd := e
      for j in [i + 1:tokens.size] do
        let next := tokens[j]!
        if next.kind == .tag && block next.name then
          contentEnd := next.b
          e := if next.name == "p" && next.closing then next.e else next.b
          break
      out := out.push {
        kind := .prose, b := t.b, e,
        label := visible bs tokens t.e contentEnd, «section» := sectionId }
    if ["pre", "xmp"].contains t.name &&
        ((normalize (attr t "class")).splitOn " ").contains "idl" then
      let rows ← scanIdl bs t.e last.b sectionId
      out := out ++ rows
  return out.qsort fun a b =>
    a.b < b.b || (a.b == b.b && kindOrder a.kind < kindOrder b.kind)

private def kindName : Kind → String
  | .definition => "definition" | .algorithm => "algorithm" | .idl => "idl"
  | .prose => "prose" | .table => "table" | .list => "list" | .heading => "heading"

private def inputPath := "vendor/whatwg-url-55d66993/url.bs"
private def inputDigest := "a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805"
private def outputPath := "generated/url-source-inventory.tsv"

private def generate (root : System.FilePath) : IO String := do
  let bs ← IO.FS.readBinFile (root / inputPath)
  let digest := Gates.Sha256.hexDigest bs
  if digest != inputDigest then
    throw <| IO.userError s!"input digest {digest} differs from pinned {inputDigest}"
  let lift {α : Type} : Except String α → IO α
    | .ok x => pure x
    | .error err => throw <| IO.userError err
  let tokens ← lift (tokenize bs)
  if !checkPartition bs.size tokens then throw <| IO.userError "token partition is invalid"
  let entries ← lift (scan bs)
  let expected : Array (Kind × Nat) :=
    #[(.definition, 208), (.algorithm, 72), (.idl, 29), (.prose, 946), (.table, 9),
      (.list, 174), (.heading, 35)]
  let mut errors : Array String := #[]
  let tags := (tokens.filter (·.kind == .tag)).size
  if tags != 9159 then errors := errors.push s!"{tags} tags; expected 9159"
  for (kind, n) in expected do
    let count := (entries.filter (·.kind == kind)).size
    if count != n then errors := errors.push s!"{kindName kind}: {count}; expected {n}"
  for row in entries do
    if row.e ≤ row.b || bs.size < row.e then
      errors := errors.push s!"invalid {kindName row.kind} span [{row.b},{row.e})"
    if (row.kind == .definition || row.kind == .algorithm) && row.label.isEmpty then
      errors := errors.push s!"unnamed {kindName row.kind} at byte {row.b}"
  unless errors.isEmpty do throw <| IO.userError ("\n".intercalate errors.toList)
  let mut out := s!"#url-source-inventory format=1 generator=Gates.UrlInventory " ++
    s!"input={inputPath} input-sha256={inputDigest} tokens={tokens.size} " ++
    s!"tags={tags} candidates={entries.size} regenerate=lake exe urlinventory --write\n" ++
    "#ordinal\tkind\tbyte-start\tbyte-end\tspan-sha256\tlabel\tsection\n"
  for i in [:entries.size] do
    let row := entries[i]!
    let hash := Gates.Sha256.hexDigest (bs.extract row.b row.e)
    out := out ++ s!"{i + 1}\t{kindName row.kind}\t{row.b}\t{row.e}\t{hash}\t" ++
      s!"{escapeField row.label}\t{escapeField row.section}\n"
  return out

private def checkOrWrite (root : System.FilePath) (write : Bool) : IO UInt32 := do
  let expected ← generate root
  let path := root / outputPath
  if write then
    IO.FS.createDirAll (root / "generated")
    IO.FS.writeBinFile path expected.toUTF8
    IO.println s!"WROTE {outputPath}"
    IO.println "PASS URL inventory: pinned bytes, token partition, and fixed-pin candidate checks"
    return 0
  if !(← path.pathExists) then throw <| IO.userError s!"missing projection {outputPath}"
  let actual ← IO.FS.readBinFile path
  if actual == expected.toUTF8 then
    IO.println "PASS URL inventory: pinned bytes, full token partition, 1473 source candidates; projection is byte-identical"
    return 0
  IO.eprintln s!"FAIL URL inventory: projection drift in {outputPath}"
  let actualLines := (String.fromUTF8! actual).splitOn "\n" |>.toArray
  let expectedLines := expected.splitOn "\n" |>.toArray
  for i in [:max actualLines.size expectedLines.size] do
    if actualLines[i]? != expectedLines[i]? then
      IO.eprintln s!"  line {i + 1} stored: {actualLines[i]?}"
      IO.eprintln s!"  line {i + 1} expected: {expectedLines[i]?}"
  return 1

/-- Audited CLI used by the wrapper; generation never supplies semantic coverage states. -/
def cli (args : List String) : IO UInt32 := do
  try
    let root ← Gates.Common.projectRoot
    match args with
    | [] => checkOrWrite root false
    | ["--write"] => checkOrWrite root true
    | _ =>
      IO.eprintln "usage: lake exe urlinventory [--write]"
      return 2
  catch err =>
    IO.eprintln s!"FAIL URL inventory: {err}"
    return 1

end Gates.UrlInventory
