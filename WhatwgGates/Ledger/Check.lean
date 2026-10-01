import WhatwgGates.Common
import WhatwgGates.Ledger.Model
import WhatwgGates.Ledger.Render

/-!
# Gates.Ledger.Check

The reference pass and the drift check of the graph ledger
(`test/contracts/graph-ledger.contract.md`, sections 5 to 9, ruling R-W6), as
pure functions over a `World`: the facts of the built environment (the kind
of each constant, the module table) and the text of the authored files the
gate reads at run time, held as data. Nothing here does IO, declares syntax
or reads the environment itself, so a battery decides every finding on a
planted `World`.

The reference pass resolves every ground, item and recorded debt of every
cell, leaf and unrouted prefix: theorem and declaration names against the
constant table; module names against the module table; receipt and
ascription counts against the module source, counted on code text so that a
command inside a comment or a literal does not count; rulings against the
ruling bullets of `COORDINATION.md` and the graph document's rulings table;
debts against `COORDINATION.md`; register rows against
`test/counterexamples/REGISTER.md`; receipts-log headings against the graph's
receipts log; and gates against the executables `lakefile.toml` declares. It
also checks the edge tokens of every ruling against the ledger, that every
ruling naming a graph is cited or acknowledged by it, and that every graph
document links its projection. `outcome` decides a run from these findings
and the projection comparison.

What a pass does not mean is section 13 of the contract: note text, review
judgments, a ruling's wording beyond its tokens and mentions, and what a
counted command proves are not read.
-/

namespace Gates.Ledger

/-! ## The world the pass reads -/

/-- The kind of a constant of the built environment. -/
inductive ConstantKind where
  /-- A `theorem`. -/
  | thm
  /-- Any other constant. -/
  | other
  deriving DecidableEq, Repr

/-- What the reference pass reads, as data. `constantKind? n` is the kind of
the constant `n`, or `none`; `moduleBuilt m` whether `m` is a module of the
built environment; `file? p` the text of the file at the forward-slash path
`p` relative to the repository root, or `none` when it does not exist;
`projectionFiles` the sorted relative path of every regular file under
`generated/graphs/`. -/
structure World where
  constantKind? : Lean.Name → Option ConstantKind
  moduleBuilt : Lean.Name → Bool
  file? : String → Option String
  projectionFiles : List String

/-- The lines of a file, split by `Gates.Common.lines`; `[]` when the file
does not exist. -/
def World.linesOf (w : World) (path : String) : List String :=
  match w.file? path with
  | some text => Gates.Common.lines text
  | none => []

/-! ## Text helpers -/

/-- Whether `needle` occurs in `haystack` as a list of characters. -/
private def occursIn (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | c :: rest => needle.isPrefixOf (c :: rest) || occursIn needle rest

/-- Whether the non-empty text `needle` occurs in `haystack`. -/
private def containsText (haystack needle : String) : Bool :=
  !needle.isEmpty && occursIn needle.toList haystack.toList

/-- The string components of a module name, in order. -/
private def nameParts : Lean.Name → List String
  | .anonymous => []
  | .str p s => nameParts p ++ [s]
  | .num p k => nameParts p ++ [toString k]

/-- The source of a module of this package: its components joined by `/`,
with `.lean`. -/
def sourcePath (m : Lean.Name) : String :=
  String.intercalate "/" (nameParts m) ++ ".lean"

/-! ## Code text and the counting rule (contract section 6) -/

/-- An identifier character for the literal rules: a letter, a digit, `_`,
`'`, `!`, `?`, or any character above U+007F. -/
private def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '\'' || c == '!' || c == '?' || c.toNat > 0x7F

/-- A character blanked: LF and CR are kept, every other character becomes a
space. -/
private def blank (c : Char) : Char :=
  if c == '\n' || c == '\r' then c else ' '

/-- The state of the code-text scanner. Two-character delimiters are read one
character at a time: `blockOpen` and `blockClose` blank the second character
of `/-` and `-/`, `rawOpen` copies the hashes and quote of a raw-string
opener, and `rawClose` the hashes of its closer. -/
private inductive Lex where
  | code
  | lineComment
  | block (depth : Nat)
  | blockOpen (depth : Nat)
  | blockClose (depth : Nat)
  | str
  | strEscape
  | chr
  | chrEscape
  | rawOpen (hashes : Nat)
  | raw (hashes : Nat)
  | rawClose (left : Nat)

/-- The number of `#` before the `"` of a raw-string opener whose `r` has just
been read, or `none` when `rest` does not open one. -/
private def rawHashes? (rest : List Char) : Option Nat :=
  let hashes := (rest.takeWhile (· == '#')).length
  if (rest.drop hashes).head? == some '"' then some hashes else none

/-- Whether `rest` begins with `n` hashes, so that the `"` just read closes a
raw string opened with `n`. -/
private def closesRaw (n : Nat) (rest : List Char) : Bool :=
  let taken := rest.take n
  taken.length == n && taken.all (· == '#')

/-- One step of the scanner: the character emitted for `c` and the next
state. `prev` is the source character before `c`, and `rest` the source after
it. -/
private def lexStep (st : Lex) (prev : Option Char) (c : Char) (rest : List Char) : Char × Lex :=
  match st with
  | .code =>
    if c == '-' && rest.head? == some '-' then (' ', .lineComment)
    else if c == '/' && rest.head? == some '-' then (' ', .blockOpen 1)
    else if c == '"' then (c, .str)
    else
      let afterIdent := match prev with
        | some p => isIdentChar p
        | none => false
      if c == '\'' && !afterIdent then (c, .chr)
      else if c == 'r' && !afterIdent then
        match rawHashes? rest with
        | some n => (c, .rawOpen n)
        | none => (c, .code)
      else (c, .code)
  | .lineComment => if c == '\n' then (c, .code) else (blank c, .lineComment)
  | .blockOpen depth => (blank c, .block depth)
  | .block depth =>
    if c == '/' && rest.head? == some '-' then (' ', .blockOpen (depth + 1))
    else if c == '-' && rest.head? == some '/' then (' ', .blockClose (depth - 1))
    else (blank c, .block depth)
  | .blockClose depth => (blank c, if depth == 0 then .code else .block depth)
  | .str =>
    if c == '\\' then (' ', .strEscape)
    else if c == '"' then (c, .code)
    else (blank c, .str)
  | .strEscape => (blank c, .str)
  | .chr =>
    if c == '\\' then (' ', .chrEscape)
    else if c == '\'' then (c, .code)
    else (blank c, .chr)
  | .chrEscape => (blank c, .chr)
  | .rawOpen n => if c == '"' then (c, .raw n) else (c, .rawOpen n)
  | .raw n =>
    if c == '"' && closesRaw n rest then (c, if n == 0 then .code else .rawClose n)
    else (blank c, .raw n)
  | .rawClose left => (c, if left ≤ 1 then .code else .rawClose (left - 1))

/-- The scanner over the remaining source, accumulating the code text. -/
private def lexFrom (st : Lex) (prev : Option Char) (acc : String) : List Char → String
  | [] => acc
  | c :: rest =>
    let (out, next) := lexStep st prev c rest
    lexFrom next (some c) (acc.push out) rest

/-- The lines of a module source's code text: every character of a comment
(docstrings and module documentation included, delimiters too) and every
character inside a string, character or raw-string literal (delimiters kept)
is replaced by a space, except LF and CR, so lines and columns are unchanged;
the text is then split by `Gates.Common.lines`. -/
def codeLines (source : String) : List String :=
  Gates.Common.lines (lexFrom .code none "" source.toList)

/-- Whether a code line continues the freeze command above it: it is empty or
begins with a space or a tab. -/
private def continuesCommand (line : String) : Bool :=
  match line.toList with
  | [] => true
  | c :: _ => c == ' ' || c == '\t'

/-- The text after the first `(`, or `none`. -/
private def afterOpen : List Char → Option (List Char)
  | [] => none
  | c :: rest => if c == '(' then some rest else afterOpen rest

/-- The text after the `)` that closes a `(` already read at `depth` open
parentheses beyond the first, or `none` when it is never closed. -/
private def afterClose (depth : Nat) : List Char → Option (List Char)
  | [] => none
  | c :: rest =>
    if c == '(' then afterClose (depth + 1) rest
    else if c == ')' then
      match depth with
      | 0 => some rest
      | d + 1 => afterClose d rest
    else afterClose depth rest

/-- Whether a freeze command's code text carries an `axioms` clause: after the
parenthesis that closes the first `(` following `#whatwg_freeze `, and after
any whitespace, the text begins with `axioms` followed by a character that is
not an identifier character, or by nothing. -/
private def carriesAxiomsClause (command : List Char) : Bool :=
  match afterOpen command with
  | none => false
  | some inner =>
    match afterClose 0 inner with
    | none => false
    | some tail =>
      let tail := tail.dropWhile fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r'
      "axioms".toList.isPrefixOf tail &&
        match tail.drop 6 with
        | [] => true
        | c :: _ => !isIdentChar c

/-- The freeze-command spelling a receipt or an ascription begins with. -/
private def freezeLead : String := "#whatwg_freeze "

/-- The receipts among code lines: a line beginning `#print axioms`, or a
freeze command, with its continuation lines, carrying an `axioms` clause. -/
private def countReceipts : List String → Nat
  | [] => 0
  | line :: rest =>
    let here :=
      if line.startsWith "#print axioms" then 1
      else if line.startsWith freezeLead then
        let command := line :: rest.takeWhile continuesCommand
        if carriesAxiomsClause (Gates.Common.dropChars (String.intercalate "\n" command)
            freezeLead.length).toList then 1 else 0
      else 0
    here + countReceipts rest

/-- The count of receipt commands in a module source: the `#print axioms`
commands and the `#whatwg_freeze` commands with an `axioms` clause, each
beginning its line of code text. -/
def receiptCount (source : String) : Nat :=
  countReceipts (codeLines source)

/-- The count of ascription commands in a module source: the lines of code
text beginning `#check (@` or `#whatwg_freeze (@`. -/
def ascriptionCount (source : String) : Nat :=
  ((codeLines source).filter fun line =>
    line.startsWith "#check (@" || line.startsWith "#whatwg_freeze (@").length

/-! ## Rulings, debts and register rows -/

/-- Whether ruling `id` is recorded: a ruling bullet of `COORDINATION.md` (a
line beginning `- `, the identifier and a space), or a row of the graph
document's rulings table (a line of `document` beginning ``| `id` |``). -/
def rulingPresent (w : World) (document : List String) (id : String) : Bool :=
  (w.linesOf "COORDINATION.md").any (·.startsWith ("- " ++ id ++ " ")) ||
    document.any (·.startsWith ("| `" ++ id ++ "` |"))

/-- Whether debt `id` is recorded: a line of `COORDINATION.md` contains `(id)`. -/
def debtPresent (w : World) (id : String) : Bool :=
  (w.linesOf "COORDINATION.md").any fun line => containsText line ("(" ++ id ++ ")")

/-- The status of register row `id`: the first line of
`test/counterexamples/REGISTER.md` that begins ``| `id` | ` ``, read after that
lead up to the next backtick; `none` when no line does. -/
def rowStatus? (w : World) (id : String) : Option String :=
  let lead := "| `" ++ id ++ "` | `"
  ((w.linesOf "test/counterexamples/REGISTER.md").find? (·.startsWith lead)).map fun line =>
    String.ofList ((Gates.Common.dropChars line lead.length).toList.takeWhile (· != '`'))

/-- The findings of a row range cited with a status: each row that does not
exist, and each whose status differs. -/
def rowFindings (w : World) (r : RowRange) (s : RowStatus) : List String :=
  r.ids.filterMap fun id =>
    match rowStatus? w id with
    | none => some ("register row " ++ id ++ " does not exist")
    | some actual =>
      if actual == s.text then none
      else some ("register row " ++ id ++ " is " ++ actual ++ ", not " ++ s.text)

/-! ## Grounds and items -/

/-- The findings of a count ground: the module is built, its source exists,
and the source holds exactly `count` commands of the kind `noun` names. -/
private def countFindings (w : World) (m : Lean.Name) (count : Nat) (noun : String)
    (counter : String → Nat) : List String :=
  if !w.moduleBuilt m then [toString m ++ " is not a built module"]
  else
    match w.file? (sourcePath m) with
    | none => [toString m ++ " has no source " ++ sourcePath m]
    | some source =>
      let found := counter source
      if found == count then []
      else [toString m ++ " holds " ++ toString found ++ " " ++ noun ++ ", not " ++ toString count]

/-- The findings of one ground, given the lines of the graph document (its
rulings table) and of the graph's receipts log. -/
def groundFindings (w : World) (document receiptsLog : List String) : Ground → List String
  | .theorems ns => ns.filterMap fun n =>
    match w.constantKind? n with
    | some .thm => none
    | some .other => some (toString n ++ " is not a theorem")
    | none => some (toString n ++ " names no constant")
  | .declarations ns => ns.filterMap fun n =>
    if (w.constantKind? n).isSome then none else some (toString n ++ " names no constant")
  | .receipts m count => countFindings w m count "receipts" receiptCount
  | .ascriptions m count => countFindings w m count "ascriptions" ascriptionCount
  | .modules ms => ms.filterMap fun m =>
    if w.moduleBuilt m then none else some (toString m ++ " is not a built module")
  | .gate g =>
    match g.executable? with
    | none => []
    | some exe =>
      if containsText ((w.file? "lakefile.toml").getD "") ("name = \"" ++ exe ++ "\"") then []
      else ["executable " ++ exe ++ " is not declared in lakefile.toml"]
  | .ruling id => if rulingPresent w document id then [] else ["ruling " ++ id ++ " is not recorded"]
  | .receipt heading =>
    if receiptsLog.any (fun line =>
        line.startsWith ("## " ++ heading) || line.startsWith ("### " ++ heading)) then []
    else ["receipts log has no heading \"" ++ heading ++ "\""]
  | .rows r s => rowFindings w r s
  | .edge _ _ => []

/-- The findings of one open item, or of one recorded debt checked as a
`debt` item. -/
def itemFindings (w : World) : Item → List String
  | .named label => if label.isEmpty then ["an open item has no name"] else []
  | .debt id => if debtPresent w id then [] else ["debt " ++ id ++ " is not recorded"]
  | .rows r s => rowFindings w r s
  | .wanted n =>
    if (w.constantKind? n).isSome then
      ["wanted theorem " ++ toString n ++ " now exists; review the edge"]
    else []
  | .edge _ _ => []

/-! ## Rulings: edge tokens and mentions (contract section 7) -/

/-- The identifier of a ruling line, one beginning `- R-`: the text from its
third character to the first space. -/
def rulingId? (line : String) : Option String :=
  if line.startsWith "- R-" then
    some (String.ofList ((line.toList.drop 2).takeWhile (· != ' ')))
  else none

/-- Every ruling line paired with each ledger graph whose identifier or
document path occurs in it, as `(ruling, graph)`. -/
def rulingMentions (coordination : List String) (graphs : List Graph) : List (String × String) :=
  coordination.flatMap fun line =>
    match rulingId? line with
    | none => []
    | some id => graphs.filterMap fun g =>
      if containsText line g.id || containsText line g.document then some (id, g.id) else none

/-- An edge token of a ruling, the code span `GRAPH-ID/edge=status`. -/
structure EdgeToken where
  ruling : String
  graph : String
  edge : Edge
  status : Status
  deriving DecidableEq, Repr

/-- The odd-numbered pieces of a list, counting from zero. -/
private def oddPieces : List String → List String
  | _ :: b :: rest => b :: oddPieces rest
  | _ => []

/-- The code spans of a line: the odd-numbered pieces between backticks. -/
def codeSpans (line : String) : List String :=
  oddPieces (line.splitOn "`")

/-- The status a `Status.text` spells. -/
def parseStatus? (s : String) : Option Status :=
  [Status.requiredOpen, .requiredClosed, .notApplicable].find? (·.text == s)

/-- The token a code span of ruling `rid` is, if it splits at its one `/` and
then at its one `=` into a known edge label and a known status text. -/
private def spanToken? (rid span : String) : Option EdgeToken :=
  match span.splitOn "/" with
  | [graph, rest] =>
    match rest.splitOn "=" with
    | [edgeText, statusText] =>
      match Edge.all.find? (·.label == edgeText), parseStatus? statusText with
      | some e, some s => some { ruling := rid, graph, edge := e, status := s }
      | _, _ => none
    | _ => none
  | _ => none

/-- Every edge token of every ruling line, in file order and, within a line,
in order. -/
def edgeTokens (coordination : List String) : List EdgeToken :=
  coordination.flatMap fun line =>
    match rulingId? line with
    | none => []
    | some rid => (codeSpans line).filterMap (spanToken? rid)

/-- The latest token of each graph edge, in the order the latest ones occur:
a later token supersedes an earlier one for the same graph and edge. -/
def latestTokens (ts : List EdgeToken) : List EdgeToken :=
  ts.foldl (fun acc t => acc.filter (fun u => !(u.graph == t.graph && u.edge == t.edge)) ++ [t]) []

/-- The findings of the latest edge tokens against the ledger: the graph is in
the ledger, the cell's status is the token's, and the cell cites the ruling. -/
def tokenFindings (l : Ledger) (ts : List EdgeToken) : List String :=
  (latestTokens ts).flatMap fun t =>
    let named := t.graph ++ "/" ++ t.edge.label
    match l.graphs.find? (·.id == t.graph) with
    | none => ["ruling " ++ t.ruling ++ " names " ++ named ++ ", which is not in the ledger"]
    | some g =>
      let c := g.edges.get t.edge
      (if c.status == t.status then []
       else ["ruling " ++ t.ruling ++ " records " ++ named ++ "=" ++ t.status.text ++
         "; the ledger says " ++ c.status.text]) ++
      (if c.grounds.contains (.ruling t.ruling) then []
       else ["ruling " ++ t.ruling ++ " records " ++ named ++ "; that cell does not cite it"])

/-- The rulings a graph cites or acknowledges: `acknowledged`, then the
`ruling` grounds of its cells in `Edge.all` order. -/
def Graph.citedRulings (g : Graph) : List String :=
  g.acknowledged ++ Edge.all.flatMap fun e =>
    (g.edges.get e).grounds.filterMap fun
      | .ruling id => some id
      | _ => none

/-! ## Graphs, leaves and unrouted prefixes -/

/-- The findings of one cell of a graph, each prefixed `<GRAPH-ID> <edge>: `:
every ground finding, every item finding and every recorded-debt finding. -/
private def cellReferenceFindings (w : World) (document receiptsLog : List String) (g : Graph)
    (e : Edge) : List String :=
  let c := g.edges.get e
  let found := c.grounds.flatMap (groundFindings w document receiptsLog) ++
    c.remaining.flatMap (itemFindings w) ++
    c.debts.flatMap fun d => itemFindings w (.debt d)
  found.map fun f => g.id ++ " " ++ e.label ++ ": " ++ f

/-- The findings of one graph against the world (contract section 5.4): its
document, receipts log and projection link, its fence, every cell, then each
ruling that names it and that it neither cites nor acknowledges. -/
def graphFindings (w : World) (l : Ledger) (g : Graph) : List String :=
  let documentText := w.file? g.document
  let missingDocument :=
    if documentText.isNone then [g.id ++ ": document " ++ g.document ++ " does not exist"] else []
  let missingLog :=
    if (w.file? g.receiptsLog).isNone then
      [g.id ++ ": receipts log " ++ g.receiptsLog ++ " does not exist"]
    else []
  let unlinked := match documentText with
    | some text =>
      if containsText text g.projection then []
      else [g.id ++ ": document " ++ g.document ++ " does not link " ++ g.projection]
    | none => []
  let fence := g.fence.filterMap fun m =>
    if w.moduleBuilt m then none
    else some (g.id ++ ": fence module " ++ toString m ++ " is not a built module")
  let document := w.linesOf g.document
  let receiptsLog := w.linesOf g.receiptsLog
  let cells := Edge.all.flatMap (cellReferenceFindings w document receiptsLog g)
  let cited := g.citedRulings
  let mentions := (rulingMentions (w.linesOf "COORDINATION.md") l.graphs).filterMap
    fun (ruling, named) =>
      if named == g.id && !cited.contains ruling then
        some (g.id ++ ": ruling " ++ ruling ++
          " names this graph and the ledger neither cites nor acknowledges it")
      else none
  missingDocument ++ missingLog ++ unlinked ++ fence ++ cells ++ mentions

/-- The findings of one leaf record: its document exists and names the leaf,
its declarations are constants, and its receipts resolve, with the leaf's
document as the rulings table and no receipts log. -/
def leafFindings (w : World) (leaf : Leaf) : List String :=
  let documentFindings := match w.file? leaf.document with
    | none => [leaf.id ++ ": document " ++ leaf.document ++ " does not exist"]
    | some text =>
      if containsText text leaf.id then []
      else [leaf.id ++ ": document " ++ leaf.document ++ " does not name the leaf"]
  let declarationFindings := leaf.declarations.filterMap fun n =>
    if (w.constantKind? n).isSome then none
    else some (leaf.id ++ ": " ++ toString n ++ " names no constant")
  let document := w.linesOf leaf.document
  let receiptFindings := (leaf.receipts.flatMap (groundFindings w document [])).map
    fun f => leaf.id ++ ": " ++ f
  documentFindings ++ declarationFindings ++ receiptFindings

/-- The findings of one unrouted prefix: it is a built module, and the debt or
ruling that records it is recorded. -/
def unroutedFindings (w : World) (u : Unrouted) : List String :=
  let label := "unrouted " ++ toString u.modulePrefix ++ ": "
  (if w.moduleBuilt u.modulePrefix then [] else [label ++ "not a built module"]) ++
  (if debtPresent w u.recordedBy || rulingPresent w [] u.recordedBy then []
   else [label ++ u.recordedBy ++ " is not a recorded debt or ruling"])

/-- The canonical input every projection names in its header. -/
def ledgerInput : String := "`WhatwgTest/Ledger.lean`"

/-- The list with later repeats removed, keeping the first occurrence. -/
private def keepFirst (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The sources of the modules the count grounds of a list name, in order. -/
private def countSources (gs : List Ground) : List String :=
  gs.filterMap fun
    | .receipts m _ => some (sourcePath m)
    | .ascriptions m _ => some (sourcePath m)
    | _ => none

/-- The run-time file set (contract section 11), repeats removed keeping the
first: `COORDINATION.md`, the register and `lakefile.toml`; for each graph its
document, receipts log, projection and the source of each module a count
ground of its cells names, in edge order; for each leaf its document and the
source of each module its count grounds name. -/
def Ledger.files (l : Ledger) : List String :=
  keepFirst <|
    ["COORDINATION.md", "test/counterexamples/REGISTER.md", "lakefile.toml"] ++
    l.graphs.flatMap (fun g =>
      [g.document, g.receiptsLog, g.projection] ++
        Edge.all.flatMap fun e => countSources (g.edges.get e).grounds) ++
    l.leaves.flatMap fun leaf => leaf.document :: countSources leaf.receipts

/-- Every reference finding, in order: the structural findings, the token
findings, then the findings of every graph, leaf and unrouted prefix, in
ledger order. -/
def referenceFindings (w : World) (l : Ledger) : List String :=
  l.findings ++ tokenFindings l (edgeTokens (w.linesOf "COORDINATION.md")) ++
    l.graphs.flatMap (graphFindings w l) ++ l.leaves.flatMap (leafFindings w) ++
    l.unrouted.flatMap (unroutedFindings w)

/-- The drift findings: each graph's projection exists and is byte-identical
to a fresh rendering, and every file under `generated/graphs/` is some
graph's projection. -/
def projectionFindings (w : World) (l : Ledger) : List String :=
  (l.graphs.filterMap fun g =>
    match w.file? g.projection with
    | none => some (g.projection ++ " does not exist")
    | some text =>
      if text == g.render ledgerInput then none
      else some (g.projection ++ " differs from a fresh rendering")) ++
  w.projectionFiles.filterMap fun path =>
    if l.graphs.any (·.projection == path) then none
    else some (path ++ " is not the projection of a ledger graph")

/-! ## The outcome of a run (contract section 9) -/

/-- What a run does: its exit code, the lines it prints on standard output,
and the files it writes, as `(relative path, text)`. -/
structure Outcome where
  exitCode : UInt32
  output : List String
  writes : List (String × String)
  deriving DecidableEq, Repr

/-- The outcome of a run over `w`; with `write`, the projections are written
when there is no reference finding and are not compared. -/
def outcome (w : World) (l : Ledger) (write : Bool) : Outcome :=
  let findings := referenceFindings w l ++ (if write then [] else projectionFindings w l)
  if findings.isEmpty then
    let pass := "PASS whatwg_ledger: " ++ toString l.graphs.length ++ " graph(s), " ++
      toString (10 * l.graphs.length) ++ " edges, " ++ toString l.leaves.length ++
      " leaf record(s), " ++ toString l.unrouted.length ++
      " unrouted prefix(es); every reference resolves against the built environment and the " ++
      "authored files, and every projection is byte-identical to a fresh rendering"
    { exitCode := 0
      output := [if write then pass ++ " (written)" else pass]
      writes := if write then l.graphs.map fun g => (g.projection, g.render ledgerInput) else [] }
  else
    { exitCode := 1
      output := ("FAIL whatwg_ledger: " ++ toString findings.length ++ " finding(s)") ::
        findings.map ("  " ++ ·)
      writes := [] }

end Gates.Ledger
