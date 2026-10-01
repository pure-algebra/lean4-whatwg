import Lean.CoreM
import Lean.DeclarationRange
import Lean.ToExpr
import Lean.Util.FoldConsts
import WhatwgGates.Common
import WhatwgGates.Sha256
import WhatwgGates.Trust.Load

/-!
# Gates.DeclSnapshot

The declaration snapshot (ruling R-W5, with R-W12): one deterministic row per
public declaration of the production tree, joined to the freeze registry of
`#whatwg_freeze` and to the authored records under `test/records/`. Its
behaviour is frozen by `test/contracts/declaration-snapshot.contract.md` and
falsified by `WhatwgTest/Audit/DeclSnapshotContract.lean`, which exercises the
pure core below; `cli` is the only function that does IO.

```text
lake exe whatwg_declsnapshot            compare the projection with generated/declarations/
lake exe whatwg_declsnapshot --check    the same
lake exe whatwg_declsnapshot --write    regenerate generated/declarations/<library>.tsv
```

## What a run reads

- *The built tree*, through the shared loader `Gates.Trust` of
  `WhatwgGates/Trust/Load.lean`, never by a compile-time import of `Whatwg` or
  `WhatwgTest`: every module whose source lies under `Whatwg/` or
  `WhatwgTest/`, with the umbrella `Whatwg`, minus the modules
  `test/fixtures/trust-gate/known-red.txt` declares red. Not the closure of
  `WhatwgTest.lean`: a battery the root does not import still contributes its
  entries. A module whose `.olean` is missing, or whose Lake trace does not
  record its current source, is refused before anything is imported. The
  import does not load environment extensions, so nothing an audited module
  wrote runs in this process.
- *The walk*: for every loaded production module, every constant of its own
  `ModuleData.constNames` whose name is not internal, keyed by name and module
  (a generated constant can be realised in several modules, and each yields
  its own row). Kind, origin (`authored` when `Lean.findDeclarationRanges?`
  answers), universe count, the SHA-256 of a canonical text of its type
  (`typeText`; never `Expr.hash`) and its axiom set.
- *Entries*: every constant `<m>.frozen.<d>` of a loaded test module `m`, read
  by its name and decoded from its value (`decodeEntry`); no extension and no
  code of `#whatwg_freeze` is consulted.
- *Records*: every `test/records/<packet>.tsv` (`parseRecords`), and *census
  rows*: every `generated/*-census.tsv` (`parseCensus`), whose row ids are the
  only anchors.

## The axiom column

The set is the one `Lean.collectAxioms` computes in this process, where its
extension of precomputed module tables is not loaded and every call therefore
walks the reachable constants afresh: the axioms among the constants reachable
from the declaration, where an axiom reaches the constants of its type, a
definition, theorem or opaque those of its type and value, a constructor or
recursor those of its type, an inductive type those of its type and its
constructors, and a quotient primitive nothing. Calling `Lean.collectAxioms`
once per declaration repeats that walk for every row (23 of the design's 26 s);
this module computes the same sets in one walk with one memo, by strongly
connected components (Tarjan's algorithm on an explicit stack, bounded by
fuel), so that the cycles between an inductive type and its constructors get
one shared set. At the landing a scratch probe compared every row's set with
`Lean.collectAxioms` over the same import and found no difference; that probe
is evidence of the landing tree, not a proof of the equality.

## What a pass means

A PASS of the check mode means: the loaded environment's public production
declarations, their type digests, axiom sets and entries render to the
committed bytes, and the records, entries and census rows join under rules 1
to 8 of the contract. It does not mean that a declaration is correct, covered
or proved; the snapshot reads no proof and judges no statement. Rules 1, 2, 3
and 7 bind only under `recordedPrefixes`, which is empty at the landing.
Graph and counterexample ids are carried, not joined. The snapshot trusts the
loader's staleness verdict, and a toolchain change that alters elaboration may
change digests with no source change, which the drift check reports.

The run prints one timing line on standard error (load, walk, axioms, digests,
join); it is informational and decides nothing.
-/

namespace Gates.DeclSnapshot

open Lean (Name Expr Level ConstantInfo Environment BinderInfo Literal)

/-! ## The records of the walk and of the join -/

/-- One walked declaration: a public constant of a production module. -/
structure Decl where
  /-- The constant's name. -/
  name : Name
  /-- The module whose own constants list it. -/
  module : Name
  /-- `kindOf` of its `ConstantInfo`. -/
  kind : String
  /-- Whether `Lean.findDeclarationRanges?` answers for it. -/
  authored : Bool
  /-- The number of its universe parameters. -/
  universes : Nat
  /-- `typeDigest` of its type. -/
  typeDigest : String
  /-- Its axiom set, sorted by `Lean.Name.lt`. -/
  axioms : List Name
  deriving BEq, Inhabited, Repr

/-- The tooling side's copy of `WhatwgTest.Audit.Freeze.Entry`, which this tree
cannot import, with the recording module added and the mask carried as its
column spelling (`M1`, `M2` or `none:<reason>`). -/
structure EntryData where
  /-- The test module that holds the entry. -/
  recording : Name
  /-- The frozen declaration. -/
  declaration : Name
  /-- The pinned axiom set, `none` when no `axioms` clause was written. -/
  axioms : Option (List Name)
  /-- The `mask` clause in its column spelling. -/
  mask : Option String
  /-- The `anchor` clause. -/
  anchor : Option String
  /-- The `graph` clause. -/
  graph : Option String
  /-- The `counterexamples` clause, in the order written. -/
  counterexamples : List String
  deriving BEq, Inhabited, Repr

/-- One authored record, a row of `test/records/<packet>.tsv`. -/
structure Record where
  packet : String
  name : String
  owner : String
  role : String
  related : String
  anchor : String
  anchorDigest : String
  disposition : String
  contract : String
  battery : String
  route : String
  deriving BEq, Inhabited, Repr

/-- One census row: its id and its span digest. -/
structure CensusRow where
  id : String
  digest : String
  deriving BEq, Inhabited, Repr

/-- Everything the join reads. -/
structure JoinInput where
  recordedPrefixes : List String
  decls : Array Decl
  entries : Array EntryData
  records : Array Record
  census : Array CensusRow
  knownRed : List String
  deriving Inhabited

/-- One projection row, in column order. -/
structure Row where
  name : String
  module : String
  kind : String
  origin : String
  universes : Nat
  typeDigest : String
  axioms : List String
  frozenBy : List String
  mask : String
  anchor : String
  graph : String
  counterexamples : List String
  record : String
  route : String
  deriving BEq, Inhabited, Repr

/-! ## Frozen constants -/

/-- The projection's format version. -/
def formatVersion : String := "1"

/-- The command that regenerates the projection. -/
def regenerateCommand : String := "lake exe whatwg_declsnapshot --write"

/-- Where the projection lives, relative to the repository root. -/
def outputDirectory : String := "generated/declarations"

/-- Where the authored records live, relative to the repository root. -/
def recordsDirectory : String := "test/records"

/-- The namespaces under which rules 1, 2, 3 and 7 bind. Empty at the landing
(R-W5); a prefix joins by a breaker packet that adds it with its records and
leaves only by a ruling (contract, section 12). -/
def recordedPrefixes : List String := []

/-- The seven production libraries, in file order, with the module each is
rooted at. The umbrella `Whatwg` owns only its own module. -/
def libraries : List (String × Name) :=
  [("Whatwg", `Whatwg), ("WhatwgInfra", `Whatwg.Infra), ("WhatwgEcma262", `Whatwg.Ecma262),
   ("WhatwgWebIdl", `Whatwg.WebIdl), ("WhatwgUrl", `Whatwg.Url), ("WhatwgHtml", `Whatwg.Html),
   ("WhatwgStreams", `Whatwg.Streams)]

/-- The roles a record may give its declaration. -/
def roles : List String :=
  ["canonical", "view", "adapter", "separate-calculus", "derived", "helper",
   "foreign-boundary", "target-only"]

/-- The dispositions of `SPEC-MANIFEST.md`, and `-` for a record with no anchor. -/
def dispositions : List String :=
  ["owned", "requirement", "foreignBoundary", "hostOnly", "refused", "evidenceOnly",
   "targetOnly", "-"]

/-- The projection's columns, in order. -/
def columns : List String :=
  ["name", "module", "kind", "origin", "universes", "type-sha256", "axioms", "frozen-by",
   "mask", "anchor", "graph", "counterexamples", "record", "route"]

/-- The library a production module belongs to: the umbrella owns exactly
`Whatwg`, every other library its root and every module below it. -/
def libraryOf (module : Name) : Option String :=
  (libraries.find? fun (_, root) =>
    if root == `Whatwg then module == root else root.isPrefixOf module).map (·.1)

/-- A field value escaped for the projection: backslash, tab, line feed,
carriage return and comma each become a backslash sequence. -/
def escapeField (text : String) : String :=
  text.foldl (init := "") fun out c =>
    if c == '\\' then out ++ "\\\\"
    else if c == '\t' then out ++ "\\t"
    else if c == '\n' then out ++ "\\n"
    else if c == '\r' then out ++ "\\r"
    else if c == ',' then out ++ "\\,"
    else out.push c

/-! ## The canonical type text and its digest -/

/-- The canonical text of a universe level. -/
def levelText : Level → String
  | .zero => "0"
  | .succ l => "(s " ++ levelText l ++ ")"
  | .max a b => "(max " ++ levelText a ++ " " ++ levelText b ++ ")"
  | .imax a b => "(imax " ++ levelText a ++ " " ++ levelText b ++ ")"
  | .param n => "(p " ++ n.toString ++ ")"
  | .mvar _ => "?"

/-- The one-letter code of a binder annotation. -/
private def binderCode : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- `typeText`, appended to `out`, so that a large type is written once. -/
private def typeTextInto : Expr → String → String
  | .bvar i, out => out ++ "#" ++ toString i
  | .fvar _, out => out ++ "fvar"
  | .mvar _, out => out ++ "mvar"
  | .sort l, out => out ++ "(S " ++ levelText l ++ ")"
  | .const c ls, out => out ++ "(C " ++ c.toString ++ " [" ++ " ".intercalate (ls.map levelText) ++ "])"
  | .app f a, out => typeTextInto a (typeTextInto f (out ++ "(A ") ++ " ") ++ ")"
  | .lam n t b bi, out =>
      typeTextInto b (typeTextInto t (out ++ "(L " ++ n.toString ++ " " ++ binderCode bi ++ " ") ++ " ")
        ++ ")"
  | .forallE n t b bi, out =>
      typeTextInto b (typeTextInto t (out ++ "(P " ++ n.toString ++ " " ++ binderCode bi ++ " ") ++ " ")
        ++ ")"
  | .letE n t v b nonDep, out =>
      typeTextInto b
          (typeTextInto v
            (typeTextInto t (out ++ "(E " ++ n.toString ++ " " ++ (if nonDep then "h" else "l") ++ " ")
              ++ " ") ++ " ")
        ++ ")"
  | .lit (.natVal v), out => out ++ "(N " ++ toString v ++ ")"
  | .lit (.strVal s), out => out ++ "(T " ++ toString s.utf8ByteSize ++ " " ++ s ++ ")"
  | .mdata _ e, out => typeTextInto e out
  | .proj s i e, out => typeTextInto e (out ++ "(J " ++ s.toString ++ " " ++ toString i ++ " ") ++ ")"

/-- The canonical text of a type (contract, section 8): total and structural;
binder names, binder annotations, universe levels, literals and the
`let`/`have` flag are kept, metadata is dropped. -/
def typeText (e : Expr) : String := typeTextInto e ""

/-- SHA-256 of the UTF-8 bytes of `typeText`, through the proved `hash` package. -/
def typeDigest (e : Expr) : String := Gates.Sha256.hexDigestOfString (typeText e)

/-- The kind of a constant, as the `kind` column spells it. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Whether a rendered name lies under a recorded prefix: it is the prefix or
begins with the prefix and a dot. -/
def isRecorded (recorded : List String) (name : String) : Bool :=
  recorded.any fun root => name == root || name.startsWith (root ++ ".")

/-- The declaration an entry of module `recording` freezes, read from the
entry's name `<recording>.frozen.<declaration>` (the naming rule of
`#whatwg_freeze`, inverted); `none` for any other name. -/
def entryDeclaration? (recording entry : Name) : Option Name :=
  let stem := recording ++ `frozen
  if stem.isPrefixOf entry && entry != stem then
    some (entry.replacePrefix stem .anonymous)
  else
    none

/-! ## Entry decoding -/

/-- A string literal. -/
private def decodeString : Expr → Except String String
  | .lit (.strVal s) => .ok s
  | _ => .error "a string field is not a string literal"

/-- A natural number literal, raw or as `OfNat.ofNat` of a raw literal. -/
private def decodeNat (e : Expr) : Except String Nat :=
  let malformed := "a numeric name component is not a natural number literal"
  match e with
  | .lit (.natVal n) => .ok n
  | _ =>
    match e.getAppFn, e.getAppArgs with
    | .const c _, #[_, .lit (.natVal n), _] => if c == ``OfNat.ofNat then .ok n else .error malformed
    | _, _ => .error malformed

/-- The arity `n` of `Lean.Name.mkStr<n>`, for `n` from 1 to 8. -/
private def mkStrArity? (c : Name) : Option Nat :=
  match c with
  | .str (.str (.str .anonymous "Lean") "Name") last =>
    if last.startsWith "mkStr" then
      match (Gates.Common.dropChars last 5).toNat? with
      | some n => if 1 ≤ n && n ≤ 8 then some n else none
      | none => none
    else none
  | _ => none

/-- A name written `Lean.Name.mkStr<n>` applied to `n` string literals. -/
private def decodeMkStr (e : Expr) : Except String Name :=
  let malformed := "a name field is not a Lean.Name term in Lean.toExpr form"
  match e.getAppFn with
  | .const c _ =>
    match mkStrArity? c with
    | some n =>
      let args := e.getAppArgs
      if args.size != n then .error malformed
      else do
        let parts ← args.toList.mapM decodeString
        return parts.foldl Name.mkStr .anonymous
    | none => .error malformed
  | _ => .error malformed

/-- A name in the forms `Lean.toExpr` writes at the pinned toolchain:
`Lean.Name.anonymous`, `Lean.Name.mkStr1` to `Lean.Name.mkStr8` applied to
string literals, `Lean.Name.str p s` and `Lean.Name.num p n`. -/
def decodeName : Expr → Except String Name
  | .const c _ =>
    if c == ``Lean.Name.anonymous then .ok .anonymous
    else .error "a name field is not a Lean.Name term in Lean.toExpr form"
  | e@(.app (.app (.const c _) p) x) =>
    if c == ``Lean.Name.str then do
      let parent ← decodeName p
      let component ← decodeString x
      return .str parent component
    else if c == ``Lean.Name.num then do
      let parent ← decodeName p
      let component ← decodeNat x
      return .num parent component
    else decodeMkStr e
  | e => decodeMkStr e

/-- A list written `List.nil α` or `List.cons α x xs`. -/
private def decodeList {α : Type} (item : Expr → Except String α) :
    Expr → Except String (List α)
  | .app (.const c _) _ =>
    if c == ``List.nil then .ok [] else .error "a list field is not List.nil or List.cons"
  | .app (.app (.app (.const c _) _) x) xs =>
    if c == ``List.cons then do
      let head ← item x
      let tail ← decodeList item xs
      return head :: tail
    else .error "a list field is not List.nil or List.cons"
  | _ => .error "a list field is not List.nil or List.cons"

/-- An option written `Option.none α` or `Option.some α x`. -/
private def decodeOption {α : Type} (item : Expr → Except String α) (e : Expr) :
    Except String (Option α) :=
  match e with
  | .app (.const c _) _ =>
    if c == ``Option.none then .ok none else .error "an option field is not Option.none or Option.some"
  | .app (.app (.const c _) _) x =>
    if c == ``Option.some then (item x).map some
    else .error "an option field is not Option.none or Option.some"
  | _ => .error "an option field is not Option.none or Option.some"

/-- A mask constructor of `WhatwgTest.Audit.Freeze.ObservationMask`, as its
column spelling. -/
private def decodeMask : Expr → Except String String
  | .const c _ =>
    if c == `WhatwgTest.Audit.Freeze.ObservationMask.chunksAndOutcome then .ok "M1"
    else if c == `WhatwgTest.Audit.Freeze.ObservationMask.settlementOrder then .ok "M2"
    else .error "the mask is not a constructor of WhatwgTest.Audit.Freeze.ObservationMask"
  | .app (.const c _) (.lit (.strVal reason)) =>
    if c == `WhatwgTest.Audit.Freeze.ObservationMask.notApplicable then .ok ("none:" ++ reason)
    else .error "the mask is not a constructor of WhatwgTest.Audit.Freeze.ObservationMask"
  | _ => .error "the mask is not a constructor of WhatwgTest.Audit.Freeze.ObservationMask"

/-- A field decoded, its refusal prefixed with the field's name. -/
private def field {α : Type} (label : String) (result : Except String α) : Except String α :=
  result.mapError fun reason => s!"field {label}: {reason}"

/-- An entry's value, `WhatwgTest.Audit.Freeze.Entry.mk` applied to the
`Lean.toExpr` forms of its six fields (contract, section 7), as `EntryData`
of the module `recording`. Any other shape is refused with its reason. -/
def decodeEntry (recording : Name) (value : Expr) : Except String EntryData :=
  let notEntry := "the value is not WhatwgTest.Audit.Freeze.Entry.mk applied to six fields"
  match value.getAppFn, value.getAppArgs.toList with
  | .const c _, [declaration, axioms, mask, anchor, graph, counterexamples] =>
    if c != `WhatwgTest.Audit.Freeze.Entry.mk then .error notEntry else do
      let declaration ← field "declaration" (decodeName declaration)
      let axioms ← field "axioms" (decodeOption (decodeList decodeName) axioms)
      let mask ← field "mask" (decodeOption decodeMask mask)
      let anchor ← field "anchor" (decodeOption decodeString anchor)
      let graph ← field "graph" (decodeOption decodeString graph)
      let counterexamples ← field "counterexamples" (decodeList decodeString counterexamples)
      return { recording, declaration, axioms, mask, anchor, graph, counterexamples }
  | _, _ => .error notEntry

/-! ## The authored inputs -/

/-- The path of a packet's record file, as messages print it. -/
private def recordsPath (packet : String) : String := s!"{recordsDirectory}/{packet}.tsv"

/-- A full name: not empty, no `*`, and no empty dot-separated component. -/
private def isFullName (text : String) : Bool :=
  !text.isEmpty && !text.contains '*' && (text.splitOn ".").all (!·.isEmpty)

/-- The stem `P` of a family record `P.*`, when the text is one. -/
private def familyStem? (text : String) : Option String :=
  if text.endsWith ".*" then
    let stem := Gates.Common.dropLastChars text 2
    if isFullName stem then some stem else none
  else
    none

/-- Sixty-four lowercase hexadecimal digits. -/
private def isHexDigest (text : String) : Bool :=
  text.length == 64 && text.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- A path `test/contracts/<name>.contract.md` with a non-empty `<name>` that
holds no `/`. -/
private def isContractPath (text : String) : Bool :=
  let middle := Gates.Common.dropLastChars (Gates.Common.dropChars text 15) 12
  text.startsWith "test/contracts/" && text.endsWith ".contract.md" &&
    text.length > 27 && !middle.contains '/'

/-- A module name strictly under `WhatwgTest`. -/
private def isBatteryModule (text : String) : Bool :=
  let module := text.toName
  Gates.Trust.isModuleName module && (`WhatwgTest).isPrefixOf module && module != `WhatwgTest

/-- A record's id, `<packet>:<name as written>`. -/
private def recordId (record : Record) : String := s!"{record.packet}:{record.name}"

/-- Parse one packet's record file (contract, section 9). Lines that are empty
or begin `#` are ignored; every other line is a record of exactly ten
tab-separated, non-empty fields. The first refusal is returned. -/
def parseRecords (packet text : String) : Except String (Array Record) := do
  let path := recordsPath packet
  if text.contains '\r' then
    throw s!"{path} carries a CR byte; authored records are LF"
  let mut records : Array Record := #[]
  let mut seen : Std.HashSet String := {}
  let mut lineNumber := 0
  for line in text.splitOn "\n" do
    lineNumber := lineNumber + 1
    if line.isEmpty || line.startsWith "#" then
      continue
    let fields := line.splitOn "\t"
    unless fields.length == 10 do
      throw s!"{path} line {lineNumber}: {fields.length} fields; a record has 10"
    if let some position := fields.findIdx? (·.isEmpty) then
      throw s!"{path} line {lineNumber}: field {position + 1} is empty"
    let [name, owner, role, related, anchor, anchorDigest, disposition, contract, battery, route] :=
      fields | throw s!"{path} line {lineNumber}: {fields.length} fields; a record has 10"
    unless isFullName name || (familyStem? name).isSome do
      throw s!"{path} line {lineNumber}: {name} is neither a full name nor a family <prefix>.*"
    let id := s!"{packet}:{name}"
    unless roles.contains role do
      throw s!"record {id}: role {role} is not one of {", ".intercalate roles}"
    unless (role == "canonical") == (related == "-") && (related == "-" || isFullName related) do
      throw s!"record {id}: a canonical record relates to nothing and every other record relates to a named declaration"
    unless (anchor == "-") == (anchorDigest == "-") do
      throw s!"record {id}: an anchor and its span digest are written together or not at all"
    unless anchorDigest == "-" || isHexDigest anchorDigest do
      throw s!"record {id}: the span digest is not 64 lowercase hexadecimal digits"
    unless dispositions.contains disposition do
      throw s!"record {id}: disposition {disposition} is not one of {", ".intercalate dispositions}"
    unless (anchor == "-") == (disposition == "-") do
      throw s!"record {id}: a record carries a disposition exactly when it carries an anchor"
    unless isContractPath contract do
      throw s!"record {id}: contract {contract} is not a path test/contracts/<name>.contract.md"
    unless isBatteryModule battery do
      throw s!"record {id}: battery {battery} is not a module under WhatwgTest"
    if seen.contains name then
      throw s!"record {id}: {name} is recorded twice in {path}"
    seen := seen.insert name
    records := records.push
      { packet, name, owner, role, related, anchor, anchorDigest, disposition, contract, battery,
        route }
  return records

/-- One `|`-separated census row split into its fields, undoing the census's
backslash escapes (`\\`, `\|`, `\n`, `\r`, `\t`). -/
private def splitCensusRow (line : String) : Except String (Array String) := do
  let mut fields : Array String := #[]
  let mut current : String := ""
  let mut escaped := false
  for c in line.toList do
    if escaped then
      escaped := false
      if c == '\\' then current := current.push '\\'
      else if c == '|' then current := current.push '|'
      else if c == 'n' then current := current.push '\n'
      else if c == 'r' then current := current.push '\r'
      else if c == 't' then current := current.push '\t'
      else throw s!"a census row carries the unknown escape \\{c}"
    else if c == '\\' then
      escaped := true
    else if c == '|' then
      fields := fields.push current
      current := ""
    else
      current := current.push c
  if escaped then
    throw "a census row ends in an unfinished escape"
  return fields.push current

/-- The (row id, span digest) pairs of one census projection (contract,
section 10): a `#census ` header with `|`-separated rows (id in field 2, span
digest in field 6), or a `#url-census ` header with tab-separated rows and `#`
comment lines (id in field 2, `span-sha256` in field 5). Any other header is
refused. -/
def parseCensus (text : String) : Except String (Array CensusRow) := do
  match Gates.Common.lines text with
  | [] => throw "the census projection is empty"
  | header :: body =>
    let mut rows : Array CensusRow := #[]
    if header.startsWith "#census " then
      for line in body do
        if line.isEmpty then
          continue
        let fields ← splitCensusRow line
        unless fields.size ≥ 6 do
          throw s!"a #census row has {fields.size} fields, fewer than 6: {line}"
        rows := rows.push { id := fields.getD 1 "", digest := fields.getD 5 "" }
      return rows
    else if header.startsWith "#url-census " then
      for line in body do
        if line.isEmpty || line.startsWith "#" then
          continue
        let fields := (line.splitOn "\t").toArray
        unless fields.size ≥ 5 do
          throw s!"a #url-census row has {fields.size} fields, fewer than 5: {line}"
        rows := rows.push { id := fields.getD 1 "", digest := fields.getD 4 "" }
      return rows
    else
      throw s!"the header {header} is neither a #census nor a #url-census header"

/-- Strings grouped by key, each group in input order, the groups sorted by key. -/
private def groupedBy {α : Type} (items : Array α) (key : α → String) (value : α → String) :
    Array (String × Array String) :=
  let groups : Std.HashMap String (Array String) := items.foldl (init := {}) fun groups item =>
    groups.insert (key item) ((groups.getD (key item) #[]).push (value item))
  groups.toArray.qsort fun a b => a.1 < b.1

/-- Input refusal: one name recorded by two or more records, in one packet or
across packets. -/
def duplicateRecords (records : Array Record) : Array String :=
  (groupedBy records (·.name) recordId).filterMap fun (name, ids) =>
    if ids.size < 2 then none else
      some s!"declaration snapshot: input: {name} is recorded {ids.size} times: {", ".intercalate (ids.qsort (· < ·)).toList}"

/-- Input refusal: one census row id in two or more rows across the census
projections. -/
def duplicateCensusIds (rows : Array CensusRow) : Array String :=
  (groupedBy rows (·.id) (·.digest)).filterMap fun (id, digests) =>
    if digests.size < 2 then none else
      some s!"declaration snapshot: input: census row id {id} occurs {digests.size} times across the census projections"

/-- The records indexed for covering: exact records by name (the first of a
name), and family records with their stems. -/
private structure RecordIndex where
  exact : Std.HashMap String Record
  families : Array (String × Record)

private def RecordIndex.of (records : Array Record) : RecordIndex :=
  records.foldl (init := { exact := {}, families := #[] }) fun index record =>
    match familyStem? record.name with
    | some stem => { index with families := index.families.push (stem, record) }
    | none =>
      if index.exact.contains record.name then index
      else { index with exact := index.exact.insert record.name record }

/-- The covering record of a rendered name: its exact record, otherwise the
family record with the longest stem `P` such that the name begins `P.`. -/
private def RecordIndex.covering? (index : RecordIndex) (name : String) : Option Record :=
  match index.exact.get? name with
  | some record => some record
  | none =>
    let best := index.families.foldl (init := (none : Option (String × Record)))
      fun best (stem, record) =>
        if name.startsWith (stem ++ ".") then
          match best with
          | some (bestStem, _) => if bestStem.length < stem.length then some (stem, record) else best
          | none => some (stem, record)
        else best
    best.map (·.2)

/-- The covering record of a rendered name (contract, section 2). -/
def coveringRecord? (records : Array Record) (name : String) : Option Record :=
  (RecordIndex.of records).covering? name

/-! ## Rows and the projection -/

/-- Names sorted by `Lean.Name.lt`, without duplicates. -/
private def sortedNames (names : List Name) : List Name :=
  (names.toArray.qsort Name.lt).toList.foldr (init := []) fun name kept =>
    match kept with
    | next :: _ => if name == next then kept else name :: kept
    | [] => [name]

/-- Strings sorted in `String` order, without duplicates. -/
private def sortedStrings (texts : List String) : List String :=
  (texts.toArray.qsort (· < ·)).toList.foldr (init := []) fun text kept =>
    match kept with
    | next :: _ => if text == next then kept else text :: kept
    | [] => [text]

/-- The entries grouped by the declaration they freeze. -/
private def entriesByDeclaration (entries : Array EntryData) :
    Std.HashMap Name (Array EntryData) :=
  entries.foldl (init := {}) fun groups entry =>
    groups.insert entry.declaration ((groups.getD entry.declaration #[]).push entry)

/-- The first value of a clause over entries in `frozen-by` order, or `-`. -/
private def firstClause (entries : Array EntryData) (clause : EntryData → Option String) :
    String :=
  (entries.findSome? clause).getD "-"

/-- One declaration's row. -/
private def rowOf (index : RecordIndex) (byDeclaration : Std.HashMap Name (Array EntryData))
    (decl : Decl) : Row :=
  let name := decl.name.toString
  let entries := (byDeclaration.getD decl.name #[]).qsort fun a b => Name.lt a.recording b.recording
  let record? := index.covering? name
  { name, module := decl.module.toString, kind := decl.kind,
    origin := if decl.authored then "authored" else "generated",
    universes := decl.universes, typeDigest := decl.typeDigest,
    axioms := (sortedNames decl.axioms).map (·.toString),
    frozenBy := (sortedNames (entries.toList.map (·.recording))).map (·.toString),
    mask := firstClause entries (·.mask),
    anchor := firstClause entries (·.anchor),
    graph := firstClause entries (·.graph),
    counterexamples := sortedStrings (entries.toList.flatMap (·.counterexamples)),
    record := (record?.map recordId).getD "-",
    route := (record?.map (·.route)).getD "-" }

/-- One row per declaration, in the order of `decls`. -/
def rows (input : JoinInput) : Array Row :=
  let index := RecordIndex.of input.records
  let byDeclaration := entriesByDeclaration input.entries
  input.decls.map (rowOf index byDeclaration)

/-- A list column: `-` when empty, otherwise the elements, each escaped, joined
by `,`. -/
private def listField (items : List String) : String :=
  if items.isEmpty then "-" else ",".intercalate (items.map escapeField)

/-- A scalar column: `-` stays `-`, anything else is escaped. -/
private def scalarField (text : String) : String :=
  if text == "-" then "-" else escapeField text

/-- One row as a tab-separated line, without its terminator. -/
def renderRow (row : Row) : String :=
  "\t".intercalate
    [scalarField row.name, scalarField row.module, scalarField row.kind, scalarField row.origin,
     toString row.universes, scalarField row.typeDigest, listField row.axioms,
     listField row.frozenBy, scalarField row.mask, scalarField row.anchor,
     scalarField row.graph, listField row.counterexamples, scalarField row.record,
     scalarField row.route]

/-- The projection's row order: by name, then by module, in `String` order. -/
private def rowBefore (a b : Row) : Bool :=
  a.name < b.name || (a.name == b.name && a.module < b.module)

/-- One library's file: the header, the column line, then the rows sorted by
name and module, every line LF-terminated. -/
def renderFile (library : String) (rows : Array Row) : String :=
  let header :=
    s!"#declarations format={formatVersion} generator=Gates.DeclSnapshot library={library} " ++
      s!"rows={rows.size} regenerate={regenerateCommand}\n"
  let columnLine := "#" ++ "\t".intercalate columns ++ "\n"
  (rows.qsort rowBefore).foldl (init := header ++ columnLine) fun out row =>
    out ++ renderRow row ++ "\n"

/-- The projection: one `(path, text)` per library of `libraries`, in that
order, each holding the rows of the declarations whose module the library
owns. -/
def projection (input : JoinInput) : List (String × String) :=
  let index := RecordIndex.of input.records
  let byDeclaration := entriesByDeclaration input.entries
  libraries.map fun (library, _) =>
    let selected := (input.decls.filter fun decl => libraryOf decl.module == some library).map
      (rowOf index byDeclaration)
    (s!"{outputDirectory}/{library}.tsv", renderFile library selected)

/-! ## The join -/

/-- The walk's order: by rendered name, then by rendered module. -/
private def sortedDecls (decls : Array Decl) : Array Decl :=
  decls.qsort fun a b =>
    let left := a.name.toString
    let right := b.name.toString
    left < right || (left == right && a.module.toString < b.module.toString)

/-- Records in the order of their ids. -/
private def sortedRecords (records : Array Record) : Array Record :=
  records.qsort fun a b => recordId a < recordId b

/-- An entry's constant name, `<recording>.frozen.<declaration>`, rendered. -/
private def entryConstant (entry : EntryData) : String :=
  ((entry.recording ++ `frozen) ++ entry.declaration).toString

/-- Entries in the order of their constant names. -/
private def sortedEntries (entries : Array EntryData) : Array EntryData :=
  entries.qsort fun a b => entryConstant a < entryConstant b

/-- Rule 1: an authored inductive type under a recorded prefix with no exact
record. -/
def unrecordedTypes (input : JoinInput) : Array String :=
  let index := RecordIndex.of input.records
  (sortedDecls (input.decls.filter fun decl =>
      isRecorded input.recordedPrefixes decl.name.toString)).filterMap fun decl =>
    let name := decl.name.toString
    if decl.kind == "inductive" && decl.authored && !index.exact.contains name then
      some s!"declaration snapshot: rule 1: exported type {name} of {decl.module} under a recorded prefix has no exact record"
    else none

/-- Rule 2: a public declaration under a recorded prefix, authored or
generated, with no covering record. -/
def uncoveredDeclarations (input : JoinInput) : Array String :=
  let index := RecordIndex.of input.records
  (sortedDecls (input.decls.filter fun decl =>
      isRecorded input.recordedPrefixes decl.name.toString)).filterMap fun decl =>
    let name := decl.name.toString
    if (index.covering? name).isNone then
      some s!"declaration snapshot: rule 2: exported declaration {name} of {decl.module} under a recorded prefix has no covering record"
    else none

/-- Rule 3: a record whose name, or family stem, lies under a recorded prefix
and covers no declaration, unless its battery is declared red. -/
def danglingRecords (input : JoinInput) : Array String :=
  let names := input.decls.map (·.name.toString)
  let present : Std.HashSet String := names.foldl (init := {}) fun set name => set.insert name
  (sortedRecords input.records).filterMap fun record =>
    let stem? := familyStem? record.name
    let subject := stem?.getD record.name
    if isRecorded input.recordedPrefixes subject && !input.knownRed.contains record.battery then
      let covers := match stem? with
        | some stem => names.any fun name => name.startsWith (stem ++ ".")
        | none => present.contains record.name
      if covers then none else
        some s!"declaration snapshot: rule 3: record {recordId record} names no declaration, and its battery {record.battery} is not declared red"
    else none

/-- Rule 4: two or more records claiming one census row. -/
def sharedAnchors (input : JoinInput) : Array String :=
  (groupedBy (input.records.filter (·.anchor != "-")) (·.anchor) recordId).filterMap
    fun (row, ids) =>
      if ids.size < 2 then none else
        some s!"declaration snapshot: rule 4: census row {row} is claimed by {ids.size} records: {", ".intercalate (ids.qsort (· < ·)).toList}"

/-- Rule 5: a non-canonical record whose related declaration has no exact
record. -/
def orphanRelations (input : JoinInput) : Array String :=
  let index := RecordIndex.of input.records
  (sortedRecords input.records).filterMap fun record =>
    if record.role != "canonical" && !index.exact.contains record.related then
      some s!"declaration snapshot: rule 5: record {recordId record} relates to {record.related}, which has no exact record"
    else none

/-- Rule 6: a record anchor that is no census row id, a record whose span
digest differs from the row's, and an entry anchor that is no census row id. -/
def unknownAnchors (input : JoinInput) : Array String :=
  let census : Std.HashMap String String := input.census.foldl (init := {}) fun census row =>
    if census.contains row.id then census else census.insert row.id row.digest
  let fromRecords := (sortedRecords input.records).filterMap fun record =>
    if record.anchor == "-" then none else
      match census.get? record.anchor with
      | none =>
        some s!"declaration snapshot: rule 6: record {recordId record} anchors {record.anchor}, which is no census row id"
      | some digest =>
        if digest == record.anchorDigest then none else
          some s!"declaration snapshot: rule 6: record {recordId record} anchors {record.anchor} at {record.anchorDigest}; the census span digest is {digest}"
  let fromEntries := (sortedEntries input.entries).filterMap fun entry =>
    match entry.anchor with
    | some anchor =>
      if census.contains anchor then none else
        some s!"declaration snapshot: rule 6: entry {entryConstant entry} anchors {anchor}, which is no census row id"
    | none => none
  fromRecords ++ fromEntries

/-- Rule 7: an entry whose declaration lies under a recorded prefix and has no
exact record. -/
def unrecordedEntries (input : JoinInput) : Array String :=
  let index := RecordIndex.of input.records
  (sortedEntries input.entries).filterMap fun entry =>
    let name := entry.declaration.toString
    if isRecorded input.recordedPrefixes name && !index.exact.contains name then
      some s!"declaration snapshot: rule 7: entry {entryConstant entry} freezes {name}, which has no exact record"
    else none

/-- Rule 8: two entries for one declaration that both carry a mask, anchor or
graph clause, with different values. An entry without the clause disagrees with
nothing. -/
def disagreeingEntries (input : JoinInput) : Array String :=
  let groups := (entriesByDeclaration input.entries).toArray.qsort fun a b =>
    a.1.toString < b.1.toString
  let clauses : List (String × (EntryData → Option String)) :=
    [("mask", (·.mask)), ("anchor", (·.anchor)), ("graph", (·.graph))]
  groups.foldl (init := #[]) fun out (declaration, entries) =>
    if entries.size < 2 then out else
      let modules := ", ".intercalate
        ((sortedNames (entries.toList.map (·.recording))).map (·.toString))
      clauses.foldl (init := out) fun out (clause, read) =>
        if (sortedStrings (entries.toList.filterMap read)).length > 1 then
          out.push s!"declaration snapshot: rule 8: the entries for {declaration} in {modules} disagree on the {clause}"
        else out

/-- Rule 9: the regenerated files against the committed ones, by path: a file
the generator writes that is not committed, one whose bytes differ, and a
committed file the generator does not write; sorted by path. -/
def byteDrift (regenerated committed : List (String × String)) : Array String :=
  let paths := sortedStrings (regenerated.map (·.1) ++ committed.map (·.1))
  paths.toArray.filterMap fun path =>
    match List.lookup path regenerated, List.lookup path committed with
    | some fresh, some onDisk =>
      if fresh == onDisk then none else
        some s!"declaration snapshot: rule 9: {path} differs from a fresh regeneration; run {regenerateCommand}"
    | some _, none =>
      some s!"declaration snapshot: rule 9: {path} is missing; run {regenerateCommand}"
    | none, some _ =>
      some s!"declaration snapshot: rule 9: {path} is not a projection this generator writes"
    | none, none => none

/-- Rules 1 to 8, in order. -/
def joinFailures (input : JoinInput) : Array String :=
  unrecordedTypes input ++ uncoveredDeclarations input ++ danglingRecords input ++
    sharedAnchors input ++ orphanRelations input ++ unknownAnchors input ++
    unrecordedEntries input ++ disagreeingEntries input

/-! ## Axiom sets, with one memo across the walk -/

/-- The constants `Lean.collectAxioms` visits from a constant at the pinned
toolchain, and whether the constant is itself an axiom. -/
private def axiomSuccessors (env : Environment) (c : Name) : Array Name × Bool :=
  match env.find? c with
  | some (.axiomInfo v) => (v.type.getUsedConstants, true)
  | some (.defnInfo v) => (v.type.getUsedConstants ++ v.value.getUsedConstants, false)
  | some (.thmInfo v) => (v.type.getUsedConstants ++ v.value.getUsedConstants, false)
  | some (.opaqueInfo v) => (v.type.getUsedConstants ++ v.value.getUsedConstants, false)
  | some (.quotInfo _) => (#[], false)
  | some (.ctorInfo v) => (v.type.getUsedConstants, false)
  | some (.recInfo v) => (v.type.getUsedConstants, false)
  | some (.inductInfo v) => (v.type.getUsedConstants ++ v.ctors.toArray, false)
  | none => (#[], false)

/-- `items` added to `into`, each once. -/
private def unionInto (into items : Array Name) : Array Name :=
  items.foldl (init := into) fun out name => if out.contains name then out else out.push name

/-- Steps one root's walk may take: each step follows one edge or leaves one
constant, so the bound is far above the constants and edges of any
environment this tree loads. -/
private def axiomWalkFuel : Nat := 1000000000

/-- The axiom set of each root, sorted by `Lean.Name.lt`: the axioms among the
constants reachable from it by `axiomSuccessors`. One depth-first walk with
one memo serves every root; a strongly connected component (an inductive type
and its constructors, a mutual block) gets one set, by Tarjan's algorithm on an
explicit stack. Each constant is discovered once; `onStack` marks the
constants of components still open, and a component's set is the union of its
members' own axioms and of the sets of the components its edges reach. -/
private def axiomSets (env : Environment) (roots : Array Name) :
    Except String (Array (List Name)) := Id.run do
  let mut index : Std.HashMap Name Nat := {}
  let mut low : Array Nat := #[]
  let mut onStack : Array Bool := #[]
  let mut found : Array (Array Name) := #[]
  let mut stack : Array Nat := #[]
  let mut frameNode : Array Nat := #[]
  let mut frameSuccessors : Array (Array Name) := #[]
  let mut framePosition : Array Nat := #[]
  let mut results : Array (List Name) := #[]
  for root in roots do
    let mut pending : Option Name := if index.contains root then none else some root
    let mut finished := pending.isNone
    for _ in [0:axiomWalkFuel] do
      if finished then
        break
      match pending with
      | some c =>
        -- Discover `c`: number it, open its frame.
        pending := none
        let (successors, isAxiom) := axiomSuccessors env c
        let id := low.size
        index := index.insert c id
        low := low.push id
        onStack := onStack.push true
        found := found.push (if isAxiom then #[c] else #[])
        stack := stack.push id
        frameNode := frameNode.push id
        frameSuccessors := frameSuccessors.push successors
        framePosition := framePosition.push 0
      | none =>
        match frameNode.back? with
        | none => finished := true
        | some v =>
          let position := framePosition.back!
          let successors := frameSuccessors.back!
          if position < successors.size then
            framePosition := framePosition.set! (framePosition.size - 1) (position + 1)
            let w := successors[position]!
            match index.get? w with
            | none => pending := some w
            | some wi =>
              if onStack[wi]! then
                low := low.set! v (min low[v]! wi)
              else
                let reached := found[wi]!
                found := found.modify v (unionInto · reached)
          else
            frameNode := frameNode.pop
            frameSuccessors := frameSuccessors.pop
            framePosition := framePosition.pop
            if low[v]! == v then
              -- `v` roots a component: close it with one shared set.
              let mut members : Array Nat := #[]
              let mut shared : Array Name := #[]
              for _ in [0:stack.size] do
                match stack.back? with
                | none => break
                | some x =>
                  stack := stack.pop
                  onStack := onStack.set! x false
                  members := members.push x
                  shared := unionInto shared found[x]!
                  if x == v then
                    break
              for x in members do
                found := found.set! x shared
            match frameNode.back? with
            | some u =>
              low := low.set! u (min low[u]! low[v]!)
              if !onStack[v]! then
                let reached := found[v]!
                found := found.modify u (unionInto · reached)
            | none => pure ()
    if !finished then
      return .error s!"the axiom walk from {root} exceeded {axiomWalkFuel} steps"
    results := results.push (sortedNames (found[index.getD root 0]!).toList)
  return .ok results

/-! ## The executable -/

/-- The trees whose modules the snapshot loads. -/
private def loadedTrees : List Name := [`Whatwg, `WhatwgTest]

/-- The declared red set, relative to the repository root. -/
private def knownRedPath : String := "test/fixtures/trust-gate/known-red.txt"

/-- The usage line. -/
private def usage : String :=
  "usage: lake exe whatwg_declsnapshot [--check | --write]"

/-- Milliseconds since `start`. -/
private def since (start : Nat) : IO Nat := do
  return (← IO.monoMsNow) - start

/-- The UTF-8 text of a file, or the reason it cannot be read. -/
private def readText (path : System.FilePath) : IO (Except String String) := do
  match ← (IO.FS.readBinFile path).toBaseIO with
  | .error error => return .error s!"cannot read {path}: {error}"
  | .ok bytes =>
    match String.fromUTF8? bytes with
    | some text => return .ok text
    | none => return .error s!"{path} is not UTF-8"

/-- The regular files directly in `directory` whose extension is `tsv`, by
file name; empty when the directory does not exist. -/
private def tsvFiles (directory : System.FilePath) : IO (Array System.FilePath) := do
  unless ← directory.isDir do
    return #[]
  let mut files : Array System.FilePath := #[]
  for entry in ← directory.readDir do
    if !(← entry.path.isDir) && entry.path.extension == some "tsv" then
      files := files.push entry.path
  return files.qsort fun a b => a.fileName.getD "" < b.fileName.getD ""

/-- The modules the snapshot asks the loader for: every source module of the
loaded trees, the umbrella `Whatwg` included and the test root `WhatwgTest`
excluded, minus the modules declared red. -/
private def requestedModules (sources : Array Name) (knownRed : List String) : Array Name :=
  sources.filter fun module => module != `WhatwgTest && !knownRed.contains module.toString

/-- One loaded constant before its digest and axioms: name, module, information. -/
private structure Walked where
  name : Name
  module : Name
  info : ConstantInfo
  deriving Inhabited

/-- The authored flag of each name: whether `Lean.findDeclarationRanges?`
answers, run in `CoreM` over the loaded environment. -/
private def authoredFlags (env : Environment) (names : Array Name) : IO (Array Bool) := do
  let context : Lean.Core.Context :=
    { fileName := "<whatwg_declsnapshot>", fileMap := default, maxHeartbeats := 0 }
  let state : Lean.Core.State := { env }
  let action : Lean.CoreM (Array Bool) :=
    names.mapM fun name => return (← Lean.findDeclarationRanges? name).isSome
  let (flags, _) ← action.toIO context state
  return flags

/-- Everything a run computes before it compares or writes. -/
private structure Snapshot where
  input : JoinInput
  refusals : Array String
  timing : String

/-- Load, walk and read the authored inputs; `refusals` holds every input
refusal, and `input` is meaningful only when the loader refused nothing. -/
private def snapshot (root : System.FilePath) : IO Snapshot := do
  let started ← IO.monoMsNow
  let mut refusals : Array String := #[]
  -- The declared red set.
  let mut knownRed : List String := []
  match ← readText (root / knownRedPath) with
  | .ok text => knownRed := Gates.Common.listFileEntries text
  | .error reason => refusals := refusals.push s!"declaration snapshot: input: {reason}"
  -- The loader: the module list, freshness, then one import.
  Gates.Trust.initLoaderSearchPath root
  let sources ← Gates.Trust.sourceModules root loadedTrees
  let modules := requestedModules sources knownRed
  let buildRoot := Gates.Trust.leanBuildDir root
  for module in modules do
    let olean := Lean.modToFilePath buildRoot module "olean"
    if !(← olean.pathExists) then
      let shown ← (Gates.Common.relativeTo root olean).toBaseIO
      refusals := refusals.push
        s!"declaration snapshot: input: module {module} has no built file {shown.toOption.getD olean.toString}; run lake build"
    else
      let (fresh, _) ← Gates.Trust.traceOf buildRoot root module
      unless fresh do
        refusals := refusals.push
          s!"declaration snapshot: input: module {module} is stale: its Lake trace does not record its current source; run lake build"
  let traced ← since started
  unless refusals.isEmpty do
    return { input := default, refusals, timing := s!"traces {traced} ms; nothing imported" }
  let importStarted ← IO.monoMsNow
  let env ← Gates.Trust.importBuilt modules
  let imported ← since importStarted
  -- The walk: public constants of production modules, entries of test modules.
  let walkStarted ← IO.monoMsNow
  let mut walked : Array Walked := #[]
  let mut entries : Array EntryData := #[]
  for i in [0:env.header.moduleNames.size] do
    let module := env.header.moduleNames[i]!
    let some data := env.header.moduleData[i]? | continue
    if (`Whatwg).isPrefixOf module then
      if (libraryOf module).isNone then
        refusals := refusals.push
          s!"declaration snapshot: input: module {module} belongs to no library of Gates.DeclSnapshot.libraries"
      for name in data.constNames, info in data.constants do
        unless name.isInternal do
          walked := walked.push { name, module, info }
    else if (`WhatwgTest).isPrefixOf module then
      for name in data.constNames, info in data.constants do
        if let some declaration := entryDeclaration? module name then
          match info.value? with
          | none =>
            refusals := refusals.push
              s!"declaration snapshot: input: entry {name}: the constant has no value"
          | some value =>
            match decodeEntry module value with
            | .error reason =>
              refusals := refusals.push s!"declaration snapshot: input: entry {name}: {reason}"
            | .ok entry =>
              if entry.declaration != declaration then
                refusals := refusals.push
                  s!"declaration snapshot: input: entry {name}: it freezes {entry.declaration}, not {declaration}"
              else
                entries := entries.push entry
  let authored ← authoredFlags env (walked.map (·.name))
  let walkTime ← since walkStarted
  -- The axiom sets, one memo across the walk.
  let axiomsStarted ← IO.monoMsNow
  let mut axiomLists : Array (List Name) := #[]
  match axiomSets env (walked.map (·.name)) with
  | .ok lists => axiomLists := lists
  | .error reason => refusals := refusals.push s!"declaration snapshot: input: {reason}"
  let axiomTime ← since axiomsStarted
  -- The type digests.
  let digestsStarted ← IO.monoMsNow
  let mut decls : Array Decl := #[]
  for i in [0:walked.size] do
    let item := walked[i]!
    decls := decls.push
      { name := item.name, module := item.module, kind := kindOf item.info,
        authored := authored.getD i false, universes := item.info.levelParams.length,
        typeDigest := typeDigest item.info.type, axioms := axiomLists.getD i [] }
  let digestTime ← since digestsStarted
  -- The authored records and the census rows.
  let inputsStarted ← IO.monoMsNow
  let mut records : Array Record := #[]
  for file in ← tsvFiles (root / recordsDirectory) do
    let packet := file.fileStem.getD ""
    match ← readText file with
    | .error reason => refusals := refusals.push s!"declaration snapshot: input: {reason}"
    | .ok text =>
      match parseRecords packet text with
      | .error reason => refusals := refusals.push s!"declaration snapshot: input: {reason}"
      | .ok parsed => records := records ++ parsed
  refusals := refusals ++ duplicateRecords records
  let mut census : Array CensusRow := #[]
  let censusFiles := (← tsvFiles (root / "generated")).filter fun file =>
    (file.fileName.getD "").endsWith "-census.tsv"
  for file in censusFiles do
    let shown := s!"generated/{file.fileName.getD ""}"
    match ← readText file with
    | .error reason => refusals := refusals.push s!"declaration snapshot: input: {reason}"
    | .ok text =>
      match parseCensus text with
      | .error reason => refusals := refusals.push s!"declaration snapshot: input: {shown}: {reason}"
      | .ok parsed => census := census ++ parsed
  refusals := refusals ++ duplicateCensusIds census
  let inputTime ← since inputsStarted
  let input : JoinInput :=
    { recordedPrefixes, decls, entries, records, census, knownRed }
  return { input, refusals,
           timing := s!"traces {traced} ms, import {imported} ms ({modules.size} modules), walk {walkTime} ms, axioms {axiomTime} ms, digests {digestTime} ms, records and census {inputTime} ms" }

/-- The committed projection files, as `(path, text)`; a file that is not UTF-8
is read as text no regeneration can equal. -/
private def committedFiles (root : System.FilePath) : IO (List (String × String)) := do
  let mut files : List (String × String) := []
  for file in ← tsvFiles (root / outputDirectory) do
    let path := s!"{outputDirectory}/{file.fileName.getD ""}"
    let text := match String.fromUTF8? (← IO.FS.readBinFile file) with
      | some text => text
      | none => "� not UTF-8"
    files := files ++ [(path, text)]
  return files

/-- The facts every PASS line states. -/
private def summary (input : JoinInput) : String :=
  let prefixes := if input.recordedPrefixes.isEmpty then "none"
    else ", ".intercalate input.recordedPrefixes
  s!"{input.decls.size} declarations in {libraries.length} libraries, {input.entries.size} entries, {input.records.size} records, {input.census.size} census rows; recorded prefixes {prefixes}"

/-- Print the FAIL line and every problem. -/
private def fail (problems : Array String) : IO UInt32 := do
  IO.eprintln s!"FAIL declaration snapshot: {problems.size} refusal(s) and failure(s)"
  for problem in problems do
    IO.eprintln s!"  {problem}"
  return 1

/-- One run in check mode (`write = false`) or write mode. -/
private def run (root : System.FilePath) (write : Bool) : IO UInt32 := do
  let started ← IO.monoMsNow
  let result ← snapshot root
  let joinStarted ← IO.monoMsNow
  let failures := if result.refusals.isEmpty then joinFailures result.input else #[]
  let regenerated := if result.refusals.isEmpty then projection result.input else []
  let joinTime ← since joinStarted
  if write then
    let problems := result.refusals ++ failures
    IO.eprintln s!"declaration snapshot timing: {result.timing}, join and render {joinTime} ms, total {← since started} ms"
    unless problems.isEmpty do
      return ← fail problems
    let committed ← committedFiles root
    IO.FS.createDirAll (root / outputDirectory)
    for (path, text) in regenerated do
      IO.FS.writeBinFile (root / path) text.toUTF8
      IO.println s!"WROTE {path}"
    let mut removed : Nat := 0
    for (path, _) in committed do
      if (List.lookup path regenerated).isNone then
        IO.FS.removeFile (root / path)
        removed := removed + 1
        IO.println s!"REMOVED {path}"
    IO.println s!"PASS declaration snapshot: {summary result.input}; wrote the {regenerated.length} projection files under {outputDirectory} and removed {removed} other file(s)"
    return 0
  let committed ← committedFiles root
  let drift := if result.refusals.isEmpty then byteDrift regenerated committed else #[]
  let problems := result.refusals ++ failures ++ drift
  IO.eprintln s!"declaration snapshot timing: {result.timing}, join and render {joinTime} ms, total {← since started} ms"
  unless problems.isEmpty do
    return ← fail problems
  IO.println s!"PASS declaration snapshot: {summary result.input}; the {regenerated.length} projection files under {outputDirectory} are byte-identical to a fresh regeneration, and records, entries and census rows join under rules 1 to 8"
  return 0

/-- The entry point of `lake exe whatwg_declsnapshot`: no argument or
`--check` compares, `--write` regenerates, anything else prints the usage line
and exits 2. Exit 0 follows a `PASS declaration snapshot:` line, exit 1 a
`FAIL declaration snapshot:` line and every refusal and failure. -/
def cli (args : List String) : IO UInt32 := do
  let write? : Option Bool := match args with
    | [] | ["--check"] => some false
    | ["--write"] => some true
    | _ => none
  let some write := write? | do
    IO.eprintln usage
    return 2
  try
    let root ← Gates.Common.projectRoot
    run root write
  catch error =>
    fail #[s!"declaration snapshot: {error}"]

end Gates.DeclSnapshot
