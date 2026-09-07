import Gates.Common
import Gates.Sha256
import Gates.Ecmarkup

/-!
# Gates.Census

The specification algorithm census: the denominator of the coverage metric
defined in `docs/SPEC-COVERAGE.md`. One row per abstract operation, internal
slot, IDL member, stated piping requirement, and authored cross-cutting rule
of the pinned `index.bs`, each anchored to the pinned bytes by a byte string
that occurs exactly once and by the SHA-256 of its span.

`lake exe census --write` writes two projections:

- `generated/spec-algorithm-census.tsv`, the census itself; and
- `WhatwgTest/Audit/SpecCoverageRows.lean`, the frozen Lean row list
  the test-side numerator checks itself against.

`lake exe census` checks the input digest, anchor uniqueness, every span
digest, the disposition join, byte-identity of both projections against a
fresh regeneration, and the numerator's coverage emit against that same
regeneration. `lake exe census --report` prints the coverage block from the
emit.

The emit is not a file. `WhatwgTest/Audit/SpecCoverage.lean` owns the Streams
coverage states and witnesses and exports them as `emit`, and since slice Q2
`WhatwgTest/Audit/WebIdl/SpecCoverage.lean` and
`WhatwgTest/Audit/Ecma262/SpecCoverage.lean` do the same for their standards;
`bin/Census.lean` imports all three and hands `cli` below a map from
`Standard.key` to emit, because `Gates/` may not import a test-side module.
Infra has no entry in that map and therefore no report. Every number this
executable prints therefore
comes from Lean data that the numerator's own elaboration-time gate has
already checked, and the two functions below re-check it against the census
they regenerate.

## Representation, and the R0 evidence each choice rests on

The file is carried as a `ByteArray` read by `IO.FS.readBinFile`, and every
offset is a `Nat` byte offset. `docs/research/2026-09-01-lean-stdlib-strategy-and-performance.md`
section 8 measures that effectively the whole `String` and `String.Slice` API
reaches `Classical.choice` while `ByteArray.extract`, `.size`, `.get!` and
`.push` reach no axiom at all, and its section 10.4 records that
`String.length` counts characters while the census anchors byte spans: on
this file the two differ by 190. `String` appears here only to render output
and to read short attribute values, never to compute an offset.

Scanning is fuel-bounded structural recursion on a `Nat`, with the fuel taken
as a size the data already carries plus one, as
`docs/research/2026-09-01-lean4-nlp-learnings.md` section 6.3 records for
lean4-nlp's scanners; that satisfies the no-`partial` rule with no
well-founded recursion obligation, and section 3.1 of the stdlib document
measures that a `termination_by` definition costs nothing at runtime anyway.
Byte access goes through the total `byteAt` rather than `bs[i]!`: section 1.4
measures the total accessor at 0.67 ms against 0.74 ms for the panicking one
on this file, so avoiding the panic path costs nothing.

Classification is ASCII-first (section 6.2 of the lean4-nlp document): every
structural byte this scanner tests is below 0x80, and non-ASCII bytes are
only ever copied, never classified. Anchors are extended to a UTF-8 character
boundary so that a rendered anchor is always valid UTF-8.

Accumulation is into a single linearly-threaded `Array`, never into an
`Array (Array _)` indexed by a key: section 8 of the lean4-nlp document
measures an 868x penalty for the aliased nested shape, and section 2.2 of the
stdlib document explains it as one full copy per write.

Span digests go through `Gates.Sha256.hexDigest`; section 1.6 of the stdlib
document measures 229 span digests over 374,064 bytes at 7.98 ms compiled and
1447 ms under `#eval`, so the digest pass belongs in the compiled executable
and never in an elaboration-time check.
-/

namespace Gates.Census

/-! ## Byte primitives -/

/-- Total byte access: out of range reads as zero, so no scan can panic. -/
@[inline] def byteAt (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0

@[inline] def byteNat (bs : ByteArray) (i : Nat) : Nat := (byteAt bs i).toNat

@[inline] def isSpaceByte (b : UInt8) : Bool :=
  b == 0x20 || b == 0x0a || b == 0x09 || b == 0x0d

/-- A UTF-8 continuation byte, `10xxxxxx`. -/
@[inline] def isContinuationByte (b : UInt8) : Bool := (b.toNat &&& 0xc0) == 0x80

private def matchAux (bs pat : ByteArray) (i j : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
    if Nat.ble pat.size j then true
    else if byteAt bs (i + j) == byteAt pat j then matchAux bs pat i (j + 1) fuel
    else false

/-- Whether `pat` occurs in `bs` starting exactly at `i`. -/
def matchesAt (bs pat : ByteArray) (i : Nat) : Bool :=
  Nat.ble (i + pat.size) bs.size && matchAux bs pat i 0 (pat.size + 1)

private def findAux (bs pat : ByteArray) (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if !Nat.ble (i + pat.size) bs.size then none
    else if matchesAt bs pat i then some i
    else findAux bs pat (i + 1) fuel

/-- The first occurrence of `pat` at or after `start`. Fuel is one per byte of
the subject, which is one more than the number of positions the scan can
visit. -/
def findFrom (bs pat : ByteArray) (start : Nat) : Option Nat :=
  findAux bs pat start (bs.size + 1)

private def collectAux (bs pat : ByteArray) (i : Nat) (acc : Array Nat) (cap : Nat) :
    Nat → Array Nat
  | 0 => acc
  | fuel + 1 =>
    if Nat.ble cap acc.size then acc
    else if !Nat.ble (i + pat.size) bs.size then acc
    else if matchesAt bs pat i then collectAux bs pat (i + 1) (acc.push i) cap fuel
    else collectAux bs pat (i + 1) acc cap fuel

/-- Every offset at which `pat` occurs, in increasing order, stopping once
`cap` offsets have been collected. The accumulator is threaded linearly, so
each `push` is in place. -/
def occurrences (bs pat : ByteArray) (cap : Nat) : Array Nat :=
  collectAux bs pat 0 #[] cap (bs.size + 1)

private def rangeEqAux (bs : ByteArray) (a b j n : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
    if Nat.ble n j then true
    else if byteAt bs (a + j) == byteAt bs (b + j) then rangeEqAux bs a b (j + 1) n fuel
    else false

/-- Whether the `n` bytes at `a` equal the `n` bytes at `b`, both in range. -/
def rangeEq (bs : ByteArray) (a b n : Nat) : Bool :=
  Nat.ble (a + n) bs.size && Nat.ble (b + n) bs.size && rangeEqAux bs a b 0 n (n + 1)

private def alignAux (bs : ByteArray) (i : Nat) : Nat → Nat
  | 0 => i
  | fuel + 1 =>
    if Nat.ble bs.size i then i
    else if isContinuationByte (byteAt bs i) then alignAux bs (i + 1) fuel
    else i

/-- The least offset at or after `i` that starts a UTF-8 character. A UTF-8
sequence is at most four bytes, so four steps always suffice. -/
def alignForward (bs : ByteArray) (i : Nat) : Nat := alignAux bs i 5

/-- The bytes `[b, e)` decoded as text, when they are valid UTF-8. -/
def sliceString? (bs : ByteArray) (b e : Nat) : Option String :=
  String.fromUTF8? (bs.extract b e)

/-! ## Small text utilities

These operate on `String` and are used only for names and rendering, never
to compute an offset. -/

@[inline] private def charNat (c : Char) : Nat := c.toNat
@[inline] private def isLowerC (c : Char) : Bool :=
  Nat.ble 0x61 (charNat c) && Nat.ble (charNat c) 0x7a
@[inline] private def isUpperC (c : Char) : Bool :=
  Nat.ble 0x41 (charNat c) && Nat.ble (charNat c) 0x5a
@[inline] private def isDigitC (c : Char) : Bool :=
  Nat.ble 0x30 (charNat c) && Nat.ble (charNat c) 0x39
@[inline] private def isIdentC (c : Char) : Bool :=
  isLowerC c || isUpperC c || isDigitC c || c == '_'
@[inline] private def lowerC (c : Char) : Char :=
  if isUpperC c then Char.ofNat (charNat c + 32) else c

/-- Kebab-case: ASCII letters and digits are kept and lowercased, a case
boundary inside a run of letters becomes a separator, every other byte run
becomes one separator, and separators never lead or trail. `BYOB` in
`ReadableStreamBYOBReader` stays one word because a separator is inserted
before an upper-case letter only when the previous character is lower-case or
a digit, or when the next character is lower-case. -/
def kebab (text : String) : String := Id.run do
  let a := text.toList.toArray
  let mut out : String := ""
  let mut lastDash := true
  for i in [0:a.size] do
    let c := a.getD i ' '
    if isLowerC c || isDigitC c then
      out := out.push c
      lastDash := false
    else if isUpperC c then
      let p := if i == 0 then ' ' else a.getD (i - 1) ' '
      let nextLower := isLowerC (a.getD (i + 1) ' ')
      if !lastDash && ((isLowerC p || isDigitC p) || (isUpperC p && nextLower)) then
        out := out.push '-'
      out := out.push (lowerC c)
      lastDash := false
    else
      if !lastDash then
        out := out.push '-'
      lastDash := true
  if out.endsWith "-" then Gates.Common.dropLastChars out 1 else out

/-- The interface or dictionary name of a `for=` attribute, flattened to one
lower-case word with no separators. This is Bikeshed's own spelling of a
member anchor (`dom-readablestream-locked`), and using it keeps a member id
distinct from the kebab-cased id of a same-named abstract operation:
`ReadableStream/close` becomes `readablestream-close` while the abstract
operation `ReadableStreamClose` becomes `readable-stream-close`. -/
def flattenName (text : String) : String := Id.run do
  let mut out : String := ""
  for c in text.toList do
    if isLowerC c || isDigitC c then out := out.push c
    else if isUpperC c then out := out.push (lowerC c)
  return out

/-- The trailing maximal run of identifier characters. -/
def trailingIdent (text : String) : String :=
  String.ofList (text.toList.reverse.takeWhile isIdentC).reverse

/-- The leading maximal run of identifier characters. -/
def leadingIdent (text : String) : String :=
  String.ofList (text.toList.takeWhile isIdentC)

/-- `text` without `prefix`, when it starts with it. Spelled here rather than
taken from the standard library because the 4.33.1 replacements for the
deprecated `String.stripPrefix` return a `String.Slice`, whose entry point
`String.toSlice` reaches `Classical.choice`. -/
def withoutPrefix (text pre : String) : String :=
  if text.startsWith pre then Gates.Common.dropChars text pre.length else text

/-- `text` without `suffix`, when it ends with it. -/
def withoutSuffix (text suf : String) : String :=
  if text.endsWith suf then Gates.Common.dropLastChars text suf.length else text

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

/-- Field escaping for the `|`-separated row format: a backslash escapes
itself, the field separator, and the three whitespace characters that would
otherwise break a row across lines. Every other byte is written through. -/
def escapeField (text : String) : String := Id.run do
  let mut out : String := ""
  for c in text.toList do
    if c == '\\' then out := out ++ "\\\\"
    else if c == '|' then out := out ++ "\\|"
    else if c == '\n' then out := out ++ "\\n"
    else if c == '\r' then out := out ++ "\\r"
    else if c == '\t' then out := out ++ "\\t"
    else out := out.push c
  return out

/-- Split one rendered row into its fields, undoing `escapeField`. -/
def splitRow (line : String) : Except String (Array String) := Id.run do
  let mut fields : Array String := #[]
  let mut current : String := ""
  let mut escaped := false
  let mut bad : Option String := none
  for c in line.toList do
    if escaped then
      escaped := false
      if c == '\\' then current := current.push '\\'
      else if c == '|' then current := current.push '|'
      else if c == 'n' then current := current.push '\n'
      else if c == 'r' then current := current.push '\r'
      else if c == 't' then current := current.push '\t'
      else bad := some s!"unknown escape \\{c}"
    else if c == '\\' then escaped := true
    else if c == '|' then
      fields := fields.push current
      current := ""
    else current := current.push c
  fields := fields.push current
  match bad with
  | some message => return .error message
  | none => if escaped then return .error "row ends with a dangling backslash" else return .ok fields

/-! ## Vocabulary -/

/-- The fixed row kinds of `docs/SPEC-COVERAGE.md`.

The first six are the original vocabulary; ruling R-P2 appends seven more for
the ECMA-262 census, after them and in that order, so that the sort key
`kind.name ++ "|" ++ id` of every existing Streams or Infra row is unchanged. -/
inductive Kind
  | idl
  | op
  | requirement
  | rule
  | slot
  /-- A carrier definition of a definition-keyed standard ("a byte sequence
  is a sequence of bytes"); every other definition there is an `op`. -/
  | type
  /-- An `<emu-clause type="built-in function">`. -/
  | builtin
  /-- An `<emu-clause type="host-defined abstract operation">`. -/
  | hook
  /-- A clause whose whole content is a property descriptor or initial value. -/
  | property
  /-- A clause defining a specification record type and its field table. -/
  | record
  /-- One `<tr>` of a record's field table. -/
  | field
  /-- A `<dfn>` that names neither a record nor an operation. -/
  | term
  /-- A structural clause with no operation, record or property of its own. -/
  | clause
  deriving BEq, DecidableEq, Inhabited

def Kind.name : Kind → String
  | .idl => "idl"
  | .op => "op"
  | .requirement => "requirement"
  | .rule => "rule"
  | .slot => "slot"
  | .type => "type"
  | .builtin => "builtin"
  | .hook => "hook"
  | .property => "property"
  | .record => "record"
  | .field => "field"
  | .term => "term"
  | .clause => "clause"

def Kind.ofString? : String → Option Kind
  | "idl" => some .idl
  | "op" => some .op
  | "requirement" => some .requirement
  | "rule" => some .rule
  | "slot" => some .slot
  | "type" => some .type
  | "builtin" => some .builtin
  | "hook" => some .hook
  | "property" => some .property
  | "record" => some .record
  | "field" => some .field
  | "term" => some .term
  | "clause" => some .clause
  | _ => none

def Kind.all : List Kind :=
  [.idl, .op, .requirement, .rule, .slot, .type,
   .builtin, .hook, .property, .record, .field, .term, .clause]

/-- The disposition vocabulary owned by `SPEC-MANIFEST.md`. -/
inductive Disposition
  | owned
  | requirement
  | foreignBoundary
  | hostOnly
  | refused
  | evidenceOnly
  | targetOnly
  deriving BEq, DecidableEq, Inhabited

def Disposition.name : Disposition → String
  | .owned => "owned"
  | .requirement => "requirement"
  | .foreignBoundary => "foreignBoundary"
  | .hostOnly => "hostOnly"
  | .refused => "refused"
  | .evidenceOnly => "evidenceOnly"
  | .targetOnly => "targetOnly"

def Disposition.ofString? : String → Option Disposition
  | "owned" => some .owned
  | "requirement" => some .requirement
  | "foreignBoundary" => some .foreignBoundary
  | "hostOnly" => some .hostOnly
  | "refused" => some .refused
  | "evidenceOnly" => some .evidenceOnly
  | "targetOnly" => some .targetOnly
  | _ => none

def Disposition.all : List Disposition :=
  [.owned, .requirement, .foreignBoundary, .hostOnly, .refused, .evidenceOnly, .targetOnly]

/-- A disposition outside the denominator, per `docs/SPEC-COVERAGE.md`. -/
def Disposition.excluded : Disposition → Bool
  | .evidenceOnly => true
  | .refused => true
  | .targetOnly => true
  | _ => false

/-- Coverage state. The middle constructor is spelled `partialCoverage`
because `partial` is a Lean keyword and the repository's source trust gate
rejects that token in an authored file; its external spelling is `partial`. -/
inductive CoverageState
  | absent
  | partialCoverage
  | green
  deriving BEq, DecidableEq, Inhabited

def CoverageState.name : CoverageState → String
  | .absent => "absent"
  | .partialCoverage => "partial"
  | .green => "green"

/-- One frozen numerator row. `WhatwgTest/Audit/SpecCoverage.lean` owns
the rules; this type is here so the generated row list and the census gate
share one spelling. -/
structure CoverageRow where
  id : String
  disposition : Disposition
  state : CoverageState
  witnesses : List String
  deriving Inhabited, BEq

/-! ## Rows -/

structure Row where
  kind : Kind
  id : String
  /-- Start of the anchor, always equal to `spanB`: the anchor is the span's
  own prefix, so locating the anchor locates the span. -/
  anchorB : Nat
  anchorE : Nat
  spanB : Nat
  spanE : Nat
  deriving Inhabited

def Row.sortKey (r : Row) : String := r.kind.name ++ "|" ++ r.id

/-! ## Standards

One census per standard. `streams` is the P1 census of the Streams Standard,
row-sourced from algorithm blocks, slot tables, IDL and the piping
requirements. `infra` is the definition-keyed census of the Infra Standard,
row-sourced from every `<dfn>` (`docs/INFRA-PROOF-PLAN.md` section 6), since
that text states 178 definitions against 18 algorithm blocks at its pin. The
constants after the two records keep their P1 names and denote the Streams
census, so the Streams numerator reads it unchanged. -/

/-- The per-scanner switches of the Bikeshed source profile (ruling R-P1).

- `algorithmRows` emit one `op` row per `<div>` carrying an `algorithm`
  attribute anywhere in its tag.
- `definitionRows` emit one row per Bikeshed definition, `<dfn>` or
  heading-borne.
- `idlRows` emit one `idl` row per statement of an IDL block.
- `slotRows` emit one `slot` row per qualified `[[Name]]`.
- `requirementMarker` the algorithm-block locator `scanRequirements` keys on;
  `none` emits no requirement rows at all.
- `sectionScope` restrict rows to the heading ids authored in
  `<authoredDir>/sections.tsv`; `false` is the whole document.
- `headingLevels` the inclusive heading-level range `scanHeadings` admits.
- `idlOpeners` the (opening tag, closing tag) pairs of an IDL block. -/
structure Bikeshed where
  algorithmRows : Bool
  definitionRows : Bool
  idlRows : Bool
  slotRows : Bool
  requirementMarker : Option String
  sectionScope : Bool
  headingLevels : Nat × Nat
  idlOpeners : Array (String × String)
  deriving Inhabited

/-- The source shape a standard is written in. `bikeshed` carries the switches
above; `ecmarkup` is served by `Gates/Ecmarkup.lean`, which the ES2026 builder
lands. -/
inductive Profile
  | bikeshed (switches : Bikeshed)
  | ecmarkup
  deriving Inhabited

structure Standard where
  /-- The `--standard` key on the command line. -/
  key : String
  /-- The label the coverage block prints. -/
  label : String
  inputRelativePath : String
  /-- The pin recorded in `SPEC-MANIFEST.md`. The generator refuses any other
  bytes. -/
  inputDigest : String
  censusRelativePath : String
  rowsRelativePath : String
  rowsNamespace : String
  /-- The directory of the authored inputs `dispositions.tsv`,
  `overrides.tsv`, `rules.tsv`, and, where the standard uses them,
  `types.tsv`, `sections.tsv`, `dependencies.tsv` and `externals.tsv`. -/
  authoredDir : String
  /-- The source profile (ruling R-P1), in the field position
  `definitionKeyed : Bool` occupied at P1. -/
  profile : Profile
  /-- Ruling R-P8: name an algorithm-block row from the block's `algorithm`
  attribute before consulting its first `<dfn>`. Off for Streams and Infra,
  which the identity packet freezes byte for byte. -/
  algorithmNameFirst : Bool
  /-- The standard carries an authored `types.tsv` naming its carrier
  definitions. Infra does; a standard that reads the Bikeshed dfn type from
  the source does not. -/
  authoredTypeNames : Bool
  /-- The standard carries authored `dependencies.tsv` and `externals.tsv`
  (ruling R-P6), validated in both directions. -/
  authoredDependencies : Bool
  /-- Generated censuses of other standards whose row ids a dependency line
  may name. This is the cross-census join of ruling R-P6. -/
  crossCensusPaths : List String
  deriving Inhabited

def streams : Standard :=
  { key := "streams", label := "WHATWG Streams (b9ba9f49)",
    inputRelativePath := "vendor/whatwg-streams-b9ba9f49/index.bs",
    inputDigest := "24360b4f8446e6c80e185c5021fcca9b67a7e0bb62490a00109080ebc04c6440",
    censusRelativePath := "generated/spec-algorithm-census.tsv",
    rowsRelativePath := "WhatwgTest/Audit/SpecCoverageRows.lean",
    rowsNamespace := "WhatwgTest.Audit.SpecCoverageRows",
    authoredDir := "census",
    profile := .bikeshed
      { algorithmRows := true, definitionRows := false, idlRows := true, slotRows := true,
        requirementMarker := some "<div algorithm=\"ReadableStreamPipeTo\">",
        sectionScope := false, headingLevels := (2, 4),
        idlOpeners := #[("<xmp class=\"idl\">", "</xmp>")] },
    algorithmNameFirst := false, authoredTypeNames := false,
    authoredDependencies := false, crossCensusPaths := [] }

def infra : Standard :=
  { key := "infra", label := "WHATWG Infra (3f984adc)",
    inputRelativePath := "vendor/whatwg-infra-3f984adc/infra.bs",
    inputDigest := "7c38e6e25ef21f536142cfc6d94954c41bc9889cd0b6fd67ab34571215acd8eb",
    censusRelativePath := "generated/infra-census.tsv",
    rowsRelativePath := "WhatwgTest/Audit/Infra/SpecCoverageRows.lean",
    rowsNamespace := "WhatwgTest.Audit.Infra.SpecCoverageRows",
    authoredDir := "census/infra",
    profile := .bikeshed
      { algorithmRows := false, definitionRows := true, idlRows := false, slotRows := false,
        requirementMarker := none,
        sectionScope := false, headingLevels := (2, 4),
        idlOpeners := #[] },
    algorithmNameFirst := false, authoredTypeNames := true,
    authoredDependencies := false, crossCensusPaths := [] }

/-- The promise lane's Web IDL census (`docs/PROMISE-PACKAGE-PLAN.md`, slice
Q1; packet `test/contracts/webidl-census.contract.md`). Five sections of the
pinned `index.bs`, algorithm blocks, Bikeshed definitions and two IDL blocks;
no `slot` rows and no `scanRequirements` marker (ruling R-P4). -/
def webidl : Standard :=
  { key := "webidl", label := "WHATWG Web IDL (a652053f)",
    inputRelativePath := "vendor/whatwg-webidl-a652053f/index.bs",
    inputDigest := "3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83",
    censusRelativePath := "generated/webidl-census.tsv",
    rowsRelativePath := "WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean",
    rowsNamespace := "WhatwgTest.Audit.WebIdl.SpecCoverageRows",
    authoredDir := "census/webidl",
    profile := .bikeshed
      { algorithmRows := true, definitionRows := true, idlRows := true, slotRows := false,
        requirementMarker := none,
        sectionScope := true, headingLevels := (2, 5),
        idlOpeners := #[("<pre class=\"idl\">", "</pre>"), ("<pre class=idl>", "</pre>")] },
    algorithmNameFirst := true, authoredTypeNames := false,
    authoredDependencies := true, crossCensusPaths := ["generated/infra-census.tsv"] }

/-- The promise lane's ECMA-262 census (`docs/PROMISE-PACKAGE-PLAN.md`, slice
Q1; packet `test/contracts/ecma262-census.contract.md`). Two root clauses of
the pinned `spec.html`, read through `Gates.Ecmarkup` rather than through the
Bikeshed scanners: `<emu-clause>` primary rows, `<emu-table>` body rows,
requirement bullets and `<dfn>` terms. No `types.tsv`, no cross-census join,
and `algorithmNameFirst` is inert here because no Bikeshed scanner runs. -/
def ecma262 : Standard :=
  { key := "ecma262", label := "ECMAScript ES2026 (0248456c)",
    inputRelativePath := "vendor/ecma262-0248456c/spec.html",
    inputDigest := "ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0",
    censusRelativePath := "generated/ecma262-census.tsv",
    rowsRelativePath := "WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean",
    rowsNamespace := "WhatwgTest.Audit.Ecma262.SpecCoverageRows",
    authoredDir := "census/ecma262",
    profile := .ecmarkup,
    algorithmNameFirst := false, authoredTypeNames := false,
    authoredDependencies := true, crossCensusPaths := [] }

def standards : List Standard := [streams, infra, webidl, ecma262]

def Standard.ofKey? (key : String) : Option Standard := standards.find? (·.key == key)

def Standard.dispositionsRelativePath (s : Standard) : String := s.authoredDir ++ "/dispositions.tsv"

def Standard.overridesRelativePath (s : Standard) : String := s.authoredDir ++ "/overrides.tsv"

def Standard.rulesRelativePath (s : Standard) : String := s.authoredDir ++ "/rules.tsv"

def Standard.typesRelativePath (s : Standard) : String := s.authoredDir ++ "/types.tsv"

def Standard.sectionsRelativePath (s : Standard) : String := s.authoredDir ++ "/sections.tsv"

def Standard.dependenciesRelativePath (s : Standard) : String := s.authoredDir ++ "/dependencies.tsv"

def Standard.externalsRelativePath (s : Standard) : String := s.authoredDir ++ "/externals.tsv"

def Standard.regenerateCommand (s : Standard) : String :=
  if s.key == "streams" then "lake exe census --write"
  else s!"lake exe census --standard {s.key} --write"

def inputRelativePath : String := streams.inputRelativePath

def inputDigest : String := streams.inputDigest

def censusRelativePath : String := streams.censusRelativePath

def rowsRelativePath : String := streams.rowsRelativePath

def dispositionsRelativePath : String := streams.dispositionsRelativePath

def overridesRelativePath : String := streams.overridesRelativePath

def rulesRelativePath : String := streams.rulesRelativePath

def formatVersion : String := "1"

def regenerateCommand : String := streams.regenerateCommand

/-! ## Section index -/

structure Heading where
  level : Nat
  id : String
  off : Nat
  deriving Inhabited

/-- The value of attribute `name` inside the tag `[tagB, tagE)`, quoted or
unquoted: the Streams source writes `id="..."` and the Infra source writes
`id=...`. The attribute name must be preceded by whitespace, so `id=` is never
read out of `oldids=`. An unquoted value runs to the next whitespace or `>`. -/
def attrValue? (bs : ByteArray) (tagB tagE : Nat) (name : String) : Option String := Id.run do
  let key := (name ++ "=").toUTF8
  for i in [tagB:tagE] do
    if matchesAt bs key i && i > 0 && isSpaceByte (byteAt bs (i - 1)) then
      let vs := i + key.size
      if byteAt bs vs == 0x22 then
        match findFrom bs (ByteArray.mk #[0x22]) (vs + 1) with
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

/-- Whether `name` occurs as a bare, valueless attribute inside the tag
`[tagB, tagE)`, as `ignore` does in `<dfn ignore>`. -/
def hasBareAttr (bs : ByteArray) (tagB tagE : Nat) (name : String) : Bool := Id.run do
  let key := name.toUTF8
  for i in [tagB:tagE] do
    if matchesAt bs key i && i > 0 && isSpaceByte (byteAt bs (i - 1)) then
      let after := byteAt bs (i + key.size)
      if isSpaceByte after || after == 0x3e then return true
  return false

/-- Every heading inside the profile's inclusive level range that opens a line
and carries an `id` attribute, in document order. The default range `(2, 4)` is
the P1 behaviour; ruling R-P1 makes it a profile field so that a standard
writing definitions under an `<h5>` can be walked. -/
def scanHeadings (bs : ByteArray) (levels : Nat × Nat := (2, 4)) :
    Except String (Array Heading) := Id.run do
  let (lo, hi) := levels
  let openTag := "<h".toUTF8
  let gt := ">".toUTF8
  let mut out : Array Heading := #[]
  for i in occurrences bs openTag 4096 do
    if i != 0 && byteAt bs (i - 1) != 0x0a then continue
    let d := byteNat bs (i + 2)
    if d < 0x30 + lo || d > 0x30 + hi then continue
    if !isSpaceByte (byteAt bs (i + 3)) then continue
    let some tagE := findFrom bs gt i
      | return .error s!"census: unterminated heading tag at byte {i}"
    match attrValue? bs i tagE "id" with
    | none => continue
    | some name => out := out.push { level := d - 0x30, id := name, off := i }
  return .ok out

/-- The heading ancestry at `off`, innermost first, with every level of the
profile's range that has no enclosing heading spelled as the empty string.
`sectionPath` is the P1 three-level face of the same walk. -/
def sectionAncestry (hs : Array Heading) (levels : Nat × Nat) (off : Nat) :
    Array String := Id.run do
  let (lo, hi) := levels
  if hi < lo then return #[]
  let depth := hi - lo + 1
  let mut current : Array String := #[]
  for _ in [0:depth] do
    current := current.push ""
  for h in hs do
    if h.off > off then break
    if h.level < lo || h.level > hi then continue
    let idx := h.level - lo
    current := current.set! idx h.id
    -- every deeper level is closed by a shallower heading
    for j in [idx + 1 : depth] do
      current := current.set! j ""
  return current.reverse

/-- The innermost enclosing `<h4>`, `<h3>` and `<h2>` ids at `off`, empty
where there is none. -/
def sectionPath (hs : Array Heading) (off : Nat) : String × String × String :=
  let a := sectionAncestry hs (2, 4) off
  (a.getD 0 "", a.getD 1 "", a.getD 2 "")

/-- One section of a `sections.tsv` scope: its heading id and the half-open
byte interval it governs, which runs from its heading tag to the next
line-opening heading of the same or a higher level. -/
structure Section where
  id : String
  b : Nat
  e : Nat
  deriving Inhabited

/-- `none` is whole-document scope, which is what Streams and Infra have. -/
def inScope? (scope : Option (Array Section)) (off : Nat) : Bool :=
  match scope with
  | none => true
  | some sections => sections.any (fun s => Nat.ble s.b off && !Nat.ble s.e off)

/-- The authored `sections.tsv`: one heading id per line. -/
def parseSections (text : String) (path : String) : Except String (Array String) := Id.run do
  let mut out : Array String := #[]
  let mut lineNumber := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    let trimmed := Gates.Common.trimmed line
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    if trimmed != line then
      return .error s!"{path} line {lineNumber}: a section id carries surrounding whitespace"
    if out.contains trimmed then
      return .error s!"{path} line {lineNumber}: duplicate section id {trimmed}"
    out := out.push trimmed
  return .ok out

/-- Resolve each authored scope id against the heading index. A listed id that
is not a line-opening heading with that exact `id`, or that occurs more than
once, fails generation. -/
def sectionExtents (bs : ByteArray) (hs : Array Heading) (ids : Array String) (path : String) :
    Except String (Array Section) := Id.run do
  let mut out : Array Section := #[]
  for id in ids do
    let hits := hs.filter (fun h => h.id == id)
    if hits.size == 0 then
      return .error s!"{path}: no line-opening heading in the pinned bytes carries id {id}"
    if hits.size != 1 then
      return .error s!"{path}: heading id {id} occurs {hits.size} times"
    let h := hits.getD 0 default
    let mut stop := bs.size
    for k in hs do
      if k.off > h.off && Nat.ble k.level h.level then
        stop := k.off
        break
    out := out.push { id := id, b := h.off, e := stop }
  return .ok out

/-! ## Attributes -/

private def attrAux (bs key : ByteArray) (i limit : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | fuel + 1 =>
    if Nat.ble limit i then none
    else if matchesAt bs key i && (i == 0 || isSpaceByte (byteAt bs (i - 1))) then
      match findFrom bs (ByteArray.mk #[0x22]) (i + key.size) with
      | some ve => if Nat.ble ve limit then some (i + key.size, ve) else none
      | none => none
    else attrAux bs key (i + 1) limit fuel

/-- The value span of attribute `name` inside the tag `[tagB, tagE)`. The
attribute name must be preceded by whitespace, so `id=` is never read out of
`oldids=`. -/
def attrSpan? (bs : ByteArray) (tagB tagE : Nat) (name : String) : Option (Nat × Nat) :=
  attrAux bs (name ++ "=\"").toUTF8 tagB tagE (tagE - tagB + 1)

def attrText? (bs : ByteArray) (tagB tagE : Nat) (name : String) : Option String := do
  let (vs, ve) ← attrSpan? bs tagB tagE name
  sliceString? bs vs ve

/-! ## Anchors -/

/-- Anchor lengths tried in order. The anchor is the shortest prefix of the
row's span, aligned to a UTF-8 boundary, that occurs exactly once in the
pinned bytes. -/
def anchorLadder : List Nat :=
  [24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048, 3072, 4096]

private def firstUnique (bs : ByteArray) (start : Nat) (rivals : Array Nat) :
    List Nat → Option Nat
  | [] => none
  | n :: rest =>
    let aligned := alignForward bs (start + n) - start
    if !Nat.ble (start + aligned) bs.size then none
    else if rivals.all (fun p => !rangeEq bs start p aligned) then some aligned
    else firstUnique bs start rivals rest

/-- The anchor length for a span starting at `start`, or the offset of a rival
occurrence that no admitted length separates. -/
def chooseAnchorLength (bs : ByteArray) (start : Nat) : Except Nat Nat := Id.run do
  let remaining := bs.size - start
  let baseWanted := if Nat.ble remaining 24 then remaining else 24
  let base := alignForward bs (start + baseWanted) - start
  let probe := bs.extract start (start + base)
  let rivals := (occurrences bs probe 4096).filter (fun p => p != start)
  if rivals.isEmpty then return .ok base
  let ladder := anchorLadder.filter (fun n => n > base) ++ [remaining]
  match firstUnique bs start rivals ladder with
  | some n => return .ok n
  | none => return .error (rivals.getD 0 0)

/-! ## Abstract-operation rows

Every algorithm block opens with the byte prefix `<div algorithm`, never the
closing bracket: `docs/research/2026-09-01-lean-stdlib-strategy-and-performance.md`
section 1.5 measures 229 occurrences of `<div algorithm>` against 248 of
`<div algorithm`, so keying on the bracket silently drops the 19 attributed
blocks.

The id is the specification's own identifier wherever the text supplies one,
in this order: the opener's `id`; then the block's first `<dfn>`, by its `id`,
else by the first alternative of its `lt`, else by its text, in the last two
cases prefixed by the flattened `for` class; and only then the opener's
`algorithm` attribute. Consulting the block's `<dfn>` before the `algorithm`
attribute is what keeps an exported wrapper distinct from the abstract
operation it wraps. -/

/-- The end offset (just past the matching close tag of length `closeLen`)
of the block whose opener precedes `opens[oi]` and `closes[ci]`, counting
nested openers. -/
private def matchCloseAux (opens closes : Array Nat) (closeLen : Nat) (oi ci depth : Nat) :
    Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    match closes[ci]? with
    | none => none
    | some cv =>
      match opens[oi]? with
      | some ov =>
        if ov < cv then matchCloseAux opens closes closeLen (oi + 1) ci (depth + 1) fuel
        else if depth == 0 then some (cv + closeLen)
        else matchCloseAux opens closes closeLen oi (ci + 1) (depth - 1) fuel
      | none =>
        if depth == 0 then some (cv + closeLen)
        else matchCloseAux opens closes closeLen oi (ci + 1) (depth - 1) fuel

private def firstIndexAfter (xs : Array Nat) (bound : Nat) : Nat := Id.run do
  let mut i := 0
  for x in xs do
    if x > bound then return i
    i := i + 1
  return i

/-- Whether the `<div>` tag `[tagB, tagE)` carries an `algorithm` attribute
anywhere in the tag, valued or bare. Ruling R-P1 replaces the byte prefix
`<div algorithm` with this test: the Streams source has 248 such tags under
either rule and the Infra source 18, so the change is byte-neutral for both,
while the Web IDL source gains the 45 blocks that write `id=` first. -/
def hasAlgorithmAttr (bs : ByteArray) (tagB tagE : Nat) : Bool :=
  (attrValue? bs tagB (tagE + 1) "algorithm").isSome || hasBareAttr bs tagB (tagE + 1) "algorithm"

/-- Every algorithm block as `(opener, end)`, in document order. -/
def algorithmBlocks (bs : ByteArray) : Except String (Array (Nat × Nat)) := Id.run do
  let gt := ">".toUTF8
  let opens := occurrences bs "<div".toUTF8 4096
  let closes := occurrences bs "</div>".toUTF8 4096
  let mut out : Array (Nat × Nat) := #[]
  for i in opens do
    let some tagE := findFrom bs gt i
      | return .error s!"census: unterminated <div tag at byte {i}"
    if !hasAlgorithmAttr bs i tagE then continue
    let oi := firstIndexAfter opens i
    let ci := firstIndexAfter closes i
    let some e := matchCloseAux opens closes 6 oi ci 0 (opens.size + closes.size + 1)
      | return .error s!"census: unbalanced algorithm block at byte {i}"
    out := out.push (i, e)
  return .ok out

/-- One `op` row per algorithm block in scope. `nameFirst` is ruling R-P8: read
the block's `algorithm` attribute before its first `<dfn>`. The opener's `id`
still wins over both. -/
def scanOps (bs : ByteArray) (blocks : Array (Nat × Nat)) (nameFirst : Bool)
    (scope : Option (Array Section)) : Except String (Array Row) := Id.run do
  let gt := ">".toUTF8
  let dfnOpen := "<dfn".toUTF8
  let dfnClose := "</dfn>".toUTF8
  let mut out : Array Row := #[]
  for (i, blockEnd) in blocks do
    if !inScope? scope i then continue
    let some tagE := findFrom bs gt i
      | return .error s!"census: unterminated <div algorithm at byte {i}"
    let mut name : Option String := none
    match attrText? bs i (tagE + 1) "id" with
    | some divId => name := some (kebab divId)
    | none => pure ()
    if name.isNone && nameFirst then
      match attrText? bs i (tagE + 1) "algorithm" with
      | some alg => name := some (kebab alg)
      | none => pure ()
    if name.isNone then
      match findFrom bs dfnOpen (tagE + 1) with
      | some d =>
        if d < blockEnd then
          let some dfnTagE := findFrom bs gt d
            | return .error s!"census: unterminated <dfn at byte {d}"
          let owner :=
            match attrText? bs d (dfnTagE + 1) "for" with
            | some f => flattenName f ++ "-"
            | none => ""
          match attrText? bs d (dfnTagE + 1) "id" with
          | some dfnId => name := some (kebab dfnId)
          | none =>
            match attrText? bs d (dfnTagE + 1) "lt" with
            | some lt =>
              let head := (lt.splitOn "|").headD lt
              name := some (owner ++ kebab head)
            | none =>
              let some textE := findFrom bs dfnClose (dfnTagE + 1)
                | return .error s!"census: unterminated <dfn> text at byte {d}"
              let some text := sliceString? bs (dfnTagE + 1) textE
                | return .error s!"census: <dfn> text at byte {d} is not valid UTF-8"
              name := some (owner ++ kebab (normalizeWhitespace text))
      | none => pure ()
    if name.isNone then
      match attrText? bs i (tagE + 1) "algorithm" with
      | some alg => name := some (kebab alg)
      | none => return .error s!"census: algorithm block at byte {i} carries no derivable name"
    let some derived := name
      | return .error s!"census: algorithm block at byte {i} carries no derivable name"
    if derived.isEmpty then
      return .error s!"census: algorithm block at byte {i} derived an empty name"
    out := out.push { kind := .op, id := "op." ++ derived,
                      anchorB := i, anchorE := i, spanB := i, spanE := blockEnd }
  return .ok out

/-! ## Internal-slot rows

A candidate is any `[[Name]]` whose name is letters, digits, underscores and
spaces. Bikeshed writes a biblio reference the same way, so a candidate counts
as an internal slot only when at least one of its occurrences is preceded by
`\` (the escaped spelling the specification uses in algorithm text) or by `/`
(the class-qualified spelling inside a `[=Class/[[slot]]=]` autolink). On the
pinned bytes that rule admits 62 names and rejects exactly four —
`[[FETCH]]`, `[[COMPRESSION]]`, `[[ENCODING]]` and `[[WEBSOCKETS]]` — each of
which occurs only unqualified and is a bibliography citation.

A row is anchored at the first `<dfn>` that defines the name if there is one,
and otherwise at the first qualified occurrence. -/

private def slotNameAt (bs : ByteArray) (i : Nat) : Option (String × Nat) := Id.run do
  let mut j := i + 2
  let mut ok := true
  for _ in [0:48] do
    let b := byteNat bs j
    if b == 0x5d then break
    let isName :=
      (Nat.ble 0x41 b && Nat.ble b 0x5a) || (Nat.ble 0x61 b && Nat.ble b 0x7a) ||
      (Nat.ble 0x30 b && Nat.ble b 0x39) || b == 0x5f || b == 0x20
    if !isName then
      ok := false
      break
    j := j + 1
  if !ok then return none
  if byteNat bs j != 0x5d || byteNat bs (j + 1) != 0x5d then return none
  if j == i + 2 then return none
  match sliceString? bs (i + 2) j with
  | none => return none
  | some name => return some (name, j + 2)

structure SlotEntry where
  name : String
  firstQualified : Option Nat
  defining : Option Nat
  deriving Inhabited

def scanSlots (bs : ByteArray) : Except String (Array Row) := Id.run do
  let brackets := "[[".toUTF8
  let dfnOpen := "<dfn".toUTF8
  let gt := ">".toUTF8
  let closeBrackets := "]]".toUTF8
  let mut entries : Array SlotEntry := #[]
  -- Pass one: names, in first-appearance order, with the first qualified use.
  for i in occurrences bs brackets 8192 do
    match slotNameAt bs i with
    | none => pure ()
    | some (name, _) =>
      let prev := byteNat bs (i - 1)
      let qualified := i > 0 && (prev == 0x5c || prev == 0x2f)
      match entries.findIdx? (fun e => e.name == name) with
      | some k =>
        if qualified && (entries.getD k default).firstQualified.isNone then
          entries := entries.modify k (fun e => { e with firstQualified := some i })
      | none =>
        entries := entries.push
          { name := name, firstQualified := if qualified then some i else none, defining := none }
  -- Pass two: the first defining `<dfn>` for each name.
  for d in occurrences bs dfnOpen 4096 do
    let some tagE := findFrom bs gt d
      | return .error s!"census: unterminated <dfn at byte {d}"
    let named : Option String :=
      match attrSpan? bs d (tagE + 1) "lt" with
      | some (vs, _) => (slotNameAt bs vs).map (fun p => p.1)
      | none =>
        let afterTag := if byteNat bs (tagE + 1) == 0x5c then tagE + 2 else tagE + 1
        if byteNat bs afterTag == 0x5b && byteNat bs (afterTag + 1) == 0x5b then
          (slotNameAt bs afterTag).map (fun p => p.1)
        else none
    match named with
    | none => pure ()
    | some name =>
      match entries.findIdx? (fun e => e.name == name) with
      | none => pure ()
      | some k =>
        if (entries.getD k default).defining.isNone then
          entries := entries.modify k (fun e => { e with defining := some d })
  -- Emit one row per qualified name.
  let mut out : Array Row := #[]
  for e in entries do
    if e.firstQualified.isNone then continue
    let start := match e.defining with
      | some d => d
      | none => e.firstQualified.getD 0
    let some closeAt := findFrom bs closeBrackets start
      | return .error s!"census: unterminated internal slot at byte {start}"
    out := out.push { kind := .slot, id := "slot." ++ kebab e.name,
                      anchorB := start, anchorE := start, spanB := start, spanE := closeAt + 2 }
  return .ok out

/-! ## Web IDL rows

Every `<xmp class="idl">` block is read statement by statement: lines are
accumulated, with their leading and trailing whitespace dropped and joined by
one space, until the accumulation ends in `;` or `{`. A statement ending in
`{` opens an interface, interface mixin or dictionary and emits a declaration
row spanning the header itself; `};` closes it; a `callback` statement emits a
declaration row; and every statement inside a body emits a constructor,
attribute, method or dictionary-member row.

A `typedef`, `enum` or `includes` statement also emits an `idl` row, as
`SPEC-MANIFEST.md` rules under "Rulings made at P1 landing" and
`docs/SPEC-COVERAGE.md` records. A `typedef` and an `enum` each declare a
name, so each is identified the way an interface or dictionary declaration is,
by the kebab-cased name it declares. An `includes` statement declares no name
of its own: it relates two names that are themselves declaration rows, so it
is identified by both, as `<includer>-includes-<mixin>`. Every one of the
three is `hostOnly` at the boundary, which it reaches through its enclosing
section rather than through an override.

Any other top-level statement is counted rather than dropped silently, and the
count is reported. It is zero at the pin. -/

structure IdlStatement where
  text : String
  b : Nat
  e : Nat
  deriving Inhabited

private def lineEnd (bs : ByteArray) (i : Nat) : Nat :=
  match findFrom bs (ByteArray.mk #[0x0a]) i with
  | some n => n
  | none => bs.size

private def trimSpanStart (bs : ByteArray) (b e : Nat) : Nat := Id.run do
  let mut i := b
  for _ in [0:e - b] do
    if i < e && isSpaceByte (byteAt bs i) then i := i + 1 else break
  return i

private def trimSpanEnd (bs : ByteArray) (b e : Nat) : Nat := Id.run do
  let mut i := e
  for _ in [0:e - b] do
    if i > b && isSpaceByte (byteAt bs (i - 1)) then i := i - 1 else break
  return i

private def stripExtendedAttribute (text : String) : String :=
  if text.startsWith "[" then
    match text.splitOn "] " with
    | _ :: rest => Gates.Common.trimmed (String.intercalate "] " rest)
    | [] => text
  else text

/-- The offset of a trailing `//` comment inside `[b, e)`, or `e` where there
is none. The `//` must open the line or follow whitespace, so a `//` inside a
string literal is not mistaken for a comment. The Streams source writes no
comment inside an IDL block, so stripping is byte-neutral there; the Web IDL
`DOMException` header line ends in one and never terminates without it. -/
private def commentStart (bs : ByteArray) (b e : Nat) : Nat := Id.run do
  let mut i := b
  for _ in [b:e] do
    if i + 1 >= e then break
    if byteAt bs i == 0x2f && byteAt bs (i + 1) == 0x2f &&
        (i == b || isSpaceByte (byteAt bs (i - 1))) then
      return i
    i := i + 1
  return e

def scanIdl (bs : ByteArray) (openers : Array (String × String))
    (scope : Option (Array Section)) : Except String (Array Row × Nat) := Id.run do
  let mut blockStarts : Array (Nat × String) := #[]
  for (openText, closeText) in openers do
    for b in occurrences bs openText.toUTF8 256 do
      blockStarts := blockStarts.push (b, closeText)
  let ordered := blockStarts.qsort (fun a b => a.1 < b.1)
  let mut out : Array Row := #[]
  let mut skipped : Nat := 0
  for (blockStart, closeText) in ordered do
    if !inScope? scope blockStart then continue
    let some blockEnd := findFrom bs closeText.toUTF8 blockStart
      | return .error s!"census: unterminated IDL block at byte {blockStart}"
    let mut cursor := lineEnd bs blockStart + 1
    let mut owner : String := ""
    let mut ownerIsDictionary := false
    let mut acc : String := ""
    let mut accB : Nat := 0
    let mut accE : Nat := 0
    for _ in [0:4096] do
      if cursor >= blockEnd then break
      let le0 := lineEnd bs cursor
      let tb := trimSpanStart bs cursor le0
      let le := commentStart bs tb le0
      let te := trimSpanEnd bs tb le
      if tb < te then
        let some piece := sliceString? bs tb te
          | return .error s!"census: IDL line at byte {tb} is not valid UTF-8"
        if acc.isEmpty then
          acc := piece
          accB := tb
        else
          acc := acc ++ " " ++ piece
        accE := te
      cursor := le0 + 1
      if acc.isEmpty then continue
      if !(acc.endsWith ";" || acc.endsWith "{") then continue
      let statement := acc
      acc := ""
      if owner.isEmpty then
        if statement.endsWith "{" then
          let core := stripExtendedAttribute statement
          let words := (core.splitOn " ").filter (fun w => !w.isEmpty)
          match words with
          | ["interface", "mixin", name, "{"] =>
            owner := name; ownerIsDictionary := false
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          | ["interface", name, "{"] =>
            owner := name; ownerIsDictionary := false
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          | ["dictionary", name, "{"] =>
            owner := name; ownerIsDictionary := true
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          -- An interface that inherits: `interface QuotaExceededError : DOMException {`.
          | ["interface", name, ":", _base, "{"] =>
            owner := name; ownerIsDictionary := false
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          | _ => return .error s!"census: unrecognised IDL header at byte {accB}: {statement}"
        else if statement.startsWith "callback " then
          let name := trailingIdent ((statement.splitOn " =").headD statement)
          if name.isEmpty then
            return .error s!"census: callback at byte {accB} has no name"
          out := out.push { kind := .idl, id := "idl." ++ kebab name,
                            anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
        else
          let body := Gates.Common.trimmed (withoutSuffix statement ";")
          if body.startsWith "typedef " then
            let name := trailingIdent body
            if name.isEmpty then
              return .error s!"census: typedef at byte {accB} declares no name: {statement}"
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          else if body.startsWith "enum " then
            let name := leadingIdent (Gates.Common.trimmed (withoutPrefix body "enum "))
            if name.isEmpty then
              return .error s!"census: enum at byte {accB} declares no name: {statement}"
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          else
            match body.splitOn " includes " with
            | [includer, included] =>
              let target := trailingIdent includer
              let mixinName := leadingIdent included
              if target.isEmpty || mixinName.isEmpty then
                return .error s!"census: includes statement at byte {accB} names no pair: {statement}"
              out := out.push
                { kind := .idl,
                  id := "idl." ++ kebab target ++ "-includes-" ++ kebab mixinName,
                  anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
            | _ => skipped := skipped + 1
      else if statement == "};" then
        owner := ""
        ownerIsDictionary := false
      else
        let body := Gates.Common.trimmed (withoutSuffix statement ";")
        let member :=
          if body.startsWith "constructor(" || body.startsWith "constructor (" then "constructor"
          else if body.startsWith "attribute " || body.startsWith "readonly attribute " then
            trailingIdent body
          -- `const unsigned short INDEX_SIZE_ERR = 1;` declares INDEX_SIZE_ERR,
          -- not the initialiser.
          else if body.startsWith "const " then
            trailingIdent ((body.splitOn " = ").headD body)
          else if ownerIsDictionary then
            trailingIdent ((body.splitOn " = ").headD body)
          else
            let head := (body.splitOn "(").headD body
            let t := trailingIdent head
            if t.isEmpty then leadingIdent head else t
        if member.isEmpty then
          return .error s!"census: IDL member at byte {accB} has no name: {statement}"
        out := out.push { kind := .idl, id := "idl." ++ flattenName owner ++ "-" ++ kebab member,
                          anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
    if !owner.isEmpty then
      return .error s!"census: IDL block at byte {blockStart} leaves {owner} unclosed"
  return .ok (out, skipped)

/-! ## Piping-requirement rows

The requirements are the bullet list inside the `ReadableStreamPipeTo`
algorithm block. A requirement row is one *top-level* bullet of that list: a
line whose first non-space character is `*`, at the smallest indentation any
such line in the block has. Its span runs from that `*` to the start of the
next line, at that indentation or shallower, that opens a list item (`*` or
`1.`), or to the end of the block, with trailing whitespace trimmed. Nested
bullets and numbered sub-steps therefore stay inside the requirement they
qualify rather than becoming rows of their own.

The id is the bullet's own `<dfn>` id when it has one, and otherwise the
kebab-cased lead-in of its `<strong>` label. -/

structure ListLine where
  off : Nat
  indent : Nat
  isBullet : Bool
  deriving Inhabited

/-- Ruling R-P1: the marker is the profile's `requirementMarker`, and a profile
that supplies none never calls this scanner. -/
def scanRequirements (bs : ByteArray) (markerText : String) (opRows : Array Row) :
    Except String (Array Row) := Id.run do
  let marker := markerText.toUTF8
  let some blockStart := findFrom bs marker 0
    | return .error s!"census: the requirement-marker block {markerText} was not found"
  let some pipeRow := opRows.find? (fun r => r.spanB == blockStart)
    | return .error s!"census: the block at {markerText} is not an algorithm row"
  let blockEnd := pipeRow.spanE
  -- Collect every list-item line in the block.
  let mut items : Array ListLine := #[]
  let mut cursor := lineEnd bs blockStart + 1
  for _ in [0:8192] do
    if cursor >= blockEnd then break
    let le := lineEnd bs cursor
    let tb := trimSpanStart bs cursor le
    if tb < le then
      let indent := tb - cursor
      if byteNat bs tb == 0x2a && byteNat bs (tb + 1) == 0x20 then
        items := items.push { off := tb, indent := indent, isBullet := true }
      else if byteNat bs tb == 0x31 && byteNat bs (tb + 1) == 0x2e &&
              byteNat bs (tb + 2) == 0x20 then
        items := items.push { off := tb, indent := indent, isBullet := false }
    cursor := le + 1
  let bullets := items.filter (·.isBullet)
  if bullets.isEmpty then
    return .error "census: the ReadableStreamPipeTo block states no requirement bullets"
  let minIndent := bullets.foldl (fun acc it => if it.indent < acc then it.indent else acc) 1000
  let tops := bullets.filter (·.indent == minIndent)
  let mut out : Array Row := #[]
  for top in tops do
    let nextItem := items.find? (fun it => it.off > top.off && it.indent <= minIndent)
    let rawEnd := match nextItem with
      | some it => it.off - it.indent
      | none => blockEnd
    let spanE := trimSpanEnd bs top.off rawEnd
    let some text := sliceString? bs top.off spanE
      | return .error s!"census: requirement bullet at byte {top.off} is not valid UTF-8"
    let body := Gates.Common.trimmed (withoutPrefix text "*")
    let name :=
      if body.startsWith "<dfn " then
        match attrText? bs top.off spanE "id" with
        | some anchorId => kebab anchorId
        | none => ""
      else if body.startsWith "<strong>" then
        let rest := withoutPrefix body "<strong>"
        kebab ((rest.splitOn ":").headD rest)
      else ""
    if name.isEmpty then
      return .error s!"census: requirement bullet at byte {top.off} carries no derivable name"
    out := out.push { kind := .requirement, id := "requirement." ++ name,
                      anchorB := top.off, anchorE := top.off, spanB := top.off, spanE := spanE }
  return .ok out

/-! ## Authored cross-cutting rules

`census/rules.tsv` is the authored extension point for `rule` rows, which the
text states as prose rather than as an algorithm. Each line is
`<kebab-name>` TAB `<locator>`, where the locator must occur exactly once in
the pinned bytes; the span runs from the locator to the next blank line. The
file is empty at P1. -/

structure RuleInput where
  name : String
  locator : String
  /-- Ruling R-P4: the optional third field. With `none` the span runs from the
  locator to the next blank line, exactly as it does at P1; with `some`, to the
  end locator's one occurrence in the pinned bytes, which must lie strictly
  after the start locator, trailing ASCII whitespace trimmed (review debt D7,
  2026-09-07: uniqueness and the strict order were unchecked before). -/
  endLocator : Option String
  deriving Inhabited

def parseRules (text : String) (path : String := rulesRelativePath) :
    Except String (Array RuleInput) := Id.run do
  let mut out : Array RuleInput := #[]
  let mut lineNumber := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    let trimmed := Gates.Common.trimmed line
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    match line.splitOn "\t" with
    | [name, locator] =>
      if name.isEmpty || locator.isEmpty then
        return .error s!"{path} line {lineNumber}: empty field"
      out := out.push { name := name, locator := locator, endLocator := none }
    | [name, locator, endLocator] =>
      if name.isEmpty || locator.isEmpty || endLocator.isEmpty then
        return .error s!"{path} line {lineNumber}: empty field"
      out := out.push { name := name, locator := locator, endLocator := some endLocator }
    | _ =>
      return .error s!"{path} line {lineNumber}: expected two or three tab-separated fields"
  return .ok out

/-- Review debt D7 (2026-09-07): the occurrence caps here are the true counts,
not a count clipped to the smallest number that decides the test.

Both locators are required to occur **exactly once** in the pinned bytes, and
both counts are taken with a cap of `bs.size + 1`, which no locator can reach,
so a refusal names how many occurrences there really are instead of saying
"2 times" for a string that occurs eleven. The end locator's one occurrence
must also lie strictly after the start locator's, which `findFrom` alone did
not decide: it took the first occurrence *at or after* the start, so an end
locator that also matched at the start byte produced an empty span, and one
that occurred earlier in the file was silently ignored rather than refused.
Both changes are byte-neutral at every pin: all nine Web IDL end locators
occur exactly once and after their start, and no other standard authors a
rule row. -/
def scanRules (bs : ByteArray) (inputs : Array RuleInput) : Except String (Array Row) := Id.run do
  let blank := "\n\n".toUTF8
  let uncapped := bs.size + 1
  let mut out : Array Row := #[]
  for input in inputs do
    let pat := input.locator.toUTF8
    let hits := occurrences bs pat uncapped
    if hits.size != 1 then
      return .error s!"census: rule {input.name} locator occurs {hits.size} times, expected exactly one"
    let start := hits.getD 0 0
    let mut stop := 0
    match input.endLocator with
    | none =>
      stop := match findFrom bs blank start with
        | some n => n
        | none => bs.size
    | some endText =>
      let endHits := occurrences bs endText.toUTF8 uncapped
      if endHits.size != 1 then
        return .error
          s!"census: rule {input.name} end locator occurs {endHits.size} times, expected exactly one"
      let hit := endHits.getD 0 0
      if !Nat.blt start hit then
        return .error
          s!"census: rule {input.name} end locator occurs at byte {hit}, which is not after its start locator at byte {start}"
      stop := trimSpanEnd bs start hit
    out := out.push { kind := .rule, id := "rule." ++ kebab input.name,
                      anchorB := start, anchorE := start, spanB := start, spanE := stop }
  return .ok out

/-! ## Definition rows

A definition-keyed standard states almost everything as a `<dfn>` in a
paragraph rather than as an algorithm block: the Infra Standard has 178
definitions against 18 blocks at its pin. Every `<dfn>` that is not marked
`ignore` and is not an algorithm parameter (`for=list/slice`) becomes a row.
Its id follows the ladder `scanOps` uses: the `id` attribute, else the first
alternative of `lt`, else the text, the last two prefixed by the kebab-cased
first alternative of `for`. Its span is the enclosing algorithm block when
there is one; otherwise it runs from the enclosing `<p>`, `<dt>` or `<li>` to
the next blank line, and on through the numbered list that follows when the
paragraph ends in a colon, which is how the text writes an algorithm outside a
block ("if the following steps return true:"). Kind is `type` for the names
listed in the standard's `types.tsv` and `op` for every other definition;
an authored type name that matches no row fails generation. -/

/-- Text with every `<…>` tag removed. -/
def stripTags (text : String) : String := Id.run do
  let mut out : String := ""
  let mut depth : Nat := 0
  for c in text.toList do
    if c == '<' then depth := depth + 1
    else if c == '>' then depth := depth - 1
    else if depth == 0 then out := out.push c
  return out

/-- The largest element of the increasing array `xs` below `bound`. -/
private def lastBefore (xs : Array Nat) (bound : Nat) : Option Nat := Id.run do
  let mut best : Option Nat := none
  for x in xs do
    if x < bound then best := some x else break
  return best

/-- Whether the bytes `[b, e)`, after trailing whitespace and an optional
`</p>`, end in a colon. -/
def endsWithColon (bs : ByteArray) (b e : Nat) : Bool := Id.run do
  let mut i := e
  for _ in [0:e - b] do
    if i == b || !isSpaceByte (byteAt bs (i - 1)) then break
    i := i - 1
  if i ≥ b + 4 && matchesAt bs "</p>".toUTF8 (i - 4) then i := i - 4
  return i > b && byteAt bs (i - 1) == 0x3a

/-- The authored `types.tsv`: one kebab-cased row name per line. -/
def parseTypes (text : String) (path : String) : Except String (Array String) := Id.run do
  let mut out : Array String := #[]
  let mut lineNumber := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    let trimmed := Gates.Common.trimmed line
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    if out.contains trimmed then
      return .error s!"{path} line {lineNumber}: duplicate type name {trimmed}"
    out := out.push trimmed
  return .ok out

/-- Bikeshed writes a definition's type as a bare attribute on the `<dfn>` tag,
and a heading that is itself a definition carries the same marker. -/
def dfnTypeMarkers : Array String :=
  #["const", "attribute", "constructor", "exception", "interface", "dictionary",
    "enum", "typedef", "dfn"]

/-- The Bikeshed dfn type on the tag `[tagB, tagE)`, empty where none. The
Infra source carries none of these markers on any `<dfn>` and neither the
Streams nor the Infra source carries one on any heading, so reading the type
is byte-neutral for both. -/
def dfnTypeOf (bs : ByteArray) (tagB tagE : Nat) : String := Id.run do
  for marker in dfnTypeMarkers do
    if hasBareAttr bs tagB tagE marker then return marker
  return ""

/-- The dfn types that fold into an IDL-block statement row rather than
carrying a definition row of their own. -/
def foldedDfnTypes : Array String := #["const", "attribute", "constructor"]

/-- The dfn types that name a carrier rather than an operation. -/
def carrierDfnTypes : Array String :=
  #["exception", "interface", "dictionary", "enum", "typedef"]

private def lineStartAux (bs : ByteArray) (i : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    if i == 0 then 0
    else if byteAt bs (i - 1) == 0x0a then i
    else lineStartAux bs (i - 1) fuel

/-- The first byte of the line containing `i`. -/
def lineStart (bs : ByteArray) (i : Nat) : Nat := lineStartAux bs i (i + 1)

private def chunkStartAux (bs : ByteArray) (i : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    if i < 2 then 0
    else if byteAt bs (i - 1) == 0x0a && byteAt bs (i - 2) == 0x0a then i
    else chunkStartAux bs (i - 1) fuel

/-- The first byte of the blank-line-delimited chunk containing `i`. -/
def chunkStart (bs : ByteArray) (i : Nat) : Nat := chunkStartAux bs i (i + 1)

/-- Whether the line `[ls, le)` opens a Bikeshed markdown list item: its first
non-space bytes are `*`, `-` or `1.` followed by a space. -/
def isListItemLine (bs : ByteArray) (ls le : Nat) : Bool := Id.run do
  let t := trimSpanStart bs ls le
  if !Nat.blt t le then return false
  let c := byteAt bs t
  if (c == 0x2a || c == 0x2d) && byteAt bs (t + 1) == 0x20 then return true
  if c == 0x31 && byteAt bs (t + 1) == 0x2e && byteAt bs (t + 2) == 0x20 then return true
  return false

/-- The innermost enclosing `<tr>` … `</tr>` of `d`, when there is one. A row
element never nests, so the candidate is rejected when another `<tr` opener
lies inside it: the pinned Web IDL source leaves 32 `<tr>` unclosed outside
the census scope, and this is what keeps them from swallowing later
definitions. The Infra source has no `<tr>` at all. -/
def enclosingTableRow (trOpens trCloses : Array Nat) (d : Nat) : Option (Nat × Nat) := Id.run do
  let ti := firstIndexAfter trOpens d
  if ti == 0 then return none
  let tb := trOpens.getD (ti - 1) 0
  let ci := firstIndexAfter trCloses tb
  match trCloses[ci]? with
  | none => return none
  | some cv =>
    let te := cv + 5
    if !Nat.blt d te then return none
    if trOpens.any (fun o => Nat.blt tb o && Nat.blt o te) then return none
    return some (tb, te)

def scanDefinitions (bs : ByteArray) (typeNames : Array String) (typesPath : String)
    (blocks : Array (Nat × Nat)) (skipInBlocks : Bool) (scope : Option (Array Section)) :
    Except String (Array Row) := Id.run do
  let gt := ">".toUTF8
  let dfnClose := "</dfn>".toUTF8
  let blank := "\n\n".toUTF8
  let paragraphOpens :=
    (occurrences bs "<p>".toUTF8 4096 ++ occurrences bs "<p ".toUTF8 4096 ++
      occurrences bs "<dt>".toUTF8 4096 ++ occurrences bs "<li>".toUTF8 4096).qsort (· < ·)
  let olOpens := occurrences bs "<ol".toUTF8 4096
  let olCloses := occurrences bs "</ol>".toUTF8 4096
  let trOpens := occurrences bs "<tr".toUTF8 4096
  let trCloses := occurrences bs "</tr>".toUTF8 4096
  let mut out : Array Row := #[]
  let mut usedTypes : Array Nat := #[]
  for d in occurrences bs "<dfn".toUTF8 4096 do
    if !inScope? scope d then continue
    let some tagE := findFrom bs gt d
      | return .error s!"census: unterminated <dfn at byte {d}"
    if hasBareAttr bs d (tagE + 1) "ignore" then continue
    let forAttr := attrValue? bs d (tagE + 1) "for"
    if let some f := forAttr then
      if f.any (· == '/') then continue
    let dfnType := dfnTypeOf bs d (tagE + 1)
    if foldedDfnTypes.contains dfnType then continue
    let enclosingBlock := blocks.find? (fun (i, e) => i < d && d < e)
    -- Where algorithm rows are emitted, a definition inside a block is that
    -- block's own row and is not restated.
    if skipInBlocks && enclosingBlock.isSome then continue
    let owner := match forAttr with
      | some f => kebab (normalizeWhitespace ((f.splitOn ",").headD f)) ++ "-"
      | none => ""
    let mut name : String := ""
    match attrValue? bs d (tagE + 1) "id" with
    | some dfnId => name := kebab dfnId
    | none =>
      match attrValue? bs d (tagE + 1) "lt" with
      | some lt =>
        let head := (lt.splitOn "|").headD lt
        name := owner ++ kebab (normalizeWhitespace head)
      | none =>
        let some textE := findFrom bs dfnClose (tagE + 1)
          | return .error s!"census: unterminated <dfn> text at byte {d}"
        let some text := sliceString? bs (tagE + 1) textE
          | return .error s!"census: <dfn> text at byte {d} is not valid UTF-8"
        name := owner ++ kebab (normalizeWhitespace (stripTags text))
    if name.isEmpty then
      return .error s!"census: definition at byte {d} derived an empty name"
    -- Span, first match wins.
    let mut spanB := 0
    let mut spanE := 0
    match enclosingBlock with
    | some (i, e) =>
      spanB := i
      spanE := e
    | none =>
      match enclosingTableRow trOpens trCloses d with
      | some (tb, te) =>
        spanB := tb
        spanE := te
      | none =>
        let ls := lineStart bs d
        let le := lineEnd bs d
        if isListItemLine bs ls le then
          spanB := ls
          spanE := trimSpanEnd bs ls le
        else
          let some pb := lastBefore paragraphOpens d
            | return .error s!"census: definition at byte {d} has no enclosing paragraph"
          let cs := chunkStart bs d
          spanB := if Nat.ble cs pb then pb else cs
          let e0 := (findFrom bs blank d).getD bs.size
          spanE := e0
          if endsWithColon bs spanB e0 then
            -- 4a: a Bikeshed markdown list immediately after the chunk.
            let mut k := e0
            for _ in [e0:bs.size] do
              if Nat.blt k bs.size && isSpaceByte (byteAt bs k) then k := k + 1 else break
            let firstLine := lineStart bs k
            if Nat.blt e0 k && isListItemLine bs firstLine (lineEnd bs firstLine) then
              let mut cur := firstLine
              for _ in [0:4096] do
                let cle := lineEnd bs cur
                if !isListItemLine bs cur cle then break
                spanE := trimSpanEnd bs cur cle
                if !Nat.blt cle bs.size then break
                cur := cle + 1
            else
              -- 4b: the matching `</ol>` of the next `<ol` opener.
              let oi := firstIndexAfter olOpens (e0 - 1)
              match olOpens[oi]? with
              | none =>
                return .error s!"census: definition at byte {d} announces steps but no list follows"
              | some olStart =>
                let ci := firstIndexAfter olCloses olStart
                let some olEnd :=
                    matchCloseAux olOpens olCloses 5 (oi + 1) ci 0 (olOpens.size + olCloses.size + 1)
                  | return .error s!"census: unbalanced list after the definition at byte {d}"
                spanE := olEnd
    -- Kind.
    let mut kind := Kind.op
    if carrierDfnTypes.contains dfnType then
      kind := .type
    else
      match typeNames.findIdx? (· == name) with
      | some ti =>
        kind := .type
        usedTypes := usedTypes.push ti
      | none => pure ()
    out := out.push { kind := kind, id := kind.name ++ "." ++ name,
                      anchorB := spanB, anchorE := spanB, spanB := spanB, spanE := spanE }
  let mut unused : Array String := #[]
  for i in [0:typeNames.size] do
    unless usedTypes.contains i do
      unused := unused.push (typeNames.getD i "")
  unless unused.isEmpty do
    return .error s!"census: {typesPath} names {unused.size} type(s) that match no definition: {unused.toList}"
  return .ok out

/-- Ruling R-P4: Bikeshed lets a heading be a definition, written as a bare dfn
type on the heading tag (`<h4 id="idl-promise" … interface …>`). No heading of
the Streams or Infra source carries one, so this scanner is byte-neutral for
both. The span is the heading element. -/
def scanHeadingDefinitions (bs : ByteArray) (hs : Array Heading)
    (scope : Option (Array Section)) : Except String (Array Row) := Id.run do
  let gt := ">".toUTF8
  let mut out : Array Row := #[]
  for h in hs do
    if !inScope? scope h.off then continue
    let some tagE := findFrom bs gt h.off
      | return .error s!"census: unterminated heading tag at byte {h.off}"
    let marker := dfnTypeOf bs h.off (tagE + 1)
    if marker.isEmpty || foldedDfnTypes.contains marker then continue
    let closeTag := s!"</h{h.level}>".toUTF8
    let some closeAt := findFrom bs closeTag tagE
      | return .error s!"census: unterminated heading element at byte {h.off}"
    let kind : Kind := if carrierDfnTypes.contains marker then .type else .op
    let name := kebab h.id
    if name.isEmpty then
      return .error s!"census: heading definition at byte {h.off} derived an empty name"
    out := out.push { kind := kind, id := kind.name ++ "." ++ name,
                      anchorB := h.off, anchorE := h.off,
                      spanB := h.off, spanE := closeAt + closeTag.size }
  return .ok out

/-! ## The disposition join

`census/dispositions.tsv` is authored input seeded from the section table of
`SPEC-MANIFEST.md`: one line per `<section id>` TAB `<kind or *>` TAB
`<disposition>`. `census/overrides.tsv` is authored input for the rows a
section's own disposition does not describe: `<row id>` TAB `<disposition>`
TAB `<reason>`.

A row's disposition is resolved by taking its override if it has one, and
otherwise by walking its heading ancestry from the innermost `<h4>` outward to
the `<h2>`, at each level preferring a kind-specific line to the section's
wildcard line. A row that no line reaches fails generation: this generator
never invents a default. An authored line that no row uses also fails
generation, so an entry cannot outlive its reason. -/

structure DispositionRule where
  sectionId : String
  kind : Option Kind
  disposition : Disposition
  deriving Inhabited

structure OverrideRule where
  rowId : String
  disposition : Disposition
  reason : String
  deriving Inhabited

inductive JoinSource
  | fromOverride (index : Nat)
  | fromSection (index : Nat)
  deriving Inhabited

def parseDispositions (text : String) (path : String := dispositionsRelativePath) :
    Except String (Array DispositionRule) := Id.run do
  let mut out : Array DispositionRule := #[]
  let mut lineNumber := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    let trimmed := Gates.Common.trimmed line
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    match line.splitOn "\t" with
    | [sectionId, kindText, dispositionText] =>
      let kind ← if kindText == "*" then pure none else
        match Kind.ofString? kindText with
        | some k => pure (some k)
        | none => return .error s!"{path} line {lineNumber}: unknown kind {kindText}"
      let some disposition := Disposition.ofString? dispositionText
        | return .error s!"{path} line {lineNumber}: unknown disposition {dispositionText}"
      if sectionId.isEmpty then
        return .error s!"{path} line {lineNumber}: empty section id"
      if out.any (fun d => d.sectionId == sectionId && d.kind == kind) then
        return .error s!"{path} line {lineNumber}: duplicate entry for {sectionId} {kindText}"
      out := out.push { sectionId := sectionId, kind := kind, disposition := disposition }
    | _ =>
      return .error s!"{path} line {lineNumber}: expected three tab-separated fields"
  return .ok out

def parseOverrides (text : String) (path : String := overridesRelativePath) :
    Except String (Array OverrideRule) := Id.run do
  let mut out : Array OverrideRule := #[]
  let mut lineNumber := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    let trimmed := Gates.Common.trimmed line
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    match line.splitOn "\t" with
    | [rowId, dispositionText, reason] =>
      let some disposition := Disposition.ofString? dispositionText
        | return .error s!"{path} line {lineNumber}: unknown disposition {dispositionText}"
      if rowId.isEmpty || reason.isEmpty then
        return .error s!"{path} line {lineNumber}: empty field"
      if out.any (fun o => o.rowId == rowId) then
        return .error s!"{path} line {lineNumber}: duplicate override for {rowId}"
      out := out.push { rowId := rowId, disposition := disposition, reason := reason }
    | _ =>
      return .error s!"{path} line {lineNumber}: expected three tab-separated fields"
  return .ok out

/-- The disposition join over a heading ancestry given innermost first. -/
def resolveDispositionAncestry (rules : Array DispositionRule) (overrides : Array OverrideRule)
    (ancestry : Array String) (row : Row) : Option (Disposition × JoinSource) :=
  match overrides.findIdx? (fun o => o.rowId == row.id) with
  | some i => some ((overrides.getD i default).disposition, .fromOverride i)
  | none => Id.run do
    let mut found : Option (Disposition × JoinSource) := none
    for sectionId in ancestry do
      if sectionId.isEmpty then continue
      match rules.findIdx? (fun d => d.sectionId == sectionId && d.kind == some row.kind) with
      | some i =>
        found := some ((rules.getD i default).disposition, .fromSection i)
        break
      | none =>
        match rules.findIdx? (fun d => d.sectionId == sectionId && d.kind == none) with
        | some i =>
          found := some ((rules.getD i default).disposition, .fromSection i)
          break
        | none => pure ()
    return found

def resolveDisposition (rules : Array DispositionRule) (overrides : Array OverrideRule)
    (path : String × String × String) (row : Row) : Option (Disposition × JoinSource) :=
  let (h4, h3, h2) := path
  resolveDispositionAncestry rules overrides #[h4, h3, h2] row

/-! ## Escaping references

Ruling R-P6 gives each promise-lane census a `dependencies.tsv` and an
`externals.tsv` in the format the URL lane established: one line per row,
`<row id>` TAB `<comma-separated identities or `-`>`, and one `ext.` identity
per line. Both directions are checked: every row carries exactly one
dependency list, every named row exists, every identity resolves to a row of
this census, to a row of a named cross-census projection, or to a declared
external, and every declared external is used. -/

def parseExternals (text : String) (path : String) : Except String (Array String) := Id.run do
  let mut out : Array String := #[]
  let mut lineNumber := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    let trimmed := Gates.Common.trimmed line
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    unless trimmed.startsWith "ext." do
      return .error s!"{path} line {lineNumber}: external identity {trimmed} is not namespaced ext."
    if out.contains trimmed then
      return .error s!"{path} line {lineNumber}: duplicate external identity {trimmed}"
    out := out.push trimmed
  return .ok out

def parseDependencies (text : String) (path : String) :
    Except String (Array (String × Array String)) := Id.run do
  let mut out : Array (String × Array String) := #[]
  let mut lineNumber := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    let trimmed := Gates.Common.trimmed line
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    match line.splitOn "\t" with
    | [rowId, listText] =>
      if rowId.isEmpty || listText.isEmpty then
        return .error s!"{path} line {lineNumber}: empty field"
      if out.any (fun entry => entry.1 == rowId) then
        return .error s!"{path} line {lineNumber}: duplicate dependency list for {rowId}"
      let mut identities : Array String := #[]
      if listText != "-" then
        for piece in listText.splitOn "," do
          if piece.isEmpty then
            return .error s!"{path} line {lineNumber}: empty dependency identity"
          if piece == rowId then
            return .error s!"{path} line {lineNumber}: {rowId} depends on itself"
          if identities.contains piece then
            return .error s!"{path} line {lineNumber}: duplicate dependency {piece}"
          identities := identities.push piece
      out := out.push (rowId, identities)
    | _ => return .error s!"{path} line {lineNumber}: expected two tab-separated fields"
  return .ok out

/-- The row ids of a generated census projection, for the cross-census join. -/
def censusRowIds (text : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for line in Gates.Common.lines text do
    if line.isEmpty || line.startsWith "#" then continue
    match splitRow line with
    | .error _ => pure ()
    | .ok fields => out := out.push (fields.getD 1 "")
  return out

def checkDependencies (rows : Array Row) (deps : Array (String × Array String))
    (externals : Array String) (crossCensusIds : Array String)
    (depPath extPath : String) : Except String Unit := Id.run do
  let rowIds := rows.map (·.id)
  let mut missing : Array String := #[]
  for row in rows do
    unless deps.any (fun entry => entry.1 == row.id) do
      missing := missing.push row.id
  unless missing.isEmpty do
    return .error s!"{depPath}: {missing.size} row(s) carry no dependency list: {missing.toList}"
  let mut usedExternals : Array String := #[]
  for (rowId, identities) in deps do
    unless rowIds.contains rowId do
      return .error s!"{depPath}: {rowId} is not a row of this census"
    for identity in identities do
      if rowIds.contains identity then continue
      if crossCensusIds.contains identity then continue
      if externals.contains identity then
        unless usedExternals.contains identity do
          usedExternals := usedExternals.push identity
        continue
      return .error
        s!"{depPath}: {rowId} names {identity}, which is neither a row of this census, a row of a joined census, nor an identity declared in {extPath}"
  let mut unusedExternals : Array String := #[]
  for identity in externals do
    unless usedExternals.contains identity do
      unusedExternals := unusedExternals.push identity
  unless unusedExternals.isEmpty do
    return .error
      s!"{extPath}: {unusedExternals.size} declared identit(ies) no dependency uses: {unusedExternals.toList}"
  return .ok ()

/-! ## Rendering -/

/-- Bytes of the span that the row's one-line summary is taken from. -/
def summaryLimit : Nat := 200

def renderRow (bs : ByteArray) (row : Row) : Except String String := do
  let some anchor := sliceString? bs row.anchorB row.anchorE
    | .error s!"census: the anchor of {row.id} is not valid UTF-8"
  let digest := Gates.Sha256.hexDigest (bs.extract row.spanB row.spanE)
  let wanted := alignForward bs (row.spanB + summaryLimit)
  let stop := if Nat.ble row.spanE wanted then row.spanE else wanted
  let some raw := sliceString? bs row.spanB stop
    | .error s!"census: the summary of {row.id} is not valid UTF-8"
  let summary := normalizeWhitespace raw
  .ok s!"{row.kind.name}|{row.id}|{escapeField anchor}|{row.spanB}|{row.spanE}|{digest}|{escapeField summary}"

def censusHeader (std : Standard) (rowCount : Nat) : String :=
  s!"#census format={formatVersion} generator=Gates.Census input={std.inputRelativePath} " ++
  s!"input-sha256={std.inputDigest} rows={rowCount} regenerate={std.regenerateCommand}"

def renderCensus (std : Standard) (bs : ByteArray) (rows : Array Row) : Except String String := do
  let mut out := censusHeader std rows.size ++ "\n"
  for row in rows do
    out := out ++ (← renderRow bs row) ++ "\n"
  .ok out

def renderRowsModule (std : Standard) (entries : Array CoverageRow) (denominator : Nat) :
    String := Id.run do
  let assuranceDescription :=
    if std.key == "streams" then
      "This is the frozen row list of the specification-coverage numerator:\n" ++
      "one entry per census row, carrying the row id, the joined disposition, the\n" ++
      "coverage state, and the witness list. `WhatwgTest/Audit/SpecCoverage.lean`\n" ++
      "owns the checks over it and `docs/SPEC-COVERAGE.md` owns the rules.\n"
    else
      "This is an all-absent census scaffold, not a checked coverage numerator.\n" ++
      "One entry per census row carries its id and joined disposition, with no\n" ++
      "theorem witnesses. The census command checks projection drift; the Streams\n" ++
      "numerator does not validate this module. `docs/SPEC-COVERAGE.md` owns the rules.\n"
  let mut out :=
    "/-\nGENERATED FILE. Do not edit.\n\n" ++
    s!"Written by `{std.regenerateCommand}` (`Gates.Census`) from the pinned\n" ++
    s!"`{std.inputRelativePath}` (SHA-256 `{std.inputDigest}`), the census projection\n" ++
    s!"`{std.censusRelativePath}`, and the authored disposition inputs under `{std.authoredDir}/`.\n" ++
    "Format version " ++ formatVersion ++ s!". `{std.regenerateCommand.replace " --write" ""}` fails on any byte of drift.\n\n" ++
    assuranceDescription ++ "-/\n\n" ++
    "import Gates\n\n" ++
    s!"namespace {std.rowsNamespace}\n\n" ++
    "open Gates.Census\n\n" ++
    "/-- One entry per census row, sorted by kind then id, as the census is. -/\n" ++
    "def rows : Array CoverageRow := #[\n"
  let mut index := 0
  for entry in entries do
    let witnesses := "[]"
    let comma := if index + 1 == entries.size then "" else ","
    out := out ++
      s!"  ⟨\"{entry.id}\", .{entry.disposition.name}, .absent, {witnesses}⟩{comma}\n"
    index := index + 1
  out := out ++ "]\n\n" ++
    s!"/-- Total census rows. -/\ndef rowTotal : Nat := {entries.size}\n\n" ++
    s!"/-- Rows inside the coverage denominator. -/\ndef denominator : Nat := {denominator}\n\n" ++
    s!"end {std.rowsNamespace}\n"
  return out

/-! ## Building the census -/

structure Built where
  rows : Array Row
  dispositions : Array Disposition
  paths : Array (Array String)
  skippedIdl : Nat
  censusText : String
  rowsModuleText : String
  denominator : Nat
  deriving Inhabited

/-- Everything the generator reads from `census/<key>/`, plus the row ids of
any joined census. A standard that does not use a file receives the empty
string for it and never parses it. -/
structure AuthoredInputs where
  dispositions : String
  overrides : String
  rules : String
  types : String
  sections : String
  dependencies : String
  externals : String
  crossCensusRowIds : Array String
  deriving Inhabited

private def countKind (rows : Array Row) (k : Kind) : Nat :=
  rows.foldl (fun acc r => if r.kind == k then acc + 1 else acc) 0

private def countDisposition (ds : Array Disposition) (d : Disposition) : Nat :=
  ds.foldl (fun acc x => if x == d then acc + 1 else acc) 0

/-- The tail both profiles share: the authored rule rows, the sort, the
duplicate check, the anchor ladder, the section scope in both directions, the
disposition join, the escaping-reference join, and the two projections. Only
the row sourcing differs between the profiles.

`scope` is `none` for a whole-document standard and the resolved sections of
`sections.tsv` otherwise. `ancestryOf` gives the authored section keys that
govern a row whose span starts at the given byte, innermost first: heading ids
for a Bikeshed standard, enclosing clause ids for an ecmarkup one. -/
def finishBuild (std : Standard) (bs : ByteArray) (inputs : AuthoredInputs)
    (sourced : Array Row) (skippedIdl : Nat) (scope : Option (Array Section))
    (ancestryOf : Nat → Array String) : Except String Built := do
  let ruleInputs ← parseRules inputs.rules std.rulesRelativePath
  let rules ← scanRules bs ruleInputs
  let dispositionRules ← parseDispositions inputs.dispositions std.dispositionsRelativePath
  let overrides ← parseOverrides inputs.overrides std.overridesRelativePath
  let unsorted := sourced ++ rules
  let sorted := unsorted.qsort (fun a b => a.sortKey < b.sortKey)
  -- Ids are unique, so the sort is total and its result is deterministic.
  let mut duplicates : Array String := #[]
  for i in [1:sorted.size] do
    if (sorted.getD i default).id == (sorted.getD (i - 1) default).id then
      duplicates := duplicates.push (sorted.getD i default).id
  unless duplicates.isEmpty do
    .error s!"census: duplicate row id(s): {duplicates.toList}"
  -- Every row spans at least one byte (review debt D7, 2026-09-07). The
  -- ecmarkup scanner refuses a degenerate span at its source; the Bikeshed
  -- scanners did not, and neither did this tail, so an authored `rule` whose
  -- end locator sat on its start locator, or any scanner that emitted a
  -- zero-length span, would have been anchored, digested and rendered as the
  -- empty string with no refusal. The check is here rather than in one
  -- scanner because it is the property every row of every profile must have.
  -- It is byte-neutral at all four pins: the shortest landed span is eight
  -- bytes.
  let mut degenerate : Array String := #[]
  for row in sorted do
    unless Nat.blt row.spanB row.spanE do
      degenerate := degenerate.push s!"{row.id} at byte {row.spanB}"
  unless degenerate.isEmpty do
    .error s!"census: {degenerate.size} row(s) carry an empty span: {degenerate.toList}"
  -- Anchors.
  let mut anchored : Array Row := #[]
  for row in sorted do
    match chooseAnchorLength bs row.spanB with
    | .error rival =>
      .error s!"census: no unique anchor for {row.id}; its span at byte {row.spanB} is repeated at byte {rival}"
    | .ok len => anchored := anchored.push { row with anchorE := row.anchorB + len }
  -- The frozen section scope, in both directions.
  if let some sections := scope then
    let mut stray : Array String := #[]
    for row in anchored do
      unless inScope? scope row.spanB do
        stray := stray.push s!"{row.id} at byte {row.spanB}"
    unless stray.isEmpty do
      .error
        s!"census: {stray.size} row(s) land outside every section of {std.sectionsRelativePath}: {stray.toList}"
    let mut barren : Array String := #[]
    for sec in sections do
      unless anchored.any (fun r => Nat.ble sec.b r.spanB && !Nat.ble sec.e r.spanB) do
        barren := barren.push sec.id
    unless barren.isEmpty do
      .error s!"{std.sectionsRelativePath}: {barren.size} section(s) govern no row: {barren.toList}"
  -- Dispositions.
  let mut dispositions : Array Disposition := #[]
  let mut paths : Array (Array String) := #[]
  let mut usedRules : Array Nat := #[]
  let mut usedOverrides : Array Nat := #[]
  let mut unresolved : Array String := #[]
  for row in anchored do
    let path := ancestryOf row.spanB
    paths := paths.push path
    match resolveDispositionAncestry dispositionRules overrides path row with
    | none =>
      unresolved := unresolved.push s!"{row.id} (sections {path.toList})"
      dispositions := dispositions.push .owned
    | some (d, source) =>
      dispositions := dispositions.push d
      match source with
      | .fromOverride i => usedOverrides := usedOverrides.push i
      | .fromSection i => usedRules := usedRules.push i
  unless unresolved.isEmpty do
    .error s!"census: no disposition for {unresolved.size} row(s): {unresolved.toList}"
  let mut stale : Array String := #[]
  for i in [0:dispositionRules.size] do
    unless usedRules.contains i do
      let entry := dispositionRules.getD i default
      let kindText := match entry.kind with | none => "*" | some k => k.name
      stale := stale.push s!"{std.dispositionsRelativePath}: {entry.sectionId} {kindText} matches no row"
  for i in [0:overrides.size] do
    unless usedOverrides.contains i do
      stale := stale.push s!"{std.overridesRelativePath}: {(overrides.getD i default).rowId} matches no row"
  unless stale.isEmpty do
    .error s!"census: {stale.size} authored disposition entr(ies) outlived their rows: {stale.toList}"
  -- Escaping references (ruling R-P6), where the standard authors them.
  if std.authoredDependencies then
    let externals ← parseExternals inputs.externals std.externalsRelativePath
    let deps ← parseDependencies inputs.dependencies std.dependenciesRelativePath
    checkDependencies anchored deps externals inputs.crossCensusRowIds
      std.dependenciesRelativePath std.externalsRelativePath
  let denominator :=
    dispositions.foldl (fun acc d => if d.excluded then acc else acc + 1) 0
  let censusText ← renderCensus std bs anchored
  let mut coverageRows : Array CoverageRow := #[]
  for i in [0:anchored.size] do
    coverageRows := coverageRows.push
      { id := (anchored.getD i default).id, disposition := dispositions.getD i default,
        state := .absent, witnesses := [] }
  .ok { rows := anchored, dispositions := dispositions, paths := paths,
        skippedIdl := skippedIdl, censusText := censusText,
        rowsModuleText := renderRowsModule std coverageRows denominator,
        denominator := denominator }

/-- The Bikeshed half of `build`. -/
def buildBikeshed (std : Standard) (sw : Bikeshed) (bs : ByteArray) (inputs : AuthoredInputs) :
    Except String Built := do
  let headings ← scanHeadings bs sw.headingLevels
  let scope : Option (Array Section) ←
    if sw.sectionScope then do
      let ids ← parseSections inputs.sections std.sectionsRelativePath
      let sections ← sectionExtents bs headings ids std.sectionsRelativePath
      pure (some sections)
    else pure none
  let blocks ← algorithmBlocks bs
  let ops ← if sw.algorithmRows then scanOps bs blocks std.algorithmNameFirst scope else pure #[]
  let slots ← if sw.slotRows then scanSlots bs else pure #[]
  let (idl, skippedIdl) ←
    if sw.idlRows then scanIdl bs sw.idlOpeners scope else pure (#[], 0)
  let requirements ←
    match sw.requirementMarker with
    | some marker => scanRequirements bs marker ops
    | none => pure #[]
  let definitions ←
    if sw.definitionRows then do
      let types ←
        if std.authoredTypeNames then parseTypes inputs.types std.typesRelativePath else pure #[]
      let dfns ← scanDefinitions bs types std.typesRelativePath blocks sw.algorithmRows scope
      let headingDfns ← scanHeadingDefinitions bs headings scope
      pure (dfns ++ headingDfns)
    else pure #[]
  let sourced := ops ++ slots ++ idl ++ requirements ++ definitions
  finishBuild std bs inputs sourced skippedIdl scope
    (fun off => sectionAncestry headings sw.headingLevels off)

/-- The authored section keys of an ecmarkup row, innermost first: the ids of
every `<emu-clause>` whose span contains the row's span start, deepest first.
A primary clause row therefore resolves against its own clause id, and a
sub-row against the clause that encloses it, which is what section 8 of
`test/contracts/ecma262-census.contract.md` states. The containing clauses of a
point form a chain, so their depths are distinct and the order is total. -/
def clauseAncestry (clauses : Array Gates.Ecmarkup.Clause) (off : Nat) : Array String :=
  let containing := clauses.filter (fun c => Nat.ble c.b off && Nat.blt off c.e)
  (containing.qsort (fun a b => Nat.blt b.depth a.depth)).map (·.id)

/-- The ecmarkup half of `build` (ruling R-P1).

`sections.tsv` names the root clause ids; `Gates.Ecmarkup.rootWindow` is the one
function of that module that reads outside a window and it refuses a root id
that does not occur exactly once. `Gates.Ecmarkup.rows` gives each row a kind
spelling, an id and a half-open span, and everything after that — the anchor
ladder, the span digests, the excerpts, the disposition join and both
projections — is `finishBuild`, exactly the path the Bikeshed standards take. -/
def buildEcmarkup (std : Standard) (bs : ByteArray) (inputs : AuthoredInputs) :
    Except String Built := do
  let sectionIds ← parseSections inputs.sections std.sectionsRelativePath
  let mut windows : Array (Nat × Nat) := #[]
  let mut sections : Array Section := #[]
  for clauseId in sectionIds do
    let (b, e) ← Gates.Ecmarkup.rootWindow bs clauseId
    windows := windows.push (b, e)
    sections := sections.push { id := clauseId, b := b, e := e }
  let specs ← Gates.Ecmarkup.rows bs windows
  let mut rows : Array Row := #[]
  for spec in specs do
    let some kind := Kind.ofString? spec.kind
      | .error s!"census: the ecmarkup scanner produced the unknown kind {spec.kind}"
    rows := rows.push
      { kind := kind, id := spec.id, anchorB := spec.b, anchorE := spec.b,
        spanB := spec.b, spanE := spec.e }
  let mut clauses : Array Gates.Ecmarkup.Clause := #[]
  for (b, e) in windows do
    clauses := clauses ++ (← Gates.Ecmarkup.scanClauses bs b e)
  finishBuild std bs inputs rows 0 (some sections) (fun off => clauseAncestry clauses off)

/-- The profile dispatch (ruling R-P1). -/
def build (std : Standard) (bs : ByteArray) (inputs : AuthoredInputs) : Except String Built :=
  match std.profile with
  | .bikeshed switches => buildBikeshed std switches bs inputs
  | .ecmarkup => buildEcmarkup std bs inputs

/-! ## Reading the pinned input -/

def readPinnedInput (root : System.FilePath) (std : Standard) : IO (Except String ByteArray) := do
  let path := root / std.inputRelativePath
  unless ← path.pathExists do
    return .error s!"census: the pinned specification source is missing: {std.inputRelativePath}"
  let bytes ← IO.FS.readBinFile path
  let observed := Gates.Sha256.hexDigest bytes
  if observed != std.inputDigest then
    return .error
      s!"census: refusing bytes that are not the pin; {std.inputRelativePath} has SHA-256 {observed}, expected {std.inputDigest}"
  return .ok bytes

/-- The authored inputs the standard declares. Every one it declares is
required; one it does not declare is never read. -/
def readAuthored (root : System.FilePath) (std : Standard) :
    IO (Except String AuthoredInputs) := do
  let readRequired (relative : String) : IO (Except String String) := do
    let path := root / relative
    unless ← path.pathExists do
      return .error s!"census: missing authored input {relative}"
    return .ok (← IO.FS.readFile path)
  let sectionScope :=
    match std.profile with
    | .bikeshed switches => switches.sectionScope
    | .ecmarkup => true
  let mut texts : Array String := #[]
  let mut wanted := [std.dispositionsRelativePath, std.overridesRelativePath, std.rulesRelativePath]
  if std.authoredTypeNames then wanted := wanted ++ [std.typesRelativePath]
  if sectionScope then wanted := wanted ++ [std.sectionsRelativePath]
  if std.authoredDependencies then
    wanted := wanted ++ [std.dependenciesRelativePath, std.externalsRelativePath]
  for relative in wanted do
    match ← readRequired relative with
    | .error message => return .error message
    | .ok text => texts := texts.push text
  let mut index := 3
  let mut typesText := ""
  if std.authoredTypeNames then
    typesText := texts.getD index ""
    index := index + 1
  let mut sectionsText := ""
  if sectionScope then
    sectionsText := texts.getD index ""
    index := index + 1
  let mut dependenciesText := ""
  let mut externalsText := ""
  if std.authoredDependencies then
    dependenciesText := texts.getD index ""
    externalsText := texts.getD (index + 1) ""
  let mut crossCensusRowIds : Array String := #[]
  for relative in std.crossCensusPaths do
    let path := root / relative
    unless ← path.pathExists do
      return .error s!"census: missing joined census projection {relative}"
    crossCensusRowIds := crossCensusRowIds ++ censusRowIds (← IO.FS.readFile path)
  return .ok
    { dispositions := texts.getD 0 "", overrides := texts.getD 1 "", rules := texts.getD 2 "",
      types := typesText, sections := sectionsText,
      dependencies := dependenciesText, externals := externalsText,
      crossCensusRowIds := crossCensusRowIds }

def buildFromRoot (root : System.FilePath) (std : Standard) :
    IO (Except String (ByteArray × Built)) := do
  match ← readPinnedInput root std with
  | .error message => return .error message
  | .ok bytes =>
    match ← readAuthored root std with
    | .error message => return .error message
    | .ok inputs =>
      match build std bytes inputs with
      | .error message => return .error message
      | .ok built => return .ok (bytes, built)

/-! ## Commands -/

def summaryLine (built : Built) : String := Id.run do
  let mut kinds : Array String := #[]
  for k in Kind.all do
    kinds := kinds.push s!"{k.name} {countKind built.rows k}"
  let mut dispositionCounts : Array String := #[]
  for d in Disposition.all do
    dispositionCounts := dispositionCounts.push s!"{d.name} {countDisposition built.dispositions d}"
  let excluded := built.rows.size - built.denominator
  let text :=
    s!"census: {built.rows.size} rows ({String.intercalate ", " kinds.toList}); " ++
    s!"dispositions ({String.intercalate ", " dispositionCounts.toList}); " ++
    s!"denominator {built.denominator}, excluded {excluded}; " ++
    s!"{built.skippedIdl} IDL statement(s) outside the row vocabulary"
  return text

def write (root : System.FilePath) (std : Standard) : IO UInt32 := do
  match ← buildFromRoot root std with
  | .error message =>
    IO.eprintln s!"FAIL {message}"
    return 1
  | .ok (_, built) =>
    IO.FS.createDirAll (root / "generated")
    if let some parent := (root / std.rowsRelativePath).parent then
      IO.FS.createDirAll parent
    IO.FS.writeBinFile (root / std.censusRelativePath) built.censusText.toUTF8
    IO.FS.writeBinFile (root / std.rowsRelativePath) built.rowsModuleText.toUTF8
    IO.println (summaryLine built)
    IO.println s!"WROTE {std.censusRelativePath}"
    IO.println s!"WROTE {std.rowsRelativePath}"
    return 0

/-- Independent verification of one on-disk census line against the pinned
bytes: the anchor must occur exactly once, at the recorded span start, and the
digest of the recorded span must match. This path never consults the scanner,
so it fails on a hand-edited row as well as on a scanner change. -/
def verifyLine (bs : ByteArray) (line : String) (lineNumber : Nat) : Except String Unit := do
  let fields ← splitRow line
  if fields.size != 7 then
    .error s!"census line {lineNumber}: expected seven fields, found {fields.size}"
  let kindText := fields.getD 0 ""
  let rowId := fields.getD 1 ""
  let anchor := fields.getD 2 ""
  let some _ := Kind.ofString? kindText
    | .error s!"census line {lineNumber}: unknown kind {kindText}"
  let some spanB := (fields.getD 3 "").toNat?
    | .error s!"census line {lineNumber} ({rowId}): malformed span start"
  let some spanE := (fields.getD 4 "").toNat?
    | .error s!"census line {lineNumber} ({rowId}): malformed span end"
  let recorded := fields.getD 5 ""
  if !Nat.ble spanB spanE || !Nat.ble spanE bs.size then
    .error s!"census line {lineNumber} ({rowId}): span [{spanB}, {spanE}) is not inside the pinned bytes"
  let anchorBytes := anchor.toUTF8
  let hits := occurrences bs anchorBytes 4
  if hits.size != 1 then
    .error s!"census line {lineNumber} ({rowId}): anchor occurs {hits.size} time(s), expected exactly one"
  if hits.getD 0 0 != spanB then
    .error s!"census line {lineNumber} ({rowId}): anchor occurs at byte {hits.getD 0 0} but the span starts at {spanB}"
  let observed := Gates.Sha256.hexDigest (bs.extract spanB spanE)
  if observed != recorded then
    .error s!"census line {lineNumber} ({rowId}): span digest {observed} does not match the recorded {recorded}"
  .ok ()

/-- The numerator's emit against a fresh census regeneration. The census owns
row ids, their order, and dispositions; the numerator owns coverage states and
witnesses. This checks the first three in both directions and the two rules
`docs/SPEC-COVERAGE.md` states about the last two: an empty witness list is
allowed only with `absent`, and a row outside the denominator carries no
witness. -/
def verifyEmit (built : Built) (emit : Array CoverageRow) : Array String := Id.run do
  let mut failures : Array String := #[]
  if emit.size != built.rows.size then
    failures := failures.push
      s!"the coverage emit holds {emit.size} rows; a fresh regeneration of {censusRelativePath} holds {built.rows.size}"
    return failures
  for i in [0:built.rows.size] do
    let row := built.rows.getD i default
    let entry := emit.getD i default
    let disposition := built.dispositions.getD i default
    if entry.id != row.id then
      failures := failures.push
        s!"coverage emit row {i} is {entry.id}; the regenerated census row is {row.id}"
    else if entry.disposition != disposition then
      failures := failures.push
        s!"coverage emit row {entry.id} carries disposition {entry.disposition.name}; the regenerated disposition join gives {disposition.name}"
    else if entry.state == CoverageState.absent then
      unless entry.witnesses.isEmpty do
        failures := failures.push
          s!"coverage emit row {entry.id} is absent yet carries witnesses {entry.witnesses}"
    else
      if entry.witnesses.isEmpty then
        failures := failures.push
          s!"coverage emit row {entry.id} is {entry.state.name} with no witness"
      if disposition.excluded then
        failures := failures.push
          s!"coverage emit row {entry.id} is {entry.state.name}, but its disposition {disposition.name} is outside the denominator"
  return failures

/-- `emit?` is the numerator's coverage emit where the standard has a
numerator (Streams), and `none` where it has none yet (Infra); the emit
checks are skipped in the second case and the PASS line says so. -/
def check (root : System.FilePath) (std : Standard) (emit? : Option (Array CoverageRow)) :
    IO UInt32 := do
  match ← buildFromRoot root std with
  | .error message =>
    IO.eprintln s!"FAIL {message}"
    return 1
  | .ok (bytes, built) =>
    let mut failures : Array String := #[]
    let censusPath := root / std.censusRelativePath
    let rowsPath := root / std.rowsRelativePath
    let regenerate := std.regenerateCommand
    let mut onDisk : String := ""
    if ← censusPath.pathExists then
      onDisk ← IO.FS.readFile censusPath
      if onDisk.toUTF8 != built.censusText.toUTF8 then
        failures := failures.push
          s!"{std.censusRelativePath} is not byte-identical to a fresh regeneration; run `{regenerate}`"
    else
      failures := failures.push s!"missing {std.censusRelativePath}; run `{regenerate}`"
    if ← rowsPath.pathExists then
      let rowsOnDisk ← IO.FS.readFile rowsPath
      if rowsOnDisk.toUTF8 != built.rowsModuleText.toUTF8 then
        failures := failures.push
          s!"{std.rowsRelativePath} is not byte-identical to a fresh regeneration; run `{regenerate}`"
    else
      failures := failures.push s!"missing {std.rowsRelativePath}; run `{regenerate}`"
    -- Independent re-verification of every on-disk row.
    let allLines := Gates.Common.lines onDisk
    let expectedHeader := censusHeader std built.rows.size
    match allLines with
    | [] => failures := failures.push s!"{std.censusRelativePath} is empty"
    | header :: dataLines =>
      if header != expectedHeader then
        failures := failures.push s!"{std.censusRelativePath} header line does not match the generator identity"
      let mut lineNumber := 1
      for line in dataLines do
        lineNumber := lineNumber + 1
        match verifyLine bytes line lineNumber with
        | .ok _ => pure ()
        | .error message => failures := failures.push message
      if dataLines.length != built.rows.size then
        failures := failures.push
          s!"{std.censusRelativePath} carries {dataLines.length} rows; the generator produced {built.rows.size}"
    if let some emit := emit? then
      for failure in verifyEmit built emit do
        failures := failures.push failure
    if failures.isEmpty then
      IO.println (summaryLine built)
      let emitClause := match emit? with
        | some _ => ", and the coverage emit agrees with that regeneration row for row"
        | none => "; no numerator exists for this standard yet, so no emit was checked"
      IO.println
        s!"PASS census ({std.key}): input digest is the pin, every anchor occurs exactly once at its span start, every span digest recomputes, every row has exactly one disposition, both projections are byte-identical to a fresh regeneration{emitClause}"
      return 0
    IO.eprintln s!"FAIL census ({std.key}): {failures.size} problem(s)"
    for failure in failures do IO.eprintln s!"  {failure}"
    return 1

/-- The coverage block of `docs/SPEC-COVERAGE.md`.

The denominator, the row total and the exclusions come from a fresh census
regeneration; every coverage state and witness comes from the numerator's
`emit`, which `verifyEmit` first checks against that regeneration. Nothing
here assumes a state: with the P3 witnesses landed, `green` and `partial` are
counted, and a disagreement between the two sides is a failure rather than a
printed number. -/
def report (root : System.FilePath) (std : Standard) (emit : Array CoverageRow) : IO UInt32 := do
  match ← buildFromRoot root std with
  | .error message =>
    IO.eprintln s!"FAIL {message}"
    return 1
  | .ok (_, built) =>
    let failures := verifyEmit built emit
    unless failures.isEmpty do
      IO.eprintln s!"FAIL census report: {failures.size} problem(s) between the coverage emit and the census"
      for failure in failures do IO.eprintln s!"  {failure}"
      return 1
    let total := built.rows.size
    let denominator := built.denominator
    let excluded := total - denominator
    let green :=
      emit.foldl (fun acc row => if row.state == CoverageState.green then acc + 1 else acc) 0
    let partialCount :=
      emit.foldl (fun acc row => if row.state == CoverageState.partialCoverage then acc + 1 else acc) 0
    let absent := denominator - green - partialCount
    let ownedWithGreen :=
      emit.foldl
        (fun acc row =>
          if row.disposition == Disposition.owned && row.state == CoverageState.green then acc + 1
          else acc)
        0
    let partialIds :=
      (emit.filter (fun row => row.state == CoverageState.partialCoverage)).map (fun row => row.id)
    let sortedIds := partialIds.qsort (fun a b => a < b)
    IO.println
      s!"{std.label} coverage: denominator {denominator}; owned-with-green {ownedWithGreen}/{denominator};"
    IO.println
      s!"green {green}, partial {partialCount}, absent {absent}; census {total} rows, {excluded} excluded"
    if sortedIds.isEmpty then
      IO.println "partial:"
    else
      IO.println s!"partial: {String.intercalate " " sortedIds.toList}"
    return 0

def usage : String :=
  "usage: lake exe census [--standard <key>]           check the census against the pinned specification bytes\n" ++
  "       lake exe census [--standard <key>] --write   regenerate the census and the frozen coverage row list\n" ++
  "       lake exe census [--standard <key>] --report  print the coverage block of docs/SPEC-COVERAGE.md\n" ++
  "keys: " ++ String.intercalate ", " (standards.map (·.key)) ++ " (default streams)"

/-- Command-line entry, invoked by `bin/Census.lean`, which supplies one
coverage emit per standard that has a numerator, keyed by `Standard.key`.

Section 6.2 of `test/contracts/webidl-census-q2.contract.md` freezes the map
shape rather than one `Option` argument per standard: the number of standards
is already four and ruling R-P6 leaves the door open for more, an association
list adds no case analysis at any call site, and a per-standard parameter would
enter a signature whose only caller is `bin/Census.lean`.

`--write` does not take an emit: regenerating a census must stay possible while
a numerator is red. A standard the map does not name (Infra today) is checked
without an emit, its PASS line says so, and its `--report` refuses with exit 2 —
that refusal is the record that Infra has no numerator, and inventing an empty
emit to make every standard reportable is a defect. -/
def cli (emits : List (String × Array CoverageRow)) (args : List String) : IO UInt32 := do
  let root ← Gates.Common.projectRoot
  let (std?, rest) := match args with
    | "--standard" :: key :: rest => (Standard.ofKey? key, rest)
    | _ => (some streams, args)
  let some std := std?
    | IO.eprintln usage
      return 2
  let emit? := (emits.find? (fun pair => pair.1 == std.key)).map (·.2)
  match rest with
  | [] => check root std emit?
  | ["--write"] => write root std
  | ["--report"] =>
    match emit? with
    | some e => report root std e
    | none =>
      IO.eprintln s!"census: no coverage numerator exists for {std.key}, so there is no report yet"
      return 2
  | _ =>
    IO.eprintln usage
    return 2

end Gates.Census
